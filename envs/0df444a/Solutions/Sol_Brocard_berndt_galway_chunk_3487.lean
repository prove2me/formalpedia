-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:48:25.70475+00:00
-- url     : https://prove2.me/submissions/f2f385f2-ccbc-4ad3-9799-372dcbc25bb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626978417 ≤ n < 627158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626979667 1250 626978417 626978453
    0xf0711070902030a060504051815041112160909030c08070c0e010b0301181e0b01140a02060604060f03050d03020307210b01180f050d0828020d0504060804 68
    0x400101081110807400554013500c001100802d0050501007004244c0301c00508a28424600030440b2504500009030300c2440d49101c0d40040340c42e25507080c2204220b07102c2c015070b60400a070b043e107180c3c040400500d0840d0700c110000c143e140795840d000e680d003e440304e078480500007401055000d40403035800402031a003988108000a8a60b984880240d40800241c1c02807400c1c0314040010480d01c184c020004840b800920010403494401c2e803c20b000c0c01288401021044d603549070504079503401070f08000a034800141c03210340c81c0e42d44298025a2079004032020742c0221700b01900051325580c168134090a603644a0702400024004013012002500014011002c0109502606511800303200086184000303d000110b964040c2c90b001500043d00e440100928076041c68080151403811403029040d24000ca92000c0f0503840c50400350000d000c0e015624040c0b01020001890016019073360740d10311141c1e81c081d940c20b40509681681c542c0a10310601001c10310081c002000600c0c09440d401c0341c40d003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626980917 1250 626979667 626979673
    0x607082e08011811010206060a14012109051506060f130f180c0e060f0901110f0c10030e0304090c020f0105010f060e0f0d0b041509030509040c0302030f0711 69
    0x180d00c05000b825034200b2800d8a41c0d04508400503410b021120044c1d5011900a000070240d50074080d000c95170b601c040d8442c0303608080712441080d01c142c2c0324524569031004103c05103088003200d040c0312402000034010890340b6120b40300300c20311804003603030304c440c440d001c0140140d081800010b4495040e40c45030061405144400340b0228102010070100b2014040d8024541c0c4680451502c01084032032603171107402030115200429225a403410109d50b584202160015142e0b810400141e4000040111400d5103000b540340f0809039490010302001d03650402c0394100100c01c03428405030100c864500f1100450f030030030441880b0a1309550494908510f0340c2c0b04607815856118692421103a0a802502002c9c655010800009074000ca0041601d202194080280800c10000800a0403808801001d07090702000203400c0c002e6004c5006103c0034160014880d5292620b80145143d215411552040380790400c240011803283c401e4a11460b01030a4209040c1c903285416614640148400302282c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626982167 1250 626980917 626980919
    0xc0f18060a030c03031701050303072001050d050109050403140a08040b0c0906070b15010e0901180204030503130303201b0301060f0608040507050907050a0c150501170607082e 77
    0x8500c41d183c400158041d9549182050040c8400d403245501a03100300d00c2a4024410100825003151407402c030040400c007031800d890344107401607401d40508249080142c0c40c02000191090040e0441340c411446641c80709407030301d4265001a00350003172079000300010b0004400038002500840703c0700e0b0081105ca2055041001d84000240c9a51182408070341c0c42c40c8460502c1681000c4d0780984040b882c1c2400e04146c4d00c030313540e40400c14000c0c0c1403080700300e41030440302029807001d140d904030f0b00516004000e0fa0f681c1c858459031011040c0341da210032070009450755480140000202d41c07021405041c5805804001c00301e00c1e04100c0d40c000343d45000c0e85556a0440002c400c119500c066009101a444e003811526141c10001e051403140d0303004501811242c1d0400c002c1d10350140840e12404c0032803d041441c03240a0410061a80a601ca9810120300d01b40011401d403a25030100820013075801c007101c1c4076903103010040f202c0100c20341d2800d02f021500f120207088503100441019111030041c502c0c032001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626983417 1250 626982167 626982173
    0x40c0e09030f0703031d030903100213170304060906050f07030e04110406030608190507060c05030702040f02070b161b260909010b030f07030f090209010f080c0f18060a03 75
    0x1e9111031404c0f00800e03680d54040b010016811200c2d590510000091410100c00d000441e03101e18441540f840050b50020305802184081d90203403001d40090707180412143c4c402100c1517030303a41c094069603020400c6410002050fa00ca0011100112000145541000c1305941d064400c00440034032240c2c80341d215190780954030a684007400042c440e6990100d0018a41410503003049400040400b42201c80d445007800314030002118002c41d6090302d44610343c0b041c141080307402d42c010032800035841070408159079001043d640142045a002e41c0048000380c441410101c0d0144076000800007107805030803201c14020060002280c980d025840307014809044044190303009600f020001e441407404501101c080c00e04904075400340201c0241c151660130011642048080000d107041d0425840d00402c9041c017901360403000304180d01600c01348280d619491880340001041c0030700c0e9924402e483c0e403902d443ca00490102c921000c0580424155460300703010414002000342082e0f0400c0150f6400000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626984667 1250 626983417 626983447
    0x506030703090213062904050f0a030b0403020d030605030c01090b0a1709061b040e132109060201110a081302120f01151211040e121605060609040c0e0903 68
    0x3c42070000000980282411b840c980144808001210040070700a2000d210550500440b410b6407412101507042c090300300001111650a500000c00f01c2c100903003072100b00b5400240d00040d90303040d03450500c5101c0d124000c4c10f07540d8a2000c90103002514a9000300410000b0b500104270319107091601c09000742a9034000171034050143c601c00c0095010004112000303c4c0d040d1026801e8400c3e4041c00d1400d032130700f040c650019001038103000110b14522140800c100c1044142c1400d080022240034010f200c54a0161000520340720f01e2001d0350038442012100b035400400c82d00c036062551602000ba403981484540c41d000c45640880e000300c0030014039104410104a0b10180341c0c8814000710701c0d4851140070100c030b40328a60040900d00300015103407000441c10120405142015200020380031200701d442d0303103046103aa00d000394050b400114642c080555450010029026800f1a4842e4440a081c80a0807800300c034040c00340c0d01c00c05018000140e030b984005030000032074012241460090421044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626985917 1250 626984667 626984689
    0xf090414011d0a020a120c17010b120d08010602060c04090905030702030111040314070302090403080a0b100e030f12030402150408070605030402091503030a0e0102010e06070822030905060307030902 87
    0xd41a4451103205045181c018911300281c460070708000040912680c401f082ca0801c4d000b00c20740340fa00e0f051001c01e003000960150004100090113400101e84603108a070710b402c00840e8050000d0403444c000f04540d80001074180c02038030050f0070189800e02c1c0031207842c0244070141044549001c00c00544015136801d009811b0380d100404d41c11a600e926514202003107103030075600d00c0e000350090b600400140c1e817000b03500c1d030740150141000c6500c2d91b64007a80b040201704607030500354007180f61040c8009041c3e1040703e09292840940880c1c0060040d01007065030b0348440300c1d86440030a0b00300f000600604014426841140c01e0041450034a5181d6a104d4184200c6401820004001000b00000d40ca818020f00703800c5a0880401c40e1121400d0000c603440307120300c610003001d000c02451600c0080e4800d5201d00d050302031030029031f403103030401080007020140d0503904684401049072840d03550909103044070034420781c15110f1050f054600300600802d84c000a0441c4117040e910001032000d61200e41c1100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626987167 1250 626985917 626985971
    0x60a020d020f0d0909090212060403031d1501060f050409020301080307030f0f020601260703050109062016080415030c080907050a030206181905040b0f09041401 71
    0x1011440034031800030718100c1c1d1034441a0035503110f40120072440350084404c106a809841000c5a180344500105144804488c0502003e03c070701800c000506a16030701007005006100d07095500e80c00c1c0c000b146969400160f00e280701e0403100030f0042101c140101588010800682403c4d414030303030b40342d1214003207800903031189409400000b4020101540010900908140703800c049980001489009548400c14002d0b00d0190141c05400590001070409405805116400300c0da400c589078500343e4043c1c44805c400715030f90350905903080c48a400250251952904414040d42805001070055600300d00b0410213581c420010400841d0f00d09030121300c0c850340308041d2004506d20030f41e410000c0c03000c3e0009140045540092000f03101300c3e903488280000301c0b40c04880342516182c0300d982100d5001210b907051036201240e50440d4411401682e1011b04490382224100451825103003400101001c20500c142d0043c030f5100018005a88600d003840c408420800019001c4007508440c00b05100070f01d050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626988417 1250 626987167 626987173
    0xc0a12110c061c0c03060b070c09050f0c0a05070213060303020a0506090c0a09020d020d140109063f0c17070b04080a2004061211041413020609060a02 66
    0x155041401005121441c0005564603442c0440000400391050390b400d041c100f400d510b8003036120b840c40c4a0341005c40a80244003c4c596107400c10329094003400828821200d0302d40c06c02001030204081554401e100c0c0c2200a1810305e000300c108800c0718030354402d5600b00d0380040c1c40c80c00d07803a1524891003000e000c2c612a4000700303126074050802c00c3c6000401080603500743e01404054001e134071940d05060407600c141b41e0140c3c4495030b040d1110040c1c0207540b400c415203490801b10307141500e50581c8907412288054002c12a050300c1e000e01c10081196500130f0500820a002c1c10b4511440d1003900c0700c140c142d0f00540030f100503055a641404c82c000e55210491b04003a180302d2446807002441240010480307a00c40c146020719200702c007525100075000240c050715000403548603105020004d446010300c0100b0401c1056240c8034859814911054184c66540942c0d0040d42641081e11440f10080501c00c20b0004503603450266044c9101c5070141203800c84000e000010361500d8040151207580340760703009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626989667 1250 626988417 626988437
    0x504080a0f0b060901241e0e0a0801050f06130207060606031b0318020607031101050103081b0604020a050411210106020c010915120e0a0b07090611060604020c0a12 72
    0x905048001030a0580302d0910f0400400110301b291585405000001308002c1d1999528042554010040b01c103040032601c84e6071900c0d81f51540000c8441041130219030008800f07485210b0030342210811140785450b001e03500e0108140d458080b01042030a0005140940f8043d40b035a520025034005070301280129131180c0781e000206c003031070f0300c000c560840c0c0d0b01d000c000e00d52013540405101041c0c100041c0c0981c200103041d1040c0b610070511450504481c00c024051542d41e443c0070341703081e40003002d041d2040c0d80602c400824041c000c10701600640d0000c0040c100c4a042500304802420009204222000c0800c9040c000c80d4250020840d4902c2d2103401002c0b80d850314802904201146001e07904100740d0030001d101c9030010802e1501504400c2c600354040d59403280303900d0001c100715451041c1d00e10403a2545003c0080e220340403441900d0a82d80c0c081d200d07036560b01c150340b5518400c41c00700d0150801e1000590605003a8041d0641983c41e13800c4901c821059103070380810030808511a0002030b60484 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626990917 1250 626989667 626989673
    0x18210c0406080a11060918090604061d0c040b0619201507080a0b1203070311032a0a0b100e0105092401022e0e24070504080a0f 56
    0x200715402480103402404400c4103d81c1d50f1150308070380c240024440c407000304000495440d59402c40031046442e05110f282c45c20304080c44c6640d144100d070102d50b82410904049180200521000d800c01550b000405a41e8203034400c00002d45582d024231a0000c1003440014440184000d202c07009030b0380380d01c030420f000c84001a0381e0240c1d40e00c6000c0d034610794880f0704003000c2d640300d12001e10751002c03440c81c00d82030b1919060780c407c02418010800c0c80d40580d0001d03505020010200042a503544643c844081e10390b66840350342c1e00c80c0503d8956040706580481c0c0c19854001c8800c039084c80e00e0b100419510b0300e00499844041d85c04c0b0540307500c0c101196500d403c2c0000340403201121f0141c841100c0c482518034003021100001c07524180c040c07402100c1181c024040d64000c000724480498a9074001065801c5009000d0300801c43e007004000c010706080c0c0c400141c08002c40c24850280348071004104524080c0d100c070840040184c2400100402044001080641400703900c2d030541c030601342c002007044641 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626992167 1250 626990917 626990921
    0x70c0615030302150601020a080d1107200904150905030417010e30090409020d03120c050705030304080307110d0f0923040f0b0301230c070818210c04 66
    0x4a54840308130600107000385a80c00080300303001203034001c44050303036003451200e004081d20b10f800710810041c41c0031030702c0001c00c10300074004001d441c0a00d22420b038808800741042910702c81980c0141c1500c0134000b03000c5c1d4041142d00188101c0f0f004608407854150703216120b1899909d245081d0005941d1420301102411040c40070301c4d0314100100305440c00000c0183c010044403d100c0d030305111500c000820079260b0701c40c4c1e007020f001c0f160001d001d80030810050802800c8a00f0860511028600d05141c5c1c2c150f05004a00b0365454980080c0154216a5180c2c1c030310596601c09042c4d081441441d0301940741c07111080042c2c400c1882c1c00e6942020000c12080054010780c0b042d08000f40c21485008025003e841168450313000040031500030480d48030785011540100203400c031694047d420004003d0b0300c24040040700340d820920700700d0302d81d00d0365030288035220340c4c05008001405158204080c82081a03005901c08003090f00034101c0d41007005d103002001189905140240443d00080c50380c14051a20b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626993417 1250 626992167 626992183
    0x7032f030f0f0114190b131e03051f110705011e09080702040b010905040207140f0111040e070504090507031d0304081906021324050a0c0803070c0615030302 69
    0x50b403181d0380d09504200d0311001c1251607202503030140c2c3d4030003107410040b02080039407001481100611a039601c00c0103c00052401c89003d01c024206120341e00c84106d013030f500302c0b607003c0707a402c00060000e9580d24101d15a9400454900003010303900d03007000044251206004042c170340e100e2400000d03591924030020640807111520280142d10f40741d090f10101d10b0000841d120580d04540014035500840d005036400c1a5a810003900140301044440811420315031380032059000e00c08469846508505079800d0f120080760f0300c014000180004c00034143c960f84415044007040c00d10600f13150300d41801e00100c41c1c0440d42000000c0c0c444035448001900d00064045880600005c0e625260030452425038440c0c0f0b4240124075083c1d00400711080c80000c0e810784400760188a070044140b40d585004404070f242021f540e440f40c400e040101307007c66028034201c034004961601c44031661101c0f5206c0d411540c200074038001c140307e045240180000c0d81c5101c0d0003d00e582c4144030989090031070500900d08900c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626994667 1250 626993417 626993431
    0xf03040b07030b0906090a0608010513060b0307051c05010608101a010f05180409050f07030209010906030f0f030309060501151205011d0705040f08061503060f07032f030f 75
    0xb6002030420240c4511600c1d582c0000162185036454440005c7c00c2d0050443e07510050040d40f0344010300800702d001c9003c6007151401000c09210f5407520301d04154480885114160f40100024804400c00540510380006a405034000140d065903990106003040300440680441543d291440d582c00000d183e0b849800072030a18041c0042035907818082c1c8588188003d2814008608900280c2640c03640c01c24410103034400d00b914038a5080c8110242e44200341c0c0000c1b481000210000b0030103240074410101103a400224202d00e04c002a1901003402201e00c0c03003a0105500e95007400081021405501d00904043d80748941c0c080e5083c0c170003401409001c0240352090b0401004100b00071000c0d00004400c030004240010640f908841501c10b440f840c0d00003c2c040e41c1041c1b00145640340498000e2040c4c007040745149070101b280f01059100c080403950b09501c051490041340c912482540800011007503100600c0001341c6880c030304103529104016940540e40004108242c40e00011061904810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626995917 1250 626994667 626994671
    0xb01090902010e1201090c03061a011107050103270b010801050601030b03061b040e010e010503011a1e1c080c0d0c031b0f0b0109020309160b0f031b0f03040b0703 71
    0x1150740001e0030b0900c250340c041c0c480c03000300d0f40c900a011801e41c010a0015444400000304030381da0300d80240600500210002580d20080c080c60155000d1901468190312200c060b0103000d0614005400503c00c0c00040b81c81c01c40003e05c080d0b1007141122040b40725901031860903606615015145003500e20007003101e4101810603101c0c402c66180020790540241c0f24042c2890240c84128249030316002d0f071f51220111042c220000035040310502d481c24141e1304164028003c0c0d5620400d9880400c0084104d42c0d0068002400000441d060452140c0c1e0780e41c00521a04d541464484680c03641500c000041d078401c0000184230045801c01c204d944044c81c2941400340810466407405400d814450464880903008103610301c0c104600600d50240e250b901910340c0c01c441d40c42c0c20fa400000e4000b2a03110380603100f8040d018580c03030181c1025208840300e1880d981d203410060700004400d900040c0001c0d0090160207000c0c4107121548010f4500c61146940094a80c58541800001c0310b101600c8001418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626997167 1250 626995917 626995931
    0x3190506060f0f310906060e010c110120010f14010302030c060d110a0c030e09040b060f0607080d0917030c070b1503060421030209030c1203071e0b0109 67
    0xb45030054a0b08808500c0c22240c81c1d50346126102410074414041c450500c4030382c1c07005541d2220601c0b07120203481c13010b441007019036260041960188000030f50309001c074103a02204000600d91013900240c040d010300d04a090078213451105a02507400b0940e018290351a15800b50b445c0e1036a10680c89100c40700c11340c04c0e041d9407542d0042ba85a68a0085032801800009007882d40381f24150440c030300350340c07940001c960345024240000f84624500d400443c0091070002d101e035250b281910101e03000d2600003040104585920042001251400c0b2145800c201d00b806000b02095080c40580400304480c000410f0444c024a1b051810070324001c00c5203079091060080c8221104424165080f40e42c1c0410540419251204240501590b01034003540c07600c03c0b0300c204000c01c600e080550a100b002079090164440d21140140c0588c020131800742d40650101c1c480c2c0080349030611a00480c010540c0a89140c072510391074983d0101c60384004802403403ca420101c080000c030800403401030071400070030000342c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626998417 1250 626997167 626997187
    0xe12060a0b04050105281205030307110f06070806130f1a011404031e14010915020406080f130b090a0302070603021801030b210f01050a0c0f080703110319050606 71
    0x1070100d2900c406006800d90103485201514002c1c1700021f802580c00c03400f180c0e542494080e82c0d0354802c4545100140c0106054604048009204010118074601400040d83e0742a400c51340e80307200a1040303a10258524110600c40020711a080b0308549244011848802106103820b0055000401c641000f400441d83c6401c142c102c4e05440949a120b81c101000c1400d044482c0d006604510020785070f00700c21072907030900340380c15408040081e1140c030040c038100a0300030712001240102c1c41044089403ca80010318103889400c8010b44c1b104c58490b40301c008411a480741c0341c3c014002c55030b03220141d11490343e07041030640402141005060b41c0c80e0661a00780510680601e000c3c4400d0a14141a00c4119481c020f50741c00c01a050030100c6019802c40d00b08103041810b40c1c031010303c0c00a100e294684400304010031582d008182c0c40342040c3e2281600c40d03461400444d4495402408ad40800d42ccd0f03a185c0d00d00000852008501901081200448403480e48208108035003024014512071001042070b410341e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626999667 1250 626998417 626998429
    0x81b06010905070221130b04060e0a0609050d0611130e0106090f14010e0301110f2106060304031218080c0607030e0606060711040504350f0702010e12060a0b04050105 73
    0x217154607841d40241c403983e804c1c2096066503169000307280031140105000c03c1c8190310500d030304107090084401a100c40d607944420340d8058503500405400001000040011500300d4000030050441513040520f401060f0705072045091042c2c2100311110041401006800d42c04000c0e400030313041008107031a95510306032604072208080e11182d410700a030b000030381950b9a029404984031103c2900d1181d580e444850903290a50302c0400c030f010800c000c200164802d010b842c1740d1035100c1d40c4003604103455500d0701c0d00c040e244416070340e5483c05000d07220561034074003041d020807030003045110750080c0b078540382c00740034640c109180140720707000700340c078150100c800744c4800160076800620582c0d1095540285007417840b80800641800c43c0c00134240010700c0100820039110407010310048407540c90301481800f0440c0704504800d44c1ca05440c3c810700a41c440a2111001410305501c14100401c5601c03d06c4e02242d051310f4060500354180c0c001d5030800044508a01031498001001c807410041581041d000400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 627000917 1250 626999667 626999713
    0x80714030a11060702180612030c0606010c08130e01172a01141602010905010f020c010318120206040c09150e040611040f050301151d04081b060109050702 68
    0x4080d026001169a940300d90f0100c410054020301083c040100012480155100990303405004110504480304a6100402542e80c0c1d00785d984081c040c261905001100d00000c90350003901c840f01e0030405a0800c2c50134080210080c102044041100d40c5080c004c188000884981c0748078a812426224089624110410a41c070b10525882041c070000c0000480c3da0455060940f0b44441001034549100e1174544c06030305e1054800d0b41e03080002c84d100d03001102c80c16810302906000d41e10526003240c3d95808ae8004008265a24402d40800c200607281c61440d07464a20850300540c110005000074803540c260360300050592000284105d01c07880300c00d000c1024107840740d2100142c044c00400c082094982048045904994003d622183c40300b03e180c4826007a403146500c00c1d840c1808002d100030380f8143c020100da030b5500c1a0b050741c420030703c200700280d80001d004446260b001c1140118031400d82147c0600550f14400401c02c1e0740c1800c2442c0110b54002c0d01d0032055504c00d0248280c0d007608054422 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 627002167 1250 627000917 627000923
    0x3060a050a0b0607061509020c031902030f1602040609050105030c12030919230a05062107120608010e0d1209020d1218030c1406040b030907080714030a 67
    0x190381c0d03142980400203100c1c0d924003a9010000041080900496810070000100303490590180c4551b80c0c65503004910419401d190700c5e4000340040c050700c030103019100306c09511500580b4509508500000c016034000c416680903521043c600300d095040c1403290303002a040d152810010784d41000c00003a6108099020184256513514558031108000d0064030443e2202800c0c01ca05443c50b41e15a0780c852603507008564007030124004020107541e480083c0d11309080c01505a1240c40d0501c814005580d101307011660f540c40040014074018540f034140c0c1423083c40c00d07980e42c1342d2010040a00c1c10580f800d0782d0000409038100070041c240e141e00452025620790590402440b840808044034000c1e0032131410280d48124510f03800c405120412030100c0c400c070442c0d0340c1e145400810500c041111502400017411600b8064414000314a041c51921203400c4020075040c01d0594640d030f82c665550003100d03a0410358000d440c1c10002290204a100003038040841119030608124020035a80c0030a40009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 627003417 1250 627002167 627002171
    0xc0606061d0a181e0507030b0102120403020a06052802060702250501031503080703020606010f0f08040602180306040c031118060d1a070f020607021516020106080f1b0105040503060a 80
    0x4204c815401c682d158084040902c41070182d481e0103407015008012180d0b0450240c0515401000c6010f030703920840c1c0580758000c2080c00510304101044550350440707004000008407415644100c40c1851800703460800e4a03a00601491602400007400c03d48503120060442d8144840f040c4861032002c814020f94400f0311b03000503101e1249204120510386c0b5440681903440015083c0107240e030224450748545800c1e2a050b00c1200680000c44410000d40c000000050302c0c2c80200d800a10b1540003441c11a0008407010360220705200001e0810f24180e4045901d0340c1310300e004004004260b14205000c0c80101c542c8848071040b220300880e0814028a00343c801d80d01102c294003000400301003445040c80195510150303260501000e041c08084003513140140c03181d0000038101720310014002030321011032140a940c1d0b844640e031940c03202c40215060710942d500c4200100307544100b0001d500b015200c0f080201010403003040d441440d201010401c1d410050204002d10883d103000030310740c1c0c02c50070708800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 627004667 1250 627003417 627003431
    0x418020d021303030210050606030c0315190f05120c010c0f02010318030e0307051f0804020a170312100f17012d05090303070f0804030c0606061d0a18 66
    0x1468000b4407502d5801d58440c805410048103141e400030740400f182141000800c06d50300c07034100700400b40c0000c4980245c2c0600800005a030f003860301c10300488406000e0b0050b10b2070445c10059010146d92074014601007a024541080640303012074110084c100d00b40054000781e402600020848041e500001e8181c0c42a00702513821a4400d90183d03032030340c101817410782a000b20b43c90010a0301100f510018403d01c180348002c282c524000894101041c2012010301130b407514942c0c203607122400107100b03a81c804400c0800145034281c2c0c1031298107225290000c1d680d03d0800e00d2412061500140800345003050164090000710324060105003a00e0945008003000004e00050300d002d40000c400303030042500000303140290b288802d0803102e42d10452038024001542d170790108540d40c0c04125419000507583c25111807200703000d905900c1e0014041e207070804c80070406444400582c0e0480d84000001810018080b07043e50510304401403450f011501c14034030038a001080c05080700115168421a030740c52078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 627005917 1250 627004667 627004687
    0x6270e1303020a120f031506051c0e06070201020702120109080d0e10060605040f140f04200c030a080610090303050d02071704031b03080d0b0103021213050d0203041802 74
    0x3040036a03050307210007491008643c0040041001d21515911000729040900091492150842d9402650019910749060041c2c408c01c0c0070780141c0ae075120015055499070142a2203909101c038501c203400c02c2d00096541d00301d80c418403178030442c60f01282401c1d0740b41403070260000f00c0303880171281c2c1440d0900e00403800c12401c0900c0c504116180000b05038a503c2c00100103807040e003000142040710b41000d92665920f65440100c44a01e48149803c2c0e4414120000100710785050b0b48250400c0300b554105d00d02500d000f203c0210140d001105a10782d81c0d01c08a9030301c01103503025640d00c2e802442590f802c070395828404c1e00502080c1c400d00006003800408240c0b807a134144158195902a500004072003c0c06d0f01e00d1540120a5010740000d6a007154655242c0c043d0310000e04484003141d5101c10054600080c040301075005184030358007141016000c0181c0c040700d01e40c0e00d881f540100542180b11035110050314202d860100342828403804e64005100802004d41c8880200e106105040405a55200040c3e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 627007167 1250 627005917 627005923
    0x409020912010911011101140c160f03030f05070c03020a0201080901271e0c0902030c0403230705041509091515080d030b130b040b040606270e130302 66
    0x9030661240d980f80078a10b50030322000d070400840303851017070302e600003041d030b5a0030101d00345c540c103400c0080b0141e02e1001141606540100a02d60107068804082042030260355014004907080c4007600000e0301c0e441c074954a25118410190081c030a42003203001282d00741c0c0c02030344808040001a042c486482c0000f1322030780080d0007000010b544107441c0c4803012200301045c1c048d500300240540e601501e03020603403040584204e25107003803238004d440360601510b40764818010358802080414007550a004c00000034007000b15813694040304940520002c5899410345140444907401a0310450410700401c505800e40301c47d45054404015003ca00d42c2c1c640c0c144050b0491500507032290039807034400c0d6003100406441d110410380d0341020940d03401e5608510118103032051035490651203206032001c003855003035a44c07000034006d9000d000400c4d1200d0f070400140071140c00d5804103000c41c1444614108521600300290961040c0341c80d042030342414400490080d510007015103524a802e01c2c0f800b800c2c54020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 627008417 1250 627007167 627007189
    0xb01050d0507031e050c0411070210141b0c0a1a1b0604051507110304090506011806030209010311031902030403051c091221110c03182404090209 64
    0x19561300303440202c01e8a144200c0e41881c8003a02c0601a542c040801c40c0f03814002c01c280080040e4140d81068055000c04c541307812030414642c18440c1d503075030044a0700c0401300500b0000c40c001145c04485072440c0041800c1210002c5814440c410080b810300003ca028402c4082d214402c501603512190086c0d0364a203007560181215806105140401040000015002040042040b44c0d940c0a803200007045d034111850180c400c616400c00d000911603011035074030441c0d02c840d0515144011202001090780c001d243c507081a400683c00003502e00d01942c140c001c0715051039564451030b1440ca001c2c495001c1c20852207009400b00380e0000082000d03d4480e44c191110710f028903a441d60b81110303483d95030004117040f41086074407039595104802d043c1d0088500382512260303402d90030031601c12084c0020081807908030300d400740207051000c80706a1000b00045c042d1204e80c00e0320341802c00000b07020010019802010302c001021450180901022140f05890451b01080c001684442c008000aa941100303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 627009667 1250 627008417 627008423
    0x90a080a23090a080303091c140d090c151b1118070e040203070e0d14030c1b060408100b0a05040f1407020102091e0a030c0824040b01050d050703 64
    0x10035030341440c0300004801031030710042c1150403185071a82e41e90815103a02040711541310b03c0d007100c0c204580c00543c01140b101111100e14006000d040d640c0409449500300b03c100c1400c4541e10301c404c0d800c01c00202c04000103421030b110404800085020003d01d240390f5070710784580048040345401d04010054103008507241b03005002c0c200c407074982c441c0c90f50550011548000010940200c0f101542400d00c2221300894256079038481c440554814411102300d031020458000080d10710b00300e0f2060003480500703d444000c5000d041e4120b4840036a6032148000707650309203c0d0303038100001c001d10034000428000300740d070211020502204160003e1403c01c81a40702507042410003080c8400c1c3c40c0c3c154005280800c4075001d4403030780e84a1220890803401202c0149030000350000c20300000e110391510310b071041e81000307060702145c50312a940c4000681141c0d00031101540b1081d140c00204140b1001a01c3e813105064007401946810b48602c4050310061160074040c100b82500c0d441800814024130001c0c41e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 627010917 1250 627009667 627009707
    0x120d0b060301080a0618020604030b1306020c0c210607300b03010c0c08030106051e04090e1219080c1b0318030c0a0509090a0b01060e0405010905090a080a 68
    0x83e440074059142d011960703084031203c1ca080b40c0b010303262120190403810303c0c1d00941154206406c65451074005600030f00a04502c0b1050703484040019100d0004000061081019008042160301880000b54244103034641c0194807140c1e00700e03804e0001508951180d4549001c85035071981000300603410620f0081c3c42c5407400380c1104040401c400360401e00c10000305034002c020482007441c00b1600c40b07121040080001c00c0400c010401d40e40b05801034040c070b035030900da411040000002c01c0046907100d503220b042c41d942c80d405903150000040c0310001844000c810f09914060701c03038003c038000f0354010802d40140550364010961854104007520704640c20341c1050407081c0032445200c1d81c0e903081041307802c1c3c8540445014913810704001c2045c0e4510803000d0a00c1c2c82407800c10080014041e03009100c00c6c3d0901c122031011003c110007500f154003d04081e228a94a80780140900003070f103074140c1040c24524185018040e00e04000600680e106030094403c503103034040440101e03250202044004041c80e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 627012167 1250 627010917 627010919
    0x5030a02150c030403020c012613050c011403011e080d1107050a0503060c0a170f07030f05040308071404090f1a0d080a050c0705060d0e1b03120d0b060301 68
    0x158000500da0300030041020750a10554030506910720900c0304440043c01078004900901d80e950042c5040303280e840065a0031400c211103041c0301f01d00418100c68003400102e14049540c140901440305614140e42840d0142800a0f82c0d00302645078441803003960008510b40004100454820202102030101041920300c20600d8030002007000c0d004814200c958002c110002030580351600419045070710160140c00315070307a104ca48d1034242d0800c03104482400700304d00400f4021985043c140744200803551010341541010301c0c000f1308035070241c41041109407426082c800403035000105640d200c016131820480c02550580448101d001d83d0780581c001504205003102e009905810160340c4598419031102540e403514200800100c1e8961b000e400d0280811400d22804c0c404c2000740190502c550890b0801503036403000c5015036104030128141c0c1070780c3c3c0c040d10b29010307070074442560302104046403501e4110040000039200c0c006082490301000c0005030f00c2c10701902c0c6400c0300b0645040100125165 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 627013417 1250 627012167 627012187
    0x105091305070506181905030a140a1202030307090f0b071203110a0c140d230909070309021906020d050705010905012f030c030c0702031f0605040b090f0606070f0503 73
    0x419448045c2c603218203005030000840003104480c3c0ba04a64004000302040c0c0c100d901c603041c50800005580c40180541000b40000c21822000d2003820111640190350f00e20301441c0040c071081c0242c0203801d90301c00e00703102009402110300c150b805c01500b00421030550f2050840c103900030076140718400300a08004c1804165150007099406a07079010700e04200c840681c800200780c8442e050b0702d03004041102c05d81c00c12940341c01e11480352403115041410904d00b403680d800003044550300326046000aa1a002303140d003141400246903140c0d1522803031612070036003071034406515010910f03042010030801046a6007401001d403c401103258106008100350845200003807926a111010402070410700f0001c03842d0140024200d1303104880d000545821600d8201c00301303659500c29001641c3c1032256010802e500d09804284820000c40d06000054031031800c0213200c15580d81c00c40d00383c071901500c010040c00e0009241548d6002c4821103103940d8034096440c0000a800002001804c41c3c40042203002c06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 627014667 1250 627013417 627013447
    0x2130b09010e010c120f020f0106030501050a0f02070b01091512140c19120f0b070f0f0509061204081606020a1b0510271b0501080105091305070506 65
    0x3182020390707800c11045407a10043d141004010001428860040e0003034005601c210b043c00c002020501c10340399a030481d800322509444040e04151441d03551441800110906071041003040031100c0400d600713022072501c507660354410500c1008401e645940340318090401150365070f0098400714801440201c1c4508040040c983d80703c2d012003013441a4412180e1a180100400101194400c8003521960911000d01620080d0724001c0790410011119600090550700201c0d00c074407400c8e594202810050003008005030305403000501808401c0040d4401c40d150841140c02010403d540c2c115503403034a290a81036031017041440c0001c1c018440c054070400c98190020885c6988a0b500c885084050342b0640141c0c5010344002010390f440035001044220f256004080c1d030300c2108808102841c03848201c00c2030b070580550212078444076100d8904e0111028940103001d00310a00c0c2500131503040c6030100d154000003411005800c140700d4030120402000300300010107004041c00082d150071915480d985 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 627015917 1250 627014667 627014677
    0xc01020c0309090a0b0303030c071b091a01050301060e09040804051009030b0a1103160c120f11060702250b070c090b040c0206060402130305030301030f0308010801060501020a021302130b 82
    0xf10481c01c1d840858906030140c050b454017110010040d61850721482c1444402d40e000550880742c00000d08a14017046542030520b0000703002c10f0fa0702003946060512401c0072145a500c007a4144142400144030301d41c0d001e0b1360045040030035a12409542c82d01d050030191806103a005540c000f03082c0420840030b56001c44d0f01ca00300ca100d140c08091a0720b9021802059a88020304070100540900003d60102400c415004c0a10002d003015101a04203403103180b002c081c0f416500d8040b90158400501c5250301040500c1c030340101e41e002d0021803d000200940f80c0c1004980f0071a107141004a0aa08500b001810402045111601c0e80d0740d00c2a0320700444141201d12036490030901e0446d409450b400c250040314030501166001d44001e5489904020094000201c00c100b403c04814022001a10400045002e58043c1c105500329848500d070040030091b0580102060741d04120040003140d8000031070310300555040707809600803400010400b000307006681c40307003a6146002d08000345034016400144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 627017167 1250 627015917 627015919
    0xf05071502190215070c03031803020105060315040c0b0a02070f180f0203060306240901081e0d021009061404140c0103020f09041a060f030a06050a121401020c01020c0309 75
    0x10555541000166120313600341c09101c10010748400042c2102c0d00c694800d2004d0340c402e080c005850321082071001c00326862014110b000d40e6564041c0030303003440c00300501d4156203060000f0600c44d207480c0c0d07255420a0001d00c1407641001010454031402c81c001d001d0341c4e01400400780e1141c07070203941d0014580725507072620084990a241803a03540c4610707940d00031039100d0b26014008207810f03102c2c880010348280c04006010884040015119207550720508820300900c00e9000415107000e40194a08500394000d450011561042d590009001e40102d40c0c10800900c44c14000399102560411a0150680c212120401d40f0203404100800862035000c0c200194020102c449110089005400f20f1041e21041030306140c003401184030a00d0150040da0100000503411300c03920a46501284040d000301c9140000d0107004001c000415110b403041000412040b9509040580f0700103000f200006040c60140100e4094204280031400940440b1014400d540c0215502c100444c0d660351a504040202c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 627018417 1250 627017167 627017197
    0x50f01050702091e01050103020a0e0d050f030a270e0106050c0c0d140105280b12010920040c0804060905150c0d0506120309120a080d020421080a0f05071502 69
    0xc071b00b5510a200355528100725403074444209810004000c0744102c0c1003c1100c0754800c01164217003050782403002e02095001a2110140c400900c91388484600c41002000d405002e0b560082000b0321072615100e044508908080c1e60b00d0640366000d5040410260b480e6802010403203041041002d49485038801a0440d0002c011030f480d00e0301d0040300480e01e042c41c0401d000140c040c5880200c101d031703c1040c1d101c3d4010104401c8100c0b54051500395011800c3c245d600810880c80700d0a10f8208906000380e0708002c0b24200801220b55901400d1850060405429980e0300e80765041041410807441c50000b28140000225240c40e420100c1d50303901811002c0f8040d4182008154181000341402c40001c1c4590b025601b002c00f51001e1003031544088080040a1056841940108041c00028442108012005030340d80d4100700302801c030b00c40d074103801042d0009041820800304555009580c400c0316903203002d11480c03500560403a45c60240d5403004d03000201c0c540300c00717220540c59401040110b40136686 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 627019667 1250 627018417 627018419
    0x10b1b070b04060e010806281e05011d060703050f0d0f1e0e030301060f051e0405013f060503010e0d03051006050f0d0e1608011a0a050f01050702091e01 67
    0x46480c1d00c03056487ca50002a40d8541c5c9010b01480c0c40075000d601814840010425560380003800c0d104040c040c0c0b10070b00c82d441d04040c000365900280c0e40f04110803888081005200c22800b0520500ca550f00113400c006000c0b448600014411040f0b0700605410801132222040b081442e4005140540300c4041c1011040e0f924030b180300c0b80d4007800e08001c000801650444e03103010303015200d1000d0350305540304002d000c20614008000c0b40707070136050b0419089d00950b201c07810071002501801f8605004021001e081604580042030080c1071800e0749005400b0074201d0148100c51300c050032007500216859400c1582c50303c023410b000107603503988040d40d42e03050107961103000400c00442924001c078030000c1e2003080020080341e140c1004040b800c000703400000b0142403540f0b403281802c030400040d07400100d0ba410204000c2d5800d0240c9070000300106c15490100c0003c100280c0b100d4494425039001e03008910101c1e0f2079030b0082090318451a00034107159024580800442044119200b9855609010b800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 627020917 1250 627019667 627019669
    0xf110a08010c05090603130f1208100b2a01020703110c09010e0703021e070308070f0e1c05010b120a05011a060403020f0a091113050315010b1b070b04060e 68
    0xd15210900c0b00e031605440c0c0300c00003051209503400102034101525110320342c9000100c9034104294074a010b481c510340d0900603814018030305880904640c01d46107000205100984e00c6104646017504c409000410b15117440c040e82c0c4034509000f1892815500c0481c3c13060038940c201180341c1000450070181c1d8071250104080181c02071081c051a80c210184000090116009038020700d10003180c01c1011200d842d42e5030840202da806640d017100041c11070b40501c04141c1d00034045190399072440c105034541905440200c0e10080740054440541941f0300001030030b00c5000c1d844000c47c0d18028044030b0701c0c14543c940e05a90b410401408440300d40c0307080d610243e80707001b0900c005008500140f000d85814599002c204015035500c8410f0b5112130031000008050031a44108a40d1402d10ae4a43e51100a9852a02c60001281d84060300a40104c0e00600d4418250109941542d6489441c19140c172141885035140480104070500103129003907021030503402c120043c0040312001e81d01d00401c0c6520070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 627022167 1250 627020917 627020921
    0x4091e0212010c0e06071407060c02100804030e10030b0a03030e010f08010515031e070207080c030601030213050c0d0f15062105130b1014010503070801050d0f0f110a0801 75
    0x4506440004d91401501c0410302e000c40007021810b008201030400481d4503108681085069440340000c00c4444110004601781722460545000807420400c1c0c0c0c0d440d1584018044006091045200c1c545002505101078007076031111000f100c01818202e1019200d140207000310150103041401f11b00c04218000e040751151039403d042c3da802502d04000e40c1400b820309242ca4002510440305904900780180401c043c6001c91803280310264002d2117941e1504940b5814451298030543c00ba41040b00140090307140d103402d560500254650010303513035480c69050106400313141d07003019407642042c6d8803114031310741350f003040c1152a140401000318699030002034407a0548081094a005e44140f003083c0b070175683e640301581c012180c00c026a041080c940d15010400720485090301c4034071403800c081c4071105500380c48584038602802c11030300e0350611510281c40c41c0014400c062003103050100c14010012042e0b040407001d54060601c40c030070405460140d441500c106030b128001e032049440025024014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 627023417 1250 627022167 627022181
    0xf0303090f0b0406180905100314070e06210a050307030f1b02011d060c031b010506060d0528021207090b09090a060f1214070f0b030604091e021201 65
    0x201e2490b500e0146000381c1a80d030300f00b48400c1351541c6440c0300c0001841e030205004035440762102d0700006009909501d4050ba0108150248a545500c400700034403512200b040003a801900c221040c1d8544020405c0d6000342c2640329620540c1c0c0d001d101481d00403c000000900601d510944400200384100401215044c04c00402403010070b1040781a90090350180c042c00180c1000c80319442d03910390040b004100598021300c0040c001d644002101c601400340c42e0200ca5007410f1080007400541090741c006101c41c050201c00a18141c3c1d1200420883c9020702c0d00011a54162240c060107503800f00701020094000c80c84600280c0d62150014007000d2041c58080e06035140f0030510303400e16000f40305116440314024000000c80e552241c0100c3c50035580c084400040145110049101e20103190035040c803070300c42c007010b0401e6001040030701030100200c628405403156032812039100c0d601c400000d070180011000103001c0b1402c00307070200c1c1070121003030702d001080d402600d0600040d00b80e45805402ca03500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 627024667 1250 627023417 627023429
    0x80603190303020d1d152212121109010f1106012709080c120702060304030f020a060c0f180305030318070317180609010c0215070c0f0303090f 63
    0x80d0040c4900103400b0340d000d040f8511078050300081c0480013020134025500124514245648924428075010350600c2c2c3d003587c88848042c1040304031048005413019803d060070000c0c5181c01c01c07001c003032005201e181c00b02a440d60a01c42804003484c0710528812540c42444824005110f6440700503100d4001c43c0e103118a202560028403a682c64810b0701c107011001032880c101d000c90b00001441804406004200e8802c4c040c0b040f41e503aa021404405103400b4032100c00038000710060040101680e650b40035a43c2c01601818101c813820070b880001c078140500c0b80c41c014000d610305016881c1e19940205081d40540407900c1d0205c0700510f29402c151340d5825448000c1c000d900c01c1000980c0c510701f9240142018146404603001e458582d520400010503954040c2e2502502003021100c1c4068420b40303803003801003611840d140a521100080489003030901c041e00030b03103c20788012000310320901180c8045070030294001c1a6a116900c0c038005400c1c43c0f10980c0080c0c4010404140b805502c0c40c0101200c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 627025917 1250 627024667 627024703
    0x303111207050d0b030d2f2b021c0c0305210103031b050307060b060f030c090f010f0e010e06210402130510060c06110c010504051606050d05090a0c03050d080603 71
    0x9078218464684440100e60b1f1074548450307542c5203041c45001c1210010b0b10514449400b00c5107201303a884235602030350700060002c661240d0a400248403084051040c00c1d145031428200709585800c0c00d1f0741510910351650841e2141d69000c9200d103112250280c10b80388a81d1b5460880d159010204070520311041002d17041c1d0704200104030019140d580011105540680098181041e923925404541c2007100c2c60f43c91840005680700541c0740a541c030082842d03007400d01c04336040e0100e100615180000b403145041c8807081400cad0320103a0303820f4196109000c4100b00b00c2114519501840700c0d0b01800e440403800b56402942446121003030b406003038412038240400401242c80d00b0001c440720383c04544141d403419030754501c0002501194008011113a0084008a29403d0500e0f100d4500120f01c2030405e05005041d0b8240041d550041c210380940d80c074400b01069a455012006e4100851410024100041c1d040c000041110110300aa200d0400752038a980340e0341c909082c9500c941d030b0540401400d071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 627027167 1250 627025917 627025937
    0xf05010f12150c0801090b0105030f070f270e010e04020913140a060603020f10050a0f0e0405010608100f18050405010e060906100906080a0303111207050d0b030d 71
    0x5210301c2082a490282d545108040b20480580c0121022501c154001803118001884941058051612500d40078605140780d860070041c040031203c0017400a00401c101d071001e02034003510034a001140d101c2c801160b283c03881d1010701c1c0ea91000710144a1900d0075204035000050b80341c0721076072941c0b28540140440c0590b580e500c060420050352044201d036800d00314800b02002010811090394183d10039280003c40b5411030041000440f41002d0044c0b0806c24040b034001d00a0303011095a82c411403d00300b0307200340406068241c60b00e021904c600c41c0c0081c508000068015840404c00e070051002405040c0010344428918051503254055151004103078130b911110b05000d0380c0016070033400341e0000260480700c5400303a4140782042d01e40d101250f20030018094040d800047c2040201200b6600f005424a400302040d12002102006010b02d940e581c0e00c86000c0310400101d036503030058030318510f0b41032070310010250154108083e07a200d0039289c030044003498100061641885c00017629046450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 627028417 1250 627027167 627027179
    0x2010513030c0905190221090a06050a06060e0619051b0a050d18061b020d080c0f07050a0501020a060905010b0411030604050703090c060c030e100201020a02010f05010f 74
    0xd900140d080091a510828000041846502d085003c0d040c005004991405c0101c1800e02c0d114050341c403c441c40c0d10420031000400d003441c55041c0c4a010041400f12556100002c0342e0034244055806404c150605042204045180d480703402079540710340b120301c130060507001880201d000c0d52074400d00c0d200c41c0685104d841401034002d04240c0d8025120041448150042c0038100740b02d2960844a541c00741c00100101508500d803000240e046103000b03003465241600080c1209600c521401800b89580061403d540302e10309e26003110b540201410f079580c11654801aa600001c845200c41400780c4100850303d4500422810111a41680141720405694640d40001c000950382140c1566903400c503500c4644440c02803101c0d401c20340300c0150701e031b04d0031000b408180c680c01803103130042500e00f00050300021003250080b41500e03081e20780011244028a420b03a1950220004030b0303801413500c1c0044000f640c1c150001e11107144994001d00140503000d43c48819540203008800c1c1c6032403030040c14411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 627029667 1250 627028417 627028427
    0xb0a0c14040e0a02070212030c060105040b060a08060d0219030308070201110a030b130f0906050c070f120203130e091b130209040b040203070c140a02090406020a030b030d02010f060816030201 84
    0x203c071003903500600d01000b40c0c0c000340d40f401c000c1d240c11099400c0807032000c2d40c83c038052110741d0050200341c0d005d014209070500001c145200b2070300b00034240110100402d050f515404800c0d200940d0151540d0203000d04090ba15041c10f0441c0f00407030008010380f0029010620602411124007105a8814204800c0c58800d4020f010445610b940011a00c41a100b002c40540284841c10f14202800107020140b42031071400c0e500300801c0c015504808000c244002114038500b0304070381d0b4014410021030a02410100c2c1544a40c07412312080b01140307003010a4248203400450300424240040f60000241c0c2c01000a41a4818a42c0340c1d2090a45215840541540c1c00400b4603c0b801400022411810f0300014200d1304192900e00004000c10048020413507a072448994240c0140028129651240c0c006500340d0b40042c0000c1500d9000705844400314040d400480314000b008081d107090f0301200e00020300915483d10fa90072194148100001c54201c0403038130808420010780030a4129041d5001595 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 627030917 1250 627029667 627029671
    0x1201050f12070b09010908010e2113080105012c010e070903050105090307171903020d09050604060c0e041109120f03040801020a0806091311120a0b0a0c14040e 70
    0x1030054840c5110689101c0240281c5020304800619582c40e540c510000500c1800c00e82c10462007030f858454002d0108500256900b42d4191b50048584201c01c12120100940107251200c111407115100200d1510019000141610b0a800c180400030860745c40d0760144440c07080084400581010052101604009030168810043d0904a41d0685d42c2e981d038500310750003102c00000541002c280c10007048009400300320304a0380a10090704140c102100010340108401c0c0e00800e2541c009100c0c2c001f191a03400c000307000d503002030640d030712032800c4d09104005d00614480b0703a000580c20b460706070301c1e07103014425100340d22402000030381400341c407100303004211404101c42039403440340582100e43c0203000c20080011380340d94800940c40350454a405014810050030042c0b094008500b080a20101b0603001c040c041c4e00004000300301010304001ca21140307081c062104c0d980c0550414003007488011044540241c8030035500b003204056a8131f01f01c4803503d01101e8060041c404100421480061200d516 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 627032167 1250 627030917 627030919
    0x150f0403080714120415140c0309100507170c04080a150605040e0d08101202061c11040f0e0705030c0c071206140a05060f040905010612050c1201021201050f 69
    0x3a40540116085425504007220020b00c0540c1402000100b059039003000406c02e02199041c000c00320b1401c82100d00c00001040e84a001801000040114000b0040b004071520203010400c03075400c051200030017070042d00381e6100b04840c1407804100200022001c4400b11041c0300d02420380d181d056610340e0340201603403070780c40040c0351540030102c0e0913507070f034420440c00c1c8440a0040c4000c00e0b21000103019036038000c105401d1040109810840704203140140551503a040381c60a96508008104070382d01c10640030302c032080c2032500d0070103901d10354420002c3c4291440700c1e1070000c4950340c809032001410001c40da52000142e003400130882c04482035019000000d10328040e1054561550b80e4044103c1011005441c180d4541c6000038881e40e405609613002980c0910130b202d2854200c002c01c86001c000315440740a10b90790094102400380a50100c00900f02807080d11200c2d42d000e08086a484801200d10b034030450312907081c000f80307420500c2100e244054240c25841241e1070074007000080d480c42030403d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 627033417 1250 627032167 627032177
    0x30b011701090903260106021e0a02010c03031b180503120403030e0307031202011407030b2409030304260601180203190e0f060907300f080408150f04030807 69
    0x9402d10b442205000c1d1080003881005e980303d580b5001000f880e04111500b19041503800c070111030081c00c80854400640d40d02820002c03030450365407604900821008110621404900c010100120f0f48000c0350450035144040c01c20303456403500101611419030035800c000c1204100402c2000900603006100039050007000d90358240da480e1150722400c00261000700c0113035503c501a9180c07541140100e81c1008507403808000c1096031501050a035450b03003040e02482a070100d0190300b100604811254411000750507280c0b21130f0b03240c5400360750049801640c548580c4910411004810004400d4100d584000c802132000d000d0350305803c02944040c1500f05070f207102007101480000140210400f00c1204030040c03070480d00d411400340c10b180028040c801c0070340210384200456401111710413441c9107982d0a00e101003200b48004e44051301280c00050910010314060700503c14010060002c07115a40180c8801a0040340008880e6030304840c0f10b0b041d440240c0c0414007082c4980c44c2c2d1a4059118100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 627034667 1250 627033417 627033437
    0x9050d052503020f0f010f05130803060d05100e0f010c020610032d030c0507090b180a1401030f0501060f0617060d0b0a090c050d1e0c0e0a020a030b011701090903 71
    0x86a424201d10301405200c03691504105070401c94036200d074580c001071000c9c2e1390f101300f040c5a442501c644000303030070580701e01c07200f0700181c0030f104060000b880185019031781042040d40d02d00100e62100d00f0316003218090751800740f0801c030690020514600c102444c00c0711901c903500390ba551420305144000140c0c0c0700c0202c1528a10f18a040204041c110f50107500c0d40301c0b4981e024600640b622446811000c801070810302c4c0e602d42c903150262604d00302c04211441c014a940c1d00400000105000304003540c05840c118000001d00c00180320100d107640c05540280b05558503528003105401651280000040e002103401400f203014070505c1da08510000c1c106200900561a40c82513600161174401c01203a84001020810004003c00002800142c0b40e403864405251641010ad220442003518680c0410300c09000300000f00050b24080d100002d80301d241030070030b80000c20007500079400b40d0000c24500b10010034550f020310602d0010010054080d03d49a00705503135000503000303c4034124103028003400303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 627035917 1250 627034667 627034693
    0xa02120f030315240915070c060302090901080d080601050307230a1b0807080306060415030504060624030b01210b0102150c0307030b010e100309050d05250302 70
    0x31801401881020070082c03e481c42042140102c0c146500e000c00491582d100e240d0301514151030f084002290f141007440d400781d107280441d10401000520030100c141c4041a075a4040d030180aa0b030b18103503900109aa00e0340d00040c0e98002c05030280c070214107800d000a840358840c500940c3d10182e0b030300d4509411000c5068140d0610030b401e8080101d41000303d42c0149255201f1040012039901c85010b085007170b5540c0700e91f401c3c3d2244010180c9900130002c00200d07a80c031540102c4004000c8811851020b1841d644024020141600c00b120707a581060000070395400f402030a1020364000e20240c080182c4500030940c000c1c0303410340c152414000c5030b0102441048064210340c1845201703c50110301d080c16400020305003048030440d29030385000d22090010094010301a2a800305481c200028180001401030342c1c1020030489069020064000f4401c00f41c4e416004500c2c0103100e8007c6030340350f403280c03074064811380a461445280340380d071500c800c00c00d5a43d203009802c0603400790041e0f98041d1140c036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 627037167 1250 627035917 627035923
    0x21020f0409063e19031b0320090609130b03100e0c012109020f06190905010f050d05060a0911032a0f03070306090e0c1504080a02120f 59
    0x71104140030700108070070795501410b11012040c0f000d2034603888001c0c90b154151040c80c0c3c0503100e4100042611a00720610080c041e0344010004882c010a0b0702c240094404001d0140914220426030b07682410452120103040a050390010b0000070801d60402e04420140811020703c1c0506c41c0390503444003280c0e0517030b850601000d8a07844000700f0202d44103503810303896850242c2c4140c05904005000718200344003403c0c24111140c29000030030101d10f880b840e0000515558140002c0781d84080005030321107210003030f040c0202c203062054444040c3e040d034420055940600f543c0059000c034a0800c000094441580d10a40d0300c140000c012004241d101c0c08920119444044030410125002081c040000300b0081503a01c210385018000c2480e200c0c0c1400d541c0c1174002d12000e508884008000f0a61030b41c042d0300001c018000c2100104110214010903e50f5058100c842c0c0340500c114001803030300400950122800d9420f12002029071107929402d00c8a100150320103c900c500981082d404240002c2c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 627038417 1250 627037167 627037181
    0x10b0a080a050c0f0609060c03090a090617060103231509030a020715120515031204090f0501030c060f02030705060403020c0f030a0b0a020f091207090621020f040906 73
    0x100006203101c0e030300c5140803441e0403103012159210301000c8800d10348942d03a403c2180d8001800b1b41c3c1241c1c80310048107085165000f2400c15590100d080c03d07022030142e03091740c000811149802e0250191612032000d176a2903803000c1c000034011518800c42e01c403c0b00205c0b06803807840c039005e50807290a50191404030b052507100b9580102e05e13800000e080c14405038100071150150400d030001c04141c110b80c20000c0c184034402c00c2c0c110710103502c810025280041d0300306680604180941a22100040090314a0450707206026600480745024058130a00040d84a814186c1e0382c0000c0022216040c00c60540e0589a0b0b94200d4045200401884d00060002c2c000b241c015807080d001013901401c00e404101e40c520300580418003075404a00680080391609203c11740200080d1001607440ea240260004640310300c180b5613400541c0c050f406841204e0020b0303603a0031604041e20410005403145852040b00c003000000d100e51492501c0e00c100580713880040000c801030010000240c50a15a881c1c20075101d00b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 627039667 1250 627038417 627038429
    0x1314030309040f06090b10020a0b0a2310140a0b07020a03080c0d031b020303040f0302030d0617060a140c160c170f0d020a240203330f040905010b0a 65
    0x444e501048620418000d1008014040799906001e07040d044000f9616900340401074108141e85012650180c0c13141c2c000b40c458441e90b61030701c000045e103884c1c0c8000c01806071000c030360310400b400700041d1f030109001c045400000c0c01070030032910314503012220100360080304090343c3c4400302100c00000104010010071140d072030b00000d015094440500a01290700b680da92903100d12120500896180d800300850303900c15441001541d140255003000c0345103000d41c0f12801a60f030728065012400840d01c03112600440c0c443c9080342c03240e58805100800740c5800c05100b44000d0142000b08051601d10000f8001040006000740d03d658503948030003415642d075901806c011400450301215001c1c082c01645031000609008042c0e1000c1c1c854002d42d6406c2064004e0308a4400540c0351801c810310104010450752030a40a54507410202051a520902e42c00c1440d10b0345511081da280c5525031120540f00140024108101c2060315428000a4107412200f240c05541c0c41c01c0f0071000383c0c0c5006000f006401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 627040917 1250 627039667 627039671
    0x12010b0621010e010308040302060a090b03101406040806190b18010303031d0309010f1704210314010603050402031e060106120915020901120606080402090c1314030309040f 76
    0x141e0502849006481a040054011045001800804c1c10241154116030307040d00d4051341c9000c00c1d24129180016074100900c0000d0002c144030020b0ba05200e0360066a40101230303e02945510820404284690b11800056800500003d000841d1050042515070740c01034000c40e010f00401c00044003441c3c8000c4002e45102c901005109241d854840c84218030070070191540380c2240d0301b40b03180c1d803401040665070421504440d06004284200c0d228140d41d80480c04a0f2000d00b060318003d02e15803400b400e405000000e1000c4003162901c280200c0d007c02c0b28000340b4000301c0e4203103038048000c1e120041c01a0b80510410342c0e007000081d44c0030084014940300c0e00c043d24181d418020024903206050015101803414580810f0100ba0101044d032403070711100b0030042e5144110030060702c1c00c1c0e00b10010705000c4d91905600103042500000700c2c42c495803007111401c03010b9445000c1020316010340070703402d040540203540911050b2155040e0804020004042364140210100020240c0d0a4000c050381c48603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 627042167 1250 627040917 627040957
    0x7020f0a0c180c3203013c050907050f070605010f06020c090f150d0b071704050a0210031508070302031b0102150c1e0c0601060206010605070212010b06 67
    0x503048019071106050301038418003929081000050585902a00c00d50102d68050052580d000c2004464822900c1128a05417250795414481c505c0c14135980382c0c4d8440720b0072481d105158049040214542c0d0481d009000c0b6140c0c1060188001c0410040c80358050080030400c040c0401e00400c0035001c0340303105080c081102c2d0b06107400f80c03035000070691014080d54020641d50310556645010150f020401400407105980c43c020b02140c03004a44040d01e4010074030340024010b124054078200e110700620303150244844090100d11500700c03004c0340d01074050f40162007000018580410a82548000751a021500900380943e415840301180e104074140e074083c0c0010011800c05000700810b405448020f440103510000020391115031107080c03d01413000400006074490086410b03196086280982010300848644100404d40d000308010b1a403449074100004005200142842c1650400da6a482c1170140603400c1c044a0541c00f04e240b2495501c030f82804c3c8482c0c581e00041c1220400070f1b04051450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 627043417 1250 627042167 627042179
    0x5010605090c19020f030403061a040c05120606070c050609011205010906050123090d030903050307062c0c0105160209090601030b0c18131e0510050303040302150307020f0a0c 77
    0xc015410001000d40d000441c01c5c4041c2074011040c2c40881e50400c40204610703504040c004213150000320b903503038403030329080f8425001580600501025600c9090b4101035440740310800c840b03801510802061840210360900060416001a1a00f50010b04003a00c44500c04070401081d1074007608801c40043c0d40c4c039020005503034000c519070907402510010501c3e0b00ca440c0c80d08040ca11541d0742050282641d10800403c0611401682d00251707040300561303480b54454546080039000719041141148114005808084608020941c1c5034012174002c100321400000196040d0b00075440c2c00079803100040b5032001503150612101c0c80f480d044800360050f981036190a20b400940500030021900041c484040941c1041d405c00107011030840c0d68208452007941050050149500003100707100b807092070308040b036410390041c9009100c01c003080c882c059118014165240250f10029504c4101d41c03c5059441240300019a0082c6240c03041c2c40c000c08074078521500c2d1081e440022110a40e2212080042d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 627044667 1250 627043417 627043447
    0x6060102100207111c0803010906060e10020604110f0603010e0115110a020f0a0b0d1523091b030c0d141e2701060801050703230405010605090c 63
    0x10764912860071410b0101c00c2e10345000e00e020300c143c100d0241480e0030025031940c2c02c0d101c802c0711180e0300610741036480d80c442a181018001c640308502c00305018413212419031420303407160b4500700000d038014140ca82d43d030b403504e5030034800410b20a500559402085900754480c000218003804a10240c03400d42d51405a000220900c1403c1c0081044000d2005020100011580880c0b41c1e80450705100c1d0f180081c00020480702d0980d00c51030071064001511950343c2d0080d003082c100c580c80e600181418580da81c0400c241d142200c548590040d503101d65501c281e1401001041d08040c0e522144140084082540720141e4070a07070b038002c4150404501c01c0150501c60003201c1e075038000314595002c641020004d0300d2341c0c00301600688240280400004440f009420840010101c00c00c0405001a640c4e40a00d4020b20441c020b26546c0d500341b500140145003e80225445000d0219100340d5610340d244001c1e4100d02d001e00304668654031060001070702d90f1480340310b9000d411080d00540e900c003102454416 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 627045917 1250 627044667 627044683
    0x506040209100e15040e01180212070201051005012102030a020f031306110708070809030c030105072d142206030b120609120a0e030d02030310060801240201020d060806060102 77
    0xc00c440100406e224038000e0050590440d8100001b04000244170068080603002d070044400000b02c9442c10001c005078150013580c050304200c3c00d155045a15900111810042c00d90440005090103003800c1c1400e072198010b50b03200c10401001410010880e408100545c400e561600d01505150300c80b01c00d002441c4501c29401007002d10444c944901070f0b132801414040c00e18060600c440104000e49251000d0045118000c03000f4000c200c01c0c0303400200500341e917520011504100c0d50703000002c0045040c120b030100d02e40c0d90301d84402410b41c0e01d084403d03049500c214550440b6a100c00c2c00070000901041d41c40b40649401d850215000c54100140410510f034480c02d0400c0b03501000900c00c0748034010508444201c110040d185e6502042c000607078101244070200c0d034046c0b055826040c000c0341d02001550060042c052034085065641001300d0b108502030003145150034540d2664850b51018101030701040406000240c10000e41c0c404034400c4075015482003419400000c03c0200941c1d045c00844 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 627047167 1250 627045917 627045949
    0x100c08090c01020604021e030a06020307020c03030c0a0b041401020406020a0212031c02030615041203090503071a03071b1b0b04030f0b0c0412030203071a0108100506040209100e 78
    0x1030441c181d100001d6403144041c1c4003034000d029601514132054602d02e147c070380800f03002e0300300d070fa000c151407400300003e600446403000103004800c4070785100c0c9000b100321407c0c0720a0f030008000003205a181c0039200c01018108940e0300407805c140381c620340c800380064401041136801520003001c143c018460303580c0c0d4500e50a603480c0c0040010030702d20507201500b40104a410400140c40740d0303070540480d58803200125070700341101c00481c0000303c4184948034a600a0700c01d68840f004240c0d681309050f13440505005001c2d4040c0300cc1b6050343e401c403c100155500891510382183d0740001c0313020081c54290103100a541052403004110303d010388400b0508002c5c00014038507480d044c5580c80c0d03041c140e11701a00041c83c585a0b017000c61000d008490a480160080d059082c00619030340c50060b42c0d9602100b000c807810400b200780c001021341102c03d030b1030403900d8850241020042c25401e10f0000c02c0000e1100303520a909100b18205503c404882c04a4a10355489070010252050200500034000d00071238 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 627048417 1250 627047167 627047173
    0xa0308070f090e0a272306011a070501090b040f0b07050313021201061a03011d0403120f06082d06010f0e07030204180209091b0313080705100c0809 65
    0x10003150f864030803030030340c8101038984c00107400e207403260340808042042c00004202c1865803454028041248076441168441c4081c0d43c0009000e2503002d921803100b40f140b0036103000c07198000c01c0c0c0c0150b0b5400403c00603101e10000940e210181d0f40e0700ca0314850943c0c05503408080d000001c01002040d0700820303009007840c2000c600f10300d401001881c820300e4003d002401816582c07107203a580c2809420020203403400a2418646107080700406420350024498120350072540d0070582541800c0d8094a0b0266404cd55004010320002d41c0e50b1016159014440117041da49e007a00041441d03050040100314400d5901e003c00340c07058103d0841411007410840c0005800c80401002048004da0074403044a180035035000b030700c2e51401d0058000303000c0e079800119682c000a00c03051042405900608445e102250407041c0f40c3c540c03c803451400040401a1079806004102040103100c2020041c15428410303004689000040e4ce00c140c20900c561815040031615480040c3e18140c2103080c85911261200003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 627049667 1250 627048417 627048419
    0x26070302040302130516051e0a0c03180806180f010c031a0102072418031a0a0c0801030215040902130f08030a0c030503150315160c05060406020a0e030a0308070f09 72
    0x1c40020b50f0506c0c2d601e0350074048002005c0c1440400c00c0c004070040c060b124a0903494800d5428090b00034200f940781200002c10150115405440710981c1300180d8407050b0041440f9038507202d00e019200d9001075885072500c6460603510802c1002d0054086440c099500820321550003240844030f14042030380541550001802030046401c1c03000262080592481d40c01151003096200f42c414403a0011256219038541402200780103c1e1a0071408111600754444104c0c1d80383e00300841110f50b46007080d00066201c000400141c42e00100ca05213403001d16503070238074180d076582003c0300301c1c0c1c481d01c028404041241e008201c4422280910300007020b940c3c1c00303107141448000b070081008103414001000c0c03182c0031011030201a4600c0c01e802d4408030240807912040034000341104446003c40305817003e5880700603403808042c0708503001c0c0c400560200081c80541c032543e031054083d40140c2070310070170004000d42500c81994200000003030305000342c60310620b500340480000c00003e034001031345040c4048288 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 627050917 1250 627049667 627049681
    0x5010915050d0507090503250b120712022b050603030408030d051e010b03090715090308030a020d0212010303080c03060109061803140d120c020c01260703020403021305 74
    0x201c40c00a001c00000003004e0b13a81d103905aa40f2502c0380c00070341e0948200390b40c4240c85446040d005803002c0a04150041603603071004007544920071450301f12622565170000c90b0f0107a0150101c3c0c030a401e81c0c1c1c100542131803081180d440074840000c941c2800280c01c65070b40c1c40d0509140c418190040401d801444c039080c2404c200a81c3c83c07007030051881707101d03950744001150304d8554000c4204c10343c84050042c2c42941e450510440f00c0d00281c03040c1c0903a000c2d01780c0000b0400541180706500b00102c2d05c030800040c2c40d50b1594001504003d0101c040c0c15020402c50b551140030344001e001c298414070400e020381d41503040051400d80c00507e2404809800c0041c0b11a6a0704009520704907a024900f1159003060f4480c1d6a0443c040c40e0300041c42a00e400740003641086e0b010900285038035050b6540e10064802180400548000c1013004025030806e85110400354403030340702e04400c00f105412103020643c1c885050b03907200350202c0c0e143c030010703130302180900c114039100c0710001810045805c00c0c021414000c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 627052167 1250 627050917 627050927
    0x90e010e130c03020301110705011b1b030917330a0e0a023601051003150b0a030516030b030d110a02040e060108060603030705070b0a050d1505010915 66
    0x28241403020941e1001220801032020011409194007500070701c000145140e1030001600940f4044506508103510307000d1381515441e0309010641c203581c987e8404441c1c3d41c0d00820208100c501074003046040c417000324103940a141024080c4c2d8115000780800b5841404011a466611010340000841d10000c0280140d140740427641200300c01900292902e0610700302c600c0c040302444000e410042a198440d1499124024002030f502e1540201e002018968200100f220b02402010740c013010894041c0d070030a01c2544004000e00a0034400404d1a031281d40c1e44150781c12040391240080e03114400c0121009545c1882207501049060034080c0303000d40e00006c0d40301c1400803086800c205146070758810111040062600340e6030054010000e0b031440540540d02c4580034010035146216481c007140d140d09000007215081900030020b0a1014208440c1d140154086213103403080003018440325601110f544110300710020049440480145404005446032000d513006a41c04100d220005030f0701070700b00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 627053417 1250 627052167 627052171
    0xb190602011d0d03021b1608010506010201090503160f1e0606050a1508091213030506090a05031e040e0a0506090601110d21020403080c0f03030103020d0b0711120a090e010e 76
    0x6800d026846d0303901504802c8222031445c088101600c5446200d09202c50300300041d00c00c1e10404402403085948800040e400d0310076060000340303654020000e42c20741c1406500b0000300c061040c0b90740b1a188210391140481d0821341995210101894046c0720104a07092051000616080e200d40e0303155403034844c160380c220703410102890900602c400001d83c010010701c0303036078007001c11642c000b921074040d052000081105030008071914418000402c0c0017660024003040040c1d44400103600d0214004010101001c0c1c007065038034030903024840464120350030b0410305c2c0b04400ca07030000941d501c0d2803400c21900060160019040c08200500642c0400300440d409138142d115041880480c030700d000d0040e20800d40c064042440ca4404600807080200c4100200b41d41784101080741e200111030782c034003a1039100a1000a40c4121540a800d00040d00c8002c125440144c50424804e244620518182810039806218072984c20000d40c4566427604148003034007401c4024618025907050800840b909140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 627054667 1250 627053417 627053443
    0xe0a06030f0605040509010608012318190303090620030705160501020a03140a0204120215090406031209080a0c05310903080a0912120b190602011d 65
    0x3100401c07410400079400c81c0e8001c0002420800803480e2060001c1d0081800c0e0144400310f50900c0181a4140c1c100c442c1015103003c100300e2074001d5101c05100400030021914880e0044c090903070b154603c944001600c5e602603001c0d17140070807190414541034045039100c555510707090002c1d90780030201b1520042660b034445c12070702b0a540e5a050550650880c031f880702000929540c00010514042c0da030503042080070f40030b494040f483d5902d40c83d007810181c0c0a1401181c0781840c00c003503071b40050f00d07000004c1400110070360111803415510b04040744c26582550001d072180120751a2000b5010b51090b60080141910340c0a041c07a413200c0c0d6100b5101c505903200c0e00f8440e050802203040001206210130003049810703420000100750b0b61880e003000e07210350103055000c100c100300007840385d0741c941c059103803030544c0051210490709198000f5201c1003c0040328203d990317514002801c0319203814640001c1042000780050009143c031800900b5104a542d44e064040d030322001d10043e00d00c00042a8901ea49 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 627055917 1250 627054667 627054671
    0x70b060405160e131103040f0506160e040b01031d16080a11041a1806090112020310110d06030803010e1f060509030102130b0c011a010210090c05060304030206160e0a0603 75
    0x10b9503080c0c4091700780080030854500300007007404100480341c403ca529440c423132001c0e41c01d242c1d600314220788070304800c3c9200c10108000100d1000541b4061f840074100c147d05050000d04040c202041801108034a83d00040316400b41c0030000d06d0480014907940182150303001450400d142d65210790f8015404000c2d10300498480c0d091440f0031002c241c52103481c910190040440002a090b811400041a01c035140200340d00b500218070300c8000d620742c030384040c2c0143c02001078140010300740009120386140d0200d10182400354002040c2c00d40500001103010307012060716541080f074440410310340a40440215846c5142e00c00c650b860000681e802c8512608240b6124011000482d02a2003009060700340d004200c4004200b0040c0000a82a10700380d0134000c222002c5614080a0b4801c0d42c10f403a03c0c00350740050360403007106200c0c0d00405901c9115400040700316540d5004900e00b81c20584044000d40c219008100700311802126501c1240e60034900000c529094101059685100d402841300701a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 627057167 1250 627055917 627055939
    0x203014104090c0504110d0606080c0406050a0e03011e051f0b0f0f0d06080d2f03040b0301060503010303081501080a09081909050310051006030207051002070b060405160e 75
    0x8045001c0703c0000300409003051146800c50f0303000303031881e038824000c030482c0da4030302007000c2203440c031911302c030f501c40c816000c0100d113043d080000a441d45d030001010801000701c02055840c20740c40038003852801119032009500d01000342c080000c1900c8000b03114889440310000b103610300344102c051a0003110f4031040c0450381c820151943c40140c1c416810307040001c10001802900b40c01d6140e20680881e80d4001c107443c0592006203003100d070744191030441c40800001d034a00340303d084184c040d0014403030381d217500302c918ac513555551515854000b40d210302c01041c0084010803e064203d40402d9210328031030799006032504c04000180001c00007030103c102140d52541c42100308034140045072501160443c042008e0005518010711114080c0520f6000b40180102c0f41041d000c5c0740107180c01000303201c2d42c0d28100f80c10000300320025040342c0c005a4080c8580000c040c1015180e10050010f64000c0304280349510380801407009442000d00620240f01039280611025a8440304c3c42c0c0401d1002c640e14003181c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 627058417 1250 627057167 627057173
    0x10c02210c01030c0206040b060f1201050103060e1608030f090d0803042003010e151e070503010914041e060b27010e01030f03050319020301410409 65
    0x564003859100c8400d4801100c10001150009009001e1900999041c03201c0320030304000f20b80f40e45042d06c00070500201030010800515005604c0c2189030070141c04290411144030425094a07402c1c0d10540d04a03543d40380500041d04248152910381c1d142410142c043e515000e00e4130f40d244180400c0d200035a10109110545503201107043d00480e401ca500785840b810542000d0182208c200c00c4a02580d441d903504085a00f81800344038101c1800b40d0182000d80050215100c3c0301d940248411036401400038104641e070303016801e84d40175521998030552203605010403502220b40400312014619003d0342000b0001d108040c5182c001d103031005e4601c110f41d25610305840504149402c550f8001115850030601101c44004040c1140720030314100b00690b82c032540c0c0ca8402200303000c043c003d00400460300d80824003d80085422401c4202d25180c2c1201800220b002ca800a800445004100e0703140c204088581c0c4c0d052072a080c01c1050800030800c0e0100300440543c41640141d8007403911480200d041c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 627059667 1250 627058417 627058429
    0xe010e040818060d02040602010c0f08060a0e1f230303070822032004140114100509101e030c0f0c02060706050f0417040501080c090d1b1401031a010c02 67
    0x2803192044c005545803612010003034080c040e01224580061002c500d00c0c64898400c0200070b002d103801070000c052642c1051224261540010302c444006045c40038070703e020103002010400103280842d080d220345000e88840c003401020030980c0341c0c448c0d401070107100b020489240403240f41008281507040d910305010b45071412007059038005020601352218052038240c0220841e0260041200c1c20080100030303008006184000380501c0d00c0d03501c100e000e43c460070308040c1303a00c0426249506001c0d0500c1075a40018581d1540700d088480001c848000c003060000e0901c03802d00f6034840c00d04040c0714040d002c50000304060b5108001c1010028800e00c170009548a050484100c41c1c0c0005040c0120314001c0c420b55464401a2021540c441001e405030b00100c404005035804d40f00140d407402d8054640d80d0314080315800082c1095802600741684100241000302c00e00310f418002106242c84c0342c948000d00c008000540c9219040c1802d24011482800d001d07900d50b500c000c000d0070b0810010b200d500100d18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 627060917 1250 627059667 627059677
    0x4030c05010603080405040f1a1011240a0912050a050705060109020c0c01020a05060415110703020f0c1206010e0a0e160311010905010804060b1302130e010e04081806 73
    0x203194605007000c0180b00c0400020001e035241600c01b800b034450721205000481e5001c80860711259000e2845030214540424500084507032880d100340701d903102d190058100145c242c0400307031768401c209616401d86021481c540e440750b101e10041040041e1600c404c151b00301d01800040402100203424044e26005070103035800a90054100c414540e100c44021009621000d00e540b860300c2022200c41c902e62000501d03081c01544103015003d81d80310740e91100040342440400641181d201c3d8000603020109030080c0400e40c1c0241d0050a02481800c0121705100e01c0e40c240a0040201801c801001c200000300c86046411000301c911035542c400018100406d94019441c14034087c07000c07012740440d88408840252401202030001d080b2010006480c00002c0344146030110ba40306000401003020f40d03000c00c1c002e11001e0001050001d401100381c0403a403081b65500c40200135400180a850040c2800d540034081d401d00025042c01c0c140c9512040f400748203d0344a20441400110380b01d5202c0c40300340c803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 627062167 1250 627060917 627060923
    0x30c0711060c0313031406041509051c03020904050105030601080d080405011b020a030306080102030f010306150302090109141806060d03031401060305150904170f0909161e08060904030c 82
    0x40e4544048081d1080644d15520090340d090100102c0c2140b0348101181071800f43e40d00601c00c88812407410f80c0c074006084145c5040e15035000d504018100c4034040e0010060000d0941d0780140d6549460040204071181030b00038502950101006012000d030024005421702d00c0740c20b140559950b549001405400500402d1044036135030042d0600c500c0d00003030300d040d406100351001d00c032440d12060070700d00701e0000708c4003d0a1003101800400200e031066000341540f140c01101c0480c00c44c1ca0343c010850b003000c00e9202c1344a1956031009c1060005e24000c10b6900041041c415900c2d170a070f14444c6035a41d1001030301c3c1d1842194035080310030406000b644000400740120070740000329030b550040a001010200ca028203241c2c146070921809150000740d107071040f54801e41e0340d950000c12a140041682200e001055202d20401540c0308542e52001c20602c2200c03860304a480340200c000004103802c4956a070107030a4035800c0c4d141115a0f400c400c1e803d5015000b5602080650742e81c1c14101d88003c4290b2000e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 627063417 1250 627062167 627062173
    0x70e0307180f0903030b03060a140c0304050a05070b090a090216080c071203080411010309020d080d02042114030a051e090402070c0905010b040810020306030304081f0501050402030c0711060c 84
    0x741c2c08154154006c0c800c4200f04605840312503544106d10801d50340d01e04240c502c2e0f400d0f0300000407074600400c005035800500581c120368800034181e032224946211900424140040490a019240b5105840301c0151109075000d604254017040c50541094410340028050b41002c2585c01070710200704425030046c2100c64001881c80010305014003040c3c004d1b1030030303107054013150314805042d4024080c1c2650303d40d01601021000800d5103031540c480e00001c4030070754059001c020000300c010402c0d0028001d03070b0200c036090008581d9840c2c11a03040071000d084a01581062200c5800b9039048030589600750f803034500e11200c0c014080744410061051811441d4031500c0421840140142191003105a4121660030404d0344d8039292008250b010324440d02040d0b81c407100c440c03016445a50040c68024501908490820761214000c42c20100c0c0001da040c080800581c3e80f400803081c40c0209401420103907411031650070000c400103214880c007540030307110741c40e9110708403016190710084072402c600c40b40075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 627064667 1250 627063417 627063431
    0x94d030601030c0614040302011b0219030b0a05090c090403050d020f040905060414090a06020c15040b090c0d030f1803080c0f120a0203040510021221070e0307180f 72
    0x11241d4080e2035130040d0b5001403181904074100040346800c42d801d0340c0d016107482c4100e400d0a840700000c0003079500c0485c0c206000c015641d40c0c0030450f034022405140b107000110308924006245070100d030f600425003002a0321500381005243c84003000103030055014586540c2c3e0322400c22000000e40310782c451405107560300180c00500302c0403950119000700b608171402d11215035001d07981406450181c2d00145242c0040b126100001e810354010042141728800307a0392a20b1000c48030403c9604120f50980d590f010620401507920001d0000c0154804203c3d8030075090f43c01507c0041c1740c040a40c03440401c0c0060403a01000500c1803019030001964460302e820750710341c510040181ca6222000071202140700304400e1200141015054807a02456a80150709082c54038040040904502c0e01020035400380322030030b80105881c280100002e41c605030200081009a101404980d0801810401044090a1011595030b0042460001c0720131b160812118420b030711006400420f00c10311941d0038035103031120b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 627065917 1250 627064667 627064673
    0x121027060e01420309060e010c050a1106010b0a0c0302011805010b030f030f090f0d0605070302070b06012c0a180504020423042310094d03060103 64
    0x1c10300c0d80001c66400c21034429889140d50043d40c0079600c603da0822074001200e004101c0c42640840c03903541c001c1201150100800c00031a0841e2101b8200c075000501c0090951001da07040300c2640b11141104008043c158075000c251802800340d501e0b03441c1082040a46181458400d401c07132001644403906461039a002c03460014020880c03428000d003c0d025600504218035004400c2d20741180c00074040900d002524801c100002d080c0d0340c10664001c0e2201c01c2040850030354442c40d0711841443e100140c1c0e5900504240c803516100416843c100316001c3c01003155000011100702c85802c030004500c0e0560701c0000050281041c0d41c200c18408043c0404861511100b608060700603802980c0c00c102c0c0c1c0040810003001d84600020303610303610f0f80d42c1c0e020400090f19114810401d0b150511580e0007600008001400c0546a0131149059600c504020090101005a03c0940c0c0c43c0300e1190a1507210081c041e91495110080188403070544020780f0b041481c40100c00c4907038110043c296400b03903840b45 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 627067167 1250 627065917 627065939
    0x8061309080d0b3a140705090115020c060f12010315050f070519030b19091503020d080901020106030b0a02030a062705060d0b1906050d0c120f0804060203121027060e01 74
    0x1100d1940702d83e034140b00000d046008211a0441c02b50b19030b0207040820208014441c1d940d01003584041000e800b0080d8000a0070b445110601a52180e40349100d500c900e1400e01085d2130020b00010b071140483d0003030102c1150403e04880c0115426901811001c1c4060700c1a03004108a002c260340025011208040c100c01000000d82a1040142c0c1003042d060310110040c4403050701e002c02900b01911044050205110b0805030000030014400815600d8403640c42503601003007959101c1180e900030042c040006a41c0c06071001900710704405016000e08113030010f1696094118680d5042c0e51342000c40da694039048165008282c0061340c560304c0c2d0900f480501038200c24403201d04d0105162501c00308041c50808080d07684240c000e0400b6111900701444100310110080701100c160b040c540300440010000809080101280e4001d56290001c0d05c5100510400082c04106800c4810500344410312800c42340d503441e11828400614240c1980d800d0700e0081109401c03844d510450f41e8000100d02c8210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 627068417 1250 627067167 627067169
    0x1615020105090606010c02012a0f03030b100915030e06090a051b061b0321061804080f0c102912070608061309080d0b3a1407 55
    0x15a000700311a54070441c280740c40300401d59056000a0750b01d074800c80558410807022440c3c8000c2c130000c0c0c000700d60105910904400154040707448481c1426000c05254040c483d50001349400d43d00c240300b25040010007442035486005011044281050500803244298420103140030072070112142420f01007185551803890034821070301c91007000c0c03440c00300b0500700581c003040000c0030f4201800c082c4000c4242048800310108100c461000380030308a03201c085003d100354001c00a601c08041410840140b103500003101d90180c2c11076500405000014801c107045900401c2c8207085641c40d0381c031925440c0d0500750854108060941405003010b02c17528824180300100404001308040f080c0c4201c18015802c2c0070035030082a5800c411030401000d4000c4c40d205901460080c01e1500101c2c0303207082282104d01e9017005540040010450040c449035600c1180409002200d0904408003945078518090762002c071004044c01c0c02040c040e40e134114140d0503904030fa41c844902041101c41d6141250303102c0ca5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 627069667 1250 627068417 627068459
    0x905060114090c190807030b1305160e0a1a1308072306030a1a040906050609010603090c18060e07030b040506010806010f05030c07080a0c061b0903110316 68
    0x2000d000c02c21090080045a031302e4900c43d14500e26802c200d60059a01e100c00420000c140758541e81a06185da50f001440701c14107070081d900090300c2c20444100030101c80601c4100042c003004000c0e070a050703584e4003d00c100b20740b503400c11541d07220812202403001d805a50940604602091404904184082000e100b55031009015807030803400d01c1c442c09003000c00035400d203812100800200e08150b640da082040001c46030003051800c540110082800c5949051050724895078900034400103150180c119401010035181c14042446651101d5180c0c81c500e2207481c205200003818002c80d0007154100b20000e10644020110301d1800d410040c02401c2c039039980c54440c0346441c0008076a90701600202d4094507060391007840503028030700d0540d080e03403010b03000116000781030040b2800590480000d11004401d643e40e6060b2a985103443c01c02d4a000c40d24101481d41c4054003c59200d0340403800341d0480307030000060394017140c00c030b00828140010304400ca030342c1c21000b1750301007120824400486c2c2e405d11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 627070917 1250 627069667 627069679
    0x1b0706020a290705120702120315150f0702090f1b0a0201060f0308031f03080d02090f03011b09080a170a1101050702010c09090515041d0a0c030311010c02100e010905060114 76
    0x7940d12000c0307031101204412320010705010320108028140000b1883e0340c446c4081c1894405075840b520f8440550400e00245140c01c1c00002d480c0118241115615004005040348407001c2c01e0007514035950008001043c0742c02e120220b40c640110f8070135000000140181c00d03410322500e4881c1007881d29603100701c50000c8540c24100003100050829050074044030380103050070303003040300c50200440694031803211503602c143d03510021207141d9000c3c440c8084800f120b100261003419200c02c0544070714030300d6100c0402c98004903408004100b41d084c048030008464502c141c0d49010015013034400c0981d00044442640c81d02040150031501513000d0f020038406601d03561491a52000081d05864003101c01c0440f1100c1d945648550742400d41220322000e00d0341700c0e0030200da035120020038a01a004902a20b0700140d0701c4007002410380000004482042100080c00554030000300a99a0b002d281a040401a40c518010451407000e600ca0f460003a440402e4680c15650b90321440d00c494000003020303100340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 627072167 1250 627070917 627070921
    0x1c050c0c09040c080724080637210303200d02070203070e22020a17070806010b0903120d09080f03063a03020f1002090a080a0b0c03090a020d03051b0706020a29070512 73
    0x11030203c0801c09000400c400210ac000c01c1e9804401a11081c52003040d125814803036080410b0b03405000d007907010f0014100684900a034010589400c0e807581c800203107401d04501740300c4040c103a030241e0030391458526140d52040e001440882c44082544d4014030601440d00024004080042011800c55594000329030741d40e62641d110303c45901c59540d2103075059008058000c19080e0860180c800701c680fa4500151202141c0c9880c40c503640190102d2001910000401c4698908000e002011050030051001c0740c402121006104103009480d413039000190840510404d40708000003035448101c6000c0d100c20a40f9215824080d40180488134071642c849240400d050800190b00e00e825608000c080c20381da10380308502c02c40c3d0392018008480b1802581c49190168a43d480d03e000c000d8403a6481a51b0365941080b9001c104007143c0c0c00e81120780010700c0400c95030740e00044194030240c02507482d41803440078480414040524105590b449a102002c0001480d08100500540141000c200c007403a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 627073417 1250 627072167 627072179
    0x50d0f030201060e2802040503031306081311090a0b1c0b0a0c0905010f030f180b13080915040e040c03030f021c050c0c09040c080724080637 62
    0x360304451217410003003042200e005405281007484000d8019100042c0b030141c581d800b00b400c5a0022051494094103404108902548078160541c01458010f401081400c3c6694690029410a4109200b0002c18000c5031103540345503c0044198030040041caa0801c0007042aa0300c80c4240381d05441c0308903200c000500c240301c103010f400c240c1082c07651008452800c1c0f0b80152080220003400100701650340411800e0081070303100300c04200c1162142401403048070300d05003042c980001e007100c800750209800440001c02c954181c0d8034031003088442011000c01090f2461007400780ea072261840c080c5a900b4401440342e01448407041da030003607444201e0705138540c0c42aa52600300d00d019031844101d88515407030640c818030180c82d400030002c0030703036038ac41e400c803030000e0400c0100380c401f500d000c1c00c268010411124100b0010b8020800c3d552100450072207003660580368500740c070148050000030000250700d5904c05c1d034110500d02291013440240b208030031f40002c010b0786403400029075000f0b0f29400300303203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 627074667 1250 627073417 627073439
    0x50d090c170a023f0610060314060907030e0703120806030d09060806060f2b0b0303030402060c0705131e0516110c0a06030f05011202090a05040c050d0f03020106 71
    0x45036005880703a072018141155040c07218134201201c40200042e200e0401000c61031a03d00d00c0d04111201c0100110f040a00d61986e40074160b601481c10706117001c10300300c02005240702d9130398843c0d01110307150410b50341d019050b0090050318104030380303130b000d8130340b01008000c0d017101c86480c0460f255885401c1c40c1d0b607030410b141d9100180520035000ca900c00c001006001d1190352150303806903002c3c15507800c0014007600c000c8160000e08039143d028040320181c85540b03244035503070895903403000024803134010b001012a44900c0050b10282c054030002501d801e0300a030800c0450000d1034041e110304249a00c2001d81c01c014401c1c08080804021201807008082d031240c0503490143e5011540006201480344083c0c5020500c0031040c2428020520721202035990804003400900e81500c001c9900d03d9010810011104140c00c040e040300040c68010740503031191002280c1c020215040081c060310b96080c076818102056105551210350460068100306100c0b0450702c12500c039400a21420b5120601021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 627075917 1250 627074667 627074683
    0x30c01090c050f130c1404081c0201020f091207050a0e1005030309131e06121407080d1b020a0b07021207181a1005030103050d0503040507050402030601050d090c17 72
    0x26100900340318050130b02074594412003080304c0c1400c20341c02c500c10001802c2456001980700850940001d4240d50000c034a601800d05215003903c021441d000c802c1c82d15400c0341c002c00b59017900a800080b1400070b010b00801c6000060324004014281065452401c000d9190040b9400580031a20500010341d504002080c0c0c0d1a00300d0061038440c00782580180f4400805c50180340c4160070310421556020086070f0711400c0c000d010501e91040c052040c60400d01d001c41107503c410051340d80000c00c100210180400d0002880c64249041e548076500760300d0308071003030400c8500a03510a403030101c0001c1581144004000091081e103542c00a2066000e42c00d4441849106500341400280801090755190380c0c04400d8510360510216002c06050011900d600710748018440854000030040c414000e0400200d5241c10444c54181d1440c40c0039600c40c1d4039041c0074403603140210340101c0801c0c05a07004805503080307042042020880c5224a05040c095150244584880242e800303100c1110f0300001704540c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 627077167 1250 627075917 627075919
    0x606120712060f090c0f06110622142b08090c060903011e0c031b0909020a0e040f0617071d0406091202030406021516081008030c01090c050f 62
    0xa820301c03206031503400c0070301241c41c10181c109a80d400300c0800a8094040300c4c0150620b000b84000c180d00307103940900700300b170310b90114071096101c0c00412880141507402c1d2105540d40401c9240e5082a85ca803c001518841c042c0314200d002d04504c0f0429a010000c810980e950301209504981051107000d8650500070b07a021905508040385001ca0750500350300400781108050000141e41d04c240000882d41c0d10b00004420140c2e0300c402d02c0041055050180794248001c0e11211840d0000c11326003d840c8904503c20b0050498010468950f20342c043d0300c0c0c44078240d401030000d1055030b8a981c81403000f00558001c2c0480094805c400d54460400000d10f20180c4d0723040243c05807081c2c0410414100500004c10403170b801902d40080600080c002160b80341140040e4004644450038507801074103000340c8018101111403c04200044071030144000c20048180d42815401511410280ea0610f1503580001c4040c0c17000150315240501c0551200007494002d020381000e45440c1d2003004201d0040d0005a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 627078417 1250 627077167 627077189
    0x109030503031b0436060506030103060e03070c0e040b070f090b0903030d02160b0105030c0f09060f060c07140607020102030910030b090411100806030613050a05060906061207 77
    0x843c0e0b101000940d2600c80d101092403818035a0ba01c1200d81c500524000340d4010696041a9401c00329401610b07240f03812240c08240a4141044045681400148006403107036403a87e480d00c640c00070030310444181a401505921049448120482da820800d03203084860a500703400140d1090301c0340d0400205c0041030f6403010401440c4c1426440b4507084880c7d030740d6140c081000380c0303840000e0f248024403036868010783c1030071f140c00d01c3e007007110384110168410b1b4066086101d0301d0a160313545555100700488102c0340f401d4952500f20101d510041510740c44c60300300000088500e0f128500042c88001c4604030301840140d030481d0001c2c011076014020000380543d000f40003c071f80c0c074603001d201d1544072142880c000406001c031200003103c015041d18203550840c21a80b40300d0140c1002160b4500b08481d07400d010043d814180d01084c1c0c0c400c0700801e110240700da004940b00c10001c0c240710303a0001ca504030048810f01e041103200940c8542050381d030a0b1180c101000244242d4502180c00000ca400013002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 627079667 1250 627078417 627078421
    0x10504021e062809090e0601180e06040b06030c01020a020901090914010912080a1e0c03060b0316020c09040309140105070524100b0d091e060515010903050303 70
    0x40c0c12503030790150074107903840003041c4800b080700146564801e54006040001100d102443c05000d001003410f9084001c2c01ca003401c00032400e500c400150581160340c01041c4840c82c074804d002807001003040c2d0035000b0a9000d160180003e20201650013402030300120140d6001c402c0313079070040e0307682e20700101d0094115071110300402c0301c075881e03500c80f10860740100c10742141c075001d0040260840d20b000c0400c41d0955480d005182c0015031240342c8503403006800b04100321204000580751210f0391440d40042e0882d0702c13140c2a038882c921a40080c802800040d41040d10390400040d40390b1342442a500350b0f001441101c40041c1035140c6880e40c00d009603059143c0c1a034803810502c408004030612142c01d030600c00c04208030030000c2d8041010b0590142070502000c003031450b410b64050380100142c0f6610b9036010f0400c0c1400f1407001c40080b240e83d200406000141948241741140c40305007040901e40381114194030b00c0d414000345d5040130b0700c182d003501114124460118015200d215190001821643c07013840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 627080917 1250 627079667 627079699
    0x2060a0609180f03090833091b06131202032b0c0f0807120e0604080d05070507050402030103050337031a090901020d05010b04030b040f061b0503010806070201050402 73
    0x40140340403406850003045868030b13103030301d1403425400d08240c100c40300010071b0700c10b156441c7d079404a03c0307040c0d0600132a2040c106001c00036522144448083c0400704103007603501c0300350341d448110741c41c40380c2044404190503558610303100b031211503603000e034000c1c0561071004100d402c410240c0c0034441c0340c111401c00c0f150a40380c02250002c4000000f1141102401c45860100314508042c045451142e801c0c01e000820519004008000c00300c3c01c00d00841051000380608580070503000041602c0346456605c5202600b4a9840c00b40a6800f0903001480080040b040c084084018080d80341c9038401c1180c00b14512641824001d0340c1c103401c2c02c00b00c101801426290f8441d4001c9200c3c1003032490058030800c1c042e000154602e80c20745039800103079400100d0b14a068814000c95006019000710303d41420300d903849000d10310340700070720080442c5c00c03151200c010802d699020000d42022000480b02c81910024087c200c1e40c02030240e2003140c4607100c005207000d0b10500842d88625070190560f60701800c0c2072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 627082167 1250 627080917 627080933
    0x914010c080d091e032304050103110d0504060902180403050301030b130b0c0d32100f06090f1e03080f0702181f030b0601081009090302060a060918 65
    0x4403080c4003540c0328202200410480345020a00070020b06600031860b0344c03498058038040040b040d14069503803841078922a100c0c0081503a00706c800a080100e48611182c02d6440644500b42146030f0042c030b00740501003445516480050541d10a45111500300c20b1704c500034614410485008000a03010401400081d003005022900a50810f1050f9590100c903501c00130310f81c0301145d00c244000c3c400b01c0c103822031202070701480310290b1084990100c0001405a03d40c03a0004c5102d00c1d0b1103c8400c44081000c219030b5800010040241c181516215511188000c04540a030b21504052034607050011601a103112001a015100c0e1248805075926555490701140c0183c000c255010030140485005038541c05507100c4940800326084040f0700c4c01002c00e40081c80c455613038485031b544840050000405074070026410030390901348000d0580d105070401c44003a41d19040903a0700c41c00d00f030010b01090340000d460ba00640f1551410300071242c44084040407507510010b142d2012807258141000705100c1c3c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 627083417 1250 627082167 627082177
    0x7090f0e0103021e22050c04030b04110102070e090304030312020901050a0e010e12010f0c030504050d082521021602011211130e13020915030f100c0914010c08 70
    0x403030050103d0b2512800014454a2a4098042411145c0115074007006a512450360700c14802c0b000141064103580340c0084516000b0002851a1890180d4440c213038000c200e200024055170400d01080d1038245401901da400c1840100e01282d44180901d80a00d054002d842c0d0060041c0e640a00384900d0314007c0b191200e000340e0302d44c1400141000a5100d03107401804216021100002080543c10011650103c1c1d10100b508020507282c1000c1c0300020f0030100e0145e1850b0707041e1805000c1911f44207040c0041709100d0304500800c00c045c02440850542028003480b80c201c4058120000079820040e0b9010b034414050705081e441c030304a00c444010360003001002144c20400100003420391199040501c551700045880c80102042201044451610040c20741c0c005002541130349a44126404038518403006011800009400351000c0400c0e00e041000508203940b0300c040310655140d801000c030007020000036620008261040201e0b510340c50040120f6019410307540c1d610000607a46480078a500700c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 627084667 1250 627083417 627083449
    0x9090a0c090612120e130c082212091203030e0c0307051513030609080c070f0e06040507020c030a031d1e120a0c08060a0e01051b0904090c0b0307090f0e010302 70
    0x190380e100d20f82e0712090301030b82012001b002c00240d83d11491801421000c0000c00310103d00783e40302d89203032030341101c280d003100380710340c031400402d00111506804d980558107500024200b81124149205156140e0828000e005c0240113039060002c00c43c0c02e1548410950055a0b00080d104c81642d600c2020040108806100c550146d100e407612999880c05407005107600303603001c1d0000b00e1514080c2d43c007400000010f09051006001207480c1002e071960038000101018030a60b510000911014020b0020380e1032800000c00380d594006103450060024075211034030018900704462350982d5400c101c0901c2c02d4102e007401d52418a02070402c200499030080300011290742c0168024940000e542c41c01c2c4070064240030001d0405450300444130070444198115020b800d0f070516060040c418406071940c500e4010458240d42d0b101004400706001d07103000c4500801c0180078110020307a01002d0b00c003844c041c158035a035074100141c2da4150302d061080a4001c40c018066541c0042005140015080310f030182 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 627085917 1250 627084667 627084677
    0x180c010503150d120215102702190305072f0a051006060806060403020904151b0203030115030e060c0d1508030a0f14040b0d02040509090a0c09061212 66
    0x600c80d4003041d03660410f6001260643c21162100341c0280e018071140341c110b018612400164030f031081c202c501010241c4224034070304004c07568801da46000f00300c8031700c0d0010010105642da8420101c6620b1805026440000040d2070000800c10320740c0b04850046204090161044420b104113500b80004400c18039402c0c06480399400840c001102070024007041c40c06098005406490071101808808004000700c2c8a184100824001070792401700c61604160040d900081300000100b80b5002481d41c000c8180802c00800c0c041196a607000000b18103980e0000a215100d940045094040d04e903843c0004045030009c90000700c8805800010340184200440042050001000d0704d01c441c01040e00001d01c0364000142e01e401c0036412000d50308032100b0501e08200600910003084219002d240903641c103500c000140307109a078031180c05960280c500140000702d5070500c030f40c56560b151508003085680c0c42d60040005919507880c8034140c1210790141103004074180a41c0d804003420105042c03801441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 627087167 1250 627085917 627085951
    0x2030a0507060213031a07030506030a03050304230102160314032203180906050108100b04060c05010e06010e061201200304020303070b01060e04270201050a050c0d050909180c010503 80
    0x920f8102e420300d02c42100d06c02c03519450a0451005060300d034014001c60007a40311520902c0000d5215049a41c8190011300d11445210a4001410f20440101640d41103600100c0c2d402c3c80d0703211110144402034401d803a103000359144a401c190642c001118407100610b211039260181c00310340c0e50000f5565101e490b0040181c6011030801106403200d80120034229948c080070700031560400460f54010b00b003c070181c2405803406880a007140b25a0040d1820058901c601c042007100035000a00702c12024800d1320070715070710307041c036001040c0c01191070364440c00144c641c1e0016140306100c3c5183c11601c0581000b88202281c1103911142d001420480e01071004002510101c0d5081c4502d0f40a0080b40e0341e1114408407180400058074070740d00e942101a801040b45182e200414403090907c20303070a08100c0c0d00c504003043d040d02d0354081c100c000700607800742003c0019010760050040c05050411581c034003e54a80303561950851010326104095a880311149400319802a005550b014403084d040c0e000d50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 627088417 1250 627087167 627087173
    0x91b0901050a03030503072102040f0506070f0215040e04211d19091a040b100c0b0a020f0309030c2e0e0106120803060301140910020304060b0616110102030a050706021303 75
    0x341c41c8c1100006000c0d940401c041c841168401400c2c0000c08085404d1402c2000b41d880b40a40c11a241d640288110401d0a6080401c00e0302c00a5900911080d032041074249800d0030034a03000e00c1201c5899207601241640c54080c00e000d1030208180c0603184005c2100101140b00307001d203407152924031402c050610340001450011790300580840ca40c4ac00100c4800d9080e000901080d900d6100f5407034401d0120b41d1071003400c0c07640404000380c49600203070001c2a0f03031211140030009119005440714828400070821800b008000000c02641580301c1c111401400301d014440f60b4288024002019a04c0065083c1c00e10401034002d400001d8801c000000c05035170320900100640400c03c011070b00d02802004102e041d160070721034070300b80d000b414240043c0340c90015001d41e100d06030505003016190b80400820b0901400d640001d40c3c1d20805082d4030342d0707810340c81d40300b00c840400c0d58000c0302c8240480c5040000c5510102c2611141e00039070b11220b0030407016695a034062f4200e0b0100c0c90413160043c2001005c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 627089667 1250 627088417 627088457
    0xa030b13021c0501050f0f040504060b0303160506010506070b060906040624030506040c0206060603150d030c060e010e070b090f0a0915080c0d030503060117091b0901050a0303050307 80
    0x900d0142500c1c1070b0070444100700c003016202e050744410312401035004041c50340d0b1980c507000c00691004850005159a503460040000c081c00000281c240c400481d1f40800002500081d24207103010707008660032680c4c2e4808000c020320841100404103c0c0c004040351140c1000aa1181c2181d001040810b050b0b0700e070000c1d40c6514002461100c1703685480b034034900000303403d4401d403904140266818004a807284401950341d441c00740209018000010001e07100c503840400312402280c0052804c40d9090660400428102c007550065605500e84550070f4421001440b56a598000510183c00442c4c0f911150f200c194002d01d41c01600020310314025002c039502d06458001904030408005000660000015000c0aa0b904508460385c44502c043c820380d078640036112031082e854a003d503620354031900100c64001d081404160100000000d20103040400b0584104c50301080344c1541d1001c03030304010041c588000788242e45c0c200300442c2c014408284181c1c000d6078800c01504007185082010f01d000d0311 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 627090917 1250 627089667 627089677
    0xc15050d231510020a05030304020d0807150207060f2a0306031401021801020312150d06050405010b191d040501020405090103050d0915050d0e010b04020a0504080f03040602030a030b1302 82
    0x1a807034080c0680e9403862401407440030719261540700031700102c24541c0d0303080d03903d100241000c2c0c403800b5500449801c000042c0220784403d6406012001e90038550103034400650400c1d441182e0980c200f2034110041e4486100d103840d042c038a80c5030981d40d03003ca00494000004c82c885c20f101095116075020001c5000040b09081c00c10380600016603420100d50240c7c40302562840243c11034004010405061180d5030007260400703d0f0000510115840c0000140c041c014030b0b40050030a810201000180541035019090030302d03081d00c06500008076928800d0110b0304c00d00401e0300f0b040e50b590800041c1c25603141500e40c014814000145002d1304d840c0000e10710b0009901c1102e944d40060410f200080d40415620700510103047c0e41420300c0c084041c00b405901460094003201c0c0e5a4910500c0b040b03c094000c1e0340220805031086545400b0004010213552050282d0b40130340c450402000603017039000003280e003110220360142d0706102941c0001c84c05048840f500c0d6078006c1410280031101c0c51a840100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 627092167 1250 627090917 627090931
    0x80d0e072c09033901050910020903070e1e0c04060504090b04150f06140f040b0705100614190305121315050301031a0115231201030c15050d23 63
    0x8a041c43c000454101400744544100445c1e4102001d100301c200c4005005200010007600140c1c984d80b154000c640b42140aa001600c81c0c8490428080c1800c0b1680d0b4403000c0e4403100322540416a60f200d03442c1142c0c1b00d00e10801c00020360070002009043ca0b580c0c000c100007180100007140e2819002151078841045401103690091000800c1002903044000c45501c0c0c600649110304140e80e00e15070070b10074000d41c07283c5030007414000780d441f080101c14040609407910200003000020b888500310f003a0703032a010034040e001d25101c450342005181c40d0b2000b078003143e81c850010140ac09005082c000d954001244a00410b0f20140c0007241d190b207100c07401c0c4d1207030a03641d0b42c9549070b600d14101648808000201c1c5001014140d0040c04038024501c0c0340807002c4e40c0c40c148a411101590115540c262040c08640c503082d80105070400c2900784150b246040760b000f0850384c03040c4cd8480154014051400b503429000c40d8041203950001503254104c00b00d0050142c0395a51818201980151030600032a062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 627093417 1250 627092167 627092227
    0x31503060507111603110301020c15150f090606070f06140703060518040b18070f03050106060f1e1209060b03120906040b03090307080d0e072c0903 65
    0x888290743c0841160010600701c401030002d55140788a030461104030740000351198410000aa0154509404541130340104504440340000c040b41542c203c1d40081d00c6030440300b410000c40c10040d140c8410b0307090460710024000b90460300c1d00c04c1003081540c85000c00310380901d600010000800c5a0748203020811810041d603011500e055407000b400c4510940003544600c0c0c00d56513a8640c030540301110350748a94060300010b039075104c0284a42c1410100740c0c40c402036201c1c4000200740d0b40c10b40c02944003228070890081c001140c4a420660b5030500b0080e585001a1a681d80e2481c40b00c48003c1300329800b10581008505508230403980e03800d0307031828030040c0d8007030341c55100401d807a00f410001016880720a005440c10b0160310b20000d00603110324811402401004804070314201000d01c111082c0540c03000c0c0c0269903820042c0b518002c1c100c0e080910b460b5004220001985140001c00756207550280c80d60600050030108004091542c05000c0f40780e079200900034440d1240581c03084440042d00a481 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 627094667 1250 627093417 627093421
    0x30a030206060108100803160c081212010b0906160f060c0804050d03110901080a0b061317070f450f0b1f11030403060f0507020c0f100315030605 64
    0xd000c0c0c410141901380c640c141040c04005406e008030907500540071903400302c0c242c0d48140c10003030f540c01c1c0190000e8140e80600d030b000803daa100c1400415022005403001c10660303903514840c034520f00494a1550f0445005c100902c030001c000e4138108802440346d943c4a88400c49512808101ca0407060000e0204114100b07000500071704200b400d491a61307524003880304149035601c2000c1e9010328490305050050f00340100382c81e1401d94109211214028008a4032000c1042d04990005498032544210382036152808034802008113512054a08600c00200702503d0b1aa440800f184000040d20b1281151040c03000143c07001d0b01c800507000d80803c04171080500180145044880320380b008110685040740c801e541e521040340b10713020300c071101d0403003041015001d00c103460180d0a6a824501400005408803c0012903840450882a40c1004100750742c0c4203c026aa10b4a40080c0c1380d40c01035440d03000c0e14030361401001c16400308600d4500031598180c040c41d041c040d4481ea4104032407407612401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 627095917 1250 627094667 627094669
    0x50402031606120f1803080f0f04050627010c0908160320030307051006150c02010921150b03010b060711060f1204060902030c01140f1602030a03020606 67
    0x41c040080d21100c000300380d89403650150048101007250202951501900d4042440c0c0380c0c04445828074001c0801000062440c00500300d00c0100c50031081840d454001c1003420b05500402d6126030742c800000c01141d1038074081b4000e040001000300c40345c04407040781850208000e020340c50010300603440380c41e04a420546141d081c0881ca900b125600184001c040000c274844111402e045249440a02c5e260746034240440d055229096010303025100303e682c3c4a07000c15059105404461000300542d81038900200c04544a034607105001c0d0001d000340005000b5211609084840142c800c16000f610220640c1c43d508050b01c01246810203594400340c2c0750050400380204500141c0840b00d003403030500613a8030418040c00c5d8050543c0190404503030442ca5201c61021144d04001c4903000840e5464949403503806003c7e0614203c0c06406804681d0100f5401200710740301c500007482e141400e1688420240e6216080341158980e10180071420802589007401071200c3c05000f41e02030202458608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 627097167 1250 627095917 627095923
    0x606080f1c110a1722180e1b0a080d05130e0402031507030b0405040b06011e0e010c0f0c08161a04092a09090e0102041406030406061805040203 63
    0x44608003403181002c10441d400c1c00118006140c6a401000307100341c034079000004007450250403503134401c0d4424140342c81e41c510340c03020f030001c1154490402601090404807400007613400d484113804050b40702c6408445151b401c10310203100d0310300150507c9946079540c0030b954980303030681d25500003003400000c451003800c0101d1070601c040c1c16052114440341c24558086a030790640c4404400c0c40741700010204003124420f4003e036038110740040061000f070802d410300d041140c400790380c0c01c0e011411000b00f00721409058a41d41e42c0004244e11180c40d4041d070b20005403801e4503107050403648501c0c1c00000c000040ea0001e807070f03005000200d00400804008182c010a60232031600a04803158810320852500c54081007100c0903141781d05400f1440340c00030400664030700320314800300c03c3c10740c4003104a00c00035074172140020480d810160140074038448109028203d224602031000507135074000b2558400d0415400542d0010310880000510f141e5074181009600e0087d80407415941e2904148410740c6410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 627098417 1250 627097167 627097213
    0x91a06042303070509070c050708060c120a050705030c0f040905040602070201080705030115050f0d0c120c030203090712050f0607080402090105010203130611030906040f030209011d010308070606080f 88
    0x142c004000260400307001803150303c0001c11400400c410781c40c0c0d040402c0710900110004111000c1140c00a042401d541c03407254001100191006080400041450955001d100e000ba480c0c0c0e02d4052070b40d1195030a0400c19031043c2c04240d0995000c010000e4804e0003841014400e50143d4801610360020740700040401070040d20740b0307007000300520040c4601006450303820036440403030800c150b0b0f551840468506501800f46510401da2800c1681c0892642021644001b08a482d01c1008000501d078403e500700c0c08281c4004485901008040c400780a480c0c0010500e140038a00f1185102c980300001c170710b8240f003160b460000071010000d020444c145240481c0c0907003070034001342d03040c41d00549060040780040e02c110405c11042032114211980c05104070303402c554000d02301030781e603036243d200f6404000c030144800ca0141c0c01400000400c4a0344824407039000350804090f040e540d00e10740707450755250004a4107440d0107a56210004800340d00300401106c5280c00005005542440071404860400c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 627099667 1250 627098417 627098419
    0xe07030c0f140105211506120702060108071d0606070f080405091e07030507110d030203010e060f01021f06090c030b1005030732033d091a060423 64
    0x10f05c00a41c089040400b24175801210402d0038a0179540d14400d480004442c401d4141c00c8100010100302c29040102614425960368080303075910790341d856109a543d43c13103204490380d030140c90306c0300d02c50481020b4a49401c904010505402c04040f500d4014107642205c008941264000500b000181081449140d0050a11304c543d2054003500030703440e2600f040140060101540c40001806441c0034034022080e003076801c02161107080c00e0a0000c0c3c000c2d4403c0c004c1c0703642c5100003070000d80070b8075201c180c1c0017000030103a0240a80c584941c0d50403200f25510760840c00403c0e1154404141c1104501c61104101a9690089040c0409000380210a0300484946041042c20000c0204030b0350482481100d000e03c01c0c4007543c0032a00b612145c81500204080200f040380c00005120f5800e98007e4207884400d9004903e03004c40c0f05088114036101c02c942d00d4032000080070350f01040301041c00e03840350078a03d1100020701e0b1090131800002d1280da102d508446400502d0720403103120068004051010140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 627100917 1250 627099667 627099677
    0xa0201050c130312110316060501050d0302030703120e0a0b160305060a050f0301020d090507031703070e0603130c032a0f27090f120810090e07030c0f1401 68
    0x9140940a40d450b00b6000150104201a0304143c195104035400390b205200079040c1ca8403021700301c00200d461001d105054588a08100c004143c07440c3c030488064036950b043d00110b145c07418654040d100700d41210b10240866a07910200c0a4045003805514402841030f8110a643d20b04031100001d6401c040c4101d100b054541001c000041d00c034041200f0589004481302040b9110010000b40684189642d4282e4242880c4d5413800304100010710500347c070310030802d440d480040707910a1f4040b070004948101c0029440d444004140c288000156040100c0705180d540700f004540b5062030400c16a441154810807810000508200401400c0001c14260f001c82a10925140c003442800c03e0601402492640300e00c85059203410790348080103a1382e8000d40a00c00c148640c244040300300c0e071103141910b1405040c1d0501040310700c0351240030f200301e046054065a55007803200070310080c5000320030304a462054410120208000742c3d0050000c00c0e0742241d8404150a04100403038050752100e410303043c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 627102167 1250 627100917 627100927
    0x80d180e0f07120c090e0c0412050d09120503041e03060509151311090612070b030a0f06030f0f03050c1204030c090b0a0311150c0d0e120d030e03130602030a0201050c 73
    0x1503484000402103510b132030740f500f060b0340b200302e000301d194415030b40010050700c0d0b12748402041000220302c241c0c4595064464003490340d5130f01c240a4040c5d0001c030008009400c00c002c24480104503000100600b007a0340c04820405440350390f81e8044483c1603d00440b242d228440c581c1182000c440c0e020340c4148801b000302162849a41c1d01c445142800c691288588403450001d031640d21542d0a00781001d003810101d0704615a20503168081e031b03100707854000c0000e041000503000d003012401341c4012203a000030198035000302c9440741161601304075402c07070820100f0800320701511800c00c9a080e08681c1c02c1c0607103070740d1441c510300800c0b05191a440306601500300755201c0940d0f603e1071000710807030b5003000c85950b04c034142e2070008800785242034080042d00c002044100f0380d0840007e07440540c0b900d513216592280d001c502004004441e000d201c43c900e82c0003944d0b41450311b110340c0141509010708800c1b40d0600c140c00741c007008490420b030000b50061f40042207100042d9424011160130025828200c7e00e41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 627103417 1250 627102167 627102191
    0x302100e09060a060c112e1403010302090a1a1306080c0a060816031407030b010e030111180604081b0307090209010e0103090311060a0209100207080d180e0f0712 71
    0x4d190811006e040c080121000c181c040d211080201d0340301c21100280c14442c024070b0740c80d1010b00c01170888480012a41441c3c021450769074011281600e07001403250303103180c0d40c521803c0b001c0d104400608811040c1905402e1f15610b40e4500401510706949009c5902800c1c40d4007245840f0308003810a1084034034560401449801c5540140c2021b074609202042840000003078010f840c64076080c0c48205580400c100b00383e549940700d801d0103c4240d954034010000d0104060a840c0c04c0380020008080411100c00c00c00503142c00000c0c55440a4065403e0955409115080c10001c080c110344012403030f0011480b6140c04c0c0030b504c0180000200840c201106c10f8002040c0c0804252040d060650720f070014070505010780c042150080c0d4070821103d480c42e00780a070801a400100c0d585000e5142130381403c40d031900105800090b225140003d15a09020403001c036040c51800c1a01c40c07603981c0140e07010234000050300c0407a02ca40001d01c405021418900d000403c1d445c01c058100d0031480c0b42200300302c10707 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 627104667 1250 627103417 627103427
    0x20304020d1202030714100b010320090103060f08011b0f140d090602031008010b043806190f1d040917130302040b0a06080f040302070302100e09060a06 67
    0x107540107281614038540c11a01a4a54030800f2030103003051044404040101d000090609244808400107000b11442c000042d02130359254030000722010f00c410038004c03090748988081c182c1c0010500d000b080d40e643c2d810702502295002d400000c85030351521502010301d0282d4100b4400f4020a14260080f032101c1c0100405e002852400c20b69100c0002809515944054222800142d0001c808540d00d061851079170002103814400d0090650034103450095902d001d01c00c400d0140c4408644000c0d1012256030000041074007445000050200e8034040c41c561946405030000c2c00814008040c1c1203c904e4000d0706074901e01580303204205142e240c40c44112110b0b850a641b1000569022500071030360301c0d11078044000d1114004c414000400d8003801050746140c0c1800303ca0003641c0c01c20000c03400005000c6040001e004950104152002040105003040709183e4424060f1050300d0081d5260760014402d000d40000031000540b02030300845851610022881d0800021600c401e9124642440a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 627105917 1250 627104667 627104689
    0x507030f05011506170603032b0f0903052205011b031e021501080309030c150702030115170c03330a02043f020301090609060e0f0102030402 62
    0x1858106400104114007500000b5030b0400000c3c0882082c0d440e500010b11491001c03032100015104400031440c81d080201c1111141015141ea41040d1001114070700824a000000d04803610340c0d0700c0448415010300d21170320000f14441d6071016505c403901c0c08400d424100c20b00c01d54045004c40d680800280e0780118900c00b04e10340651645c00c1c0c110207400c05407200c0e078080030610200200030381089a00396003c42c07958000d805103096050341da40c8880300207a5034010550520303003540c4183d0004100d840c200c94003460034516101414a4000c01d5404242900c0b007120240f600900014000e1041d15040010080c0c7d0305200b8000f031100d100000c0029a0b2008407054001c50700049520101c4000748003c05051408564a1080e10701c0c28010f40e501c000354002d1051000420b441014a100240d091690304001c0040f40686165003229450790010070886282c200d9142d9a59000c0702c00040e0f060203100360f103078001c520000c2c1d400d042d20592820130100d81820302c1903034410020400140d442c0400c0e01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 627107167 1250 627105917 627105923
    0xa030e161d070e033004081207020a080f0d031a0a030b060a0b030f060306011a07061104081b1003090b1b160506150d0201050714010605130608060c030103050703 71
    0xc110303444112050f140c82001c0420380303415000e81c9a420708404104095110401c007120f42c21103245100540f400c170980164090072106402900103400c88000d940041c0c070300540002d10a000440c0c0c0e03035114a01c1c01d1001c0802d29076a410845141050a4152192060b019030907050800c0d1300341c02e8400102c021500b40401001c1110f0b1030042480e5407908000c42024000420115035242461100c10444100494515210348242d40000ca45929058031030301c0c4184e49803104034102101507030750801030000d5400580300c6174024000001c1802c4100300e5151403041400600c903488841605010000140034941d42c14035080096400009510901c1c0e5940700024410000f0101e82810081125105840d070040c94404410880403e01ca130118410380158680310500c080d10120a09018044140260290103e40b09000e01004580701540d1113501d0302c01c0c0300c00091202d44800019031905003c00c0c5a03203a299490b030003440404401c0008035000f2180c46505401c56146a8826030b84241501000b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 627108417 1250 627107167 627107219
    0xb0a05010b16050c04091b1707090203071b080d0e07080709151e080606010c11040513080a1d030601140d05240601020d082401020a02060a030e16 64
    0x282c050040c10300407031008040c010070602403079a51703040406801d010840809040c0f44010000514015800e450042c0c0310424000b4000d90b80c1380c040d25500039000100303500e041c8200d10103559141489500d15402103441900c9458441c60149407041c00c88814482000050b030150400740a040302c0010040e04540c85194013050f4505003e901d0412a0342681c0001001d880500b000203581e180ea859101c103855800080741c55598500f00111076081d880003001d01000c02041ca4002c02e07080c81d0308200c1d402064850000141461a6034051140c1d100200c2c08001452281180e001d54003442410910000110300400d66941030400c0c0d2103441c444100442c1c401c4a02c4210141005014000d9400d40440003900703d40d44088000c9074011450112035450040c0030390940300d02038034001e0030020300032038142d00340c50591141c1040e4080500042d03070626055208055041e00140e99500040c036485020343e50104d5240140803101c0d292401c0b00c9403024000140030340c14000c2c03070000c14a840039a141c007620 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 627109667 1250 627108417 627108457
    0x6050307180f1506170403050406050c0c0d080a03060807033f0c06060603050f06060a0504050d0f060501050909030a0806040b060d1e0b0f0f03030c03040905040b0a05010b 75
    0x6420000e0150b20940740c02c050510701c0c031115007418a0501801c48460351103400d00300300303000c103250030b40c001c1281d004001c9035081c801807068900c24805405103031022001c4481c1081e54800003a90301504483c1210380c4240014104062607150294400070001a0018440c0300d056070788080300034814001041c90f01220000414a00024584003101a00301d14110030101d4046900142900c44501e810f1300e025003042c034000b682e140f1a2042d14816044160709103410344441041160a5105000c01d004004041c480466940d8801031003e2800d0311445a055203a42c176850124251041640305a1250881c002040b100200100c11200300004e58034190300d1030f54070580054001c005052489401c080d000c180707040d00101c035a0003110400c2810305414800a450218441550b15041b603071a044030b2074404010643c107101180c0c600040c0024107a0742000710842d407052940e00641c0c84a00700316107075001e100521028103603a0b500321310240010700c4a9810520000240c1c41401c00c80f411003014042c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 627110917 1250 627109667 627109709
    0x80313050402070204200c210d0f1b110709061208220806040311010b0616060603061811030327120106090b03060a0c0207030314090405040309031506050307 69
    0x4000d0001001c00d02e4850f511b0914062012990303080070401070110b114a50700140350394603441100c000701c03c442c6200e500e4409411406005481c0e0300400074001ca455103101c1c0e10300b0b5140c55816480c02c0c05d5a032004072182d401410036161003440c0c1d000c03055040ca1f0082c11701420005118408099421560701983c0b840c00003411a4000308121503100f0400c7d0f10b407408a0218800301c0e041c1d029901940d40c90000b19107034107220b8200c83c4a9400b196208404014000f014864416510969030041200040103580da444050650320520100c482e1840c00d02851000c100c3c119040030102081540158108010300c20005090701c1c8065110864100c968075038200c0390b171030315000000c1100c048001e201083d40d03840120040d09a000b591ba02c83d0082c100003902010b4a482640380d410410750003090482d00d9501c06449001c0042c01d54046440208100004c85e02e0b6401030902035886552074490481c910304000e548814207046100780141000f904000c1c43d0b40018a1f1419161039401e0f1940e0564184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 627112167 1250 627110917 627110921
    0x12050304030b0f0414070509160e06030a2f0405040216050a14012708130b0406080a050105120d1d03010501090c0f05072105040e130309080313050402070204 69
    0x15000904581c002c4040010f544103460b805801035100b01d4082c0d0b60041c1005096850b01e0080c06555041044100020703a038020400b02541900030908085090f10101004a0020742c01140c1401c019030b2103110322038140784500c90030456a5081d0f02800969501c2c460800540d22807403103102d00c960f4010401500032140000f5907284140c0c4603003102c0c90580f0760301d03000d6010b40580400d50429443c01040c0050b0300446d04000111403031003064402d00c0521aa109046a0041100400d0103885d100002c508041c8680007480584684c0e11070002c0b5260402000c4152901600a18050030f516808120400c000062540d0703801124201440c03501418228503072007120100740e0561543c00e01d000081c01c0c032003c0d84400600030869135020400301c0c00c1801034500f44a8428003e010b240361103100010004c102c10400c0c041b90662400c907141503641c401458100e00180c0780c042c12400303a0013003501095040751581c001010340b580a1402c101054912420f0a0920300c215800380c2d40002d40704007195601c2d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 627113417 1250 627112167 627112169
    0x70b0d0f0e0d0903020f060702060f162a1703090904020411070b040506060d030207140609090414010e0c0604090513080304050604060c08060904120903150920010912050304 76
    0x144080701d810311568000185a0364503032000740c5c019500000200705a042c224110340d40190003403c40c900d800703081c3c1e04c9410aa44440c5564008110740c0b049803001070050203180c0b0080c4203895070a030020081c1d80b140c9041aa9a82c81444954000544030139519003f00680703074400400c80341c0c075450350350314004107014000030034484006040c0003411004000ba0800c19900483c01142166410341d101c409111a8425819029000da80007d90801c0b0105660308240f5030000060556424400c0b25004074141c02400d1318119090b0b9064510540115000d100b611907208200c002011001103040101e58148070b41e0144422240c3c45400040c0703c080302d0f03102e104072968882d003025541c2c0341c2801c0c21a06d81c02c0c01e4404903012401c2ca032400811510851420b070140000600c1101c06488a58460981021030100e850511140410002c0410240700102e40000100d4001003421951854895440001a030140c24400b44401542100c0e136484a042001d40314410341c10621042c05040c100c0c914011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 627114667 1250 627113417 627113441
    0x2d1104080706020609060f011205010e19060b0a06050a051303050a03020622110f2d01140301030503040611031204050c09090a030c020f0105130b040e09070b0d0f 71
    0x40018001440d40001520908a030000e50a0303585a0311030b150515110241541e05545006100c401484030107a205842042184907000000d0300d010303020006c0d401c0c4180190b5510340c6400b2035886100f0311400c0c0c00389034018081101d1740b541443c103041c40030385240940071380001000342c00315045a90040100400d0069074000c01110201469454001c0d81c82404a902c6004114540c0100c1400c0084003000c42c0000c0d8403074003900c9140089001d01200403440c212555000e0f516420030040d201915034881058040f07156208540b0100c040094000380610510701c1c14510300f0001040450001310a0b03500b40c80c06407906000b80380c4016042440c0d03006e445132000310058840188001c102002804d400d0706441a10b100c051980c5032230544d52110a50040500865014821000149800c104c01754581005060040c02c1400740c1b0701001c035015145e00100c0b4100000201840500004200980e2101403c0001c040103070400440b2000f0303000380d941c60315000e81c680c00e40c4201c0a0342034202c0e03000010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 627115917 1250 627114667 627114701
    0x806031e0a08030f100b040303090504020904021b060121020109091a10030e07061d0120030a211808090612090d090504020c1b06042103080105042d 65
    0x900d51040055044140c4000c81ea02240d1700d00010008412030a80d0300b00d80e05911003000c02464501404040d5000b14035803540142d00300803019003805091009075184a200c00200074660604540a502c0c41c84540c02c1e2400e9454103034280300607a8003c00395810b444802ca8007107000a02620040200342c81260543d50042070b2042d103001a550642c08020007059030012104641d5951a0680e40d203100088800c0100044460840c0f00b0350040b030120003115408000800080310030b4a8603410b642125035141c0003d0b01a03035441c0e00b112050303031584150001100080000c03840c0100c0020120b0910300000700440f01c0802d056415030340d00d07400e4505150304074074014040d01d4403814541d120160380c41c0190204144180204160500c1c0c801e80306004280c00061803000c2c101c3c00410b4401400c80881c99008000b0000854801810912040c0f0001001001105100035150162010300160051405186407401d41c03a102c00002c0f40308200c100d002855001460030041c0e401000d8006881d075218901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 627117167 1250 627115917 627115921
    0xf1e090c02030309240705090d0204020a0309111203040e040503122805012709020604060206040308091b0d02120109050717070b3c0301030c060806031e0a0803 70
    0x250040002c41c40b80702054145c44290313240c180c00102c007868126961000071101000201410f02500090a1244004180c444804182c0e4006016a4081c44800c00025210403c200030040e12102541603410125501d601300e001e488801c0b07503a4002c0740f2450038032031800d0b030104061100c00c2c0119a001e4a0080c140c0e5143e24050820651803941000c06071a4029262001c1d1070141c0d4922419044e80c5016400780512a01d410050408a112200c2503c5541d961040301006030b80d4a4000c00050803145c025007694030f024180a040030b2801000c20300c040e00b24200e0400142c80310a44412940000c40380c41c00668410b002040310b0382c8108442d80c079950b20303002500c424070400251100031a04121b0521104800c0c01070441c1d156100c501c900035030380c0030610010050020890824580340b5400b19104030300e44c0314031442c140c48139410107101c441ea0400001441445414105c900281109041440050a1900120b036403560003030000752650415101d10340300910180100b480b5160400c620350740724 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 627118417 1250 627117167 627117191
    0x607030e15031003030f051812070e0f150102150f070c05030a0804020316060c0816150f0b0409112e0201141806011205330a060f1e09 59
    0x50150f5000540100b9210440c00040601ca802182c01b055100d42c0742e050020a0002401700c0d0032080709044480780201c010103e00c02ca440441544610581a80c1076200c1c108145003034005004812140d0454100100300904000002100d0f6040800440400c010f695040800c94003031050920050944c00001854181c00f0740c070a6006000c2c40c0200c0941c1c248400c0d03000808441d0040b48640310100d01200760b44804502c117600600b8820070100c6c0c01c240b20043c2641c03071044202e17000303039805456982d070034403107081c101c4522400e0081142070710104207201058940c1e000160000c98064407440c00e40e03d440310640160307481600c040c1c0d0740190705600311000706800fa0203440d595240c0c1000c00d0050300040c0324004e49030420340400c422076004c0e0060f03900302403080281455150007035901e403050000d010107488030382c241407407021401c01d0302042c0d034002c001c0d9603038102d000604418030450030b01c5003d110105486240404403850a900510201001000b44058070500e0307000300700d0540717495000148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 627119667 1250 627118417 627118441
    0x181d0d02071421030c030c0d0e0402040f090207020307030c0b0a0e2707050909040b07020f01050609070507020f130b1003021c0203040f0b04030207150e0607030e1503 73
    0x8990440c0c0035a1000c036199010314010070726034a403055000c001030031800c4030704014048400c008804501900d140940b29503001d403456002c1c1020350440d5118014610f15150321529443c1c0d0441c1c00c5500750324051624110b03500000a034081c0303004484e80000c103c0f085640c1045860001c550040303059407015032712080c941803038103e20480d0300481c0d1a840040581d103001a0451341d409011491380b0080c200409001d08000c000a10140c10311104101c3c0d11030359503c42c40f0040c81288104502c20452400d010000c0c100800d04440c0d0555038100701c01d02507203903200c90a01e640b00685141158841056000040c0502008490107801c41d02c1500c1c4200c0a000c1900842e2000200b40c1b0800882104008101c08920500651504582c2101c000b050800040d80065420a010b1a428400c1c100e09864590b40040c0540e01203001d40e00003035080000389002043e0003640441c0b03043c4581c0b10038600e8041150b40c89824802410400d098207107d0060340c0b12740808111488404e002622441c18452480b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 627120917 1250 627119667 627119683
    0x612100f06050f03070e060c011103161803021201240312081009020304061b0201050f090f0a0b0a2007021e011707090801020a08010306060e040507181d 67
    0x10340100100c004640c01e4000c40c102d0703010003c8903107440c0c515a03503040100c901c0441c003030030b06611420802605110390382c2405201c00c019640b008156803802c2c60101d0f0380550121020407000d015002120b503404000745c13802c2e00d04483d015208180f4482c0716025413801002c5440c00080041e10074403000140241c0002a03e00380d038440c402c5000700b03a6a100c1c0035510300c8000c550b1400102e1046405202c0c48085070040c1d50400d100318400f051000d4000c041031000500655a075006039507590405c81036400601e00d1540000e17a210103400a00360000810752a00240701c00234040420950124002c06d00170741c0f12003500030301c0d035441d07290f0f00520a143c22150b80c490714050303104900d806098060007000b14007420316081e0586602e1405420781802245080000b03003030406021b00030b440052050828001001c100d0000da541000540c10740c030345102100c283d80c04c5000504007042c200310004000048030015a5208050030700c1506003003107100301912030040b00001440c00d901040401c50400100d0714 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 627122167 1250 627120917 627120929
    0xf030d031a0310150602030304080417070e01030308100b03100e0402060909041407060806010c0213140c040f090204050609091021050d022802010c020901080c01080f0c030403030b061210 82
    0x28109680c81720220303030b60b010650b030217440403100304810843e0007201580c80040d1540f041c252032046541c0c0040390301c0e44200340d005038049483c140c100200c801070b504008000d800c0c00c0d0720231403c1d810130312002d07400c5010314010030ba07004c4281c1000c00c0075950750006503080c0b020000c160341c0d02441c040c81c003000c0c80b160000e0018070380c3c894010007041442c00340406c248540c00607981c0402650098082203611009039003503000e42c0d90348454460711101070b0300d81c8510034074206108541d601c0ca0400454000810b640c03007022000d1051205122540d220720480e15072800484902031181c40d82051403181e4400ca5005c0642090f50354840c400c0170381010818122107010f0760079111101031802c0f081e80c682d0150841c02c201e4400c03201200c10012910041c428440f40185018601d440d507030350202d46203038400c0c0c009403500d0340092825403080da4000c100b168070040e0f4044042c00b0f0300740b402e0700c2400e40c0070191004050507144c1030742d8500c58035104280d51103644e010f807070304503182000d16031500c4907071050240d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 627123417 1250 627122167 627122201
    0xa360f120f020f1c0507120509120606090406091a2403010c0e10020309060d0e07082406010c08031005091005030604081e0705031201050f030d031a0310 67
    0x61985400401c00c200340400f0380d8003604440c40300d01444078070749154110402c1804001c1c4040c4010a01048003d14200403903111142d80e0035134903080061160070380042c0c007115444501040b00c2c035110003c0c0203030025031294010945445510745040184c0951024040003144c2c981005000d0700c1c01c10b0040360241e841104181640512014182611220440040030420388075543d41d0508102c1d0010350748458030305c1540d0609c6a020001036441d449000407100d4035450b2441d0341d2010200b80070f45401000f400d07000341035104034440d40c0380851013a41c1e04003103c11103000001d0f50300e900404d1340d01002c42d4801d41042c0e0380e00e444869803010351024042c41303000b15004c00000340d008401280704c00c00d8440080041c1030340d580b21b42e40c0901d554014205005110303629100e800c101009103000d807901d24420f4014649845040d25a4556042c0581c04103218451568404020351000300d1104407845d0a40b81c003194400b0341000500322031255800ca55014814441130000d480b805da400341003004401646 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 627124667 1250 627123417 627123437
    0x4020723070e07020601180626010605040c090806070905150a1b08120106090b07080c2e1103010522110d020a020106090b06042702120901050a360f12 66
    0x1000803108c46000380446900201d0780303009006407803001e070501004110000b05000b51940c0205e01541e4503a6442404501c80c08400d00c6411000d001056001006240041c01c092404c000a0501000c00d030031200b0765407002400c512518400c580b644006482804508551010380ca0040307003d81c0408000300c03001d84800c001080c1d0901c50398101d81140c80144510b41001c4d626103462840d6480308580400c2441000d4100c40782c4049000301c8215038072185080b4145080300400041901d46080380e40d544903000704014451a505c0154921409440c5c10304440c2c0d07079206401d0140207118201150400c10008111444c0b00c0031160010807289071590300074040c0030781d201040d500760f03016004180c0d4410f409000078809041720881821440d8200c032000010096038032400d0040303902c000211250f0803401010042c00500900a0b40c0c0c10098411003045035034a4031002c0d01c070f04640802280340c1c511140c0b01060722003603001c01c0e550155070007040f8010340303041c01d103040440e18441d400300c9000715a210714 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 627125917 1250 627124667 627124709
    0x5030c0306070801170313060e1804030504091a031209040f091707051c0309022106010603020915340b04171c061404020723070e07020601 61
    0x2030050050080380c90b0f0f0f02031642080703252040500c040c00c40110910051101440c600c2031a01300381e00800315515003003001c4c2d07150024030070420904c00680c400303805100180300000303038484e048400300c1d100e1441c001307486800f0a0204202140c11208a50b1511561036280c02d103044a100400048008407000c01000d080300301c4101c2a07a0940102401c401d041c1e14100340003451200c014184144a542a03400756030020040706038800d900340c0b8580c0042d42c0c032600e0108609001c8400e820a8000500e806114051030b18078580d40e0105019103420581c01081d4110700c2c0c0c40382c80080136601e0826058a80303d0340001c01c852201c018002d00e8080a0140c00b07040e80c1c070004c0c1100d190301c01e1340d0485103a002550f240d03213540c0d01c20003d24207407003030303111082200c000d034a0452070f514504400c0e1500c01041c040c0c07400c861f00800e1040740b00136a100307070300c100720100004034442640030381404601d451496600034001102e041080e6644422600c1d00310108002c44240c0c003260041c1030794140e000c90020b0390b0f2041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 627127167 1250 627125917 627125923
    0x1208060406081f111201230406181d03040e040c0b1606050705090a0b030601080f101e0803040e0a0e010911190503010c020c01080906040f02010c0501111305030c03 72
    0x58458078250603507180f480191182c01c02e000d180349902c1d003030746050030000c1d900f020318800741e00c404208109620168200310100340000059001118203000c0f0b00d040201c24036901e079604035410045907032101c000c1201e0080d125000480d4610720103403034485a581d4500300710003c00b118121060002444045980c1c4017a009803440181c4201d0300340c0180ba12550303104000e0070f011f482142841000c1c00700c0c01141d5201032004000e00031060349645c41c2d04200c0c00140500c0340140941c241c034a149c3c420402c0010104598a044481040101d00e0f06d07007002e10518620840350700a19940d00000070003140103044004218004c1c60416010000e0207440181c80c0e0885012020040242c0c1d0703048081890b03850120800c0260032808003180c184640c0e1440081c0c04c4501c1100500d0260300035a5620201d03607001181e0700d40c4107003e50050090344c50185e845540208181000a0503c103503c449242070001c00d501c1900d100c2500900ba0745c0d0ba400b50701d00e036004907910340f05462007445089014116800e000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 627128417 1250 627127167 627127183
    0x30902090619060804082503030c0e061608070b04050607021605090a020a03180507050f010e06030a0c12020705070f170601210c03080d05010e04030e0d030c120806040608 75
    0x284400d80010f810104115602e180140c0255107480d4107200603841d06014aa0030885c1150014144640c00224a03003c1c06a0b00016504c02c00d10150343c101d0b04064484a089450a000c00e84400c0705140d511314100b10700e40038460000d085a50740380100002c01c0000507020380210201d4003101d00345030014a58819012040c05419082819580895004642e580140207e080241404a01c0c44000350030b00101541100c1d05480541c4441000c008504105040c040ca9041c01e2a0581103070349140c1c0802c08902c405400800c0b0166a02e000404680c0704220324502c0d05a4240299a141c1040c1856a0342d80f06501501d1541c45280b880020510302c076810003d80020b158019080b6603283c40c8580024034050030a4a04444000e500c03500092444130b10400918802c2d680303152520545a22041140c2d03058000300c0b4210000002e1001107a00701c984040300130000c42c1c400d12850301c0741c6801c84041e0405e00000b4442400401500107a507081042c0900c100d109844c00c00140b0358540d201540c848034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 627129667 1250 627128417 627128449
    0x1e06050c0c12180918030d0906060803040b040b030c040e0103061517101e060b04080c010e01021002031909050a0b160e1203070b0907032a1403010605060a0309020906 73
    0x440c504460f450304025140302c0d803200301e020000b101000c84100c214110f070300142a081d0040d0796240c03404104603003803280310050b1090f03800840c01c207402d0000362a003e109500415080d41e201000052040d14404226405460700919101d00d0f560b44e498050050203420080c140407644950f4041500c6035210514001d013103c141c01070010801c4008848003c011007811240d0000c6680420200d81e43d45d400b50310002d0204100310307551a480c1064850410307010400031410048a4a40b040d05a13034001000c90142403512801039483e140e100742c200c2c02146c240d0200c01047c0c28030a42405029000c521214900d000d646580080e80c2c41002c1c60400700030040ca0540400c000d1400e81115041c5513510174800700442c0c04603440c10000381c0321251388410498294545038030841080c010483c082c01c05000304d420905210740707001c503102d906404140041c011110342c0c1081082c40b0300191f0b82500f01c01c00800c000740c4110380e00c40442c0b070002c006c2c007170426042e40580d0000011504070b040c0f4456a03620300311 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 627130917 1250 627129667 627129697
    0x15052214070e1e090c0d0b09040f15020702041e200f07030212040f03020109080703080f0304081204050d0306051509040b030304030614041416031e06050c0c12 70
    0x10340b00342084480c03c0c001543c28003034081145000b880c3c0c0c4460084a014284043e03c50f0344483e8500040c005890030030319a540905501810b010010303901444245100f03074801040324a40e20744c8000c080081c000c103030004c0c3d40141003111b0200c2c0c40407120303001810303264401420311103c0320003884801c0001ca00c22801000d01c10070800440c1500300d10010300b440910900c103460480e000c0b52000c001c01c0c0c0082c2c00c004084000e81200b00110741c1c1094120380100892009092103d2542d15250203e00036660844511180000090204075a100c201c1d4000c1803400042c116604090801030782c2c51841c81702c0940800e15141d0003052600d0301c0c1d80c448015000d04190586031088090910010308103051255800d88400c0c84007000145c103a010f14540003c02e20007201e05032900e414605042180c41290078001d8103ea07440160201f1a0918001500e40000d00022020f00c0f16600044c0205918070141c411031410042c845905182d8005084004914089500030b401544290f04c0c248034080c1c170b0213900d031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 627132167 1250 627130917 627130937
    0x50a111608030a0f02040b0c010b01080f06010c020d02100e0112021804110f071101020c06121b1e0309100506012a0602040306021c05060d061505221407 67
    0x18a208001c6901c058403503c0851804082001c54050b078120b5000040c0c0b041022982051060003403003407400c40c84003442e0410141c20590103080c651400a04442d04010b0400411400e5444a80d0a00d00d89940a00303880c5504000c284020045200c40e11024002203010003200e0080e6410300a0340c0c4221170f541076a11040c0c48550400000b00007580b800030910700d06011804c502011000904502409070f60100704001c0044002400c1403a1424074901c80c08080c88588814039000420135401105000751428581d09201d40c021640a1414110400c601880c00a40328401541c041c601400f140d004072100c0d0861903401205541007103466030300003000002c440003002510f030034500d10707070030a4140d103208862981c4854040e030f4466081966060340001d04e007029956070019030700c02c903086842d082040741083c01c0000c2c2400400e030340142282e9112400003601c81d070380f58940802000c0080418007200180d9901e0030101403003100004100f464454005100c05e5202642482140c2030f50b1510044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 627133417 1250 627132167 627132173
    0x503040605060a3f030518090c04140312031006080a140c0706064202030919120b190b0307030213150303030f180506040807020d080706050a1116 64
    0x1228201402e07050703820b113259980035883e0030f00328500c0c0c6000760b80fa165a1021159000d035044242c008040c084e4411008101102804070141c0f01a50500d42c40441e10032174800c0000d140940e403c08107404036030008140f0041034034500420b000c4884035194039850303640720002c81040300c1030980da05581810340c5002420a01880340107002141c481d101c0003c24070f4640095180c0070030340340d840040e00e085410306040d680307106250390b00890705010403000705e040640800035100e0040400e12402400c00a01c54800c0c1c80311899140041c3c01180c2c1d0720070711248113080520040d04281c8603541c03803184080c0b4107086d03007969008081e041c450242c002c200c10381c40c0d9030038000322030000100d42a11035541c00442107400c00b8600100001c0d8000d940203d1540203003c00346c011590010038404035584510072000005001040841d0302ca42c10a0040761075a1940c00401c2c10810503a03070050025000180000400210f03500a034004d000c00342041064405002c4006080d1107880300400c00118104815000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 627134667 1250 627133417 627133469
    0x512030301050118030503040f0501030615140901030e1b09090a110f0a17010c09060906080c03040507080607110607030506030a320703060c0201050c03010923070503040605060a 78
    0x20203082000b0800c04c030355a495903070441d04a070b0030002c000d0682940c100201e680c18007030f11014042d9040300c0c50a035005c0b0300025200b9200e40030750f007103220310100d40c0a2071a070099001030440d200e82426201c004080407489114207184103151441a19a5004600318040014040c0c100300c0d442080b07207900d00010800c02c8500032007924070540c007007031134200411003400c404264000c803a17040c0d00100d400340d940c0d103000d40102d000e0b400c180c040100c0034104018003507021111075040b011025803959240c8450908038140704150b00014414450340090003000759010142800c40d28089003981d01544880c08100c00741d450035206607038035501c603a50010128a0080c0d10980d801c0c154082800e603a081d801ca48903045980d81013906994114200402c00c0c04954007030101925980e1008000c0c51911000968050206000d400e240f1a519203400f030080d100d000e1f6541da1091074400700121440e00b00b100a20a9008940889042c1d081c400411030a04050300400103031018462005810684032000d030308 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 627135917 1250 627134667 627134687
    0x4030309051c02060702070b031603021c06032003070b12060d060c0905011206060801181107110f040c0f0e010215040b0129070f0503120a05010f05120303010501 71
    0xd00c0d010b0718020000d849840c180d940c420001e1070700a004070b0b203001c0320060300303000e1242c1c00864250000c204004011109081000d90018513040060302c0e21081010042541d25401d598450249003400100c18010720071030380f43c1810b0306581020390242c9010185600d0f14202c1c880d1554150040c030500c48001c0008143c1a44808040d01f0116030396055103a010603a00031155806c0807034000c82003807141d03590107506106c810702403100500c841803514100404c0100141726960301e803a1448410a1129078035003000d040c05141140c10780e215981400e008008114a03c005403041200c100320885509082c01013610010740c42d280c00381c02c2500741d03030281c9003180f11261050444c0560120704040d030355208041805580110f010404640c1002d00c0d40c0c1d0302140100356004031004540350f100408050f00101d4040f40d90140340000240040d2420700d1850088004000444000701d0801c0f500f450907500450481d9140c140380950280d40d023082c000e40c41e9041140211079002003005010550042040c45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 627137167 1250 627135917 627135923
    0x30f030a020d0905060a0509010c0201060302030c09040302030d020309100c020f060103080c0705361006050f09060307020d0807360e070306030606060809030a0305060619030f0c09050904030309 85
    0x1c158110300d80e60fa1030810300d0440310104490b03547d000740405036001f4841c6901028040c0001c202290441c1c00181c5d5039004a421544503a01090002e01010301c240140e9441050941007551a81030149686c0e88030b101009000c1c102c039142912001c02d691000819042a559100140804c0d0b429911001a15800009a00c41a20440c04005243d40300d00700458048141246a00340b4103c2e20200c500fa295030055030303440703405059070078800c1d00d030300e0050010204d52060070000d070b49c1d900d00840a00d8901422040c543d0110011040080c45500410319400030102c590300d101040d950050165001551101010b621907204450000902c20b0748018100050403a042c90482c6603036121040e0542c001110320f800000d40716001001000414020321020340032a09000389a0318040711215900c1c020310403500d040644400200708a501c500f0100c80c2e40070514403811154495040c8064041c08003c03458003081c510b0a1702410610b1b110f40074400644100800c0d40e07186458503281280500301501040e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 627138417 1250 627137167 627137171
    0x1b0612050f19270219150302160b01140427080c0c0312070b060102010204051c1b0b040620030a0c080d0501030c090e060412030c0504050904081b030f030a020d 70
    0x1011654a0f01103650441000700b000c0c0c0003203801e841070020403e0b00310302c50500301c19070b400c1c2480116072004200600340010324005072101041c229565201002c1400070b0420920880049860881d10320b05070301104041d01c00f80441c5241c0c03440034200c00240d04401c010b43d91591030f040c2c0041c1c2120b0047c07c00780104001c503480d403c00200042d0400c111030704600202900081c8440c2001030640903d640600240021800d003880c0034040f034100c20703148000300088045c2c900d0142c104182d20300603100d0004a040e10400c40354480800303441a600c42d02403600480c900c1c401c0040c00340d405c00d2815903a02451800b40d4101181081c0030740d051480e61000300c0318010309100407900040c0c1c0740702e250300840c0541032582450f0b00d00143c80701129001845281150030030b00820010231001d00074201ea100c1945000662140c95401c11900c030300075500841e6110b410307031040c0003e01c041e040192a0722030940d4200c000518010514540ea07103d4021000b03840c12082c0000303200144607034050007089415001c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 627139667 1250 627138417 627138431
    0x4290d0c060e0604090507081f051c0204090c06030b0f09040c05090c190309150c0c11010c060e0601060201150f060e1f0201050a0b1c0b0c071b0612050f19 68
    0x1401702610717800c40f84c4500085651041020b01c0070b1407030003480d6007101e00c200340042d5030811011825203100243c1d00e040840090340c0c8141192665800b00351025000000d600800b521014002d0180031001c107001d10030f1240c1461079007149003001c00341d400b0f00e5001b661404501c0c80e00c02071008070b1070020201d8440c0f4005100e0b00b0b80e00c20200d020070405100650340081d0505513443d0469401c088403000c40303000b07483c007074041c03500d990070841c07000209403c5040041e003490b800c001241d11444001005140c2814032604018541001840505952060300284603c1208001030782c000c1c00c0c1c6d84a2001040f007048402c0000d00c0c040c1007082c2d040200580040081c42d07400d00301040c03c044802030074006030755a00c02c00c41c03248503620600e58421811148054500c0d001c0c0403a1141098030320015001c107034800302080c8819070510803261155802100300302040c142900f0104800141d2282c800480d071060400c0c2c2c050801d6119003442902402002c42c819159003881c0304e414503071842a180390950300c1c81c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 627140917 1250 627139667 627139679
    0x3040f03020a17091314040f020f04060e0a0b010c030f030b0418030804050c090622150b040e0c09010f081b180103060b0a1b06090204290d0c060e0604 66
    0x1c06800f440c0780c0248000d030b40321030041c1480441100f00d516900742c54685500d840c5050f050b0b5601c56041500201c410020b100305000240307041c540d5103651b6610038038007440080c00a03816503069104a007040400c001c05003580005440c507004a160040000381050810f600c290702a62010542140103400050890150905c200805100d90b4040d404542a14204401c00c40100502e8084407025211195207091a00126010213002c0484002507048400030043c000c10651000840c4007000b1310a1500560b600c60320912640240200103103da04180000d000e917240d44110b82d8104010b0b518624501c18108080b101110041c100c2c0d00a04d074203040018149000c080a041081e2140354100c0c00351401400150894045a2021aa486090003000001c6401c01c03030000c03a140c07000c07081327810211180c60032074010301140fa00290711600e0072851440384220103410004000f01d00c0c4d00110750390400010002c02107056a8004c20300c0c0001103007800510311031030384000003a1000d0070323042c2403d464003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 627142167 1250 627140917 627140933
    0x10501270605070506060a050a05040e010b030601030c030b010603110301050d0f0204090c0f060c050616020f1b040605061c1a060705010903140304080f0a11011a130e0303040f03020a 80
    0x1d0700035030000d040481d0040500200348a032a800040440d0007010311031421010800d00c5d5140c1c4105485560740e2a1580a607580079045800032100040a5421941e103915041240c12924081619401c0b401350006c103106000344104103142e02292802821070303207003408004a06000503012203180b02025140c0e001030b281d030b0180c0704a00384500f0703114040909000c602021056681e0050041181e4081c40740d0204602180701a04a291030f9034110901c61340780c1c01a480c010b046034501c070302d520680310017000440c4080345013103880104030380a11405503210200070b4107015480000340740803240b248079540703640302d60b03c03612103490312403080c201139803102d8005942c98010440988181e51150035200c101544880424001103044009501310309107a01c4840050150380e0503d0000d130800600790600900915040764028115802480001c2c4614681d58048400c030028a0203503442091468a00105019006200540a00031801d56a580d201d0200312b0080c02d80a6095019009010020455423 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 627143417 1250 627142167 627142169
    0x313030908030a08191e020c0f060c03011409160c02010e120304140d0807030311040b07050c0102071a070f0c031a0106020d020627070905100f1202010801050127 71
    0xd51203100b502d24081c80c504401064098403c00076601d04103910340340131b0030f040401c5481c4500385070040e101ca10a4401c0c40c5400044603181600d0b22410342044428000e1030001c5042e0340c0346141c160300f54403403881484880c0e802952000095451071401000749031180341e0070f201c0c80d40140f501d0084074041c0341c0880c0700304404202110b0503810015040c4040c0307400d80c0c10900220000c1d251a02c002c042034880781c1a030b00070b0b05001070405032620242e60f10840010151400b600100f030205903582e003d4a030865443c12703c1c0c2081c0c0c0c0540120140003500803160090103000050b03002015142003142d50310b0200c8950f94041c2214040f410b15404400300d220844010800b03402d0151080c0c465040150113840c107024110071b80211360080040101c001e081c1010703410b0650000340c10168482011400500f0401c1503086010781c43c6c545801c00801c10000310b0480304070341e0310002100300991114003921517444198406404204c10800401031544a01d01c0021074a11b00c010400e20001d1542ea081465409 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 627144667 1250 627143417 627143437
    0x61a34050114101503320108030708071401090516050f090705030a020901020115060921050a02010c050a0203060a0b010f050f0a0503270703110909070306020a0306031e0c1a031303090803 82
    0x120200c08001c80300c800c2d1b05000d05468001582403906c16541c1c003400b031040001c02081c044600300d075110720201c2504009465070788101074a06d40188010f003100c0003150780c45228851101588142d00c1030401d0801d460040314180d8a046c030715aa0001d917000030b0341c00b07034400303034115980c599801249884144403032020f08116a60350f0000352030170100c0510b1841c083c403c0704c80120300e00b014600081c40041e51030303035440d420709100b000e80b00c580c02d10a04041813008082d4050003507030208182288107a1018442100907215543d10003a1054100c4039402802c04d00c0481100800100103039a0145014580c41041440b0300d82d903500004506541044080a0344101a0f000d22018400c020200c100c4120310301041d194252146481d083c925a105068803014080d01e0340020301e440a103100350850006180c110340e000f0341d014940286094501c80440041d84c0e5206c003500d01103000d4801a030140b600c442000f84a50941c0c807840403804141d9201c6600310103200d4118800a1980d2051014004e4005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 627145917 1250 627144667 627144731
    0x28030b0106080106050c1b04021c14220b0c0c031201090b22150803040e01080d02070f030b070903150506030f01061a34050114101503 59
    0x45007600280035140103030440350510000f0321120340b00d0580080c1c1109001c0d05071418404050401005c500244550304012420320502d2031540c43c031f6059504030740024041c002c2d007040c06540742c0c40240101c508040c80011a4100360700c044c80070400d1407800f5604458140d140e18600120348030070514640c855289800301c0e002502c0100402c10a40c410500c03809801e8a41000800e411500f050048800d5030702900150b68900c0600e0b02c01014406401c081c0031494116955941c036454800314004003403166403100e01c070f101e041c201d102e403001c00c0580880b01c600a00580c444e046990b0f07528110350050142c0100014a0300010108500803501c681000b1313946000202800c0107001d15050035403080e0340c0000c1e607050040400030341c000c2c008104182c0c1d10a043e11501d401c21031603080480c2e25030000300c250b034800e400312030b202513544081e202072a04d216078020000d5121044141d05075150442d0240080b25450408001c00208410141002651494001100c60480d0903918010701582c03000c0d01c50b64 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 627147167 1250 627145917 627145919
    0x10b0d1106041508100515070b090f0313032003070b0d0b04051302030607021501060e12100b2b02100c0219050102011112180a060c0c0209070e0d0228030b01 69
    0x540c40c40720801c0035246c00c1d100070402c419450030401d0740707128051005141580000c0058002403051029060010240041c0d0b651010383d40d05007202d01205000999071b110401181b4101c003107001c42014403021024028004161401e0b03580e000d02d030800000d00c2c12080d10b8030002c54003079840d445800e1291030320840e0f100480d80d043c0140f501c1c18074000d082605550042d903010b1910300002a0680c1118001d150078003115480d00007103a2a0b43d0010300c5014944100c40d031b50f102526454100e1304a4540a49100161101403c1d1840c80038001541045030020301e250018050700307081400e246860305a04011940c0000c0b6408103160741850800b000502c50b04200600045da420301600c14a01300100b10281000c480005030f00c00305402500d4030f4441945007016017610b0101f44800004180c2044040003240401d54000d4059040610308920801025000500c3c031802959001c407080d00c09444010079007100d81c01c2c000302c507080354441ea0080b0700d07038030034040d007284001080f80c003441c0701d1084d00c2225 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 627148417 1250 627147167 627147181
    0x130306020c0d110c031e0309040207080307031b0f0507030e030a05011a010f1413030b0a1a040612110a08030703050702040510180c09091a0111010b0d1106041508 71
    0x90300c10482030343c415400400c9140080e680025201440b0540c00c52181a0441d5190180c1e04e10b100b2003820301d07006400403400e001440b21441c084e520844070754a0074066040544542c00c16905415080c07404520703505010812544a44003400100d0f01c00c2c1030810314100d107140000d24001c04110304075056911404004084a609190780042c442e00b0b08000c85098484880505450044034009103941c03000f04000c000f00d505050380c1d1004581002c1525011700b4100c03d005c001e080300341244203110f01040840802804c0500c01c21048a4050b4600004003603a6596491040444201940d0143c0b517950040b4540000380014503100f8483c1d1141a41d0313000341c1c818401600d0008041d07000c100c0c001c02c020400d0040751600b0140c09841c42c940007550340000b40003615421340c0350704499859840c055440d15041c070a803003e6040f004090329600c400c200703041d00090a0381c0d61417540340d80182c5604c55050004e0301005142000303000c02131200e418640c46030040404101f201603100300081e4428244000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 627149667 1250 627148417 627148427
    0xd0e0304171f110909250c0c05030703031416050f1f0501080309060c010f0c050301031b14010c0c1d061c031d0102150405030c0d03020306031002130306020c0d 70
    0x82003941000034070803909011003c28660103803903070040c010042100010480c902c40d503541225800e482070710003040078007106c0040920045581c2107a41c000c3d1048086507070310340000c502e4201e0307a06a580e400841c04400450007250000c0c0410340c043e0040b410104001807007480f40000000303002004280140c02c00240180c00b08c03a980a2010551a1400500042c0008811104598019500380f9900c8100301d0415006085c124607841840c3e1800c0300b40380604d580321000398100d90092542c00c10480350040c0300c240c5038110744035184d9480c1412070001103d50150f081c60740010b00030034030243c40d81e0384c841840c10390111507601e03100c5038401383d000c01c400c2c0c0c40c1a0840b0070300306c4d49202d810070421080d03680107003107464540c005030301d802c544030702208451b0700c00c010341e25038400c6901845010781002d1038004d503243c114900380c5e00b240c090900c185400e10701c00d100ba03e2040d04018001c000c03142c1000c04817002944444024810b58110b00000300200755140010610804030720b00503c2e00141031440201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 627150917 1250 627149667 627149713
    0xa0306050402040b0f0f1308012306030601031b080709020408010606140403170d0e06040b071805040f29150702010e0405070e100c11060f0d0e030417 66
    0xc4124410711040c05101201c1d0207540208540c0a205d40c2e442d4101c00691020780151901c0c16040c3c54404408541c0580641100c400c00805150812000c000901022514070084a115402d640320300010070100755181c0500420007400c105003031050b502e80350b0f07640c2460f04a030843e426054001404204200c024401c16000b080b00c3d00d000e5242840340e869900301840b4130710028180d004846407a0201c03081000071120740c5010b1540030061903900180580e100c1030100e5041da0b4840d40c075000142c241c0e004403010b03841d0007001800a040b00e802c1034100001000480801080c2d0340d030303898828601031419a6030f880d042004240c15200600c20740704011500c0c1140000c0840e054003441001c0c010b0341c1192030001761007000c8130081080e5403001003c9840ca009000c050354007000c050204d0b10120b406c4000700700c0a500540115075402e04410a00c85144951281685c1e4400c0800401d5112407030b0307034407003040076441009403807800303940c0c81c444409030081101c200c070a0f8012000b658058441245080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 627152167 1250 627150917 627150919
    0x5060105151801030b040e0a0311120f0d090605040c080607030c1b15150e060a0302061b01090210090608070206161d06030c030402011214130212070602030a030605 72
    0x3901004108104004038040c0c200b100c01110340c82008540c56a000b40c0003071112050280c000c00c0070806212129640d07907001e00064001c2890101590040d10b4049017140340d901f81d07090078500d00b001080d031349062680700180c0e17610016600c50700d0b01c8c00500f0602407140258001e4504803112402c2a0302c0310b0800314094035003800d06182505494415811141010071072165266003d95284036060000c001c007400e6042c40c08091a00c01c8010202c01040340000035a030001d90441c00c40c0c0c1e5440300b800564802800082d50149003882001f40414514480445806048001141d02c49141d804039000c1c0d24541c001c240800c00e401c3c0203101c055408141540d000c58244001d040030304280003c2e449034101d007525801004022040f1001049101c202c00103a044054040c50b03a0385080581c4490300e8100b5507040340020706070b071416a4000094010240000448509450162541240c050688403e500126000101c0340c00c030f540b0594080c03080b82c0051840d6009950307100c2c0f0741080141140c02c00e400071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 627153417 1250 627152167 627152179
    0x2130603031e0522170a05060604091a15040e0a02010c030320030c0702010e030607050301140109051c05060c1e0904020f0406120f090b0f060112140405060105 70
    0x1080400e40c80305400d8008030016070007454000140741c04851500c203501d00c469621180d4600c0c05120000c0e914070104517a1042030024891190220b550f0700c40c0e25107080584079901c0100030924a2400d54400d5051703c0c4583c02c200c01c004560f0480c8074000e078003107400310f041c055000003203801c0b801c0038000d510301140010007900d060a49640003820400c02c80300007900b015520103141c01500041d0040b01352001903406800d0720b03481d150746404060f80c00660201c0c0000e04081e00c804281c180054500d008003601c0d00d500703045a081c050442c0c0c11580180c01d460400480b00c2001500b602c1e44c0011080003805620950080d410906000e8074103200901a401d6104c8100803040c50340c4041c01a42208001240219589411000004001c1c5c010034035041400e0070f002400141c901d030080503100030354040c24000e00c810f00d446104e00c0200d0700c0400c006000650528005594000e03200506a440b01c81414101c800d40c491007416002c4450600388010350400440602040c000e00700040d03401841c00301d40f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 627154667 1250 627153417 627153419
    0x30501050918060a050c040519050315012904050603040f02040506010e031504140706050c120301060504060e13020d06050f0603041112030c0d0f1d01081b0c010204060201020403021306 81
    0x4100e6403200e0040c0207040c21541e40000c86c0e20504401c04680041800601e440c0d07050b158280824561400381c400d444c400d219400c000c2c40a40145880c0c030b4101e03400c0e076003401e00302030700c000b40400c0944901c10801c9801c0801c10000c96659903400c050350003103020300d138400800350051050204944e006000641402013a0b03040c0705281c0d500050300e0322118013540450650307480350325200c1901c000f0300440a00d40e00035490b000c1481903212010703211240c1400210f96011180002e0441d59200038055031000036402c00c02401082e004006520580344054140d00762065042c0042c001c0b40c021048103a04151900020001840c00d03130f6206150400803555039245041c80c4c1d03200444202c130358841d54040e8069080c00200810f080c820f540c0d6110740c46040d0340b803501c58404e0080006000003815008140c90b0013803641407290000482c1c82c1141c0685800009031100c1440d0010701905001902480b00104a00d251000082c005040140380d1900003503111400c6204100b2044059540c50121a2820030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 627155917 1250 627154667 627154711
    0x50303030705090409051203060109090e0307020411130303111b180c31120b190204050613140607080a0e01110f0604051c0806120304050d030305010509 67
    0x11603030001e2180c14000e689150440102c1d0140909241c00b802c64001c0346460182e51940100543c40750318242d0710300f0f4001c0d407110107800848048040005450f80144040d0f0010709140d8060721400060b8407040b420950b861103501c1005407030360000c4001a043c1040c029220404010040e090424100d104208150910104800c5044800f00d01c078a40081c030040360b0076510b280110f0b1400800fa411030038215103448400b03803a001080c600c16041400448001420068000b0b40b0154164451071404094440e00b00b0400120020a08030700f44603401c001c002030554615008120002658000040d5a480c4c480034100c60741041c1c5100c0c1c040c2004110300320010705010221000342a20b03040008003030034242d0040390000c0080208180502c5207a00f0b41010030703000140103210305d01c500d00321b0708181c009211035209071a00030310100c040782d400e40101c6c2080c80c03d50301003089000028105c80c1803079912800208c40e906140c1c0242c0201c0c1da580018000c0b4200749034656400300d0801c0110000e511100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 627157167 1250 627155917 627155923
    0x38090a05060a1802060f0f0d23090d110c130e0105101203050310030605040b06040c05090109060e190e090f1c05071b080106090b090412050307020f010230010503 71
    0x5078024412200040c0c003100400303142c030030344111600c1b0b151180d0312845840c100d4001016484e0049c510382c00c04045040c00e100c4110411442482504040d0100010b21042510303482405031950380a070094130148206e6844180190032103070200c20300401c0d1009050301c11800c66101401d40c001ca06c40c00340c002d02240400303840020110b82e040c5845552a96842c0c000210644984c1005188504103024481803008001c0c4160040d10100c40810108d11544c02c280d505104c0e0700302e158040b40d092002041401d0203000c1c60b1403c3c0c0009001001c6000a14501c100c0310b0f0044e0b008082d4040341c2005000d440007041282c0f12020140c100148008240a884002d07001550075201d4104040040c64000f00040045900080005e00c000146103a88a5003610701030f141030700030b51045a180c2000f60a103840c001041c00e01503034114080359071000c041001140c850f40300800550552282c5c801003c00080c0920080a07aa0341d203000984040102c080e50b005000403030540c1c0b044945481c5c005019956001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 627158273 1106 627157167 627157211
    0x40602010b01170c160519030f08072001150303020705030c0d0f02060903030c10060e072c011403090c0f03060438090a05060a 56
    0x507401182c00c40100e5a0088640d45036030003280d044403000006114a0050804401e210229610303070711302e041460f098180d03208400c2c021039030030f0560190718030110795418a0040c4c13103402c0c0b80e10001d190007407060401c100ca443c90340e110a0042400d612610300010300e803202602c8240d4a00707010791982168400d05009010b030701d503821003500d008510390f400e0303e80c4003004503112520742e0280881d0303802c000b1406405110401c155428580d080003010200751025201103813180c00d1000c41c8400ca8409016102030102241d60029202c1544052071103040301482c0001a00d81c0ea440120780c3e140c083c400c4c51741c0400000040c008000e1001c1003400703403e102910303240952500783d020701d41d942c1c0e000c0b40e014000c52051f12102d10054100307100c21407003002c0e0124403910a40d1401e00101441003d581d00c020643c801ca50b13003803c008003030104561100601c00b04211105901c00f11828001351 = true := by decide +kernel

theorem cover : BRFrame.Cov 626978417 627158273 := by
  have h0 := BRFrame.cov_init 626978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626978417 ≤ n) (h2 : n < 627158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
