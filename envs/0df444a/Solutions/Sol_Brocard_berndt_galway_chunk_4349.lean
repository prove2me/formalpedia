-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4349
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:01.872126+00:00
-- url     : https://prove2.me/submissions/ba34e44f-cf08-4033-bb54-1f39bd393882

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782014388 ≤ n < 782194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782015638 1250 782014388 782014391
    0x31d031b10110a02190803040b12070e030705220204181b020a0f08160b060a0603141f050901080706080a020f18040b12010504171c020a030f0e06040303 67
    0x4115480890b070a030803030400034071241c10071115440541402044807180010180380c0e140880e031740c0c00416103503038040e5004e5455031f1000715048043c40c00d400052504880146080c4600031102030000e03403100c1051194600c2150f45d18220100f20303142c84540030007030000040464031103684400d90b01540c0815040b80c0110ba10b04403102c0300e001040c14054049500b00d50043c001810b4690701c01001c000451400c0c0d074224030a014100306c2400d0801d400f214a48038a040c608181481b2080c0000941950130040c00e15060103003e00c5010041000700b41d05c85082c0d8120155550491002102c918054000755001501000003003048240080d000c0200c0b1a02d40d075511705582c1c0c000e2204204c2c0a400d05080a070303001003052181000070781135008502d038801807000907081d02c000c00049803800c00d029008800c2c1d46800401003030061442e0720382100c01800b6110b030300d04200e281c10600c820a44c011204000d9034041211100280700754000381c1059060303a420446100f0000001ea9210f40c1254200c000a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782016888 1250 782015638 782015659
    0x1b080f0106110d1b0605070203070204060515220801140f09070b0f090117070c05010b030706050f0705162402070f0605160c03060b0109080613031d031b 67
    0x74070581d1410b1401000101030100000c80040890f41600e9400d00902c41651071024040410500d100d8103002e041c0c0c6400465482c140c5105110a4486582c41244150006910720070448007a1007203800e01341b250b812105500c0e041c1ca0940b10805995004000ca0350318200c240000700b1646600940517600a100518280d44c400307040555500e85405025107582d402d100f0f0010040f2a840a0440e00d001418506041c0c1045030303009140c0042210b00318002140b040302e1009016003031140d0000318a0641c00340010504040c0050705a10032062b04c03d06d00180003400005002c03050114100c02e942c800f841a45044d612403886854400c80b509894041c51020400c0001c107000241800c01c4900300098001e03d5460301c401501d403a003000d03545050704040e400c1d441002031038840c4410095849031000103841010038000401400460700001c10552080c01072040400300802e030881e0b0142d042c9809281d0078003803c1043c0001e101510740d945c141c4606502502040c00003a0000f82c0040180e4414260703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782018138 1250 782016888 782016899
    0x601080c0408190807331413020321070210030b21031b010c020105011517060d08031303260a1505060d02040e0f0903090111011b080f01 60
    0x5a1241c0d10801100c0c2e446107040801e14030041c68000c400d03a0081e8201420300b29180c640350350041b1140f001d0300301080c44201c0c4208089039003080540c6401e400350100000314010103003020b032000141c02030703070030404144000085650400030b030712030421000d1034190006100c10300e4840075007009004a11801d00180021038881c81b92061300804000101811004d8059420400d07145c124182c2c20009030104000e000ba074207003040e100c0740032618480000071750040300d0320009084401c183c01816991202e0b0100c4560746a110f0205075080302ca040c050740490700d4500008062400482c8001d02c60b003008000c00410040c071481c0c64036880d020b40c41d00581d00800300342d8903036020364042000562521030404600305050301d5105aa956400c4005c94081c035846500151690700002d200e6116580c0000d014045611040140c1d030300310038416010030050a108200b00d84a0043e07002060411034540000325141c14250024144602c9110000c41803054040d00149401c400320b4481e03424042c40c0d00001034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782019388 1250 782018138 782018161
    0x309120a0f0c050a050411092e02030316080702070b0a0201061d060405010602060106140c1e0a060e01020a0c0f0312051807080f030a08040f020415240509060f0f03040506060108 78
    0x5456035580581894070904400300f1189d02001509000e043d00c01050700f141400e0910001101000c0603001540c491411400c02c04048840c0b03090075042091030000d018010b41c000070104241c8102c19425500c600c1100000c80c010310b52580300075640807104019501072140300e02c0f961f010700d4041c0c40a100c40d81c4c840c0e10aa82d00c5a00f0710076440028100c0c600c508041007014040c051113001c0c0c20070344000c20b202440d6070b82c8034040f04502c0101c5801501c41d5600300816482020705100204009508200e001071002d82000d141d142d0140103540f030141d41400b018401d01040500000c6000200300905200c00d0300281e08611184d43e1041d0301c24a40040b0700200009408011089064000d500d0300c0c00070201115410000f4204541000b540815680140e80d240900b00030403100000d1061910b10b02360b1030360511409040d01c1c4100580d07418601040c603070b000302100c26240c000c2e50216520404c401c40b0207098410200c41c0c40c034a08001c001e20080000210740140a00302c260398080c150340303c2a000c0c0a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782020638 1250 782019388 782019401
    0x7080106032a050d1b180806040515090c0301060305011e0b0904170f070308070f050703080c161b05190b03062e090501021c020309120a0f0c050a0504 66
    0x36512103400c518050395210b440141010700d110301380407a02e43c4404000c0480308119082d882d0100303501d074580000c03100e944610100105a800b00420260900340c45103034413040c111189055200160b4006030081d00c00b08203840c0201406002000700300c1e9039090190080410820b504c5011000020540c210440d6020744010310790001c28000c040e4481d50340b0321740055210344980d141c082050000d81c2c42281e580307002d00085406500e5503515071034600c02c02014200100604800d002d030a00000010980c085601036001c40c801c0141079640096504040b0a150401c90080910300c130b19044104440301c0050b07020849106036901c4400d05000c0418403030b8001c0b40d000707030001d0b601c0c1880090341918103051609412401c0d550b04090340d0340445505d0301c2140310700b00d180d400720f15110410007042d43e0401c854940141c002081c1c442c916240007000307480b13100d000581440396005010080d000007083c00070129507940944080560409442c203086440d13403e204035486500b0b8044002000d081501400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782021888 1250 782020638 782020691
    0x170604030810260106050333070f2f07080c010305091005060f0d1101111207170408060403020d024b0303090a060518060606030a140708010603 63
    0x40070601403c900d40c1c0104034202e0002401d507483e4540000c140d2800c0c03001007650b0b0b240e128030031a41c1c0a000060a4010401d40060030071001c03600c00c001da0302c3d0784400462240c407a07528110740b6400100602020105140c6054240300400d048843c0b140351000803440c1c00c03500d103501500c403804408001501254400c80b00d24240c2d030410cc030040f440103540d030300c0207034090f10040803071504034541e40100c1e1682e00c001d54216501421203500c614503603000f03c60b07005440071a200810340707c03422000c00d200360b014582d030041c0704280d603111005040505006880c0585800c82c104c40c41c2e4506410000e42d5219244d002101502900424446040e1071315000c5101b50b0719054042201640b040b0701000c0c55215140d45403600c003001c2034800c60441d00344010341c00b9103240c0f4010100640b660034200e08403100900300031402020720003850101000400e02a9000c90101c0c3d0450b01e035940c104980740030304800002000c0c0006200c08100321240c00c065124142c5046130343c00c05c08401c10b405c41e4031844070000c3e0b14 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782023138 1250 782021888 782021909
    0x6050307030210051308010603061a03070b0d0c050c03031e10050102060c0a050d0c03061503020909010506090d0c0303082d0f19020c0c0f03070b09040213170604030810 74
    0x5041c503d030180c0010103074414480202100941c0d41c0d50324070308591b40d54000b203e449840e02e54074240c419504502c0c1500e640f04030050b00c80a46000c2c42c50210384548410341617801c0d02d030034110a0b6240110151050b506000007a41d0740c0386443d9042200e9410303030056046200c0002c00100c0e991f290106d006205540040c0c00404954580404100c000d410904441d02040010401c200c41d00300b02e40140c0194107160389001c01c0c0e90381030884001260081218400805205202452240d510783e4211411924260345041d9103d801101191403140c0713111010308840303c1003070000101680115017503c0340c88418a08400c108207070b0039102e110100d00030100703103100607000400c0354007910080503500b0108000b060b551884280c05080c0030b80c0c210445400c100e4010741c007003042c0380c10007254100700c0440c02c40150020078200385000ea42402101d10b1140074543c08500300f4180c070071031003018015144011039001040700b4909169a501d6048a04500017503050010444051011103101c040d90b040094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782024388 1250 782023138 782023159
    0x14190201050d090f0c080105090a0302120d061e060201050105010f020a110f03010c03020301050a0b0f030112030e180406150f14031005010e01091136150c01060503070302 75
    0x1101e0540240c4402c01c40180d44400f1440041c500c0c070a155859481812921a282e28002c0c1d80b40c00c4070700040c0380e03c03181c5d000401940f001a07408201214141413a404664903001c14110400040c01c0d26000b00703065051404030aaa4801e070311020100b1600240c1c000d2200741e89501c01110a9905404d90358007503400f050300342000500c0c001161400d40340240c0308050900e0359100090954885440c000082a8000014015030400074402d60242100300680c910f0f01e80c01c41c088841d00d210521400074140410091007040611542c00301e410201c2c010814160400c0c00a9103109440d4207a900300c0b0794a240602e0300101510a51b241011910002c5100107010b1400ba8841488501c64101d0756041c06400303194048480302e8070945019004c0c0c90400c03e0a91b0600807140220b0b082a458040e9a04060104025a040c001e030340c0f100d0355080c03086444601c0c7d11031001c2c40c0d400c08911400d42d0703c84041b4500b5241a070364400944200200c2c1c0700288085c9598005040d00ea1440703004c0a50042c0c0d500a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782025638 1250 782024388 782024393
    0xc07090b060d0203092503060501080a022211040e07080f0c03070c03020109050312011707030809040b121209011b021005070302100501030318080d23040509131419 72
    0x6001d56070000d070b0f84082c0e804101c01400c6d0710041c0d00d9946070700003d440c07907820309000f4044988100340c05401c100c00181110f0007280c0004850f10108021200340015840f416074a00c10310350449001103480446603a2107a8980240c40d2507050116040c2c0d000800140020f0b09910b24210b1440c042d945c0c0c00c40072807941d183d04008850911340b02000381c080d9074981d1040d00026004200500460007101c604103c02c0d4101051802d500c0d8035000e480744560310050082c8007049403202110311105085400103000400100403402c45520b410303100c103940c001c100742120301802c003100800c141102681d0341002e500b02040016044d0070b200201940000c08480501c000314000c000500445000f03004903802c6182c2c03d803151090328004d0f08104d001408001045820980581d801c001521000002e014240b0300c11200804103a05600b14170b031003200400c00700003910034000454010b0308010380a00e4141ca489154000e0751910340104807081701701448800c0c404040880c0502c0415140c1c1580140c004164 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782026888 1250 782025638 782025641
    0x3021e0f090603010b07140f0309010f120203091b0103090f060507090e07030e120a021914070b090a060c121805280905010501050d09110409080c07090b060d 69
    0x14800120030140400030351240381d40d03540c091402440c41000075030f42c072041c81c0b038140140390380d612100200b9406011400040c1a0100583d60845401e2910203601d04070381c40201d8031150140c07286205180700200380a0040004a030742000a20b40f284029204043c8000440446151183c003811094004007103400050f0b1641140f41c10000390f05c0d200581c1c1d41c5440065425000075200c3c0d00109617220300000d100401031180d03000760225200207509111850310065102d0301202641c944d14178500c5005030801442072518602e0f509072100b00c07020141c90b680d40c40070355800005007d201d10104940021020300c60042e400140b0f6110001d03c03040d211609003611600074210a102d03008074003020101d00f940720140b0210502d820b8030440341c5202d907040c05405100000e504002c4185060070300610207641c10030210380381c04103c610001000c1c100d80c100319420a01c070101003a0f000d418228550180072000d030103061051000c00503286495903c000301401c840c00c00c8c1410341c00a506000c1c0007c4440e0341d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782028138 1250 782026888 782026897
    0x506040b130b0a020703030207060c080f03041a0a0b13270c1203032304030f0509011101140105150315040e0c0301060e15040501140f0d0b13110103021e 67
    0x6607007558410a40b0380e00c515015401c1040240010303480f02c40f04205160b0f04005000080c941424540014000d9817109900752050810725a500240000440c1c20440c0c102d4482410651503d0041500c0c10034903180b4004e4070b0129075441c0325003203818107405502c0c2caa2180700030040300b03c841480400b0075078150a07540b840c1c6060a0303414121500d00040d00f00c200c288038a08552003540c0004141d82e244103015503c0102d003045202560104040200281d080b00c40c03840c0c00300041c140942c4030481000100d4001c0301000c4491419406c282085c080c20141050680c141c8a04a400d003608865251041d805808102d5042110041c01d460610090800b40e01c8089020188410744406065500100e4252900d40d44130b10302100740310007044000028a0003103481c40790300300d07000d00642d45043d5408580a805110710741c030540031941c2174000c940d108a00c007420203600c1010280c0510f090f0042c101050500c0304195640e1030882510500c0c0e41c0b09100310f84d8081c43c4e141d405100843d081581c403074150030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782029388 1250 782028138 782028157
    0x16090519050705130e01051203070b0c0d060803040308181e010807090b031f14030a02040e1f0207050c0907020a1419140f120f031005060a1211040506040b 68
    0x4000200405281407060000b1700b428801040d115403602052000c2000d21503040c1e90150000e100f008005640903001c2d03a004000488502d44981c0c156449034000e1910707501c18811f0303100000e400410050840c029250f42004a42480d2407510360901380f06002400b568502c48540d10840c04402d250b0140b0790b1140c01000901c0d203034001c943c482c0386d01e080e158000c0c1c460520320b203141110003a003128044090405400c0410704600e401d9405004241d85880703840d002481907842e5880d10b81c203450308210702a1742007001090901c043d201855040001d5121080030303201ca0185682c0714199081c031511540c0109060b0780104021a610b0f22508191541c0a03200074440c003e981010244200d503988145005001e0303482c41265001c0000f20b00d103004e00d030122010098021080c405403c003006410f45d00c00ca421003100940c0d0b80d480d42030a2910942e00e801c0542c0c0244080b4415403034a510070700399400d40c601d1800404ca000e1068800880d50f000e11300c21198440d00400051201c40203800140485c50b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782030638 1250 782029388 782029397
    0xc050a240210060e04170c070b0708210106091505040e1f1502060109060b040b0a03060806040303050a0b0d0b130f020d121803030903021e0d05160905190507 69
    0x441d480d44070301500c000c4d600040c000c605460900007480b104091001100401c042c03031603d0705d00006807654940c0c1d610300c2420410710004c100601402022803c0710b0034444a600200d4007000004030081811070300307010b0707000003810701d9201040c0c46292004640842c6220380321241031070f281c12042c0380b1280b4020040c031000805024154002d0f460350040f0710280406084100d500c0c0000d900080c60220b05034804d447c0305003407940030402005030300e04a60640d441c40c0f480c1d82d507440d4502c00c00d0f0040d014030b80c4200741d1882100200010315078568001e9028031000031050169044900c100100b89019038405801080c5032404103180102a4400c409201d101d99a00b0800c07a039123400040d4401150714040e105412030840c4004d005501c03500120350040c1c42c0422451031030541e180100b59070030500000b40500045410000c0c03a011006000c2100c500051a0101d05621880e010351501686034070b4000c2c0782005000803d60101034010301d445030400386c083c8210440e428241f500541000f03001d400910 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782031888 1250 782030638 782030653
    0xd021605060a031b120b030c0a12050f0f07030215120a051306090b060f03060103050a08071104020a11070b1606050a0b03061305120412060c11030d090c050a2402 71
    0x100b4a2640440c0000b8407034451110305c0540d0b0070458280d80c01e20101900c00d4202c00c0d02489907651312220401501d05064045c070607001c007850064500003825011400c140300d04240f0b812051000220601524800d490000543c1c80c0d420851140c2c0c0910001040c06030460780020b4012040c07940210303403009840d0204042c010464443c4011035560020544000100004000301800d10301c9241c4c169060a4000340400e40c03450b250203407940e0312090000c1801d9000141c0c0001d00c8800c07031002e42c008000170421541c0d81c04071800030b044d0b000c10000042460040a0001079060034031000e41d070a182c1c1030101c0406165866131820000d2000400754002d40c0d9039200341403642d03241081505e03c0f40c0240c3c50401828030071403c10a16203800c000e00c00092400412040c40013a5625074050000380d800031000c654280465402c0d914203e480f00c240c64248800301e0400340f83c5400f41c000307003001c0740a202c101d010305440300203204900c0c00794026100d203e4a42210320b00450412203610311911440d20603034244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782033138 1250 782031888 782031911
    0x120515100e10021501050904020603040b0402060d0e06180708101107120809010b0933061c0515030c100c020a15110c01200307050609010e0d021605060a03 68
    0x20b2031548040000180d02000c1280d01310300503410b6807805440103c0711712038546841d500007900c5100080c00205040c8000010600b152114015241c0c000c20b00700041c0308040c250741480d603440c0000c5030401c150b15000c58510207401804034095003643c4015024000002c20480d0000103841c948012442d040b10410231000803c00746556811660310725600c86259003441c0788894203440ca0507006c00e100da9000818420250309001000810071444403260401e0b1038000c40c004004a40c0510080d04084000750346070304044c000d01415100e1303860003020032181c1c2f500414000c80d01e00070780e003950b05907102c0604803559142c08255048403c1c541d2500d1903540c0d4450380072598140e26940303c0c0c50a00074420640c900641c0080c10208a40e54440c0140300d10011840002c0c65a40e12001315100d60454211851545070140100c981040c0c2000480e6241c0c02d040c1070b0b25000b00601041030b46140034494001e01c54a1022943c4041c01240802ca94580b6040800700807c41c2d00140d00d002c2816580c1514905 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782034388 1250 782033138 782033149
    0x715172d0f06101107080606011211180f0d080306120109050304050910120305070c0504090b1b0c0111071a0103030206011a160c0f14330316120515100e 67
    0x98840170011f080e448c24890000b600425039908000c000e0760414410030540b00f80b520554000310b121104d40b280501d4030074003080c00d607226150b0743d0350800910407102c030900201038019070050030192850111840150310f402d0172500c80d180014281d8004205c00c01132413816030324558000c40061030115940341d6400311180404600c83c2c0803004540c002c21300c0c0c2c040c4944040311070014803043d41d01744000000c95440003045070005000a041d529500d00340f540300c0c844242a541c03010642e03402040344184203620498103401c03030981101c3c50012464502ca1400b0041e040328100c4e50706800409141c0d0910780d680d118580c150880204da00340c01d00c003021b000e88010056003c0c007401480408405810024074016500f0743d500484031111001c4986165a2107491240c8440440c0029a0100c449555004d94a5640c50841c840010f0000b0003072154994040e070401c050302720701f07071200300e004029200c840c42031b14411200441d80040f4524034a50302d0400541140240ea454505851031141481c000352 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782035638 1250 782034388 782034403
    0x1030f0201022a01020d0503060609150d060b090915010203031302030a0210030f06050f130e1222050114160312052707080715172d0f061011 62
    0x810070342034503d600c006560140880c40c0d44c00003d103085072940c03a004002c030b01c036440303142d4405000301c00161007040b81400d030805840c4c80705003215082c01440ea603103000728440c2c0c00c01c3c022140300d2003008000c0b40442c40403000d20303013400806070082d601f103940b0b01104200c2001e44400030398040c010808210010b0327031400303205540c0304410f440c0001c00030441c091020803900142c00003400303861541c4d482c5440e0350320104100c1800d0f0020402091302d4050310149800d00100c0400202e880e0004260003001000c180884e80d5080380d040e0800110350380c0e40c401155401c0b1641101c40b0700b01003c03c07140c0401210a05a0000c5038001e041c40d003c51014400306108179402101e5a07014600c0d8140314100c0007a0407517080c01d014002400400307600d0704040300952116000c2c8550748580704910f4040c040c260090508030582c640101c64075181c0c1ca40305203503180114440007d40c0064082c0e000410f0344a0050444900406c030890315042a59101010f0280e2282104402814440c4810080d9400c02c1e0412011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782036888 1250 782035638 782035693
    0x90721380a090507090c080a1a0d150e15070201020f0304020f0d0b0c09030f1222030c03120314040f081621140307050a180504290a0602030301030f020102 68
    0x20421b1020750000c005800107410316074040c0c11700707100722803081d600c40640000c00400c56144400701031601e0800c0d000c900140c00701c1045803c00041400c003004c04910900c0d440141000441c040d039460000f00d080f84a0b11645051100c0107001290150909407801c0c045808058844200b000107a02e0740da1060030700f2200030a007030b40d00080252650a007400102e060b0505d8038001c10013110441c2c005000382c0100710704000b0f410050b42d4a00041000742980320011034200e0f2414001a44038200754880181c80949180440c1c00c104002c540b006621f074000d88a10741188448a0001403544e4039060f5901c0540c08000c4074408182c881e0114400300c0010b02c81c4840c80e020300a002584943c098424407116aa140c14030005000f008403850708403049440c0c00701c0514100303d5000d07240c4404200c101d010b80007131340c1061070200c0d50310003441480035181d00707041200c56020740c94031407004000c0012100d001d00401a04288010000600b10f000c641e41614414015250705003807446c001041c80e440c4580d103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782038138 1250 782036888 782036891
    0x60d02070f02150a0518041805030703030507050313060c0207091109090a02160321020304120207170a02150f161505040b0c03090721380a09050709 65
    0x40e0740c1103241a40c0c64052044038030106500f8a800880068054011021035100700c40ea14903841003180e54903808031030701c0c81902000c1003d5010130f0a140d9503d80020400f240801d1801c03000c0707007515000e44240d0780302d018801c2542e604656640d4480c0c014000c60040d603010351050500107d1403840340c1c05403014460015040e03545608194081024602c030242c004c0c28151320400c0324107a1440d00c110803e81454040c2400001c181c1c5502c2088640e242d44144030800707030300c08000c0c0007c009242c041424068515400c40e8a001e4480070b0402e10941e01c1c210103d502c0d808007014400500341041005800000781c1207040c10300048208102066010404400542c3c4020078100c0800200b0f501450800c940c10004004a10703007560390000004c00505507003902c140202c00518200d5080000380060124100c0300f1130b1114940c9a0b52030032820910089520425030661400c04907041030255010310403002c0280642c001d8502201c40000018102d01c00c031540302c52400c008a001040703001d0013084070490 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782039388 1250 782038138 782038163
    0x10e06090f0c090103020904020d0305090415090507080105090a0b040207050d0c05100216140309030717070b18150d020a21020325030b03010e03030103020108070f080106030209060d0207 82
    0xc0c0c03a05060100b24103510a104140050005d6120f24046641c1f1075416603840d480d010303040c141078516010319079240d079006082015810112a102180038119003600c07000380300a071500703074023a61964024011160051402c400041d400007c3d40c104006000010300014544085502c0b0141060340781501000420003401c1c800c4100403040100304507480020904608110410030300e0002c40300d064001628a154907081a0307030100e01441100e0388200014201c610056a42c004011a0700c803050000300303103005141002860380d4401c1c0c00c8070405da400c03032242c17410090300e80100400c10340c59540320900b400091140a002d2282840285000800e944464513000d400d058040520721240360b00c0300c02c0c68014403d014610300210204103040c0c2e110008a0903195081e04101c0090034086000d980c10341c20710910030b02d00d01c4040003c5050741d00070398541c65076a884120989905140101c404009000b00e07004004285c8250f0103001c024000404c075514040002486c0400e90b0455003042c0c41c3c1d40c00c201c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782040638 1250 782039388 782039413
    0xb13030506010b0a020a020904020a09140901110708071b03140f0c0a0803030f0711030a0815010806030d08091501061206050102120901080a0603140d1b080307030905010e0609 77
    0xa1240180003110ba03c43ca4011032070b10081d110040204020b01841103140441c0441d40c03070345502405440300040400100d0b5020141020182c015a0400c15035403070102c0092110b841181200c4600b40c10110b664584001580c1b4000c1c245032004200c1c804d48543d0b00d021001450f11120b240707031504e0300c100030241c0e034030745d00b0001e0b0421000f01c0041e8454190324108020418001c41580d40c404030001c20181150384010090710324400035550300402d17000000310300464507000005c0c00d026003050010012200510001076501030760644a56506520000c01942c54900c1480c1c3d06a00120f4403007503d5a0000c0900c00200000c002c0e0003a01c0401c00071000705903141e20342e204440042c031091004060b10701d03035416100424803600a215040041e220002042c0c1d001315046000150360000f104030105a01d84021900c031040012850300103880400b8841400074040040d4240721741040a0500c0c60700c980400b600107090301002202d0954032814507010a03c424048203218592810107401a4000d55 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782041888 1250 782040638 782040643
    0x50405091005341404151d0d0213020d0c1e08010b09010e01020f0d080f09070b0d0203040f0b07090501200a02040b12030406030902122a0103060b130305 67
    0x18800d80041c652040e0748540d03e0710301e100c0d1a0030340007014100a8a1256540d0494941c12a20b04001003407200107000551314005a840c06030200e0956107041c1e8507444108921403a04010441c5540700408006000c007505c0c00f01a4000080d486850052611802455100580300c07070302005004034100e44118144408418096030110f42c1c6840c02d42402e6040c40716003146401690a400d0400017018101c80240c1d00030862180802d03944400c0366078260300418001c242c00d1013118140c0c88803e40314013140c1a864000f981c90160b5080c604150300740425020642c0003500b00503c03c0e940c000e4198290b401040a2a0189000c0c210300e55070f4aa0150500740098030b1480200108031940784001c0c401d040700103002c605a192070ba41144e001c100c000315500010b1916a4141240c0d5044c040010300140d07154160740400ca50520030f03107038a440c50b400030602c0b40d00c0b1082004551600603c0681118442035400c040c16101c050506000824940350f06100800703800c030788012407442c0061a428014031404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782043138 1250 782041888 782041891
    0x41e090501050609030a060c14030c0a090f030803010e0402011214060111150103020d021909090213020c060406050c2b061202010203120705090d06090201030b0109050105040509040507050405091005 87
    0xc0d103d00c0d10740209034020030359452040c540070380029505c202030321009105246034203403e20a90102c03a00c82c188154141240d42c0800c6588002c600c0c62080000c019003490085809c980d004034040f404d5a00e00342513110038180c000c2c4100d04100303416100c0011980c191244039500e000341c0c1010100c0e403030b141001515500d950900c11020303078040100c08030806041401a415a681514074441c60780c800d101048600e543e0001200403919281d40200c1e054029034010029240215141d80b800141d90301050200c6c03040710b4078000241c10100000d0f0214002e038220b40c0c0c2005070040868038003802401030010a00546002d0061118920304414884040d4013504016162140c00580040e1059001035a44e1154001d4990084034090005080500420a440301e20f4000b419080c2c00440e189418401042d100e0822800b1074505108003980394840e5801d201a60ba068440d01e24041c107003010000d001e04001c100315002e1141e141c0100389516a402024010420a40105400095240d006041d60070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782044388 1250 782043138 782043149
    0x1140a020c18010b27030f0f06101a130b04090f1b020307030c03020703050a030f020114011a1602040c08010f141f021518010b030109170c03041e090501 67
    0x51640c0140124400700c002c403845561540a410702c52031716030101c0f40c031002519107440c2d49401456000462000c001c56205604407081e0180d45150b0b0307510158400f00c80c040d008441c907c54035441c0030300ca00e4061000404129042c6410004403640d1048100644e80c82a00032104544e22000401210b85850251014100c1945400c1c4030346000910025036a001d00c00d00941007040020070402070600a1005a014680000541d906ea16541c107004e000701d144510304030019071802086008000d00c0c801e2090698005801e03001e4882055140c4032803540140e94082ca00002d80201c080050b600c1d032241c0c4410540e0b070303120a2510340c90103003060b0f42c02c0c150780d10881810340400202d4501d42d4548080280400382c2c07500002c840c0b000b0500491a00309a4690401420400f1051107c5105c24001460780340070074000901420304107905042c02d83e0309060008051540b15040001880d0100c2c0c040e09410031814220b0f401c00f5620041a110000000712030b1008020517402809036401a0140501410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782045638 1250 782044388 782044429
    0x10c09050f0d0510091403040b09010e03160623040821030441010e0601090608060a050c130906030209060109030305030a1a060703020105090d0f081501140a020c 71
    0x8426103c0c1d640b0b60800c01c1c00740401a55070035a035010000a1041032074000703460f000300c94070b45031100c610a03d207500c1011024003040f60030442810f28030f40020150018070b140d2042c07100d85490711606403110b40c4540196000c988805483d0303005c2a031804050001082e0007002481140c1040720340c0c0000301c2e00641c0301080c180e000c008000118110190302101d007031046105ca0b61032031030080500341c103c1c440800300c441c0b01d1038030314091444041500034a21189100e020745010781d80c1c0340350b10001c0790228070400d00c050b00301000140c045442d80d8049640240411001884c10600c22442d51040101740c20148003156141428025030400b404541d0340010203082100c0001c0c11500d0142081c00005d0203142802c1e162440d05180980d1010070000545000d040315407900c2103440c0181c0038100803600c2100301c1c4078000d101303a00f40c0d1003055508c001c580e6079119640a40c907441109650602401c2269043c4003042e45401c081001c00d6004009246165000d420062642c00c100441000295207561f50070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782046888 1250 782045638 782045659
    0xd1a0601050f030f100b0708070b06041b0509181305010f020313060c0c05061017060f071206030b010f090509010b210a32031213020d0203010c09050f 66
    0x140b41241c201c80e00003440403081000b907522503043c400006400e8004140c1c195001c241d1804106000300503001b031610654020f1501e685007000e0008071036414a0142c01a04003450000350746000d0300040562520292040d0408010f66500401e11030003681c80179101031440500600f4820207205002850020a2055155040043d41548917200100e03001d1300559660034241c180c1d074002c01542c1d180d16489402d68035a890144014020130f0b120348207a500c03070143e221005644e284086007841c030a031200008050162500c01003125801c1c0700b07050044d0020358440000c0003142828041a009151001e1801025030800c6061007d940c0041c0183c011a8180646a46155100c031005c81d1140840200401200003041849160581540001d803e61280c401c031020000c0c1050b0b400560440a006441c0032003c1c04801d841e541e100d10302c0c5841c168a281e80204841c00c0031100d003030020f240010701d45802809160000303803c5800302c0714598086294440c0810003030a203c40360300403050040300c218010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782048138 1250 782046888 782046907
    0x13180207030e0f041d1b03060f0c070812131a1009020307030f050a02041508010b18011214090c0a0302030304031e05100e010b04020405130e0c0d1a060105 68
    0xe800e0003100c8600c02d0400c403d4900c8181c8942d401010b091001c0804c0d154a0301000c3c03005070f10f4603216000c1d4102003080c000c030341c0094100001c210380201d144a6158081d03a0342c2c0c00110840340c01001c4110344100d4204100b10b4105011102c050103411440084012010f140c900480c14580d8040e00c215541615010002220005080c40040b680070000161341ea503030352902100145000f0000301c260714034040030b102420025501030302c181c4410542c903c17075400403078405444901003445250030140d820401c2c1c0500f54911282c02c80000418102841011000a150300c1a55459075099842107040001c1010f56681000b1000c2203c1c015900c00ca81d440c21500400d03142c0c4036502018090000e0182c045002c3d45041070207012103504281510700c90182d9210300c0014090142040b4500d40c28900d4035040b92405200b20390072030320001d0018460003110402d2001074294505001a940111404403543da16074400780301845121b030a40d2001c0c0141c141c8401040c040217051181040000d105c60300a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782049388 1250 782048138 782048147
    0x8180a150e01030b060c010c08040605010803040503033001140315190b0d020a08060405160506070312090804080d030f0c080403080916030305030f0603010c09180906021318020703 79
    0x1074800d080c030303020030220002004141d180c405c000c0758861561038240c603507003000e920100c13aa010b240305140c2072003681d903614030a9a030b9005500815600d80c004001114860540c008030712802c0144000031000d030760302e01120011481d0264051422104001c1c0c807055039140504c08443e540c0d0030944030030801d040c08540d030052810542d020030006e9030744080c584004d41d00c419208071103a038001e042c07650301034849087d6030f00c1d80c609640494080c40b461012684a0103400c8894003900d4015003001d00308402034404032039400b02c081d41891356580e1101d00d4004180340000a102429401300141940142443c0c0181216001c6c500c4c00b258901e0440710440c101c0e40805000c0d0010b0301854002e480d51918034200341032100400b940019030f103641a00104040e04500650700c105060f0703840058561303070b01050500345c40c502443d40f0001440080300f84440b0390513040c2c40d00c910a407410b002030301c9d031401daa80310202d80c00440c0c04ca405241242d03080100c00310759140744e00a0350401d01c3c00e504001d0507903000380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782050638 1250 782049388 782049407
    0x1525080717070f030f020903032a06060609040f200a0912210203120f0703061221020106030f050c03010b0d0816020d020603100f0609180203060301020708180a15 71
    0x1050b844040e10001074011b50141c941c0400e008041d00c1d5244822004290310101020101d10030410b9034508540306031010492510400000c2c140510f41514801040000e1a41c008090303030741542c48a4206102210380b4514100c0c401150005594411422024240721002c0d030104806a441c4000c0100241e05812800504084081b001c1c4d9001c0d44204141d00b540100106090200d400038104000710b0182d103036031800b500385900d04105d120388403c00c500e0f1500141d00d0284c00c012510603201a40c0d405a0b054560791049032000207143c3ea101c2da00e0581c0c100f003100b400d44541d40000070b03441c850b1038203220b21403401008071041800310806030b84014150182d0340150b400d2070301d6102400d041d900c0359148003400f103a0050000d6680d01d002c004c05004a425030062101100d8010030204920b4001d019600948114080b00f8080c02c08031075003540a544000c28031905550288010b00020320914003900711140640c00450700084a6030034000088202e81c40707210b12160929174442c0884d0005c1502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782051888 1250 782050638 782050667
    0xe100e160506070609080f04050f040e0a02012f071805010302030a0b07030207290604050c04030b090a060e0f10020909040b060f1023040602152508071707 68
    0x2640362407203400d00c04c00420354254060b162400018a080c441c0003640020b000b46e070300840b512240400b0305818841101c06140004141c1c0c2d1040d41c0100166000c0c030682d08011100c06038545485044131111001c080080141350001e42c00410240a901006d804000850b100c032841088650314680020307a42c0c102b00304010b0b2904150340042002148a40c04035075509800c03555140d0a14103410000c6161b40f1405900c4502071134807000721300186400d018850180d541d16131068141821921042031100c00a400c2091610900040b03200141c224003a8603a180719001c0508003035094a000103041203801c17400155442d03c10054409540c0c0d50b00403554102e42c1210031904c00d43d40ba04003140b1405800b010b595404400c4100c07101c2420b50103404109901c1d2085601902c41c01c886169071070303501841c000c640c050b8000701c81103d2064020404c0660140101c0450b0545c14144420740d07160081d00d0050000082c5c11104009000c1d80007101c1c120454451422000246020180104801a10141d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782053138 1250 782051888 782051899
    0xb0906040c0f180b0304140d02120301150203040e070309032010020906130902090f0d050a0b060d0b040c030c0e04031e260708060d150b060408010e100e1605 69
    0x81c0564000c000000405004101000f517582e04080c2400510503c0b010300c00e004034841c0090f55040f2910215803111074603070411850f0b0840c1d00303055840d60b4051451900004600c001c0c0000540503190000140c020340c1c00c0e031800078400e010703030400174403c00030004000e180e0b8080c07144005000900250036003c0850000700142c44450b95000691144540c0300644034902c2e41c94030208040015a008117030908007110400000d1034004c0502426285103400641203400a0303800720081503600210540c0842d005028052480441d035400405683c180c8056904a42d611400d0007004000d1020b0344c06800e00d0380c0300340018686a40c00a1200d5034841070b00407440c00175900311525034000e59074009040e0b40502401a02040721410040740c0d582118a440000c64000100e41541488090306000a401801035404514100080005010084445da170016010440044c030b0301420310540800b03451260280410041e46610b440640b0090074040e800c50700402440c00f0b1102003406140101c1e0000d580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782054388 1250 782053138 782053157
    0x304020609010e03030c0d1808071707120f0b0703020c06072a060f050718060f200312150d020904050102191809021611120102040602010b0906040c0f 66
    0x129145140c00f004160144004105408081804a00c600e0404a07030359519192540204a00c80724468500c102c0303946800854042c0300040c0145076501505c21080c1c00c4414070b55803041c1d80100d40c2d5450380203844840c008001142040b81c6981c14541128291400354100501040c0e202d0f00c40c0c1010700308100b4000d100388824100c403514040d928010516466000200210f42000f0000d0844001e090024901e0540040c206600031078006c2c0801e8004e0400741d80c0ca504003035007907401040d541891002d000304401004400d5515070681c090981805019607180e94820742c22505078070001c2c200c4942c0c0145040b4428140d282d6400003006207404031081202d0741c039107083c00303402882614440c100c507501d8000304051054201c9040f1034030148840c9401c010b01e6403040300b10202d020701c140c0101e04110311258000801c85402e10301441d0840100240da04400c003041d56422a0b00a41c000c0c00580d44072215050b5918004110690026098400b40100751301c20030014629283c0c105802e090000c0302d007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782055638 1250 782054388 782054407
    0xf0304020109091a030118121110020406050d050703110d0b1309060b130c12020703121e18050303010b1303120801050a1d070f020c0d0b0f071403040206 67
    0x980907002070a0400b000c029400040c106000400c0a4500c118020340c24034070310b42c07c07003c0382032150404c1c0c54000090b03404140780e0303120403a071071840f030441200644546102d01e41441020b00c010401001e494031042c0e82c03590081c1000091712b1000342000141498189204101c20324942128507142c0001f200040800300c201c00030307240303080805544407200d00c1d14501104000541c0c0c08212203c1040711a03a8070f0101c88402c000c152407906c0d0a140010340c0f04510000003020a8024000c92482420440002d00c1040b102300e044030000c001d07050717001103440c104069260080c403030510045c003000d082c4040b40f40d1a4946c40e6907848184203988580d45c1c00200c03005921440c025a101540d0711003036001d40c1d00740c0008000d110b44030a000e80351003016003400000d60105032000001204801c2032815119a68002d401ea03006c000c0300c414081940101030450185507203860030003d6040c440c4410f40e0b1702d03040c9100f0700c55481c9402000b190900090184c80f585000440091300d5006034100d40ca99624010344 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782056888 1250 782055638 782055647
    0xf010509030a0b180601240c030e06070309060f03091a040206070803130b070c050d081906080106170304031511070804150305061f031a1203180102120f03040201 71
    0x80c0b0001c2e04029109007880a0301c1c200d54010503001660808690325a40c03154034041e54840355803200d42642001c4c4c803040018030301410114007414081d0400b0100c0030303424008190300f03602c4902c0403400540051814891550090803105100c0402c1c601003203000c50036602e000300c0c2080301940c0365031802004001400c6650b42e0040f2000300c0e9101e80e80d507803a400c01c00310385000034400b800c04a4585015030006540c10f44104210045d0700c2e00000188050620303628155143c01000e420325403480c0500761502c503074080f240205401807425030700004040c1c1c5010400441030051070801103281e0402c100c1000864503105281000c104480000a15507048a0b0071040c01d2140350001081d60001080010315051909170307003400400340c2d850500541e0384500c20003810884000e40e1900b4541400310210416100f50b208a0025403c0c0340c501540c03110410001d05150b60f00b00d4040000d070f1002409183c12883c5256000386240b080c0000d10003100c12009213000b90003540401d0314800030100018055a106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782058138 1250 782056888 782056903
    0x90c030102040b0705071a16020d02030607181a0306011803020d2009070221090301092105030609070c030507170d0e06010806040b090a15050412030203060f01050903 73
    0x4000310b41e42d03541e89508000b1904440c030191103a001c3d4110008108031010800d004112040c90740c0e91800d6294914a8407030500004181c1c0c110300b00c0c902030350058038204030301c03405011540c07030307814113502c50340310000445002c2e421800c2021213110800c2c030042008010f898201c2c800342090420b1842c90300c3d04070300540b9280d0020b5405030034107001c10705120365030b06140161a1340b8050019164110403c0c450a03402c03e8400c000141d120f003d03800c255205041c0c010301030485c00c1c88450f140078030b000d00103400e580030000160342c0c0803219006102c580f101c1034022082481d06040c01400c500e8864009200c0140082c002014040c0003414042098801c0c804c0b2005594003504a070040351052543d8070207a0494400001c22500e822414400c0c03546c0010032030f0486044900511460f0f80f41ea82e804056036001c0c142c40000d219500345440002e681c4507145203554a0440300080c1032400d070820380c1003405940106400d062040062009a445a44c41907900c0700007800c000d990341710a140880c0c9028407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782059388 1250 782058138 782058163
    0x108180a080405040c1803080a0504031b08060708011406070218070c05120c07090b12030f0a0e0904030c230d050c0709051003060903210b0a0e0603031209 68
    0x80d0200d0104100d001405081624815101001084900a001e40301c0342d03414641001e1010000c4001c00014194400400e012000ba280c1103007450b03030303070b030f43d000010840d490a403011200700d9942880224010071455910280900d00b20b40700c0d501d044098042c2c0050760103d940030b8031000500c0429034842c400031310440030313140741030100500c0c1c0004014004255a4000c030be8502400350740c0500300c40301c2c4042e103040303e09060142c11300303078900f0140e28001d02410b603102e070704034100c0c1b09140b013100c00a0000c4c020030005810700d01e82e41c1c1e000d02c2000b4402582090300c64406c003501740600010036405000041c50a503c07001003486821000158200110320b881e146226104154420f10792a504c4405000741d402c21008403010151071b03402c00010380d80f04a4402c00a03031062074040020840a0300000141802812701d02048944120158010b900403203400105c0342d01c9822410340b03420042c039224002c0c518400074001c24200680060744a120b0761495502003003007a40032605030303036041c00344100c280d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782060638 1250 782059388 782059393
    0x905041b0e04031209020918060a05100b2818050301020a0903062a09090e0102031612060b2701020f0c130e030c07030302120405010c140a0b0c090a140906010818 71
    0x6884816104c0c90000c100030843c1d02c0c00b8260200d8ad0b00c088902940e030207000150f80e1043d05500f0044d15006c103401c0400c40d0b080c00d8400c2c3c0d0180c01c2c04400405030350f1850f505903403100074030200c511017000003c40590085000f82e01c10400700408580c804258000d40754000300110f0450044e1880c01c031021181b0813024100034008281c0300c030940c1c110540310b00b00d8501400510048101242c0705080340002c8804000c58983c1a83c02c4806900ca405a12181c5000c003100051340c40e12880d90712a142c0001090520710743c90724080400b180300c3c1c2603499014000900c003d014400d0110707486516030744d0900c6603d0140c00b500c000301001d5485c640001303410002c1e2408487d164000b15000980c2c0310010300c0294054000c0112040d20f062004048409407203040e110f0400030080742d0780d4800382a0303090250784140e00070094104002040c4161003401036510600c1d80c0d8645200408200c00342200341d004d03554207041e55441000d162140003103c1d5000009080600071030752665080c01e04018000340e20310850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782061888 1250 782060638 782060641
    0x60402090d0b010801020c190b0f09100e01020702280b1305040e1c020a03050412060b060a0c03030605011b0204020c030c06100603110906030a0f02090a0905041b0e040312090209 78
    0x1610550290400c21200403c441d01000742d2341604048044483c4087c2a04c1802c9001643e40715403844010740004050041f00ca44440b1004c103c030031101000400384041c0d40016155041d4608140c0421000b0000300d0007081140c06180071b40e200044900c40c0301e2240c00080355406c0c0800306160143c00409000d0403d20400c040319044a440c0c0034200110404ca1020400108805200103500b250f40350341354580c145014200700701d001000c403072802f0484055480b5910a4819103035030b800780c044140161201c0c10320481318513010741a102c5680000d030401005440400301905080d5442d84059010b0f00d00580e188528036050b800d611480110000fa80303d04d03c144141c0340103e4514904562240e9000c000b01c2c001da1a0541592051010341648586e0034030100340d02c0d51035a1300090480006881c0146813031000c0c07010803041c02e55a4055044981c1c1c5004000a02c50024144030300d400010902c892818100354005024040c06080502006014281c0042440c0300e580a070321800c1e00106480c440307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782063138 1250 782061888 782061899
    0x303020301092a1206091a0111011b2a0f050f070308220e160206090c15030705040e151e0603060d030207050a0902131a03060402090d0b01 61
    0x80e40c000e1040c0e0340041d02e4280780c2d41000315404032110014160790b8000410800200049070024070328180d000600d03507036200000300412a0300c20100e1804040c01c00c00c112080c0358001400c02e105192682c0f10036410400c0701d400000318240349900200003400e1a082c0c04030455000640a1810a9429115514540c084050025400e1900714051160040340c900c840030010198844a05100041030080700703020b0143c03200950b040980c01c10f28545441d001607a92003e4a40c0c0c0c200c001d9030042c03146000300c540c1c01d150941c1405281c0e8480f050800800b00400e240c000314000c4404016291020280400401d00d564840d4080710001c0240b001c01514604040c910a41c01c1600388014a10800a02e5a4004070003203100041d0111a80105540d056545d44800d1090300e4100300011401c50140c0302c3e010400355205a02c0102801c1054001600d6003403203002d4911b00100c9400603a0166180c0c030007008091521001c881e44180300f03440c09030310b402d0381034081285041c000a0040c50a103400c0c2c0041803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782064388 1250 782063138 782063141
    0x60614071a010b130b0a020c12030706050f07020c0901031a100b0f1801021f0c0509031e0706081003031803060912090603021305040b01140705060906010b2d0c0a0303 73
    0x201c5140c01c0071300c0350119510040e80c04d851003070005181c0560007441b1441c00e1403030304404502240400300b081d81e1800050b0303a03c42046400444111850308083ea00313006407203a041140c1c50852005644070001941903466250140080341c130809811184840011070b0441c4010204004014079007042d034036402c0300e008100c02c981085e80c0010f40d60311110701501081d07100260300891b03e03030710040384042104c141481402030148000d058052240400000e10142c03004c002c11403064a0088440d144d01c3c0241c04214248009070303003c00c01f00204042440880c1041c0b025a40480350b041c105400c080e60310608c2201d00641c4e0381d002610040ca0b04981e0f800340802c0c40c0c101c075041003043c0da414070410748409060301240182e058030040c00c20701010511060074254044020124141086022a13420b0200000140c0c4400d404541c0c3d40c11480900125500030041d541c0500108907c650030020b4001c98030000107000441c03c0b5468001014072103920344040d08966580d000c00050307840d07a94941c01c001c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782065638 1250 782064388 782064397
    0x1902150708041b05130b1207180c0509011d01140316030c0810050d1a040c232d06041d060a031205031005040f061701060614071a010b 59
    0x2c8080c03c40f030800e4051030303030800001010384100030460302011003000d02e0b880040c40c1513003006400c0701c0c010103500a201d0041203604020f104a05508014072000d4441d00141c0b160383c4807000901c41300b4081a1000e80c0c00030f8080403c90009170440303000c6110700c40129240030304c0c601c6c40c4006c800c0000c107201c41c40c500d140c2c09016044c00c0f900c0a00005907407500c1190381c0034044960101c0380d141080d0601062412280c0c070758060340625003000000048001c43c04100030309540417190340e09901e001f005000c0e500e40710000c00ca0f0002c0f140940c04000c200100c6c81c3c804440541020381911195000c8002c0c50040c241e818a01020704043d0311240c40350089a0501c031440408040a03402e24002290707441d20381482826658002c0d030203901c2d45507540080d5082d030000b410145000707207082c0d004240c9884a00c0f41d8401c0c29060711000c40c88620f040c440c010004040040c1800341d074141a4248070b031070340125406850322941c1d41103030354a4005040c031300c109020100d44d0043c82240c2000004668403900b004e0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782066888 1250 782065638 782065643
    0x10e01081f0303110c030607021e030f030a02092b1202011e0e01060803070f030806060d0911040c0305060901030b150a080c01020d02031c020a0c05060403031401050f0105190215070804 81
    0x16075441740729404056071002e00325503540041c0e21840000342d10301c0e5541c0310030f401120200304503030504020950004150b00308030303607030034001d6404185840c15260221002514854407840c01905038500c0d00d200d1508410000301030201d044506461391818400d522684e2021400224005407002e05d4805101a003811707100d507005076003000c1d00401c081e030010040f5418568042001403158100d9a015078041c6030040116030301c0341c002d114410a4840600a0840a074800d90030b510715148030f4400c200844000341e0f2000201881d1074200001515180c040a0640350012610400c42d5602940c01000700e040340300c10743c0c011178804d400003145e0b00b000a07014150f04007602610400c5084800807652030003944d21030750a00c26021528003000265500030191f2406900c1c241c0c1c03103040b281c0c80e080e01e82841500c00b240003990700c1d800496600d0103c01200c0c0988012550b03444200350342c00c0004d2442c010301035a06d0714164825880d1103014020050011441d0340c550503000c103480c003004054031281e0111030070b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782068138 1250 782066888 782066893
    0x2070c09110f070f02150c01020409051003050a030311040504020f1801030524030c1210060b13030605131b0e0a0227031609150b09010e01081f030311 66
    0x40790300000400c141e45140031811011414403a103a190358005940c1032005903080500c050480380301901a40080c141c1c10350510015030740e245040c0010040382c0d00142a2160301c6c009080074800074002040d50303d01070b505480d0100d000c06130181c0d4031740c06106680c48140c0c82403001078000500c0200e1805000e601c001c015440311030030800070065003600c07800c5551a0300b82e130324004200c01810380c1002803e842c010290407a508041d4280c04a443e055801094041c554040000c5c0089000c4c50700940c4050105580c582e030426407201e019524400c21804020541768a400001c2e49025024081c2e58103181c200e11944100075400c500c0301104400f40c0500b641031500c03500044c8003054035000b00c407801c10014004403a2075401c850410320000f104154117a15000700701000805151401200026004588001841200319010102c030610240d01c0304c541c2940078080b034481d503170300710190345508082820036200320307601e0b5200701c948652451800c880314080d4001c00300a0540c400300c8045000d517001d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782069388 1250 782068138 782068151
    0x12a08010e011d19180605070e10050a03150303080f0117071202010c061a0a0812030f19060806071403092517030d1b021002091302070c09 61
    0x10074006501090090000c5504002280280c032000b5989007580700a084100504814000d8484002c3d264a51005000808105c0404051100c0780c49100c1d00944c0605008000c2d54154020444c0340f0f5075504840706200020810083c7c0700d00942052216103c0c5400480c4155280e2038083e08901041e1052203640c80d00100102d10903060809201c49102181c0051040a190103000074840e441010200e0400440c5061840044c03807500540c0f40384071411000d0408800e0b40f130207005840e21302d5408010341d544101c2e002c00342c0d07215013003c50350890721681400038559142d0021140c42400c242c0f0524006181107400100254086440340c00380340c9964030803003a0701c41642d84c5005400140c80c8900a42c20513042c5208111080300090440f03030f07000102406c0959550010010350f5076420900340140c10001c0c495024042c3c5104500045070342c03180c0140c2c88103100b00001d41d580054104e9031820f0782e000072200640d5031450011084249614800d43d50f8580301c1c40c00d10101e042c04d10518400300e080c041c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782070638 1250 782069388 782069399
    0x30501050609070912230a02040b0303070218061504060302090102160b030f190f09050c0607031409030a1403180303030615130302090403050705101103060909012a0801 74
    0x40415010f80f440d90765901407a814880c010a1540c0001c40c00c89284812007030800d01820794051350161010400d001d400c512203140140030650303904510491203038004001110050340d0303003240d003184070450b034041170080e545d011b0200360140d800250084418901050004480b03034945c000303140c1014280d0a640b071010246400341403a0b400b41c051603a40c52001d2000880003484410301c5548601640d52007580c101c001d424080c02c980103085800c1060f91902d58030401e1120800001d0340d5800305440035450044a40c40040c00a003100d0141c00c40c141000506141e00da40401c6038040c1c9079000f110440c10310301802065a5240c2c070034210344c3e20b0390410803409881c5250200c01d403841180003605504840407610f940c042d90340d101c03003245000003000000200158951841340703032240b48240c454542ea4410350400c2071404039003a1400d0079450034609841c1c02080e0603000d03290000c01c169401c1120707440e410003c82c0945602884005070b01000d05510740001c1d05400c18a00142e03650701c400d1100e0b40c0fa207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782071888 1250 782070638 782070649
    0x40804150e01082a180a330e090a06080c1e040c110d080403110102180906040905012d06120f0212060a06091a0d03360305010506 57
    0x150007240c0452184400142c4d1542d418a541014a030390802c402910395204140b410316800440e0742035490000f060105803d410080071000140c4546030503544115424083e1403103007101100b840107a1400701300480304c140e000e80c0402d091000010065099480e0001c00c400080005100c0c0c803810748540d040205c894280003048480c5401d0200e51031000000c80b0b41480090030310b1207420410450042c900c2c05403503c0c18052041c0700c0c01d0703d80d03841e8000c0c02c050400134001100401ca046035640304104e49014480d40c1c000d0400b03c075000303503081c0741269a210002401400110300142481d4245020100b1a011518448410300d0000c0c0980c85140590488081101d030f407070040c18041c0d150900c280c408101c0642c0b0049400327100528481300c00480c02c600c281405425500040490b4581d0710512850040c2d0080785080d08140e0940d00100c104071001516801d00010040c00b404842410a1406c000380352003500c42d006441001d0650401040c03884041e0030040c44261707080e500c0c0c180807503420300e0503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782073138 1250 782071888 782071907
    0x1505150103151a0f040b030609100e0720010c02010e010f0b0d02060c012904180807020d021201020711030c0405040c030b07121812080c0409020c010204080604080415 73
    0x540042110240c02d1030400e48200c5a0541041c061002c00d00074091084c610358010000740c003050f06c2c040d03201e08243d414010f941d200507048032030b01c801010040c0f2041d09003140c09503000d200c500d02920070305031429000d4022406060070407415400e182c016075400c0c0c1c054008020302400b00000700140c03004906020111840056400e501c6031840d042e000141c50060054109249010f00000d640c940f41c00f00511410036603528001c100034004035084141c03526125811350b840000b25040001c5404d9a42c2d04c102d0310801c10001d100300d24000c40a415901d956950480d952507040085695904030306140341d00d1b03000c1c5c9809610030311500506c1c081c079052901070103004d00d501c000580d030041d0540e510b03400341d031000a001904100000103811800c1000707020f14080b0b1a001c0c0c0b4100e01242a900300f0044c2840d00703c05100522016109110114040e01d04440031184084c2005868802d06403605000e0300c10359200c030000f4032a0300c09000c141f101d0300c0d000f04101c13a509a1503210034248184240c868a10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782074388 1250 782073138 782073161
    0xc020d0e10030207020609060a08010314070b0d050901153c1203020c0907080402032e020702030703080409061d040305070807020d0210020102040612020c0307030e0303071505150103 80
    0x958008044824000d0700503028a5200030a0385040c0607d90300800c0d141d070891034480000401640042080c0140360b646401c0b4184403001618103030b030411400303d042d48a4501400c15043c1d039040041c121071400e43c4102078544960703802004241e581c0c05c00042448150781e1944011840500c801c840c1001005001d03d2032a00c80d0400951502d01184010307144080001542035029801d80f8000b43d5540000e6544201d066850721071907410240149460186000580404a850300c01500d488603020741210026800f1200b0250361040c66101007403d1000f9907000820300c1034040ba01090100031034006a0030344803204201c9204085800e0142d41598060300d0103400308504000301c2c40030450f401c0060050764006040100c82c0602070340800c04000c56600c080c00142d5021a061040a901000c1d24101018100c0150300b0000d2000c40d051f02d0784100d100c0182800018844100c16031400d00560301d107540c01840f1040004030760000c45001d440d007105e0071590342c642c010317100030258002c0c03103105007005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782075638 1250 782074388 782074399
    0x50105120c160f08190c03140d0906110403060b030703170d020c1510050a0305070e040c0510050c070f030b0a0b0604080a050102131406030c0a050f0703030c020d0e 72
    0x44411503441001d0344002c8600540d9004240c50502148210340c1554006114010080d5200d404c040404504103400c0d011904100a00641c100443c4d8802c0311140403201c0c1000b0565900102001500101400c000c010042404d1a440b28240c0030004090407c60b0302840341407040031155002c05441759080d00006103110341c0d094a00010305e01d2807001d04804a10745074014a040c403408111864903054421000d40c2128000030030010000d1015200014601900c00781030240c210354036070b900c0e00c90a010700310682410800041c207110b860311003040100009040d100b0342805205000b0003560041150070aa0302c982000003495081801011086a410005510254649100090190600e603001e903078003c0c818030010880100c14460903040d070f48a90300059a428040107030b8402000c00703030302c42c66800c19040800301c840d40b0b07400c2c120799201c500c41003020b5880705004d8003529140075248040003201c50101d6100b0030560140d210307a4041c622a02180c030284008a0100c440108601d1081c0c1c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782076888 1250 782075638 782075641
    0x603110604031703100504060b0d061715090102040e0c190207260c060a0909110403050d050a020712030917010b030d050703031103090a211b140610090605010512 71
    0x1c8054000744d41c10160300b01d10064050307540c0d03002605544580d04040000540010024800032041c402e0308028852003045102040c50b02c44465220b10428000721a540304082c0010700b0340e0020b41c1141d001d015401031001c3c407030070303e82e90580c01500800d0b658448201c0c2c810707031156650300000d50001110b11043d03424a0a12511900743c81038040c0480410551007500d03240c0a441c4d5641c80030f4040c459181e604e0101440c41c004d50b4805440e4181c0d4030b6540580300b00003e00208101045d1030001e80b0482c03d1099072021001c900f2803410000c0e9101d40d0300383c05082d03c4a02050f51150032281100c2d0344a45400403141c0390004036080322011864581c1c15401019030140c03003800349000d080058041d0500060f03240d821070756650240c0c0300300c0c0c010300d19400000c403041c10820754071103c2c9604d80803100d20504a2159000180262071501c40d89140014010112000c000300f180440d1001c01012060310307601d0600c1d0b500316200c3d05041c054201458240b6801180e2944100c042d0741032802074002540da01e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782078138 1250 782076888 782076923
    0x4180b0c0412031b0b1f05011107090902030a060f0b01110d210b0307120b1f140d0807030c0c120c090c050c030a020c0108062707110a0303060311060403 67
    0x5180b00c80884d40d000072942c0711890045018086142c0c8941504109041e40d0f000600b00c4440341140d58001906112400001452102001903500180c0310800000201c03c01a400082c4c40c042c43d5007001030006040601002c0501c070f580e000b87d51003d00a81b200620f18083d091000c0e110034403d44060000350b80441a5000c0e41e40c202e0054a540c0d10080340003d4444801d40460700780101a00708801e040001602a410030000c01c1003a80d10000c402c0020001240c802d08005554403d0b11941d1441181910381c00d2050b84d410401d4090305070311400311a5962010f15028102c40c00e00d40b001d580002c2c00000c006640304400b002e0700951a0b00c440c10104090400350030100504241500000b00038081c4516000e1880400041c00c5004030f540040152001d420001031080d0300c02080d19000300060401c140c03420f40000381c00c514035403883d1816880380c3e803018401c031400019501d076203120b0712580c0d040c40203058041c1c0c02401503e00603500b92525801a00902c0150b12583c80021b045844400080c0301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782079388 1250 782078138 782078147
    0xf0d05040e0a20070c0b03010b12040c080d0903170906041211180f060406050d0f061107080d0608160339091a0303041707080607110607020a11060a050904180b0c041203 74
    0x2d0041c451180d00703503356280c4845030720b410b030100e03440d10108003440818400c2c070065462540e0031641c4072544a180184a03808510310b40501d01c071307000d60810301c401e503901003208070080440c5080c4003034104a10390321a68440349100070155002074011070345001240d03d904003405250f068400103800390b0b410f00380981d0b60910202740074400343d81c080c0d41c9407650000995550000d00400c1d00580c0c480d81ca03840f140810100f100c00b254400102ea6020440800c01545000d01200c1240d800483e0414550501c840140c0e150741c48030000c3c0302c24840c01030500b039006201043c68040c0c2d03421040400003030078900f8148071f12400b506a000d9065009000c10440c05140860b142c1000c08014103603055680e682e2803c41c81e00c2030980c5c1c03030400b01c3e00380303c2e00412003d004c100f03469006110f80f004001c1d20702540c55508a5526001401e03000303210008071070075918050000c8070b041c580054001c1100c00d054400c0c8221101010b481144c00403003460102d145641c10740c041c1d80c01d460f4010508613040066907001d0f038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782080638 1250 782079388 782079391
    0xe0606071505181e12180a03030210060504201c090507061704020a060f02120408010207050618030a0309060920030f0d05040e0a20070c0b03010b12 65
    0x310602051040140940e255000b01c03405021040000c000c05001d80460a08120314180c80d15a10580410710f16055034000403404007900140c0390141c4c0e03546015500a0f04281c00c100420740080c0220750000c10075a0014581c410606051001c00c182a203610401065900340c4100340200008441843d40048040008261741400701d40711000103c1480f2942c0d081d00c1c41c00205827425008038608000c1c080d04401506542e192203110313155203251690020300201468001c03401002160303545040c00a008011608020381180744950f01c84d81d48000d80c41c042e611403030048800c0d004100100f10750354110103040c8950410740020b9400c15204120440013040c4249054888949401c01d000200b042900d16500008103100740d400c005011905140c6080b07420f00c0165880c1c0d101c40080701202d98480c043e40c0c00d50382d11040b0200789440d031074419006816500c071134821031500d000b20f281102c10020000c000076171113501401300d0150350b008070743d010b070009204102c45030f6003c001300c0060320340c407411aa = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782081888 1250 782080638 782080643
    0x714031c0e030a030c0204050c04051315170a14010b030a0305030606070213090201020105070e0102031e090301021903060f030b040b041a0702010c1b0c0b0f040918031106010e060607 80
    0x720600c50398003000914181020703206502060402e2044425400c1501896034000c440d011800e161a2410010a42090094440002150b030ba541d00038103000481e10980010100c1100749400480c2c1c0001090f1140300310141100c51141e5102c8204110b00706025440100700c000b0054a1100b046880a40d01d070b9000030052603005c002003024000681d10b001000446001c50180007031100c0d894400a402c44102402800c10300c440407030800c6560f03a0000c100d5850010310081c0c8081c074080c0301c1070b06c0818080d00300f6240d403650022a10003030a400d1a009030a442c00cec2d07a6418803a8968850780703100801414000942158014400203022034500c1c0c414540040c85107200c040194240e4040c04c01c0c10310107584080040c1d4446001d05416a0301102d090070002c0000742d000c15140d401d0307031071072050880c0748282c6458200201d01c0c3d2072850321110a4400038402c0240c24000031910160140d2213a42030031044012a44010515024200002d20541070b1429901e421013191210390800c815070300184002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782083138 1250 782081888 782081897
    0x3190302010b0402040b0d05060a21060603120305220c06050a0c02280506090906010e060c030301090c0f08190b060f040b0406080c0c100b0d02031504050714031c 71
    0x303001c01e50700c3d9880104001d150b00d0442940310074000407200e040d01c40241402d80300d0700f807180c0c0600580e0040003143c0941201002450301d42c10880c41c10102070151030344040d1041c400026002405901504144d02c5000d4105007007001ea45000741c10700c4102c030010409014100013840034807140f0b0145004040c0c4100900344161100400c1d03001980055075501610f4004480f0920f1100d112144031202c0e0107050103c070110b0400c44440086500001c0051195040005101d1a403a051312000221081d06d1001400d8a60720340c2c450704000003a004480c0001c0c0020714035030b000e0b8000c510982200b03020301080103110740081c05004440b0b000d00401200703154010010083c0c0740900070b000d401000201103c5a07426103480c40c1c8840601460780040030400407900810001d189034001080e2980020f02038000003c0102c1c40d4004114544a40d24000f034151140902800000c1001012644114452412102c00d03589820b80e901c0301c00c881c603000c40e415502250664840328401988802e507030302c15142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782084388 1250 782083138 782083151
    0x4140904021c0609050d031e023f0703020c1009290f07090810200a0201051501020706021902030a081b010f0204030f0605060d0b0c0d05150319030201 66
    0xb008140400168411186a6a280b1080e02040000d0100b0711050902d03080812614000c04c0220744608407003045000944e90004e00b0030b9225028540011385120100c40e626412008a45907809205800303030350b0076130728885c4000196001e119001721040c0d0329509001e4042100e101083c1400b42010f400f04444040031940f090483c100001101d15080040210b000030504042c881100d20800c098226020070455100c148003950700001e84c507048010103907000a0b40c1080c10290010140c0c03007140c03c600d500c5d0002d42c01140a9054000b00e006d1a0552031584125030039000580c4d07100300901c580300150300310001c006207148951031050181c41c0090240e03405400700b55140801c03940400b04d8000d52604074000300c0840c0409228002107000d84e000300314605415178a450303540310804500144210b48400005807540c03103c00305021802e501000c1c1c00c2840c144a07540030700c00e412082c4540122803030b00f800100082c10302180004c0d0303c540a4050400060020018401c106440c041981076648612 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782085638 1250 782084388 782084419
    0x10303170a0e010f020a080603061605161205070b182802030f010c120504030212071a04030503010515090619090e07020303060a23010e0103110310090b060414090402 73
    0x52001e010381d40c12001a50b801b14002c0c09092010f0141c0351034001e901c0701d070800c00140c00c0c9000003002d0020364102035031a10848208034103c41503010008004440b050003080c50603400801518000f8440d01320003a881c0d4a00a0a03e04288a403803019420350040b1a501a955003264131580000c550071000c0c4502030301030700443d152848a440d09082690b69281c40c80d4104c0e0301c01070060710421240c509210b24141518001d684550490038103a014400183c200308100e50391268402d41d165410303003540c5504d040e0401078482c0d042441154024a0f50b0f169140030a141d8500321000044002c0015061518039603031164494608103d00007802500e44011031102031781511188109000da004690300e00c0d0600500200803040c0d070008040b440348039403034101440303c0e0003e00140c030028a41503aa103118500120058200321030480314805000013845515581c002106082e0303a166a0300f4805007406109200081c400c0d486004c3d548614070818801c1c5152184542e60080d000414100305c001c10030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782086888 1250 782085638 782085641
    0x30c04090603140712050304032907180902040e01031b05120f0c01050901081f15110d0503130f050106050a0914010f080304050d0606150f1403010303170a0e01 70
    0x5810984450100760301a000c8002c0400640c0068008103400b0007101e03000d1b0703803580e0380c0703004a0000800007102000c000c07504061681403030714400e00d840b1071013081d424088000740c14542d1644005400d100d01450204242d0006e000700c0d422034006000c2c400840e032071a250f800152507031269610302d4030203020000601d50380304604105142400d8005e4501d19000706140c0740f4194098489505010041c060800700c2c0e031708402d155904c050f8015191030740301c4404440b1114004030303401030b050342c8100c242d01000c0d4507031021500418481500c1220600c806c040c106456030702084542502507044c06400c440010190000a19064031520000c00c4c1180c0324400660a1542e9400c120303d12942c030040341c40d41c0030f07428000034010b004806d1024013113810005155120301c0743d03000c0c881c002c0d240300c9611400c00c40c0940c000c0b00140829584c600820440302c0005203005404000440003c0081c5413a10800c802c0b074044134101c0b0307410f8507070320074440c0c810b6580c8101240003001346103040e669011518025034207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782088138 1250 782086888 782086901
    0x1315090807120314060d030e12190308010b120112051504080a030b04060501202505090114010f030c021c0e030709090f1b1505181c0206030c0409 64
    0x100b4204014074441c0000400322426054000b1101d6110014802a510781440020310140c00d0b1401907622044000030034001c014611000d0301a2140c0c544c2c120801c408003900d0802c07148640c0e603045099a0b1441c2044090044200c0c03803000d560a0801044551071480d4600c803110b104c6c105036010790003060100a254030003101c0135948018000382c0703621403e9061240392002074046404000e2641040002000200d40c0300c00056480b6100d020f10916a90070040880920003071103018903210702c800700c10f085042041c400c803800340c4a41700001c00c4000d01c1c0245114980410ba445000d2900b901070f00310060000004210107502907218041c9000080d140303046050411a21020340710a45001890324001d074503480f55004500e081c2003000040c24040c00030401d20f4100e2040c1d8001c0b000a080b20b040701c03c0507442075850504c5103500345030140e008000b42c4690800400c5030989002d21400b44000c01401d00070b0b0340010720940c1e800e02c00600d0500c000d5a00207202217030350750800740c5070b002e04403c42e0352 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782089388 1250 782088138 782088143
    0x5060709060e010201140406050c0903030705070e10290c1006030c06020111030a0203091507030c0e09091509010609020403030e031c05040b0309010f050c03090c03061315090807 78
    0x20008801e0207090b800100c8082490030a20007000101071903c000032100d140684010001510303900411901c1400c44140d0701c200100034242c958456080c03500c03940e10300444c89441400c858160015420698844284003164520518100c1c0095070087c0007a80d00c06080c03130481040010b01c41c90f010a50104140d900000c25584006250340c150708000c124000329a02c080110780c10441600e0b24520b150060300c1d00242455809601d9803502d502150a000d220f11307180000d200380c002045030140e45600103c2140c282d5896800118150034140320860008803450521580281401c8030031403000c28000b54840c401da400010038946030755089040e42d00c10340c13095001541d0012100120324052041d0300c40c0441248a5980c0e401515201038068000d0348201b04c550600440024090807080d0480740d10800d0b000c104000500e0000c1c03500015400a9440460902c02d440c045444c2e0f0800040c02801f0750043c2440205518203955603840320700b0f90102d12041c007502d41a80c0d0001441190107401c0d500d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782090638 1250 782089388 782089397
    0xf0c080705010b0a0e1b07020f0607030807080109140606070303090605011d0934050429030a030509120715021f0614060703170f01050f090408030a0e0703050607 71
    0x6050008001400f01990091201c1900c405d052018007800740d43c040b114028240c00c10f60310786034035000107515a0401c02106400c000c0015640c01010340c8840c100d481050f40c0e444140e04d598079120701c03104903526101d0044a031007858021550034070f4000c0c050000513119160102d40c0789200d5072148207944080c0c0c0b25002c1d1980225541c640d0410414040760700241d103070010441c80710aa131480c40ca1710701c1c044500e030a40081c00326400840c0c00105101d0040c1101410512003c40c261003200910800c1c4860f03c403c0c8000310010315010b00d00400c042100e6501695958108941402040451803d106201046100303000b40081c80020181d0302410f850b00c950050702d020100d44d81c1144005140c015510181441c01c5c0f0148481e8001d580c0d003c03200c2d07009071590360702c0329200d1905507000314000161110313042c1c15100b002100b06c0c540d040b241c1606e20954081e079030f00300514288591842c0680c2c005100b840f050000030903000072684444418000c1e542194646a0389440f101e003403140944a450015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782091888 1250 782090638 782090651
    0x2f030a02010b060309060402151215130c0807051c0e010f050106140a03020a2a02040e0102131205010612110316150e131401050a05090402100f0c08070501 68
    0x119020b11446040c1e201c1aa0380d00d24600c1d2481c405612080010002407180002d000c42c01200c80c612020340381c10483c8601c44010602306032031107042c01400f44103518401c0c2c0f040410f0383d8903c071050041c0e40c520b0380303d9254014907850314035041d580b40c0c1192400102c150700000219045007414026101c9440c2d0000001070f10841242150050b01d2050708600c05014640c050304007844078140445580c00210b240040c0c0390440802c0441c0e4400c9290510880300290b200c1200b61000320203903000b4140c1c070885081200c0b6140d41001c40c01c0c0d000700075009681c221070400801400005618003001680300c0c0000141c46601d5404101d984003929000b603d8869680f082030742e081c201004125102e0f0801c5c013812092a24185841c00700c46032400d003282c200460b130180c06900d900ea078240c01c40091220601441480c6001042d2052010244581c0d80f0507001c901d0001a6800c0000605000c4d980140101101c03050800c010349079022003290080c100600001c42902003208031001d8a00300e4420000403d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782093138 1250 782091888 782091907
    0xa030602121003120513030c0b0c0d0e0616020609061605150123010e100c0c0504060b040b0c0a230d0e1e060c032b15062f03 55
    0x101d4400412400103440700000a0000c142e241c030100e0000d00651622581d9204080c0300000203107541d520040903140c107807402044900888015003460601501242c1486e0500c07681100c50389051601c250300321104221180305118045880401540054442c03485c00702c0500c0801c541d64840c5003403651a1061005900070401c0610400780c1c03000d05940880c5095050107070b1340c001103294041a45070301d20902c102c3c0364240d0040140b090604002840040c907100484006007881e000160110b400c5c603003006002c202450144240c2043d01c100f00d446500f041d08001c2040c00a90005002c88564407840e41c00c0c3c2d0001c5d55a00c0d04c80e020048180c8000b0a40000503100b81c0b400404440341000d000102d0b41030481511024019100c0b01c00f48441080301c2104000424114070580d0740302c56445c00001801070710500800345a41e0300000030740d514003550340c2d0000c00780d0480301d0800035520303030056000d000c011b0031b40b04400d890a4068018184414000c4a81c4403044075101709048202b65000403d00c0e804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782094388 1250 782093138 782093167
    0xd110f1309050610050d0e010f02090a1e0501032003090304060801060e01210e120307260f0a0b060c010b01020705010905060f030c161a011505090d110a030602 70
    0x2006081c000740b2041c2407600004000d07100c50a4942d0401ca40810006008115900074a81c4040c6182c0200b022503104041500654042d00d070b49805845580c100080c1e06006100010030002c078010084405070600740110045d0810062109800c2c5c4804031185404a04100940c011044000210341c0c503880c004024041010591040c800d101c4001c09102880c0d030044611444510086058088000d50410140042002c2000d0022a2051141200380480014000d6000381140c0d10f034551500caa140b500303c0120740700802518802c14800118031182c0c00c01d0b0b422500484010000314840290303a01081c43ca4004d4800e640081e074440c14030b0340007542c0500a200240c142880c0c0b03250074500703010103d02c1a2280d4070811082440000c0011400b8044d00d0680303d01528130055076110b182d036800e161007050080b20f001c000404c7c03442c00008080000300c00021038048030b6150103040031440b4082080001c1100003c1d44e81d245031040e100d950b90b80e03000410018521902c1c1c01038031501850103030302d13 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782095638 1250 782094388 782094427
    0x3090b27030f07060c03031109300a08040905010506040513020c0a1707060b04060b040e04020d020a180606080f010905130507090c03110c1908040902070803040b0a06030b0601050d110f 81
    0x3a0408401c104030005610ac419410616250483c400744030400000d515038190124007200c046980507451443c0e0800070b1103401042241c0182c84140808d90b00c0c0d8003000075a00c50b500c41c0b0369020803103507070503a40103981e0b40251070307200c4251003035540ca0174864445441000191380c541003501d0b000281c0c841040250302c104806028140c500700304860601e8643c0c11188641c1c01690034060a1000240031581e42151010b10a640580154030403075440e100d0040502c141114010800c0c1020800324078144942078070380c4039400001c501051640381c202000020800681141e108240d022925008103808000060040004240c0022100c40c0800001c4c11200c902d1903c001c1503108021800543c00001810700d1a609410900c3c4045c1115190204103481140e009042c40c5001244030703018852410090740c03003030f0301514500110b41e07202c9640700304a5465010052501000031701003280c1d54031442c05404a0f498402000821002c0c510710f0800c181c01402c44e54111031400038682d5038821240c00e000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782096888 1250 782095638 782095661
    0x403120f11060603060a0207061116020901060201050606032202100206011e0b03040b090703170915090d17120a1a0312120705040315060303090b27030f07060c0303 72
    0x342083c0c01e10070300182e2206409408110015000b288490038041d82c3c0e40507251101c5080d0301d19556180c48030520485069198059100b190014000142d95006001d020300c2518014007031031647c2d85102044150350b2105031420442d1401100c43c200503207840c5801c1c418540140c005003883e40c90321012400e0351120001400709581c1d032810401c41c980841c002d880c0c005510410300348882e070f202c8c480d15242000603030001d480e05d01e400f20141c80340d0031814000c0150031003c0d01c403103940c07000b9200d00042074802c8912154100f4281802030000c510140c28841c01040c801100c1e07440c0880001c0d0510045505940e10310303c05550b0300e04800d100c0e5a40800101626013074010b05070241c002104050940545640300c3c50f0718800d40c000900040c451000c1300c1c00340d64441610412282c1da40085d40040c0610b000071004141c1445010451120031002d036810800000742c1100c0c2a500c4188098002c08201c580710313014802c16443c07500103501804101702500c465550045406650304009055500c0040c4c003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782098138 1250 782096888 782096893
    0x1805090f0f18030315030a1713090c0f2714030606090403091a0d0f02091212070201050d0908031e0a02041d1803220e06060912030403120f11 62
    0x1d8110402021080c0d0341d00c0451090468580302003100403e00f80305034000c00802c420007201301c45440c402110050304074048400d0f20b04101540b1902640c0448004002c08800300341d8040f02d0cc2c4070139100d41c3c0b55004442d14140308901442d4290305003a1104400c2d045003200a050b00c9801c13256040c20800b481d40018210740c1c0c1e004500b0544c501400c0c4200c00d02402e14071101c2003030783d48203082c5200d00b111408a0050000c00c0004012590000203400010301d071885000c9030030881e0f0740404009013000301516008001450000240d006427016405500c0d01d907801c507100d0803140d000c2800721020f54400c40c03444150300200e4580100c0341002904c0105903290f00c920601c0300b030100001c035003003039204a000848148207c0d11555203818268040b05603e49440c03100060140204100f496055564850300e0408120f060f103d02c0c440c01111001c42d186500900c0074000d00c402450040c400842c003006243c207503071030306849441d42d2046a02c041107000100d040030346c585041d190302c0600c000d03054401101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782099388 1250 782098138 782098171
    0xb090c07020d1b0b03070906020c09071d031e01140705040f03080d0212100810021207050913060308040e0609040b0a1e06080c01080c0f0a1805090f0f 66
    0x280030342d00d5100c07002c0e04803e0003406000c1100000224800035044120040343c50740751806000744020a1401180c0060088009600f101d0030b02c50380160180c41d454584070070714607081880c6000da034148250740d6454411814551071000a0309000d4020480031400441d41d0445c1602ca8403801c81c01401034010401c080000b003201c40d0408114509481d4031081c200da0343d82c50314012030301a000c0c20031000304080f000c0d402e00c500200e9051407001190a000255417921110054480403802040c61058080d0403000010b004184914024095010001c0078006030700c4002c00400300b220035603001211034400002c2c00780240c00700d004845901c69401c490300c44061030159500e00390044060050040a40ca504c290580c084102840000c00400c0410401c401d942d02c070701c955030710303400e40440341d0110300c40401240c0f0800500c0b003242c0743d042800c0c22861902000120071a01150411440e00c0c080700f94a0000c140c903900c403261140075100038072074110707a810440031240000c0005044604140312602 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782100638 1250 782099388 782099393
    0x804030e06070305070204140604050106020f060612190b06040b0a081b01050904020a0207030b0c030105030d0c06020712020a141b0f040621030906020d050d02030405010e060a0b090c07 81
    0x10240c1084000740e41c250380352082031809603a21300440b00000d500a0401000804400d21030310f041d4460103040303505004599803200e060b62154140f815500045e00540c00040403814409022880603504100711144204c004629002d020615042211184000300a0126600c0d0a02802610040c100c03101c07500e00d0b2400d048113998940300384407004269149202ca06450f8003440c15500c03103e602500541d612455103000940310109400119203118100b00420f1420b81041d0a03603043c0c9001074020030101503803a606950041c41036200701c81c059000c100d444000f8a141c0035031604400a0b40003080101502d2400c0f681c1c40074940447c000310351080201c0b41e4016140c0d44920858102a01d41054424291011402811440e040300f00c0007550442559200c1c2e10207611101e50704c3c02a82c4801d400703034554108a841e503400740851000a50f0612445005600907401150061f1141d000014a0032540500905055003140c5c4244c07003030b9803502550307014180248505e03423062104002038030b46003041d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 782101888 1250 782100638 782100647
    0xd20100906030e2d0645190b180309011404030606030305120c07050714060705071401030c11030a2601141003090203060f10181a01080403 61
    0x28401c1e40201601ca03100040000024044071041c10090f03481142c54400c03e5030786041100340342400000500c1854000f4171010580c50840046a8a03008501181201c1200d814840541c415034110076200080c0385034070002081020100014031021358074620741c00c4d402c00d03540c0c01400821000d0000141c40c40340e4945500881142d603461800d0034100c08500c9805142016400b85810041c201403508001000f40742e04240a4885881d4400e0901d8050b0303511303641c2d10f01c0c41c0030b40c1c04000e0983c0c3c42040300744100190500015941800640014101145030311610329004066010f5401c1c0a10195042200d5074036000c1c0c01c510001030309044d031a215040c10b80607640c2c032078112601304108400f014003d800e10301c00120704400d80c01c60484a02540c440318445611051190000d2140e84160700103400c840c041c2c06144515500100a8071032039455102c84002d482008185020208104030b01041c0c010044070b0400d0113241030395001407582244981c01c0300c2031018542e402d05011030102000b0000e03030320 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 782103138 1250 782101888 782101907
    0x8162f0112022d1c0501090b1c0f06090602130501180501021e031b0105070905090f07033209100b0d1502160305220b1608090d2010 58
    0x15004582d141443ca104203400500580c4010a04400c0300703440703036511060f29040141a00d440010401c01700000b901040241d0078003d8181101c40446d40a2030082080d01420362811800349030046070303000507513547e0700c1264050050000007444201c018410355901c42c41c41c207580c00002d54140030311403c080001c0d5980c560100d402d01c01403a807064110040800b441500c9120310700010059034200c81d810070a010340b200322001d000041c1c40c3d03500000e41d46031030a4441d015a1400c100e408180d01c4440080b809890400b1780c20508034154940b070100c90b4440307030340c12211108025031003000741000100d40e401c2180480d40695843e0030458002520340e5401c885103c120b600101c81d515400e0b0041d40e0001a010707203001070201340724501002d418550420001c01420070740c0c03050036401239519088103404451500840c0d1022405000c2c0703040d1000c54003800e29565005002d0a030a002490001950034511104204d074003600403031725208208072415920303c54010031030750f260940400550051032142c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 782104388 1250 782103138 782103187
    0x3070b0106052b0f02070b04050c0901031a09070830070215030403021513030314280209030601261b040507170703150509010308162f011202 62
    0xf030141d0249490052a800140c1601c4002015520b441c600e092000c440b0b1012a004e6505010310715841031585055912039068070780c04180c013a1001070800701300c084004002d20421071071280e2080442d40440401407070103003101d4410026450248546920142c0d42c01c010f02114460040c0f05810050713454000ca03c4040048031130881c0c4035911810300b00d00d844c000104090385017031a06c0c14415814405040300c0c601038000e031014840b5105404280200c41300440d03225413091400403403403008800c4100300c2061b8001c0f070741000d400c002040000909148080e80074a816120010b4002c25490361005400c140076a040c010b04081403000c0003120b04070041a05146c0b1072130ba42d10015000a0044280da00303200e8141404401902e00703608003074010900b0444100f21000e1110000800307107450f80c90141aaa07120080d00c0c2800b40c04104120010005c0c841151203048911902c030300102981e6044240d190362480e642404400000058070690000100d44a010b0040001c0d20b1130440d1030029040b45217 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 782105638 1250 782104388 782104447
    0x1e030d260408120a061401020f0a171308010b01260114040f0f1424060307020f0d0905100305060d11010201110a05040f14010c12120e03070b010605 65
    0x2074941c50809240c0c40b404034000003884110703051113602e030303401e90115041d1a040701050f02e041c800304006a03560320000c42a04c000d94060b4602d940020038207440444003080c040543d81c2001c4050980c0c4164088a410044550b0b40d502c40d001e84079a07201801e42c1c042c04111821160440341e01008050412050041036400c0044041c1c100c11074031030340e201a40b81042554200320040c00200b821020341241140e05880e08000300c08240300c0700208a40841141001e03500903a80b02c403030002d0000f2604018058004d600825900c08403003641884001d180d00019512030b0901c81c28030040010022001d01407800b05031030302c8100013a0362247c654446100350408102c580c1c1115050040f409001492000d0390b41800102d07229100d00e400001030000e581d1403800820f681a12441680c0044d041078501f14000b03200300d058407000c10f020045d000000c8a09103050300b55000031071001415207401102e50300303081d4000140803050082102030744c4d000d001a071900d6890a6810f442c04080f25015007c07410000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 782106888 1250 782105638 782105641
    0x3020304050a02130209011206050315180a05070603110a050901030213050415050301050105040203090a0219150804050607110c0f0118450e0c1e030d26 67
    0x54200320801e02c5550080c80e034802e0b0010b80c280c0002a4026481380c901046140104265400c0d450003140d0546401500809500b8068041c08022580180003814610300d81090013100000912284417250300a20003003480c0d0b4a410001421102000b4081810b58010f0204030780d401c0c1c2c004110f91a9203403d18015072505400300c440c1d81030303180341da00255110785080c0140462008161607141221001c1b002003203103a80e14000c2c00103912081318400c0f02c0390401c0e407448005107440040703030080d00e8282d40000303071139a1070b411500100c00c21441c0c0c0e400480c4a0350204010810100311203940402280b41034215620b0110310541d9490007151518401c0301030140708a2284d100b43ca01c040396040740c410079009140d40d482c1c4004001d80310764440c54100d04484030100ca0790b0121541c3e0702d03074140e003001c2c80036400300b948000d4004011500021019014409201e603040d0b030382c03e00c94000802001894441d41c0c0452040610b001c0c000d80d10b00040c003034524032543d98586540c41c1e40201c00198110441d59 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 782108138 1250 782106888 782106893
    0x605030307080c0f0a2111012f0f0927010b25030801092301120203010b100c06090c05030f100b1507060b03011d070e1e04020f01020c0d031d041b03020304 68
    0x7031950047c092045986424841c419420b2002010000c00b10144035507010030099113025400d501c00c42e4010810064100014188e42c02d00503404901d024025080c07400082030202d403003440031000e0f0f114070080c4030045607440351a08102c10140000c40c4010003444469400d540103081d520051103041480b940e5075040d4208040802d10b8064006e54110200315150b86600d4003508051502c001030b0b00a40c82d01c13013503e803103090000110f842200d0030f80707a15000c1041640d030302015004030041244c80c40441c40d0002010b8504000c14103000071392070090401340911341003803412030350910b041920071090320065080403070511048030b020344e40028011540074ad141c80800c2c09003035162006024078252043d01506040046100c0058940114145c0584c1c0c03285013070520781c00c090001402c0f0043da0314020400610b400043c81d5040507042c01a5100300750b03003000007084440250000e5000c5501c0c560018082400b03001c0403000340c2d02c116030401c040001c0c03072201d42444540c0400c030014075500201040c10f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 782109388 1250 782108138 782108147
    0x1121b080907080a080d05160207090e0a0b13060c0212121b030117010506010309020a0b0c070306050108010c080912070b0903120a06090c030e06070509040605030307080c0f0a21 78
    0x60001c010072101e610510340380100050748a41b1140301603038940804604d44500c160100e00355600268014200941010403140051420900c000e046100381a00b850000d1114800c00d44114442045181850440c0c01c0030001c1e29540c544023030454201e001d182100c1c0e40c400082d2140c80b00c840c0000f00c200c1d560400b00c0440c05113886007030040c804002c40005910501141c5080e007600c01d410080c0013a8450300015410365501c3d400081d0701421000041c041e20358540044c0418010079011a6141560381d101d900071544c0030b070000e800994498100220964000c440542c205082100400001650181d00c4040d4011024020300901140c40801c101000400545660003a040000c00b40e50520008138402804a88150129142000d06150005001c0d00c81d2147d0032000d4000350540c0d035039404084459a000c880c0f4107030700c1503031040045000d80b4200090034405104400c2c41d540c558800010900d0310030070045080403507100e070310413000040043e040050840382e1614075001001d0928070989 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 782110638 1250 782109388 782109403
    0x10c0f0c1103030d05041b0305070303030c27090b152a0f0703020108010b0313080a050f0d020a03200d09060e061e01050d0314070201050705070e0601121b0809 70
    0x540c0b5110104040713481d5000c42e40943d009601c241103440e0038451200e0001806142c5100184c184e0300242e00400101e8026044403012092601e02428a024101101004241450a122503982d4010011b00c019001c91048609500c022a04a4030f0700d02c809003028640e02c100c04c060308514480e400d0b00710400c020404814060407151044c0d68050481581e550368540d803902c0103074002000310000042000c5140b00300c1c0c0c0140300782030140030303101c5141d00c500c4c055070700c01070f100c0c801c00000300300c000203142c0e03d0310240241101da1400541e0780d0b068510b0090640d55401081e041101001207001060140c001c1203409501000030045800d030240d007449001418a00c2d06028207001d51070030040300b030001002d171820700010190718040c0c0b41d80350000c0c400ba102c030102d801404a200445482c81c0d4000d90030280c805140b051404c2c524180e111790312503040040a51103034507041002401e2008968202c082c01d004103504003c1040054902d814042021240180c284140210b080115100c0700c810f00150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 782111888 1250 782110638 782110673
    0x415110418140a23040b0f04020a0f0e0411090c04030b07030603080708090307090b06090d0f06230106020d120203371a0a0b0d0615050a030c02010c0f0c 67
    0x1026103001c3c000900a0101261420f0099001c65025512504c2c030104141c020f6411001502540d582c1810380354800c10080d0090b84d00010401c00018200240b40e641405070203030503c6820705091605d402d121003180550184e120b59991401c10084880c8203064404503070b000310f0540c5d000e881d201e50640007001a9000906101d400003811000d2051213401800300910039811a032056548000b4002299405000e5960213a400c10407544541782030185010010300a0841422421050782d0b01e1007140c00b51841e4001c0000b201031340700248204095103500621143c00030703001101404900070720295040400c8004540e0102c081080607440600b0040c100f14075024040004850400c0342e0305c0715510031600501070307051013034810031003210f890840c11940c009444030b50802c2c02e2890b10750325500100c0c5540999691034100043c0c2401251074048010200d88503203607100e840c908000d0503140700c8003d0344250fa04107441544110742c068168000c44c009450513000340350f898034002d070742000c1d100080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 782113138 1250 782111888 782111921
    0xc010b1c021e0d0c06120b0a0512010e0a0302070e010b19110319022a0607080c0a1b05131407050a0c060e031206100f030b01030e060f0415110418 64
    0x4400c1000441c14400703056642d5901e460707201b415030314140c8050b01d00c00400340381c2005405004020b2414441030202c10741040400214488004078800c0d0315040c000d89040e03005a000c003000b00940844d840c50b09014141e21a03545192140e00f01e500b44130b40da44600e4041c02c0000520100c0b11244090082d1440e038004008a0008031a210000a60b900300e0768116046031081c09925203a1420000c90b18408a030f000743c850707070601c0c40a48441700030743c014000840490281d00c080e080010242c180700352001c440910600d411505007400e1080c04181c40e000300042514000e07039044c440f4070700c030081039001032140340c0341d50340740c41d480c0342100e41c15a6a11700408060400028a148600107c068556118158545d6400c2c1da51141080626003c04252070040307012120b20440d00303440b0750441010484107040c0410500c803010070b031600d095400c80f540304403980428240410000305d2103107407140d0340e8001001d01000340c4565070201e15224500c294600f00c1e8007845445880305550300606200c2040304d50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 782114388 1250 782113138 782113159
    0x60f0e040308152b05120738090604170c0319050c10060e0901140a0506010314090c1005030610180815041407030305040302010c0c0b040b0c010b1c021e 67
    0x4c0c1901440c0800704607078a020760b4000103e15210101596000c507000b244459501920640340d1034150f01407644061041100c0c00511881c04400c0d1030303c0c2c00303621141d0003804549013a04101881c01d1034680c508070109002c004042c00010300105071440380d45002d1280b900c00200c040b080c1ca6a00c5402c0401d4294081c0100b0301d030040040b64095422185410195040f40d0f0310401081c1c22621016084944840e0b4170300402c0801c40c0d140c0c40b5945c800340606001880c10800380428051030800c55040f02154040d400b0800b00d42005e0a01c003405d40818204182036051000c00141e19002041d104420444049100901d00c10041d0543d8000e280343d40c1900c0d08680038244024000707034201d03419a140c3c80e46c9488800e84150000d242c90449426540d03042c20036046500450300450200420760b0768800d40100407800c1d0703012000410050898101e410f543d0440c5010244c03d5500052410303224028032010342c40c0e40e54410319000080d90b81110390543c0c00350250002c54841c840c420f0004e0300034030f0110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 782115638 1250 782114388 782114449
    0x190309060f0609110c0304031407030510020406030c03200702032a15070804090903030b0301060f0609081c0c0515010609061409033d060f0e04030815 66
    0x14000e1054880c03401c0144a00c2213034241002c10b901c03403154240c0301c590042004002140030703200c1c44821540080240d03a042980d07501e91524002e0090301d41301d085039002408120b0b0a400d482850000005400d0902500c1c0c2c8242c10180d1414101206030b080950014016085540c2440340400061001d980c0d50011240c0d20182840b1211207180180035815200c104040e41c40f5617000d403495a5403081c0c41d640b61a08010310071025002a8030110145134503038019554684e001e000300005400f601d41010001481d004c0018003103641e580c0103404941000a000703040244503124100745200d682032180d20340c1001e00d046c41c42c0c000340c80da452644443c00d100106086074052100307001c6030b0807680e0760740041041c5043c900d05c9101e04400e4541c1680190003041c07002e8642c10004a15006150820014001d400000e1044020b10f0b645100500c1e0b8846060000140d110501d80145c494034003991114509540e01400200c0050302c040545460100c440010340d8400c500012150f10900340b014900801c034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 782116888 1250 782115638 782115641
    0x18010501090803070c03021c022715060304020907180b1e0412240608010915060303090303050906070c03140d030b03030f031008010e03040e0601090506190309060f 72
    0xa006503400150309a1000070006000070a54a421790003840d0b80801602d164204022a81c0c00100310300380e142d990140c4030159032800400c00c09100700c244040310340c02034909030708800c0e04014122008141b0700e06c5842c10741d03103e010641390304c9a07055500b1459a1228901510450074807061a003202c040d4540109501c100d40010708a4180c1d6a00007452509446480f83c0700380c003440c06a8030701134001508000100d40e828030b482406012040c10300640b2045403050300700b81e400e250070403149607448151800801c5000071414810000d0306004000643c2103507001811003000303103c0641004408107090383d4aa0316841100c0c5203c2d031203144091a80e0340e80c07401c0c040003006001d140e04907006000744000160701030301a0205e2400e00070040c0d842c00696508024040e040a040d00e91103040c1c070600403402107000d20030100194050802540c8451400d40c950300341001c0146094100f05400b5400c0040352150001d40741404048980d02a210842c030380c08400034085030001404181c2043c18420746004603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 782118138 1250 782116888 782116891
    0xf090d0e0f1c0c0f14041a060417072c0403030209030114040201030e0c090a0e0109120c02090702031201211b080f0f0309010e1f17091c030c030b18 65
    0x503c240c241560781d583d01e4405960072a1098103242105100300f00203901d030540c00f2003040d10320180c000b00030310200c2c070105000d80c019801c40100210100d051111102c0100003070340c000c02c0d03144803802e200000b4101c030040c0c0740805039502601519540201e01051702a40544101d00c01c0500200b20070f0007010980c451304031090b80d00341d000c28030b000718840c80e400d000b08911a607908003401851303180c1c50b0290500d0090800d04c002c0080c9541c2e519110b0300260904c4881004000303a603071401c26140c114010006810030261280095500420400b45031250120580c0d046401d0100850084014030304683c03222103d40d0401080c40d441c901585014032078074910b130030603a9171030401c55102000c0b1104155542e0300c520754108195100f480801a80d61048030290b40c0700e240a404030826105034046020a10606200c11001c50110a0003280202a141d015640042d4000c0282a1851410034982c8990a8500904100f41d03c80b4003040342603000390080b180c035101c0030704908510070300d1700d2014010490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 782119388 1250 782118138 782118143
    0xf06070206010e01150906050a030204030c2312070506090a0b191101060e0130110102061b070f11060403060902040f021323040c0203030403080f090d0e0f1c 69
    0x40c00c0f0010811180c00e0002c158401425210400154140f80c0142e926030014074900e41096000c0001000049806070810f00420700505e0f0710b00d5002c0c2c1e0740301003c2030100040c0900e0103031700e10302507614030600c3c00560081280c0040e030740d280d0398500820214a6601441d08441c0c0340c40800512200790620590420384035034699503e100e060741d90811020b080c1c400a00c01e000100d0104c0300184909209540046409108058031031080070300402c8203c071000e0011003e0710f038000c03e507032881260b580500407aa800001c40030380e0003003400f21204580403400f8800e8054500180502001c0c00c01c24240051401e82074001d00c081d840c0c654916000d4064030272584200d018034140349101000280303030700a42d107a81c1c3d03651100a28660910142415030700d8604124800207090790b210f0206500c0f14070914250300110341c040e560728036240c140a00b2404001e80300d0404410750f0342c204600a0310119220001c13401c0e900d41841640480d0000038120015801c203103500200c11070202520902c40c000f0742c0030180c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 782120638 1250 782119388 782119409
    0x60406180801200d14010810050c040f060e030f0f0c0a0b0406090b0a020a0204141e0403021002280302030414030301051507080d050c0a11161401020f0607020601 71
    0xd032250001820b891034500d00490f003903501c600c12507010008030080d08100c90155030000700c0c00100c1c2c030a80911402a400314946800110f8010200c00380f6000e0154040b41000010317280c6490041c040c8115061f504c80c403020488035098411541d5010b2088040950b001030840380030b01105003c007501c8607a445072440c4500622400068003040b2134045c3c504076035075521100b031600c2c5003110784255540008007442c01c41c0203503411040140c0d9503204101c103451004c10020700300d10301000c1030026018031b40080518925064200000203900180700f07182410702220160300c5400c0d40c54101c814010f8000741000005ea426208001c0950540c0a1752043c2d0058a0310040e5448062809440c0c0c84207005058010f20350481d04252404404003c0840f984102459840c114080154108482080d581801c4580c80001d40452159100c000e00c110640c01e80050561049900818043300d0340501c620f101991008140c11220b038000d02c052170389040a05c4c281c03807003460b0101d0000d444903024010300c0c0c07481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 782121888 1250 782120638 782120687
    0x905070b0d15080c06031f08030717070f060209040b04020d020a0806090106050d05100902031807080313030b2e0504050c04060203120a060f0e0a060b1204060515060406 74
    0x3800b25201c41c800c6450400142010040c4001444095440140f034000700941002e150034150f901c00704024018a0480c0c00b840e1141110b1514810075080c503804115840d00a01040c03020070302014400d180103900c0000103030b03140c2c038031004200030700410320600354014030201710980c00b8400d5400402c9803a8059541c410117075200c208018901d1028015880003c0e0140448007820865074807581e04050103076061040290f903829210140c1c0d1040316a065015040d61960344440f604128100281c402480618100008604ca1014080740f51001070240c060b9040030800a090a40c0000c05006ca4084c1c078102d90084210000030541e950301c1007601651030800000c0d0618800c4042c4c0f01500c01c1c82d0b01451808440130b904144a507070242c403140f10503560345000280160817290000050068090004a61604400c08011104c1c0c5a2001045060800001c070000c941000030b01d40c000c4e40204002607d0711200d402c070300303102c3d08261005d0300160000b0f00444c00540005130704e06003c10a0040d0410f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 782123138 1250 782121888 782121911
    0x80402040e01060315050a020403060c021c0813030309060902060301060c050601050a05010807080601090b0406021e030403050c010f18180e0c01230c010906020901020d0212040501120905070b0d 85
    0xc881c021321002c3d01c0b8281d040c041d0718205480c1d130072051b0492a4010050308081e02e0b901c8050803a03070201c558201581c429000a1505003500c1d0341a4802400760030101038a03d40755000d0b0004481c3c0341402810943d0ba412403000f000181d500204004da00645020344940e1107860140c904036814000360358a106142c00058207103032403c0d2107420380d40184e40f400405e44421000343c41000018240380c0c1400303076002d8049901807203d4060401094954002c1800142045003403016900e076850300c00300c68004110900c0400c4001806500201081c038011b072900010550072201030000c05821110800c24080000b850081c00010650810404804106c0780803c058001c2d6104c6082d100c03170303000c142d600314102e80c1410300368203814042000303c2006103000c0100040c903003103a224400455860358045248051541c0c10000d002019603240020450b0480c0a40c4184050180b403141d181040919406208148601c0c0c02180d030596000040b00d07485504e8014210268000e1903810021500d000b604031070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 782124388 1250 782123138 782123141
    0x10c0c1401090b16080903150a1a030109050706180e07020714270c0c0a0503070b0c0403240b0301141b040b1603110a0b010e0c03070806010e040f0c080402040e01 71
    0x310681460300b00e24990013a50f41d00321241c0142551590500501070041c0920745071044482c49820002c0002481c200c0004001010004907004a070281e132401daa003a00107900060381c40182d0742c2c05c0c140145e500000380e16151040750030383c02c40807114100d0824800d0090b0002501e60a40b80e49440140941c480b18062195a07814000454541c2e0310200d00380c03001c01030f900d0b60781e0740148030000c02d9481d00b210500d4413454014240411581e5500009035070041c0250003051940203415030052904d0300b46103444506001c15207150003841100f100310301d21070024040d48a41020300e0040d0003400202908ae0060282c01000c4036140c078095000c000b4000c40701c0b040011202a43d000000150504201600c4104a014441411014008012450020910200406417a0a114030f03030f40d001941c10018000b642d2080640600b1040d1414410700c0405034205c071038680d010000b8038010b19180300c0d42d40024040c1007030a004002041c40c21103440d08aa07480320300d1030310881c000c0d20240050042d0007044ca0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 782125638 1250 782124388 782124397
    0xb0702150c09040f180b090c04050403080705090301090b13061a0120160b0a0e0306040b07030e1507050d060b13030206070c1e0303080f0609070c02010c0c1401090b 72
    0x2a10788008002c010300c640703007a6115085000e00e041002507225452071480c065030403403c1080d103c00145e041040301d4640200211104000306403011f00c000d06181c0d5016020382005040c44083c07000200d206140394030700358030806d8480d401181444090030902c18108000c024501c1c10303540c940c00c002c009502c40e8102d101e0090b00640c10b07076070800031103401109107a08001c1c94096882034000e10745088900400e407107034000542149003190341d84e030503294405004492104e0441e4001d4020300108004565203220040d07104046040100f041d220301400d240c00d05200840d141c00ca65042c5003480f0340c4a60240140c811001001c80810640383c0b10009100755010b00103100b4030203968600d0600050170100054802184104a07c00040c0d032540c85068800d1400742c070351103074036000704020002c1c10b61151055030040032104008070300342040400f007600d40c00010a00c0e420700c104003580d40110392080b003400303d0307480d0450036940c00d80ba2900c81007220003042c803c2290004d00800408074030701c80b50f039003140d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 782126888 1250 782125638 782125651
    0x806190e0c07080d02030a1422060b011106040506060f03072904091404020f22050c0f13050a0b04060203180a030b090c040e01021e0f04120b070215 65
    0x81141d0300c0c68803030000c40d8881e60040b03505150a00c0302c100610224006180108480304c0301041a160021112110391001818582c4546444c0300c189402c0110629561010390400700211362341000d40010785000048618030600c91103004100400d204002c54041c0c00380314100c0b2260302041800080550b20342407030080902108001c04410025015141c04a400141018409040c541e81c0d451020482e441448040180d4424100308021442c10380241d4520302c400700c4490384d490303030400d042400c80044225481c50086c4d507840804d22004448081d60084040c08429541d502d04044940e10013982034400c2e02c0c054218000041840081441558140e8189500440c2800c3c0d8840c100880c0c0c80a007500c16400035841c0d0004408908041401c0d441002510010038603c0e8254051100720b4031411603554440c0d1061010b029040803590484582d040c403180c0c0d2544074900c0802c5c03094988200e07805481c0c80301051600004110b910801144510742c1034095403101011001700c880c41d4502150b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 782128138 1250 782126888 782126909
    0xb0601030b0112050702010e0a0c081c0e040506040f15030c0503060903070303050c0d050f10170c040b2806140304020d0f03090807230a0602060430080619 68
    0x42c1c07541c0c2995031119900124501c0003017402305505240c1c5041440b103c800740d490040061051280b4401003100d100045100a800d05070b11550b500000c0400041c500001d200da82c590700854025070f1650404041c03200d600c00d00300600d140d0f41100000107484c0f88011180d0f000c8121000560349400f0402d1071081c618100074502e01130306543c0803402000c00800e00049403506103c2c031200e0545911400d80308580d8044480710701d05019950024440079540521108002c0ca8811a03041e00080742c0032660200a880c003050402030345000a030740030300000b19114a40b03450000b0503050103404500601315411038070b60200703140c1034940100440c071040f60060342140310041309000091084001d4201d070f82c0a4907289408680760035580b4180440da9210020802d0741c2203061140f110702c03000c800d0400e08111500c103041403914a0107522520010310142c080d90a4080004120126510144c8601c005040d46c0e020343e42d2000e0b010f0b100340803d8420601817864000319680141042d01d90205a502030f0b00e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 782129388 1250 782128138 782128157
    0x1b01050f0f040c08030a0f030b0927010f09030503061801050603040f050a020a080618031801110307060608031213030c0b1005090f0601080906010f140d1506030b0601030b01 76
    0x103401510709405082260345100556000a2210041c0064210aa01661101d01801d080400281903c0c60007000e9881501d030801489082c1240c4076003e155084840c00d11f608600c001c241544c010b104001c18800b080b4102840d0f0000c0661140007548501401c4900700440c0d555000d0030a4840d80c02d019154000742e04001250108002c03114000015100c1c0003101c40484096020030100c038008d6014203400d1f40500300f400801c1d082020701505e4414004011802c0000079211119004071540b02e031410703c14408055042010705000300c41c02150040c20a025136580c0d802c40d103a499004d2201c4041e50000507020420400381c184a15820540554650742c20748015145e20040040242070903a507a001f0500018164940c540c480740b19200ea10b00e0507840f131034000700140c447c103401010503c8681013400180b00d4204101d840406075805203c41c0e042d6080d40801007004407004d643c0c081d002003401050712003030a80b6a0000300950f40308140300c40a039141c113001901690312a1000d0350104040d40d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 782130638 1250 782129388 782129401
    0xe030f12070f173303011a0a031115030115020601090209030309090c1b0307150c020a080304030507060e010f0b1f0311090a0b0c06070c020d1407090509031b01050f 72
    0x3c44258016109010800c4103100c800a0b401c101205143c2c020201641c8001c0042586020301c204d0303412a603013200c00700100c040100050520103050000030004410309000010b181c50f0020800c0080c2f41c500003ca81d030756122540014004404982c00f0010b2065400111311240a4000d5480054000d1b00a40c03e100304282005100700004200f0340c1c007032a0070700c81010742000e80d5200b91142e042d030740091750707640c5110f090510040c01c0000c01c03c0c08090400401e024102c0d4000f8002082580101c082c684035142d234642101c643c41000d1016201034103154000c02d000c2c1042d4030601c541405c0520030003213134511009000b00445400c60721602c515074001c12003019400380c1c02c0100c00b0758001c15668a00b910590000e828585603030458040c2400108800401120030031016412100350706100a22000c1d6500040405445180003000c0b14200c100082c0070701820000080688034950082c4414a01f10b40303003942c0c80d00540036014052a6440d600c20200783c040c46214005c5081c407172410b60326690b52 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 782131888 1250 782130638 782130677
    0x102070f17091302280c050105100b12071b2004050705030105010302090d0b1509010905010f140402122a03061e12070b0d0b061603120e030f12070f 65
    0x17508103401e00c1c1800d98100402400c12080004917071964640602100c0c1e1400d1030340c04c44800510047c8110f1190030188902d4001c203040c0d03940c070001d015406410350380d800005c80b41007000116800f070300209007801e00c0420000d0441030a8a41c140411040d00f02916401c2009030b40003a110307400410740400051009500c030342c00411804002504a210b198042d640e58100d248007191418100c0c046000b00c1142c030720b420003002d4014220300c6400e11640d410031024040106081c81074a0099000c066070210719100c81d0181d036001c031030b021071600d031503d426201c4000ca0740440034544980485050390707045000404066a0080a003d413442149a111102d24081c81000b06480c035032103a8a287c100e007107528204944006001081625074030b968018010703005407034401c0b005920a52050059501562824044100d0150545041d640c91340c11204808000c0c060385252523594080014000407c8010310000c100044048040b64a41c1e650031800303c2d1003522003086103000400c522801800007007030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 782133138 1250 782131888 782131897
    0x70c0b2802010504121115250207030b0f0a0e03030a0b2121040e0c0d0609110d09021306031a1003030804031d0a1e06081915080102070f17091302 64
    0xe043c00c035515107e0f00201c030400343d44111541c001c000c2c2032203030703581000140315010710006c00c02c2c0c0020160141555541e8158034401014000000c90a400281c3c000e011600a820060032100940742ea03810309080e0321001d000240e61040c02855603050302004225113402000c4001c8a07000604003218100c000b01c044400d00c61080480f20f4010b000200390201265401d5010710320002a140d600c0c000c01a032001540e4856000c02d5595150105440d001000d010880c0c241034540c00002884650398070000354240c103000c5071090706e44d103028400300400c10090921f50340070906403616600365443c2c4514148880560000030000cc0c804408500042c2c010b051061400010600000b03a0310100c101044002e00685e2088072207021000e01c04401440d2002954050a0580342002281c5071008500c118507061040040015960b00c42040c0010703503101c1c480c030150003e800207566030161070a181d03030140613081d4180c0cbc14040194401c8050340000080300d544980141503040c1907001d5100e40f6001350032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 782134388 1250 782133138 782133167
    0xf0f040b03010e0f0706080a1505190e010f051206070c03050d230a051005010801150203040312050c0601090b010c060c0201141f0e06030a08070c0b280201050412 71
    0x100c0d8460200401020721060701351200d0080144840751070900d00810244014210015603880d00c0103c1541c2070f0342e0305140d029690140e844220030b4449412080d50801c044d40311080e1400c4c140300204030102c034081c0e58003c880b0f08403001c0e00150000c0003003a494032010b07034808001ca07030001c5007000000c1c0207002808880300c0302d90002501101c00440e13001101c00ba84400d04070b940c59034081001110081c46000d410160f00500661840d041c8800a02003440601031603a401c100c0004100d15984200220f6001d1580041c0e840c6440c4a42c00c0b010b002600581599035150240f00c0021034102503e100f80b8071391810580d1400f000c41e0154495074028201c00f07008c00215500d904c0c8040c03a000e011682c4501a0540ca20002404804008481001555a003018840b00c0701101400819500001c00241c1c2d070b50400c071402d075200443d14010441e0512a0b201d140142c0012800b603c40b0200325000c4200d20b000b01011004041d5141412422168221001000c2161007003e0a8080d4851240e614500d00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 782135638 1250 782134388 782134391
    0x61206060c010f02071709150309010609111e1201030f1e050610090b01140a020f0a151401050d0b07230d06080712030e06090a06020c0901050f0f040b0301 68
    0x3040d04125030b003500c0c1c83c040d40c5407056400055107001c01140314041c124451030001c01c241030070700000006401c54074400e003400c040c25004c008148060350a500038002841c01441c100031b0449036220141c1141c2199800100c40c0031015204402010000c0c1100d0509480796038561090382940e50303200c074507050042c040d191014401d464815018020318030924050141000740040d00d4130b14080c2803500c4803500000481400d0840f109003d236003054241f00452103804055840341401c42003246000d846240048140c85103140b188180400642a502002581da00c00d0120400060260038030702e40a00c2450b4021044200c58004100c2214119401486078907140803440390004640700380020345180500700d0a000204261524075900c03410004103015009130010360b140190142e000c10421201805000b20050251410b98a600031030f88460b600408007880b060326904000d54a40c041b18a0600842509002041c0b520702192070042e004001005582d00102450902020f041d8425801d60150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 782136888 1250 782135638 782135647
    0x1401080c1c0212072007050d0f050a06050705030f161d0f04020d0e010b10200a0506070903061a03121c0f090b0a0e060a0e100c110c03030906120606 65
    0x70742000029074040c1a5541e20b1100701840c030f0400c441d4110203100d501541751b2041c88204035940710741c0e019503a140e8100004081110481c03c1142c20441720000040200749000100900c460b00040a540110760780860180340b40d8451113160040c0036002d412401041c00200c1e11841c0311400c0703074007014610000e01000c03085031407040403905076000b20850742401516441c01140501c000d20a0400000048a02d442c5280903000003400c5c1d42c005500300c04501d450800105103503d003c100b401d0103154081304440152418110040c4045110301003111264240560781090306160640b2008215004014001142349150003101355880002400701d100d03c21005c0010a2101e84552041c40341200b00111b031030042c6240c03030b070b200701c2008105a102a103003103195400b201d4001a800d034041a003050009402140c990098030744070103102407510342c5042410f42c5a016a024450324440242c4038225802503420302d08040e101d028441c15150449824444c103904407a8a01b800c5401420190556151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 782138138 1250 782136888 782136907
    0xa0b092a0603180d050a260f1b0c010504030f0c030e010f0207081009031b080f070c0506070f0b0106111203220c0e010e15280f1401080c1c02 62
    0x910545a070704d40c01180c800f03d480016a03403c55082c40802180c400d01d07005102c0030011750751840001400040c01104600c0024001040501c144503041240512098032170003441c4000380642003c80e0b0481c00640440e501e41c0c0e000380a91176030b02c036403a03064403400420300d10303080110741201080c989002144110000000c1003e020f00041c444811403a0700416040d01c142005403d40000481400c00410050000c40214041e14280c50842c203c00e03841c250b680300e09007000901c1d8134041d00072035403111000034000c08100e502076035414020300c280310804590b80e031781c002602c12280e024041031158011060f1008105a61402140e1143c0c10582c443d0f4400100b2010303501c20011420100d50151200406102d4200840710142c0144450444181a03141c0390308655500001310b80c6450040000340001e4500300680d800c402410540d101544410383eaa580048625040c030344140d480c8035025840c1c1d10100d500c1024554170400d281e14000e0310b0894200030003411350301da07141c6040b543d075802e0140499 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 782139388 1250 782138138 782138143
    0x1091512201903121713080712120b01020102030c220b040609241e020c1e0a0b070308011e0302060301060504240e010302090f030a0b092a060318 64
    0x10251110100321260307007146420303241131945040c00b406000c1d9462010100800408540e0b91000c0700050030099090649020f0201d4004c100000700000c60070792a016000380d22441c410b1546042d40024801060144010780c00c0303100607031700c10900d00010003105c03880c8505450940c26a101102c90707281c001e40d440c00342441542198012100242c0001010040204845003000d200400f6502050010300c40100282804045442040c59000c64046202d40745000f406844854174000e0700045850a036606001d4864542d035000d00d2007002c8030b440c082240301c4e00405450007580d154491041ca64200305138501e035a1a202d100c0c013600240000d004c80182c407000c0256001b481540c076100c1e00d580c10101c10310701d1008140300802c022036854030040009984110582d01050003820016602c0001e5801304a409451003440c5405200303000d4180b0400c43c00c84800392088005030280c4680424078002200d01d03400007030341011184040c00390398000b1301e8800001c6401c1400c11360040001004200000e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 782140638 1250 782139388 782139409
    0x80301060503040b070807020d110118060606020d05040b040b070c030f0302160503060615090d1b0305010b12030f0d0902090403090e01081f0515090901050109151220 73
    0x45002c0140000c1058822400b80c010f0f0316401d0001d0710340b802c03110080d9a0800c410210382080003c07401032008000070341c400e1800724040c00c00b01d0041211400c06502070070781c3d4411000180310307807540360a07054400d0003514251185417040078a000e103428002101ca41108000303440c00080b512000000481a821016141d4425005802c0103214101d940180100310ba1169000390420020442240c0e10020000e00d0242000c2c3c140351205074a5000c190a105040d500500b400326000c1e2400da40c51079030700c0764001c0b2480703640284641e4410005101e4040200a00106a03030700170710404c0d89508000d07001d4104d0034a880d000088070803141d00003907581001610150041500071000f40034801c070210700340e4094003965008100003200365442e4101c0d1014017030b1903d18a5901d002203081408200d440608041000302007482e1400c0080b495030003401d0a100f10002c0e03e00c1c00000d2000d001d0400080000c0f100100c181b40710025441e00c42485400744444140364064410030350410039500d60382c440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 782141888 1250 782140638 782140649
    0xf03040b06100507120324090e010612080a08060609061801020c0909071e0801060602030a030509010b0922080f0909100e0c0d110318190b0a18080301 66
    0x1100309040c80d90600c044000700503141c0d802c01c00c042280c0340c045107840e48440341506503446d0010707081d0446d00426001c000f030b0707203020401d41018150002e0134800c00d0b000211058182c4000b00302e6903a0741c1d50103e12980745c0d1030313006018410501559142c0c1c0c0c010030b64103a12843c09000c045c5004041d5002500e6035100304108110100043c039061000d59040004c0110b03424103803029183d42c00d15800507907640100e80b140754207507604400080e0b820540000401d0061910740d000b40009034407844080e40380e03040303520540006864080001c84992050280c07182d00b90028041d12404e8448900302d000038501c001080070076100e101450000940150010302c1521800d14299841d14488003c0010141e005014070000c0d0000307103400d119074141c0725149038100902c43c1c180c44e9614084801321002d0041e108015444190101c10040d1101458130701c0070301210100c0a4540e00000c415401000754115003014100d0b507100030000714020100e51110100341c501d002c40e030007034180d80c0d0744040e190360098201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 782143138 1250 782141888 782141903
    0x10c03090b070807110906060409090201020a05010e0d080906190c05190e1c0c0905060d0503040306090308010b03160e030c06070501091115030403120e150417040819080f0304 77
    0x207a01880040000140d1054003241c90340601e06000c7c0000d101c4e400f0302c1c010b0220b040e42d141900c07411680200113424016501c03000030300644144101c02519140922003100114581c0380014402c4000402d85501c0303918000050b5108010000c503001c001c1c5540c54031b003003e01204020030800010420b05e400c2001841d070f954000a5503110060120640c10000c01445c4d03402c2c41c01e803403c0040e07900b840f10829903421000c00100c40c0d40d024006801e899041e000541540030010340402802440d802000845020352501c02d50303640c1e10155840944000c4070210026580805006006403145007090980e0100808803400c52409a0001d41164031800d400c0702c1c142e5403050f18500f0025141191009820116162904000803808949061100070401020005410904a090f020940c407c00380400c1d801304540343d00386001407400100c0c405503003c0c3d8080110419142e500001403045400b03030b651580251011340484200c101e20b030f8000b03540c22291401c0038010140002c85d0305000e14801c0707014000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 782144388 1250 782143138 782143147
    0xc030503100e040b092109091f092a020307120e0a14030d0201090210230705101410030f0c080d020322050f01050d0f0507020c011701060e010c03090b0708 68
    0x398900703200911184521600c075010860009014001e03030712080340580351030580327540d101d1151410541800c6a02c09001511381c000c610720303020768400403e580c030480d043d09031102c503110002a83c00b0740074246401a481004038400003180c80c40044a1001e950400b141c0980304040012010750a030740205000000c268001415031030100b00c600301d440014002084031501b20b8000ca20031600745414030050060700040444a8400c0360b8820014026006000740c4a41051074413039203420319080010105400c245441d48004c076810011070080b00c2c9406994030781455603072140c8130304d60030000036100301c81c0414000440c0103083c015118040b541b94061540c0303640801649140307410014440c078079010f4180080c005d0717071102881c001844000b404d19070b41380d83c1010161805400c01400640d2014148824020320720780000d0201c0800e28241c03035090745980c2c240c1011308c407000240b00fa940020085010402c040d4004c21101c050b0a01a107003041245032030741c0501c841c941c030404c1e04a848640c0043c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 782145638 1250 782144388 782144401
    0xb10030b0123071b0504151d090c0114090409060e1203161d0d0b0109061d0403050a020703050a030f0f05090a03060e0127120c030c030503100e040b 65
    0x302c1100744003611000740d110100203202928950003003500c018043c1d520310704598a080300d0280ca903002044000d01c18014150074203841416100240f06800701c08014400c94512402160708480c40780c4851710084c8581000c0400456107048400e81074207540d1020040c0170300544840c010031500501071030000c204510310790030080c5030009000001445090610900c95030422050a440e05070403d4078089036060500c0d20700c51441c1d070080481551110078400302c2c0c0204401002e2180c100c850304401000039941d40c264010303c03081090b5481000c1d1068100080000f4010070240824114510481354000d803aa96200d00c0c0c9002c1d00e0050300415540d030a4600d01c140e10070791901c0c10344100e2410074107000780b800100d1210a190300004042c9034544991601e0000700754042450700c60761840500c41c810040c80e195036414020001542c404034403120b81030034240a0b108800069a1582d6810000d84032910b080741d80750400307085000ca07680c12900006508200100c1070340100d020300828041e608108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 782146888 1250 782145638 782145647
    0xc051c0923040c030603062906071a0c040503011a040612030219030c02100210050a0209030d0e04021c020309010b010201050c0301030308061903060e060f010f0e0c04080a240b1f030b10030b01 84
    0x7a049248655010040813000802180352007000101e6800420b9033a04c4204651038103000d1038010f9505986003160511448541000381003501200380e80804c01c1d00e4881c10000b003942c8405034080d001d0792020603142180382004e1002c0ba2114020310789107070407a07402d81c0050702d00c4171801c0c0c1140060703021501d20141c110807072080315000400300302c0861402ca00403010030780364074084116030140100107540c9a0152210740444a842d002101c0366081100310001400083d00161820710466180000c622415401441820700942204503201d055078a10343e001c0b41e1030b000007480c1c113402c140110361125400d01d40d40d03507540242d4414400031801c4496000d4180c600740d00140881c50141d80310380104003802c1d04040903c1034800200e809110f070350300c00e8503184d181d00c1158071448091080760700c1802809804104070104001001003000840070301d0040c0010349426140583d4040b401201c501420320f055440350354019030a040120f681506000041c00d081000c02c091000310341c42ea01c1d0f214013583d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 782148138 1250 782146888 782146961
    0x1e08010b0f0c10060b0418021314010201090b090109140703110d05070902040b2701050406030c030b0907050406020706020708070b0a1224090203010e060405070c051c0923040c03060306 81
    0xa201714142703180c040c0d40c00391444891042035a00d00104484214a0b4400e4110b00170040d001110500307907041914a02d070080100403802d40d510802d0851800c1c7c00000031403400110f9800c0085480c40c200320724104868079860110488452140f50800140380303440d80054001000c911440310b44502c0d10700c8103960071100d21020401e08007d40c000d400f20390383e0403200352002d5484610b0300148481440030154014423000c051039503c11002c1d0304000800c1da1100050060b2282d590030382e949541d885905070307507a801030f0090641c1904403100900461a03001c0180883e440c540c64550f030450007402090f0103c589001244600c03e12902003401d4036202d00d091000103000a6001714515858500074165030708025000c01e22070707910f600104003510300c2074042c0325a064101c03051f15034100f11444c800004040c003501ea0408035400000000d428404d0b03009400b49a522140382a80da920b13107000300b000404030f201c0c00c1000c3c1030395404c0110110b015841640d0301100594000902030f65260a14180a2403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 782149388 1250 782148138 782148179
    0x50105070201120f06050303030a1d06150d020120060406060501090807091107080a080402011713060e01060b1303050c04090f14070e071e08010b0f0c10060b04 70
    0x282081804010b0b64041c0c1c007280107841e44a8002844805140001d01904196000039450b00c008800d00c03030700025650014400070405514030020b080d01c21461506c502c8100ca42d002c1000c3e004205071420709240c4c1e5100c030180d205162400c240480186019041280d080c0030304441c0c0d01c200200402c0040b0392050101800003401d01549840c071306041c440e6144881c2c001c1d0656140c503001f206055440c0c420542d07400561101b40140c03900d10360b00c03008100002c1181c09074001040d107a00b038800b010481514501407500c1c518a0a003c0b4690303254900604480403001c00f41c0d660710701c0005501e0000d10050604a00764103110600c0c103165041480c500449144114415494407540f0800a00d01020302030619901a1111045110101e84542025038551000701da980803401008002c036446103660204e05d01103003890488070554442140c898034240141907411a08012003034656641c007010300030240301c4a080318403e80310a8080e0381178078941d0388038090030000820180001680100c00d4405d412 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 782150638 1250 782149388 782149397
    0x31e050711011b0311040812070b0a050f1f09110409060902030f0115050d020a111603110d020d02030f030a08011202030709050a0b092701021603032c060708010501 72
    0x1144458000180161840f80500b03042c0c0e6688001c072000784440607038000344029815582d501241e80402c45890340101001c440c80840000001d03120341da10710a03c0d01071485101c071304006586d2042220340e902501160520000000240080c0e00c459a008010b45000c40f80400c5481d1803070300c000402586d505800503840d044c014401c2260008501440038111032480c03180344240b41198000f982c40c0e1050b0100c01c12058000140d03c1c000642202c56014111821812101ca01d4005688809405590b0000800300c400b40d03101410ba92406808000c00c442c0010501c0411b8000796000a04d0104191038080c900c0e00013080c1c9100481d00070302c80b1401442135185050207003246a000a4a414060082040203030740c40020444400c070710350025090010103041c00b46d0909065496801c03420005007900d001052206030154040c50600075102d00c8891600c0c902034039046650b043c0d02910403013664244801c818401100004599800c40c80320010100203840c142c14200802007076184140c00260520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 782151888 1250 782150638 782150651
    0x10b040e0303060915061207050a0e0607030207030204020d06080a1103070e0906040321050a0902040b191517040c050918060f1503151009141303031e05071101 70
    0x15103420181c1c81e48240420701e4817001d035074241c000034028015000c43c181e08040031020131407006d070018010004003007140c03245c804014025081040340c0c13007000c1c070080042e00585c00400040c1415005400503001c0100c001c01d8890701c4003006460700c4224001510100203494440e90b080c2428840c0344050001030003c0c0e2410300d03040080a44e11007001e000101044210300cbd4401d00b0b1102007003210300b0f24114800502850070440000c1000e0101d01606920551410441b12950f20b07010310009031129500b204281020307c0c001400e03000020705060542400710401070f56951000c840c0d042881244181d21a41510382010701344501460300a00a4007440303880c210100c03070b0b02d00000c0c1550f44040364010a0a05950310b04003a03100d0030020301d10a03090301c10201c91039008490100024800c02d0350201d900003407507840104a090303405001c50111014505404603540b00716141840f0300044c041c1c1004620781c86000320203100d818a0b070f11280d0400350f48a0601100c26800942805a82104002030019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 782153138 1250 782151888 782151901
    0x70b0d151a1b010207200901060203030702101a06040e010806010503011a0d11060a030c030513110d050307200310110a0f2c0306090d05040b161202010b040e0303 71
    0x4920640c0c0004100b803119207810924040d094046414155000000ca01c00d00c180c0c00e0b1850f400b80c01521030900c600e03030b0580042525880041900e106502d41d81c002c0ca12858010714100c01001c00b840380c01d03034550460091029940b5403400800051183e802c020b207880d072501c032100e418150123030000d81c401d904000040034050145190842c0000045640c0c3c0001405032410801c14980c0101181d08050040303201c8001d203405500005110050f80c03010f10143d56010110181441c038554028007071400303003800b030502c1d0902518886036030b032007031048a2a09000362103000030f011004000c503070502103002c6450f80c0da040a01400075518810501072040c001607584858481c0291402c5030100400b041e10150168450300a0b040c103206503071110301440c1d461180174941241521041c5000b481600c000c908450030014000442c145190381e22403e040c203102810740154040004d00720001d110501c0d01012a410801481300c542998000140c414241d40070f0000307598600040a030182c2050080104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 782154388 1250 782153138 782153189
    0x5060702030c12071502091915110109122001090c0321170601030609020f13080a0c090b040609180620120c1b0106031b030809090405070b0d15 63
    0x100c194444800340e01d64800d40003086156101103491400000c01c00e100241c240d516427803295200d00e90342c2c4c0d040349904049030428244e51260700001c0110744003013003584040b445032015000d0342d13206c541e48845a5055040d0507094030035801d4251000c05804008204206002c0030900c070b00e0240c0780104604100d99070340039050b41048400810300141c0e031000034041c1ea1195005a001c1c195001c1c045403034400302016510f02da00f10300309020313080060305800304641500080f6040fa107030b8402910b01240b0700f4480c850010301502ca52075a0011303191600418a6806030091290b400a9840b200881c150581440c80c00e640040340812809079071840d55400c455003e00844800c00300821055104e520740f1050300c03400f445182d15520b80c0c1403490900140040043d0002d00459002d8882085a4504240303e6458240c0f6488001c0843d5010012180300f41050408550310138001d2040e910044d5482d03546c0c00f86944880f103440c0e00c480c0d80754140452020403d0411300a400c00100350410200f517040b00d040d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 782155638 1250 782154388 782154413
    0xc1b060a05010f0e1308090301060e1b0c030a0c0f020d12030605120d1404120b0106020d030c0c0f020a08031804060b0705070b03130204091a15010906180305060702030c1207 76
    0x601d00c040105c03205083c01203500c1101c40150025000300121551100300001d0440d0903160b14442c5100304c44503901a45104090343c92a60004000e1803070003080b804155200c10300c104d021582e00030b052825a0140c0c0c1e07402604554180500410080c10f4480a4000c0c105e65094100790b00c641c61004401c209420001070180400d003890600708020400200402c0c658021644003038050906860050100b02c424000d081c122065134084414201034100c068054860b4054400c0c0000c2c1c0d04003100c004100315580e41c0c00c0c2540060302000703603581c441c42d280342581d210101d92442c0c20304642c2d180c0920b007094451070f401026046030365401c00c0300b82da4032681c0f900060312032899080ba010000c0b41c01c1c4e0034221a404141a4010300402c0201450f02c1d018000e842e20010030b4040942440010703030103803120402107030421016580c9500c9242008000e417011948500144081d1090903c0800081c10800425000301c4e200e400541d256500c0b6074441e03250400614105003140c02c1072000000203080b0030141d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 782156888 1250 782155638 782155651
    0x1b0e101404170304081b0102070e0112111f08160c050303040b1b0a0c0c210b091006080105061023030c0c16030b0a09110402030c1b060a05010f0e 64
    0xc2560008480400e45076000e50b4024285d00c1c004c94a20100d0342880340c25104040b07100380c00f41c5c1d024558420b00d0040c1684244900d02051241d5400301e400210115a4580d4403a402040e1980c43c0113840079034814252a10b00d80c1d800b150540301401801e40700b1910880140341c03940f801540c4240150f5070340c0e8407400041c10041c40006a8004203001d0094036003d00120488441d074540c80d0f131656280200020721040050307814440400303001c205440501d110b038444402041c41780c22020155030f00e110560400421a21540c040d120400303a00c0d8500380101b400810702000045a541082e00c200301e032600550003e14240710604e0f10b2180744030301d00d41b02041414160881d060b16584c9504002c42c252180002d80d4105000c6e034600c4d0221303402c80346010415a4020b001c03100c04c030f42c0c8040c115400c540d01c4100c042d01100102010004600d090b400443d402100225024202284000050011180c203012215150880303400c000841c1c15602c00c031401843c485200b0079600e864141c40000c4500050700c00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 782158138 1250 782156888 782156909
    0xe07110601150215071110020307030c050306010c0f020f04140405070b1207111507170c04061d04090804030807031409210f03040b0403050c040b0102070501080a1b0e101404 76
    0x920186c0550b4960050f07800c04410394045541d2202c11400a50040300e007000460f1a00b2148050644207030156031040710180c407074084894054171403580000500404a90021b4400251a12038a540c011b420036000d44401c0640c003401e0502c0e105040c0901c54201c031024003070620641a4416125028980203140c07402c28900c2d9104000c102800d0400d407808402160954038140401d8660001100001980610844031030780c03100d400d804c1082c822440782e5000919050143c031084c482e100c101c4004140e00620008286105035a810019045507109442817900400d0358400e05400c80c01c1c0b00c01c100342c0290882e2814410341c002801c140b0100890b000003071080c45286128070000c1203102229903999048070703102c03a500c0c1c0b40c41c2c01541c01408102e0365030103080c0786200141498000d680385400141c000e810310710305103c011a1090380007031030201c529844100d101000804101581c141c010340d503503210421446074040c8003085141c056203d0412403814545401c00c640e10381910160344000e0360 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 782159388 1250 782158138 782158141
    0x5100504260a0c0501080615030a1521020907030504050a0602070206090a080105060f1206150105070b1003140c01080a020a1701120b160207050d08040e07110601150215 74
    0xd4404244000c0c10195041d407007442c8205090000c41420380c4200d441c00d03612032003199104d03001d020f40a40b4042c1c0f42100107209001207410324480e070304401c040e0314002c41a031243c00d9031112003503005136071170101d44001034910404d10190b040001009a01102d00e050502003804d2599600741d554105480287c00c11b80d000c1020400c41d505c000031170b030b04d2031401004003000c2c0340c0702d244c064020102564814803d0360000c281d4184c034140350256165a1a04001415413aa41d03c812030311080300c010b50b41410490100400800907542c0c6050301e01980e800c0140b0304005003146030500c43d103503c1c2ca4800500360b01c00c2107000f42c240c0e84207242c40e5100186032000342e25840c0c40642903032269107410408940b042884008a0303584801301c8280c42250103485011510340b10549848610002d40f04c5180043e04240028000f03030410088901c7d01c00d120303802e84c619040e9205043c2100b244265500c50001c2e00c00a2100d06040303040105e2809004904c4819502d902d41440295030b66644e041d090f080d8502010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 782160638 1250 782159388 782159429
    0x3080a0b06030f0f0105030a050c040903020703080d1a060c19060204050d110315041205090105040e0f090f010b01020a020121090803071803020a0b07060f0c0c050705100504 76
    0x2004869034010280090b62079081240d4403100443e400c4640d00590b680103000041d1600d000140035440301d401101500c4e02c0b400c84400d2002178a041c16054083d0f00c50082d000000840d0000200b802c541d509200060000201400d0043c542c3c40401051240c9020f00184622400102d0710110200c000220340c14011001c0c03800d030020340030320fa101076800021400d0b41030a2007074505040000010450950320442c92022000107403001c00d0745c010f001d59415024185200f030241d070040c013810005041050030030b81d45a181c80000d440c12100442c00d10300c0c00040c0b01d9170030340421a4041070b1003480001e01c00d007000200000e561340c0201001a040080180c0154441140079035110001c0b00d0f04802440541c17202e080c042155030050b95000001458402c0e00c08458101c4001042606c1e8014008004240f070103c0800060b000101c0a42d0000c0c1d41e5458081c0004031417252507101120b07030702c0380810481c503070510342d08000890b0702c50ba00402035200d00e40d01245d40141100c0564036030091082c0302a5090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 782161888 1250 782160638 782160641
    0x90612081b01060b0c0d030609060b03070537021005010311060a03020c15180c09420102010f02040e070c260304020a050f0102060402100c021302030403180305070303080a 75
    0x351300104402d040001d1442d41c00802051b0ba07480b80d240742c1c03010b118242d9200c0c2240216051031045d1006200f00b440802c0c6201d120380d0003061201410304c080030400e501302c0001110380000c040000c0118952614040003580c0500004980500f80e034002c02c020361650321500c074a1607113042e00d03500c141800200060802d000380e042c0c8421424039001c58000d1990b0f00d840a081c43e000f9100482050780041c65644071060004540b4004100500744500725100c0400c3c2c1c40c41c85002c103000441007034010312001d03031450000c0e0f00f010fa1710302195100d140d5048000c002900b1100304038548548140104014800f81104422442e0400c030b0318942806621040e041040300702c00082060304c200380421300b1704500e0303420b0180554050f0740219000004299038030308001003070070701f00c80c400c2c0541c21281c0002d025207890003401885040d141081100314402d03a001403280038900079110061603000c401c1c4130515500070301d046982c3c6100700d5000c0ca440d065031555956401c40c1e1000a00300643c0d0070008003000c1d0316 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 782163138 1250 782161888 782161901
    0x5090904030e130207050c1c150c12020a02060f06010c0f0b04050319030207020f0d1a25020f06010f12080d150b27010c0f1103060907090612081b01 65
    0x40441c02c40d240d400500d08162a101011f11161080c80003402c2618030500d0700c1280c4c002c080d88080c01d401e84c0d120640040c000382100159400030300240c0b0003408400701d01d41c0001e10b24503003254090103103072a0802c020360054001500e128100400384c0000000920034a004841040d000380403880c1c6031b0342d5407601702c3c030398420f05c00c031201c10700c0a1900d01c11440b60181c0103849076510032114541c3c903032000300a0040c0c14207408009408164072000c546164852141501e80000e5600700204002031400040c1c500c1920309042c10740164051420180920801d2002e075024003041e1a141c0a21403401075800707078141002c080a400b4100000e01c01e84103018680c050f5100c07540000b04081d100b90390700061a01504421500c00c00080c1001c02c00c248020070160302000904d0586550800c01400d032186246408240b0f800c60300c00c40140708100483d68104441881801d111004040c02801e0288540075500103074801e8030058101203e4800140c05041030750380e585882c8245916840d200388842d0b015250 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 782164388 1250 782163138 782163169
    0x3101703160f140f0705060a1b02010201061703120f04080715021204030e130501150e0612040b011505030f16180902040f0b030907060c0312020d0f050705090904030e 73
    0x6281c1a41c1403010b5000c1070844a55424000345c0b070b401691078050107040c2c1309402c120740020b6900c010a071520405441e100c550310b801032000040254840321000c40c2e4401d01d08510f5900e40c0003050402d194500c3c4102076500c90880c815030a082c0c00c0c156150000d40c00344400007004048100e440b061841034980c103407508000485c0c1da030456402c0908028100400021042d030044468040c0c0341d040380d00c03601419040720000c45e103412103004002001c4501034008038005501c803030100482ca05900070341c915240102d001d29200149540741943c4052240703901c82000d02803000610800503070307281440801d0750040c00c005001d001c3c60a403c0045501039242c0f60040011009520081482c0a00e070340a401030380c50301c10074107007480d4484007454140d000446004060707030b0000b1010320032140309144000c1014400c0c00c3c41e082580300c840300070382a60000400381000c0c41d60b9050140c041c0800340140b82c0c101076a400e02d117207404104408030711810002080075051000c200e44640c059240c020702080d0002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 782165638 1250 782164388 782164403
    0x80a030c050c0d1e03140114031501090203092a0609040615030b0405100e012c0a0213090204050f0409032a120e060315011206080303101703160f 64
    0x41c1c10292080010001d8036401d907104d000ea04104c50700034424845050408070100155a00e01095032180a204030340c06a0140200300031265040704444e00e040c041d14200d100503840385088605c1e1803500c1c3c803003078024101205000145240480d007107a030703107100c0c40d0175515103680da040c04003c40c0107413016074001ca92440d0940700d1303031f040d0350344c0340d4400000407200312024081c0d5218218204c001504030f001d00401204104d0041001c46440300b400524146203400c141000841144000f191030400c5034100c4001d900013500c00b00382d01c20403140c00050702c1051011410b241c02c04011135100c804804000c0d00890340c4489800a04d4040d40c03421800901d4001c16441015400450389119014a40115072080d015540ac40409010b98800020b0520103000c0608680c0da02d1007038108100c1408180d030506c940112144269002406008050040100196078a003441501c02128070340c150700c000100200c00000a440900101c01c0740e00c01100c0180880403c2c041c0c0c10400c42d16100c10b08000d1040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 782166888 1250 782165638 782165653
    0x11090709180213121a0c0309070501050c0a0b0c0a0908030a05070f020f03161d09061f05090103060c08070f050418060504060e16020f0303010905090f0f0105150409080a030c050c 78
    0x118007180940d01078032406a820b581d1103080c0c50351141c7c081138584506940120000707005a51055001d091048007450454000b01000c8d1150360b075102c000e0302d851a82e88030000d54a445281c02006010082040e080290320345005036100034041c3c0140c1100034406110b031880d10302550b82d801d44107003c2d146c00400380c854034000c94804107400415071003084031200300300d000354443d40901d0b100180705000f00c1003d0315043c0c1e54019100d202c190703619007407000108034a00100c2d141d104c0410050203544901800035a4488140024241000042c00c1401b0002402614142540d0210a590071980b00079030500c9003200e030a61400c05020306d0b030480d40d00039150050000e5110ba0b220b40e018000c40e42418064025170036124100d07110090503000c039030503030f100300010041085035620951740030040a00380c505942007017001d2030400c40302d1030020809a44513020b000c4480a0b0603140c100c1a03404460800031a1219030744c00b0240d000b810100030901da65038010440103070042c01184d0010410300c042d20107a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 782168138 1250 782166888 782166893
    0xf05010e01021902010e0d05090612090619090c09050c0d1e0c020303150d030309140f0705120703060b0102010b061306020607031419020d091109070918021312 70
    0xd4003c5184000e07180c00c12405214403074010f2103003590700a24500545806882e2480545069104c40030a5401ca0400c10800034220000307520b05004501e03980140c0130f00d0400202002c0f07210304144a50314400e18109000b40000e010700f10781000c5400e2101c012841d69600010242a8011090f00042d140d00f04400703850000d80c40200d2010074261001c042008441e014022656400101c55201d03216108502e41a41d038030307205d1a01301550340300380703808524140d00359038050040c002d410728143e0a901c0103078919401d100521200e80941411780b181442c902d00c800c011940d8454920020381240da43c0e020f40d0400d64030179000f10030010401340c1340039614500160310001f084031921404c1d0040c0554000300340401d10a0051710000001c40342e2459441d1034104011288041c1d01da619080d11341e08120a524101d1a0300521a48074000c50110120400d940240444064010101c40c10403044441c00d112906c040c00003030303580a82c148001603c42d02840002c2404201c5504200030300754414080c0e208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 782169388 1250 782168138 782168141
    0x7090807031112192d06020702040507030b010e090a11030403020709110315100c0b1f1d043306091a1507030903020d2306070c020603040f05010e01 65
    0x760781d8142c80e0f0030f07541101c0104654035000c0d0f61041e5101801ca0302e60000114001e001e2000022100c90211a03514030801404000c0f1440c45d20100c1e00140c0224070b1b2401c0d0328140c485d00703034450503904051100b100000002840c0030030060981c0d100d50a0440800d040ca0b080c0c0e0702c203900c070000d17074540c0590b64101410040d607161042e104090015040c030024004074003e01094078001c80843e54042c00300c1d1003800030070654500fa0002401006960601030002c0b501c4001c0b00ca010302141d803806010507010b280e600103003d245400602e030082c0c3c0030303621b50150400c0094190703101d03401644200d1248004031b684400c0c000049085035142d0180740d08801d0364100c580c005002c440c100401082484244510704140c400041c61495001404404183c15242c4aa005000c034912a00c1c00e41d882603280d5000802d41c3c01d4452040d0760254288103072243c1c0c42c0c64003e02d400781110f01801083c142c070702488001e04001d4040002800741d6400b00c08241000300382c0b00001c00d03c03540038009104051100c0302c11070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 782170638 1250 782169388 782169413
    0x131109040305031609120b04140a08090301060f0509011a0c0d030b0a05180f180f011b110706050a20010506030c011103040506070c0e0c07020901051509090709080703 73
    0x131031455045403218402e402005c08004441d94503180d0300d18000d042d1160b40340b0400003030058800500c050b044c200480c6046c0328401280b1f12a0010750b403183c401c0400c0c107003102c8081d0412010452038150500c42130f07444204a50440d2800c1c44071300c10581c09a64021021302605583e60134603c070341418500f00c1a01a0072000400505403003507140e659503a01004001d600498401020208030302c0400c1e295549242c0159004800b99410500d81c030081a42c5442c00c900401d500c0900d0351f43d0205480d884004031008201c1000307910700010ba0308403089845484601505c600e01c1408030020361104018001e40c440e44d038212aa81200100120780072007a40a020304644551188c003e40645002079070080911080b444040001035081909000520a080c1d0240c41c065a05c0c40c01c010002401e00601681c0b68030a120030b03a0301c2ca840301480c1c414801c1001042e00500d114000e69030149403100b10050a807a008030086034402d021392505030058920343c001c0e03000250b06000305003010051140894400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 782171888 1250 782170638 782170651
    0x110301060809150f04140708030d060306050106090503280c090510081209120705190e0631090605010b040e180a0f03021c030f0b03060f13110904030503 67
    0x955603124034804810300f0a5040790b1450728103118401140206441080343c11105480c81c04440c2c0309520355280b00c0c9960005a21404078035142c3c1e00a20030070545000711742c01008541011806075041c00c00190726905800002d8004e400035507100d907a4154091094a00180c20800d80c0592a4960a814014203002c07110000514242c000001d96003000203a514040e4600392202810440640c2c100303c0340200c0350340321034058800c040002c03402d544d96074a010842e9141c05a0808190b01c0d0160000140070010640c5100b0030300c81503d26031481c1d0601c01201351700ba2840e900d4034003100da18440d01c0140044130001e0102c2c0c3c41c000021030b0042c052401401036860344809041c0540d50700710302072040130210410300402c0d001040c040c00041c03028064030721503034400d0040d01d17010740041803c000d044c400b201d12100000e44482044281c40712030b206115400c00d040c0d014010929104071440254500500f50500240c002c3c103080c3c090010a242200c400300b001003401c1814141420010403d4000780c651 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 782173138 1250 782171888 782171893
    0x302220c0f030b011d1002101410120f0b330a090203010b0706050c0d02031609060f1e14030925120f32071e150201110301060809 57
    0x1401e02d58011042c1e641c511100c280c039005c002a107101030000700548008200c065225442d015002404103004802400c13030140100c040c039251042080701780304120f0f40316600d003d060145160201e1178581c0a010700580000a94410b07031900c04032840a40b4109521104100c0030440d01c00c02d210000c030040d132004100316200005039460f4030290301203200c20b01c642c000c0b080040160b00c00148007a001198450410440d0074141520401c0c3d810a03030b40101c41208a84400b520120000380d013010190000d40410710307088c2c201100020b00071b00301c0c0300b5010078041900d103200c6509280c1440f4181d0a1190101568501d03200c0c10300b841d0f150b98614041d04684107060f40703480780400417a5040c0c148400c958400948500c20303045130722a02c0308205104410f0760300d00d804100c200104400d45c042050032400c5030000e00301404c8404902400c1004c0f6030803042c0081d4522000b20151989512503600b07032070501a5044c038500012000b83d00421510801c24140f0802000000e03030705d508100c00621032030102d003e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 782174388 1250 782173138 782173151
    0x60f060c010525020a0f0602040e010b07030207060c08070f1b0e0a110901080712020f04080303060102102306030109050708030c012d1d0f0d020c09040c0302220c0f03 73
    0x200300907101e1043c50010010f038040504240401c01d12244071040074040c2000500e00341d2110844000c5100907002004c14450000300e10301003550400458004100030b1034011114612955010140c2c401c0c1040600f0b07500204040005003c06030300360840c1d9103010f00c4210607483e560701c05910101c0e02129282c80041c41c0c1006a050a4496421030307982d5481699001c00b19520f0301d00c01d032081d4941c1c00540070300b81c3e424865901f2800090380184040e00d0700c3c0c8010350700d0b0701d00f407000207140504104050000b41c2c28070780320b000c41e0369401c210002540022003e05096a0712100170a00420404802401c584502030000468050100040840c4a0004000e0040c00016555901160f0241c000a28003200c0d03040c01130b80f146825030089903894034410310b24112281085c045171801d01d405070000f030280c2007140c1110095404120b44010781c0000e0325071106500e070980700c01c10004903c2c40064010301d5050400700d8140005003c080f000700030494100010342c040000109410b44400501010a24009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 782175638 1250 782174388 782174431
    0x703090302120405150307020a020d0308061011030d20210a1109040b030f0d02030d0e0f19150c0801090c08150f0a091e0b1c060203060f060c0105 64
    0x1c08440a0b190064001788482c58030b40044050355000134460303070450040d01da4000043ea10b0243e2020820300994030302949051031003c024002411b01c0b51101480040d01030004000b02c0072050707810045e1303c4440040e4915001040e82103614802c0d43c90201c100d0005240c1d20903c034100b084001c4101300c0c8146a00d40d5441d8000d0341d0031142d02e0350001461003400d204080d4a464680c1000386000d0f0064256400c01e2001c0071900d1601100a01c0e03000076801c0420a070044d4481841140c0d1048040c80080800356030703058800d034603004034002c0d4801e441d85900b11710040c400008101d81d88500d00c4401005a4001d0340c400a04029003030142d2024207003422a0740c0150b5104180c00d230301540c41c1c5400c0a10503420701d01000321140803542d0380b682100f00f092001411400a1140614413010149a541c2c40c2158607180000c5403003024482e8440d080c0d1440395480141c014400d03080306a40000016a0b9840d9440094420841105101e90048000989102440041d0071044c040c990103d00b0340c3d645440c26 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 782176888 1250 782175638 782175673
    0x60f09190b3703120207050102060604021201090b042405030c040b22060f09060519060206040f050141090c1e040204080f06060f01050301050907170703090302 70
    0x641060507502061207603094010031546100b440c0c20700b6000c01182c01666503403003882da14000ca0740300000d40c111400400242d40c0600c0030a0f40800b044600311710b095552102c407125110103004003500a80e60b0a4481140c1e181c42e800703059020010401d0081d0f06825140705400ca401c5405a02e010340217240d408030003414240a800b80ba400d0082c01702c2000025440346454070300341e0907070500c1c0c215110300340000c0044000d541070024005019000c0351941c00c0c0001e0200300201005c40310900425028100403c540c0400c5c219001980241068180700703490074114090040710045410b8104030070341c0c8810850010306860002c441c1801c2c0200ca810a0b000c686081c00700844007801a030f0001181c1c90340c5460822210031200340707580c2283c10346030320305000314040f41c001e0b4000708a036a01003405070750803802c20040079034000000c035260140c07000c0d103100080050006200e1180210000400b00b0b55580c064010b518001e03000003084006450000001006000300c240140d0241c00b41110801014140c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 782178138 1250 782176888 782176909
    0x518060f040807091401060302090f0910052404060c06060b0d061806050609040e010f0e03030709080313030f050a050607030501051201050408032707060309030f0309110405060f09190b 81
    0x100100c40d05c49078a480016800fa40c4410940c0f940b280c11404a15115030320384c1d01060140d50947c1c0c0007100700b4107200c1130201c1140341012020601c000300e002e503940340300340e4002c0b503003a510741d032a140700440310b5860400c0c082d0143d6008215000c07004a910807401016a00010868000a05060352030001d08508002c4400f80e018542d0000d004010103080790030280c0003041121003032000007031100102403640085581c514401c00864000005103c00c1d503038046914000b5081c1c580103149072000700035250700d13400c20b1407100a108203451003408003401814458a01c94641080c11b8031014039103c40024000d18090183e24031035012180c4800c144201442030714440c82c2d00c000c2840c955140d003100b424414958903217041000d8201030180700c00002c240b060200400079514003103050b0300d1914000e044210030059040c01c043c90300d40654082003910301826035070401524001090386504020440341400c100450b50412a204240441002d03907440d40c1c0050024000200943c100e08410004042d14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 782179388 1250 782178138 782178161
    0x307090524030601092117030108061b0c030a080106020f0a050a0809030307051b0108060405060d03030c0509030d1d090f160905040e01020717190518060f04080709 72
    0x20041d07a940c980718000001103410040506004880503900c07890080b03003d0545400002540d8103101000402641591413694003052442d07890440d8140700f00700380da81d000180596080004480c0c1c1080c060b500341e040321048185d0106a903900c109a44e0090040c06080c400e202c014454242d021201e908003260640049510402400020407140c9a21a05400c2017034040d40c1408204102d17070001b01c0401034094208035050842181608050014284641c01000316000e0750426040029540c0c0700c40c85143c003c9d505007030000c0c0c410044601140c0500a80302c141d50144a04600c18110300d404c56103d0010200804443c01900002028400c0829056030b023840c1240315200410b04400d1804c400344041c0c801480c05207130540d0f0320800181560f180001115869500082e902c0a01c00984841a014600e5085d0b0620301810516202030724100000d488040160100c0c85400100000c250040e121000421135521080f8440308100c031036000c0d00c2421414410414005840803c078042c1101c840c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782180638 1250 782179388 782179429
    0x90b0f010815060f09070c151a1e040e0c042003010303050f0c03042c010b0a120b060714061003050c0904050102070218010801110c0d20010e010203070905 68
    0x46004880802c445000e0162940664410b0f8406120784903900030b980304680300d40e81d51032070421900b48039034001500a8105003017405c2c0b050300482c94000c211514504002074402c0103d590010240b400d2420300403003940d50007414000041507041d03000500420210084908024050300e107c07034001a10041c4001064164003031004101082c0250301901c1c00c0324224840360b242540f920800c60540d030280d001018200a00207900041c25070000d0380710103540c0094511003c030350620101c03040354011151414200244050494106241e58011544007000681041d440e00814602110303407500ca4400300e0014414500000d400300d048403c5502141e4021016000d0b40300400700344451008020001d6500e07640820080c0300586032600c01215020301d01700c07a60001d505040581d401d640034103e0303c898401d414802041c402e00b0200d100c0b21018880c1c20300d1003003d44000043c2ca240c002098000c50380b94039085444006c14410340043d0b00c10607907039031039859481c0c5400c100f006c04101c0302950b03450350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782181888 1250 782180638 782180653
    0xc06290315090c1513080d030c02012f070213270305040b030705091309110105090f0415080a05010902090601170a0c0e030304030620030613021615090b0f0108 70
    0x80c00c01c504c2100c2c420201c403141c10303d07101d00164982452189135205009540c49080400a11640351007041c40903007541c8000c0c0402c5605000c50021016585803031810503007a030100d10084a001400ca0314a0340e030150010030b10342502e0703a0143c0184079800300f06d020046001c0d444005030402403a07020a090f4181c455505007800c0c54001a0103820080003441401000c00c10340f0f19985d41e044101e0002250354102150441c20703890080340005040407041d060002c01e02c02d103507903527450400c5d245201d50306690000e070f00300c008009840300070304580c800c0103240200307107411080c0241034010b545010b009446d141801d40351031004640f0f640e030500810000c00400381c04a01148a160403029244c81b02c1d143c0440355040c040000f0b410340e40942d00848031240c0c0d070002040980b05441d4184104003124aa807030035071428401190150060700008118164005148420410f070420310f03580c00798108003c2a0420b180c410f600b030061100c00700640d00c01400d03000154401d0880600e440c183c60841e0090a003e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782183138 1250 782181888 782181913
    0x42301050a0c06151205011a0f0d0819050d060f05090f04060908130e060a05010522090204031a0a0b031903090801020a020105160f050a0c0629031509 66
    0x2400385410441d10103894055138420340203000c4550000d45185603d26114246502d02182180c5403034031086440b100b08889604190f58031100c182d0001001c0d907001c0100e1045142c0355a0310f110b2801e82401ca0b240400f0440d2150783e1210280c8000300c5007047c100062616500101c81c20075180c800e003907004a4134000201140380c0d00a0036034005104d660f01045105081c2d4924440e500b02c1d1040b07010b0014405002c110340382c03040000b03a400c4201600c0c40d0b80b406040100082c028030810350000c480011445040c1c10b00210103003540c004003401034045445646903d8084400b0802220481c4001010000314800d030605116003801c049008004001181420008242c050110481030701032018140300090100000e0004002007486c0f6800042c061410449441c4446d005074036003820054024dc403040401c0c2c1100454000b0841d50905d40c500b08032903e841000f40042400d8200881c0f4200c5002d581e10018682000011104800740c0f170020411107540000c0403421100201250b000c0c0701c00043c1d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782184388 1250 782183138 782183147
    0x111090103110706090501020307020d080108120a090806251805040e01061d0f070f090b030a0e010f052208040306180c140307173a0302042301050a 65
    0x2c100300c2000c0840d0808a158503142e04035088803809442c04d0350008100110700d0750600c007248a2012034144061035504000115a803100078202121402c040050303091001742c050041e00380203000c143c0c01c5400c5454125507400d00e02038946000c24014502103042c049181c09820312441e00b80c01e6418021415140c882008060300b042e00c0c003c40655645c0300d0125140d090700021591500398080448043d0800303001380c81c05038200420303c0d010003011408000d0056813185482c0103d420680c0c502d602c0381c40b180d100000070103c0802100041d0b180241d100c0203001d20b030704440d1095540e100000403c4940211000510010700c074028100e110401c014000150540e0008081070103400020700f1200c507a035035644034452150050300006100004054191604000541c003034a040c003d22400e4164a9075410b0351946034202c00e20090100940001481100b40600c480030311401a984655552084014000358062301405113641da004800c0c141407800281844c040a0040e9210b900c0e00c0c450100445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782185638 1250 782184388 782184401
    0x3140c1f0e07081c03020f0921010f02030f0709180504051606020d090b0f12091504050f21070204200415140403020f09070e0d0b0604140f06131b03060501110111090103 74
    0x1006024041c0c009c40800400744900c00302c2c820042030041e56030918401c400f404090061010013041a00c040034040d2164164420020090360600070805889070303c0c0060030700c0b03902d0900310b466044010000650550024203045491803944904500b5620782905c00c81900c1011258000b00704100080030400c41c0c110305181e840b004030801c0c0d030040300c041d8501c0c592081c019039099426522035030003000408020700c0f60550a94110180c0009404080015a614018240003a100e591380305d4441d1240d62210200f4101d40e0405c00001da1b56030b496802081c001114020002d0014004104100491819808680650b50000c10030030140d0450402c200a2840007040d081c200141c0306560b40052721071440c2d0741c850302d214001c203800514092040c801101c0310b003110303042e02149404c1840f03100c0c1d82d90081c4030342002e01030783c00e4603c1103440c41d800005042d6030300744100069900e400340303010983d16a01000c03e5401c02d907a010010524a1400c901f0f880701140c44404c1d00204101c2852558086c1c0c3c0001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782186888 1250 782185638 782185669
    0x1b08191509260f0c0c0a0b0405011b05011b030509150402061912020c01020406031a0918031303290f071b0f060903140c1f0e07081c03020f09 62
    0xa900c0d01180303000f80001c503001100041d0f4643c0c071000300c1d1011481d0100f40e000181ca800000c035400c1924000000b0440c4001c00e03501c2040d9145080c14405100080d0070985111582c29031011030508000401001490219001000c5000e81070040ca240c43d1409891030049400030405810901c4284204244042c4610500d0900c50109269008201c0c280058540f213080c01000684880c83d15001400b501c0c0301c400b03035541101e4030782181843c540d40c2c07036981508807510b80c80d158191600050800c1c6503215655041070080d9286000000f0800302c01c080203102c02140c504408a8401000c041640c902d0a88440042c149801c1c00109101d114986650070351040e07409410f00d0385010789070105509440c8506550140e203030510f0030181600203404050324064040018a0881004111500c0d0140d660104201d80050100f14074680001d4101920041c0c55901361a006a03941508560303900c7c64030f007889080c904282010b0201800791003643d000d042011001480d009030310041050405049503071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782188138 1250 782186888 782186963
    0x41d07020a02090702060f0f01031a0a1107050a05101103010e07091206020a0e03030412031407062a0519120e1204050a0e06030a1b08191509 62
    0x41400350365100c40444c0100b07a243c002c0c050604203000c403090600802000560ba200c8404010400640c0c002c0884c0c0c503404001e0050003842d291114200040d04420449288200c1c0100e61340083c020b0103d08804080d00c2042141c0911040032002c2d801d48080807210100180d0600041040420751488075a1000c158984508215200c02000c8180c14080c01c09554081d4003040c00e0b00a51741204062200d5507044004504192800800c03180031016648000d00f003203903041c41e08610484003001d65222590019003400090f1407112142c40488221150100710000e0b401446001e0340608116104d04080003c02265105541025908601070403071031746c800f40c4c1d6424000c0c015002484256402a1841c4006035201d280108016500752203401081020410905001da030355000a0480a190790114943c0382200160700256103111890744030250314000d1b155410090480340340c031203070030b20b200344c0e2006024140d0742929011208818401003010b0003031a005580e02c1040051400c0c01120170f400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782189388 1250 782188138 782188153
    0x3091503020c120403030e030a0506070318052517031204031803050706180b120c1207030902040609020720030307021f0807020d0c0318120c080111041d0702 69
    0x10030a03d007240440300303229100d5011409004040e4400801c014852080740100034403010354907150b403105070191044007171540c1d520403d100c504000d5501c5c2c080e41d41200030386071615109a9918018405201c60300c3c0b030451520740c003240c0d032410040c101801941d61402142820040000c034a084503000e0420780600400e881d8240403885189006d03030185108030040d203851460114042e00c00020800c0640314684900400d000103184032060b1000e4404405880515446103207041d200e82c800c20f0f50841c8260141010441881e805803c000655842a05c0801c4255031b11400a0128011007500806040012540c90400c4040140b14200313424000c05803803400c1220750014800002020344035070b4283c2405070308042907800c0400c003544005607002808409080380801044a030032400004c2c02d0014a19000e0220740e181c480c42c801a0500c103e005440b0212030034944052010b51241c0720056003800c118000c0c108405080d1030848480390b200443c644c480e0740551a070f00500401c03003000c5102d49034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782190638 1250 782189388 782189407
    0x7060305061c0627030507110109050618150405030309010e0a171509010e070b031003060606120f0c050a11010902030604200307060e3114130309150302 67
    0x125a031162841044001807013a625144040420b00e5200e60081804e001070742d1300e010039000320440d24616030004024104240c04001a40d07079403019003001303030040300105001085034004041d203c85c0601c03ca85581d410410302d8090401c5110f5030260603056001031000b14000e50240507122602d0714010003a0054503242c0305c000ca50500001100d404d6588544c40d031000841c2e80ca00303080e0300102c05600a05c841c5080341c200c5039480c2e50350320410842c1c900000004d0040141c514920000c1c43c1d103e541030010696440340280340c01c1c80061042100c03841d00e841c0d444071450a01c05c120f0a00060740b560303030800c0e241813015160f44d50b509080600300d5498020342c10050350244030240c441d07440f8503a480d0400314070000301c150220900807410f0280d440380c1c9003801004c2d0800780590702a0800c503104000500e99002050010341070f00c03101c128544a035560508072900c10b40012918141c2d4801401081d42c2c0c83e40004032103054070301d010340803c81c00304003400100c03400c11030554101c9860501514080900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782191888 1250 782190638 782190679
    0xe0d091401030e160e060f090612030f040303030c080f070e1201090c0f1802030c0909190c020715050313020103180b0721140a0c03181a0f07020706030506 68
    0xd030001130f8035520100078848070504804083e04200c0540d4100c000001100c0480d0140742d02515030340c4580b4482d062007001040c20000c07161142e0080704403d0301c480c1e5903d8083d02920000c00440b000c5000400080c140d05214000540302c0d071000d07510140030010200c1800a02481301d82e1102e02035403111007103004241090089001090800c2c00720140310b02d040e4584810701442406d00b14910300401c18000c0340c02d1201d050311481c0380d040b00d091200b5121100c00c82500c0311070042e071105490412804000852700071841200311800b0651408011500703150172681c5d03210884401c940c50b00110b41c4240594441d5010400d440096403c0c2581c102403a2201c40d10700c40f084070100000b900f45c40038140502141c056030006014610700520044411108544000070003d010360b2202d550380500b0305959109810082d4500109404115504031078204548003e0162505180a040c103034003140c6c0d09084103007020312410703280d405488114208842103024110140c039240d0710007900d03144002c505072070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782193138 1250 782191888 782191903
    0x20606040509121c0c0207030818040e0d0206040b0703060e1f081501030201030c0804050c01120b0406080a0b1806070f170106020a060e06072708120304060e0d091401030e 75
    0x203000b54001c20360250101c0c4c2c0603540d049005008540014104000242c0d14009a91808081701c24031039002036039002040040282c940d2449141c8903c420213100c4580110740c0f140101c2c022a10004280d8403820194152162403060384111140c0c400091500c031108e01c001071500800030307003003445556a407940e1450104042207032030810407010010403c6681511039004400d0b041d0a0209083c68552030721503e075440b0540b4103040c05032500c0d0152856109500c0042c0098004100304811500c1e0451075584d03000f01d4070100c07130401c0000c02145200303040301c801840c0c041501004081981e58440704654102c0d110410009004814180510103429940310341d0103809507600614880c0300314245401075460081d110003290300010240701566910001c03a03804441c1c101d02c151000c00030030101d5454059250f00803034050158046c07100300000110011030141e801a4030521055003070f82c0c1c850f03845017112007126001c01c218010800210054144920040005040010b60008031102e0941040407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782194244 1106 782193138 782193157
    0x40e0705060c070513022b060f030b07020d090e2202090f1611060a0f0e0a060c020f0c18040f1a0115030b0102060604050912 55
    0x4200010001400d001c0c04490396200c5101840d51a6075403809071034807412410780c2c2d914000c4d4860003500c85030032080000340342e5001c06040d0b40d24180080ea0911050f42d4550100003600384184a0440c0154090b080413140703898010002410a144201c4010902203a884240446d0142e100090b81c04428010031007c00d802400b42c0c80444014203d000307502c1801001000011540f418480303009101d0700c0d081110070300301c03844250340d040524040f150542e8031000010b11100d08981001c81511066030002580751a038146250178454004001c0d40c0340c58a03411f8021030300340d04210030244800700710050040600c411000880c0d1841350541d41200019000106040c4211020f80041e41d551140808011421200000c2411002403050719220f48600d00310b070700200d0280c000e01c40b898605030301401440e540c0c0c008010042c10040d120903242c0c81107036031081c8241002c07001801902c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 782014388 782194244 := by
  have h0 := BRFrame.cov_init 782014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782014388 ≤ n) (h2 : n < 782194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
