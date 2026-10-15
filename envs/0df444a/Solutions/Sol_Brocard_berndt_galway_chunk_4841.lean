-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4841
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:54:41.049815+00:00
-- url     : https://prove2.me/submissions/0c0bf22d-b61b-458d-8deb-9f63a32288c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 870503597 ≤ n < 870683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 870504847 1250 870503597 870503603
    0xf040804051e0414090d0203030c0d0203190f05060114090a0e13050601170c030703031b0c03023309010503060f0402040e09031201141e060f16060f0204030807061a0d 73
    0x20015117800c4031050305d040501c00150302117400500c01e1010b94030b200400d451042c0401c200258031f035070710b102c0c1c1d901d400c9502d50700c1021220308044603089106600d0b40514003c0c042a80d4420714001d140904241501c610103c503a04410290720030003e990160540d15040762592402540c0100a500e81516110007a04509010454901043c1b601300c03040115581044041c0c001c3c1041d03d2841d14080c14421800e0400b43d03055801c0240b40c03040000904a580207143c2c02004e00e040010901d1030680500103000c4295480e130b600700514900b9091160586004141c165240340c40e55a4520a101000560900850f0419000c1c000880c80032805040b05124407180001503803108a618810b410f036400c1a40680101c403c003002c12a240d48514007821401d04141c8c846a4408966a010504910484003164006800440c100351556109003c04000364001c5038240041c1c0f0b00c0c5030b81402203110310b21004040d1001008090009105504421360481140a81720018981d01011038001a400c500407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 870506097 1250 870504847 870504881
    0x50d0501060504060e070f030b130504050d080a0e0a03050904020d1103090c0a030b01030210230a090503010606021e0a05030a1110140705070c09090303060e0f040804051e04 76
    0x240594189407103010024002d017110703040d05080c101005840c0d5031511494a04140d01c81c903407100181c407030070784141c4401c081c03481c2042580f81070701b0981d03115100b20076030b0000100c28802148109540d030040506111503500038100a81c0191340503201035100380341280c0c01940030711141845c2c5c03926208480c1c0420300882107a9491400c5002d09080c07800c0354401c188142c2c0d48560500109130401000c1c0c1c103481c0d040c0c8800c0002c148500080e500303030307010010340c00c0494000c1b00c190b92042c1c50342000d085040496103c1c1078020b0340340c3d410542660b05502407407006038402080e00b903200c1002c6040100d000403400c15200e0075401906d034207055501c04140c50010803038080d0758086804c410015060403d180d000e0070800340240c64040c402407030014103c5410071001143c8881440080c6c6483c100508000d2010416600c0b03030315015001e485184909400000142c0000c0d914085100c0507501c00e69000345940d15003420441040303001d4810341c029080907a14000003001984482c0b003000ca05030424210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 870507347 1250 870506097 870506099
    0x6120b06070b1b03040c0308070201050c011b300b270f06120a2301060e0105190807030305180303030708150109050117061206040609030e0a031208060604050d050106 73
    0x40360a0210301524103e00e00c0300100100804100542c0d500c070f0940ba440808999240402e0004881c14001d2000c860a1946071201c10152582500c000c01104582c94982d5014402c100b1001d411400307540c07480540f0001c840742c801810391025445882c0ca00c000411401d0380882c060030301d003c1c48007210100080a0350000030f000da902100b900c5a540b01c0b0301280c8003880c4503135454010340c03203904a08008086501143d9400b00e42912040707c18200c1c1d210714020001d680d911070114121103401e10030349003d01d0007688600e07020300c01080c8407410343d29914000c022840c40c5a400b100d00b580030000c0c0d007000c0c1c079031180b009840d1b6805100842c020300780c5907100c04040c203001c20482040b00e08007880c5410300c078010004014903600080b25424408004c1401356107a600c040214216058855800010f40101c03020042000345a50095075001d000e9541c40d08000900c0c014840700140d2801b000d8413482c400c5111460036442000c840e60700640c05030043c2d0801d0790b07450204525602c400c40494040e5100c040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 870508597 1250 870507347 870507361
    0x1605060108070f060203070b0a2706110c07210c0e0a0605041a120f0a0f140c0612040614090318040902060301290d02030a050f09060106120b06070b 65
    0xa90000f07000e440c440101c00782d142040c041e55902c500c8000914020701240000d800b80529800540181201031007140101d1090625035030582e000001150b0710b625100f4035141125030142551030032040c4000030613a040c28803140e48801000d4203810f191024525500070001155251520300134061069807903918140403006100307a4500703030442070196113403020341c0d10080d42c0d5400d40c0002d400180d4100321044120301c200c90400444030070300c03220fa100d540621400c003c0d0501d4608034040c010303500f00d048602d0184030035495031204804135603c410103100f616680740303400715000d0300503210b1100042c074241524226030700700740704541581c0c0a0f000490a40404448103c0300f2030400401c4a0800c00a0010740c0007482501040c0035401c000d0007800d5031411410324070114030b5140505540d80d40d0300c0da001015104040e40c41201c0c050546403c29021840c01a10700454601458042c0082d2410341c1c20680100c2c1c40742d040d01c90b1010b0b45500d412403100c280d02c2c1d51006002c00c0c0e006d040d0950103858105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 870509847 1250 870508597 870508603
    0xa030309032319260f0a1a0909160303020706031a0307030609080d050a05060a09020901120b0a170106030b0112150b042904050a0b03150402061605060108 68
    0xa141039050301060116082940034822511100a4401a400d6101903e101200c2c41c02803080200d041025504a14403003940e095840d40c03140b00c00350011400d9030f071407000300000d0b00d40c1030a108880d840050b680b41040e00d400116241d0040120044920f990440710402e0b02e40d1000b80d0064001da04140b40500c5119810701804541854803980d240c281d00f801c0e80802d50725076842c800580543d5661000c24204615001259000760703500b9424849801e100c1a0340c1c008080a90f00c0510074803c01c0300c00612400386009603442d5101c141c4034003c03004400c540c00b90140140c0c00d846070340081002000700390350f040825066580d048240000980b0350452401c4885607c040c0c110080c42240e40302c3e2000043c0d014082d2841c0b034455540c012420030001030100b0050400180103001900f070640d213200c2209e0f400113a031040070000703c41c240210f84030503146d403003107800303035504150160003001e540c080c2c907083c011159800034800f0301507600d44070701d40c52292071400c81e14500310781c02d4000b0001088080c60030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 870511097 1250 870509847 870509867
    0x507030f060302030a0f0f0b07020106060906030e1b0f0a06030209030d030b13020a1815120c0c0807050a050321060609010507060c0311040b071a13030804060b030a03030903 76
    0x480003008002d0950300000e50342d0501a6004140c0c9000410003000c00000d00c1c400e07988190300c00b0341e0780f5003030a105102070301800a9015100c00140c080c0720004103039129003c1e4201c115942c42c09480c0110b41d0b041034640301c1d650305502c141c001400d00d030710301095102c411100e00104040e580058440c40303540201414004034050b56820181401100420ba9541100f48048101030f05070041e500c41c0140d8041e0342c0200c180055040c60b4010090000350406481d201140c505150b075620001165100010700440e2000c0c0041d00009203407006140c002140032008203a040d001d2012502049a1680c2c1c0c24a0b5a00040c04040e559809020701c0340f0608180001d150002d908440c003c1c2013800700c0000070300e640504040a8040b0780c4403415440321b2802070303220524100c03c081829a42e03d842d88544015540120b60440b41c0034102c180307079000404640303074050154005007140d01c000c514680f012a041c00c1c01500584c0c2d85550741d00d2614865408000280c82d07a44282c4010900c0e010341d0401602030111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 870512347 1250 870511097 870511121
    0xf071104020c061603090605010303050a120606050301140d0b01061106010902030c07060b180103060e0c0f03031605120705061008010905060a150518060a051e0f22050703 75
    0x180410303103a032000403d5069010602c0780e002c0000e59002e8904034044c001180000c1d010605c0e00d40080180741e8088000c00d1443c903507072261511000c198441c0d0301180c800380700d80b40000d1006e00c0180a009851040e03146d08540c0109030300501100782e1110211480f083c1e100c48081030408242181c642030601500e801040b800800710705620303004140c11410b208403000100495501c00b0304120560b10100108844030350340034450f1596859103040d100500109003000442d00c6503005100e2640b504d9000c8401820000c0d02840c02d0940c4501c030406107a42804007112203010f90300710181815200710190034001d004500400c42c50401c4080042e01003c1a006412140d04020320840032400018056801140800c800609540b120082000404454002c01d6004494035030304000303410204002809600c0c1100e022150340e590320300f00404c0e2809101c0f411101d03040340702622102e1404174030400f44c0340f1010b030128181312103140c1440c1003c04030340200f204907036541e4107118001c0e074148502e2140d216 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 870513597 1250 870512347 870512351
    0x90a051207050a020409171206030601092f09060a0903120c0812150d0b1806060109060e06040b0a020a0b071b08030606191e08070e0103021e0f071104 66
    0x2005842e40c985403c4040340c040d0182c0d443d0b20015041184050503c82040408a0f03c00e4442d04240b800f40c100c1001952094424829a03002140031001032080c0072416803014580079070102c0c801148440c4d4192006106011030081c050034a0540740c5030010701e984a441c0e0359050b561811480c00c645211564141d1108011445910200160002d400c84940344c200d41d03000c2e02d640d07454050468000f070f12503108603000903c4190740c90411880300c4005002e045025061501d15600c04d6880341d03601011034030140000e071302d81c2040041c140038680c0c24440b01d001402c4949031079224107011100e0b0340282c03402e00059000e00c52500c1805021141c01e6004907081c038103031000030318209600200306038622000d4446280000400c000d56155011507500164081c40c1c0e845008455001070b010782c106151800001c0a100341c250039943c45a940a40301e05002c0d00c034612103512410044000303400c00310343c41900d0302c0308003074070044550f04a01814030358490890107680e41505190080700300c080390519901980c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 870514847 1250 870513597 870513607
    0xe010803070614071d1212040807050d02010e120a0b04030c061d07050f0103090606090e0d170f060f120609010b010512060f0109120c210309060e0414090a0512 70
    0x280c3c030117002d44846030704008208802400000044203a4155003800b520f5100e09040300c000c84e030101d0050000c542c10b00041e683c1442c1c1c1c0c0c4e070038480410801c03d40240011246941050710b403401c54841c0f00303540300c540211071640c2600e43d82d801540e281a034056010564600144041181c1d40c01401202201c1d50040221401040192552003105000701e900c11903600c5141c0703500364441e07485007844541055060000d1a41c406244006003d80035642d0418006c448100c0e8001d4060b03010950821000310845280e665424100540148042c00040d4040f0015004148507a07801c5803201c1c000e6801005030651342040142c660031224850f0019041c00014042205114201940c031644804182c902517151480c03200120350076440d0f600080c600181d101048424001104401025510134614007404141024248900107020003c000c001684015040c800f062085030b43d090310940c00780c00461102080c01c0b201e000d940d4100c490804540c0522541c00500c0000c221407400c10b8400b0b103d940c548 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 870516097 1250 870514847 870514861
    0x1c0b1510020d1e2705150708040b0306121032150103090c091512020f0d0615080c19030803010b03070207030204110a08010e090a03180e010803070614 66
    0x45060610040b220304070034014240e102d006143c0c04284e0b00d040b040c00707101ca0020321003a60081c4540d004043c0111041d1400300c01c01c0340c1d20344c220b942660f004002c03281490303d0076007a076070f480e44001d1502e034011002c4c45090460007420172021140d000c03c0d008c04244640b00c00c0c1004200114000c5144940c42c00c4c2800121505900c510305030401500740070b02c00400500300040e0003520700c0340d000900c0c5a005034800034001c40254044400d880300e4030b244aa40c2da5a50701e0701004543c0c6098082c0d400003802d04494800e1800794805404907100b007001041d40c080012403456170007000c0d8070841264200a444820304e240291810343d40011501c00c0180032425621180310901050203480000c15000000c516014000c01c4894000c42c0d00420030f00c14004c0707800c01e41c02e540c3c210804160100c0c0640001154903001283e2181c482c404c01c000406520b0b800b42c80845042c42c1e440322900040324410f9000c41c12600a00401b03018206610045a8920340e07450b290049445031000c00c0c3e2030340c0c0400240a21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 870517347 1250 870516097 870516107
    0x611071a300a020412031115010609080708030304150513060203160e04090309030f150207061407021f02070807050106060801031a0601020c0904151a01020d0903020f1c0b1510020d 79
    0x80c45da010318010034240c040c2d0444178506600d2480340030b203440c9414000140d160b400303c1d07404140c0304004140c0741c40980c1d03800780c941da078001624001c02e100041080c604804010f03030300143c0d020800c200c001c4200031075500d417034049a0094a00c0205d84c203a0b059035100b0560050600441e0050540e010810b025054038000c18086080c00000c1030500510340e0344050041003880d180b07240d100d01c44115610061460120010441d46c1c400900f924800d01c005043c16001141c4900c2c10300b400c8034201d10f85e0401d5140c00300254041d01040750061024001480403032000d12444000d46201c0d1104044c5505600b070415450100903103c6500c1002d007800c000159901040700d1050b06425100e070140c079100d62031b004040400504600c14036515100b1640d45490481c030f0300c580408020380030740394601c108102c00c03a10008113000c00303901705406150705482d90034984110b00d0804e00703078040e03404848107a95a90002c80426200100400341c00d41c0d0f240720b40d10f4644070030b0542c0c00c982d00040c408031810600240c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 870518597 1250 870517347 870517379
    0x705010b04150f0f23010522031208040b0406150801060e01060207230d1401020c0a02120102042301030b06030718050a0e0a0b060c190c0611071a300a0204 68
    0x1405c1ca01c48608480030707074010b00c10b640110702c82ca01152800000d80d02c02100d0f1400a11055402d1904c032961801d030309000301c4440740100d40001d0180c01581c0c0350b0b15044050241200c1c120032a6290041c0080c55039400c0c8126406020005841d0280d0f5240c02c0c0000e19040031170300070003002070051501890055042c0c0b042c24468609480404500341d185c01e103110398288150200e20345500026090031400000b05060150501c00c0751101810b101c0f01314400d00701d02481c00354039600031103a160300f2030b90f00c885040c0070303d48141490003068410131400803030130a800580356a008540c545079113506e5000500b41450160100b6901c0e04403031b40c0b901d03200381c818410280820420954646070ba41e020b031078140031030740720081103803c40ba402c0c0391030b6440040c060039400068400e020100e1001c140c0c01d11a02070001481c5c0414001c00285092460144440c2a0941d40312842081048084206440089034081e60b03074402e01d0700c054085c0c4082c1a072039440c00080909451501c1040140b103401c201d2014a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 870519847 1250 870518597 870518639
    0xb0409050912040914090606030a11060915040e130201050301260d0f03180203060f10090c0806011733040e01020304050d080f06060705010b04150f0f 66
    0x480c0544803040a1420070700c02c40800c442220300010080351110307036030b040b4001c00c10303100449908903524200d500d45c03120400d80b051a455008500403c1c04600714164030344610100400c02841c0440460008d000c10400180000300c00b04040b404106030084c2020341c1c0d42c07100503148a50710401c82a40002e040384014001c10f2482c2051516050201401d0704840a88640d802c1c222a03d10952400160000c904032004000180c140425089001d0010700301c1e0b2041c0340e0140060039542c88134400c1c2d0010b40c2004061001c583e80042c00040e8102040c040c00c894640151280000d50170001c0005001d44190700c504c4041000c1e89003481140c410102480030304c0c00d1089141601e040a070060040300c0840320309196440b40c10400302c80340251040d4002c44c0a540b01f00100ca00404152a040e2405107089500d41c442c034002030300003120b40c2000d400800c41c50b071064000203035401c00c40700028102c03118501c2a2203840b00f030700742c180011a0301004c0e01c2d02030142841c0d0900301a10304003140e000490420f00707034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 870521097 1250 870519847 870519851
    0x20c010f050a120f0509121624051e01050603240103020702041b1704080301150309020d0b04050111120a0209061603030e0c040c0f2f06040b0106090b0409 68
    0x14000748500080d000b001140c0f076091200710300058aa82c00b40205031071400f22409890604654103d0000440e0f0100e0201c0d0f28200303800485441d41000c003001d6000089d040c03040c070460490399010901c00c89200391001c0140c9030b02981200f01d40201024160841b50043c9010414042d120208040c04c5a1261a620354100401030303940040b0f020f0b00403180020f410904280c0300904510320012440725964060390366000b1022804504400f070300c0c003541e0143c1240b0302003005006020380d5040d440721882035801c010604500759800707d07140c01d076542c80542c0e21120f10002d000403c10f082c020040115000800709042507180040d0004912020b0b00612426500107200030f195100d00d800d444c8440b5202c1e1200030443c0d01401c01401030000502c0341c500500880b0b00921071071616100711340d8140d0b01c6503600320540c0d80520054650340740340c0001324280540c0c2005108400f400c01d0034510cc00c0d082101400190a080c50618110901a0400000c0c041c1014052002030700340d1042c0d40486d40705030b05c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 870522347 1250 870521097 870521107
    0x60c0f05162a0e16080c0a09180914061530030a0e0103050f0109050a0e06090c04060509040b04200613060210151403070509040605090d020c010f05 65
    0x1000c0d007902c14a110742401940c1d001d0b0a0742408103015014115418040b55281642da41d01c1000e07100740883c00d001c00400c60250114201a07411400b40c81642400d0910410081e1192100148141c2076a601a0881e0b2602c10020810084141c0c1c1c03c191014100206480e04000c9191191280d148400a0080940d0380803a4110302141c1d9400c0b000d11800242c10303901ca946165010740f80d174400c00110000c03c1c24000250b006520030b00c1107a105020100e21403800da400c08502d44090310b0043c2000581e40d80b20814403910f0501405007601541009000b0914000c40105110590786950f01203446044c42c203041001040041442c0c5501a0340041e0b00d180351200301c01121100240030700c0141d0400310101c1c00e43d0006d842d0801d1141034491940032184051181d018000554008010040b0000b1011104121034918200c19041e20300c2d0060540d0031480e1560301051a0b90b80c100e4054600684500500031906000d00c021000c0900030f01c064000141e0401c0064202c8846080081c20400d000034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 870523597 1250 870522347 870522353
    0xb09190f02090603100609060203040b1b031905130f051318050d050d060905280902090c0316110a0803150d030225080a02040c09030b040f060c0f0516 66
    0x10458141d0b102c020440ca480307003804208482104054080c040110b980750380003042007400001a6800c42f40c0000ea52894032448603507031410054400550034807440f0038060551407040003200c05001c5040380d500d80e138170b40c00303541000f803558003c960000311520321010040c0010344030740c95401d035107100d0003802084903514100c0c03640b1421440348029040d80203285103c0340040e41300c0000c003d4101d114206001c1c06486161800c12164107030380401d0a816009803941c1d1541c80d4001a6540c040d00d0000003d035400700c2d8010078103000c011030741c0340154613002041200784c0101100b00828186107103058402070b0301c203100c2103544818036000985196800720000c0d61754041e001811200041c083e01e01d2003040042e2070065039900c1c07401a40c0c020084d484038200c0c0c0a21184203c1c2044912541c01400013a2864003032000500c2d07004028010842d880d10044013007440b2a403454001c601c9003111444007040c1d0b0810604662025080f1020040031106510081d0f034000e041e624079281d60301444010181c18a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 870524847 1250 870523597 870523601
    0x3010b0703090f060c0302010c08090604030c02120d0309020a0602010b0112090516080604020a060f0f050f12190b040c091521020c060112030f140403050a14010b09190f 74
    0x3a01142041660f0080459043d5200802d04c0e812440794000b03004070042200180c807401c4040b20802e030540d0020b4009400320f403044d001240028000b0b44240301360303001c48600c9800d004500f00031401280c0c48208400440c1085c40d40c9074001d02c46440208102101c00000034507110809611030307501074a501d13105090100074440c640720180110381c04041c26a8074a90140c036150101e900b0391140c0c91b03052000984034022041c020703401c400e590710046009109001030740d00340c0003038030700c072020400a1102240d030041c0040480d000d0031000c0003030760114000e8003468056505000c081400f40e81082e900d900200d40200e020070549850340c032400d028840d10b00003191503450408444880601004c45400d4008080d4028071000510790180c0f0901d82c1c070f03411100017044811f140100015801c45a1010070b51090940030401740034620034510340350341d948a1a14003003401500785c580014003000703140215003d00c01d1210f143d07015074042000385421140c80d0844160078000030380d0300341c64114444001d11a0b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 870526097 1250 870524847 870524849
    0x1e0e04170301060e0118150c050a0506100f061409040e010e0601141e06030a020717121014010e010e04060b0d020c012712090e090f071a03010b070309 66
    0xc218090349943e5962001806600482a5140421500120317000d82d903d414030000c1c240c1c0c18000e508003101c10301480448810b0311315901078589010b202410700c009182409040e0040101605260000303050203d082d849030030702d9000c1014424420600e10313688000105650680408440006d4920a80c00d21395000d082c400e00000c0c0c031401018000308200301c03a40402841d44005954000c6c4107110b0554051042d140e400309a94403040900000e9007000c4243c00824132140b15040c4c403a803c0c2c04445d0006441d802103041114503110040800200034617400680d0001c1c80c0002421640801c06400a4880241070b0b40450400c01100c000741116221a00503600074107507c640550354500c442401002500230380386440455091031200c0c01460031016610f07080d141c0e41c10301c0000c9901240c1d15041c540012000903014802049000505070358440d6880f4854100308010380b20324038030058502d0406d1855000b88807a0700d280201c3c114281000015207040d2006400065911500b03810300b0355480d100307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 870527347 1250 870526097 870526133
    0x80705060a091d070e04090206030a020706020403140d0305100302090609100f140a0609210302070909080705161505090d050d120524010f030f06060215011e0e04 71
    0x4980201000d00071183c02007440f40482d50760f00c0c0100700d0544200401e540e035010010b90300c00c500f400885c85c003207070135402003620740e12940f001443d06a0f60391310044108004081c902e41c540020081045150701401040c0d03000440d06400800c5605541c0014201d0f180609503a004108040008441501211107480501400e003041d41c003032a56107240444c9040a444283e02410000c440085c0007806460040190307a9003080301e42444c001d209c0440e000f0046d2501c141e0440c402c04000144203071140c03045402c220300450311182c1e169001c0c1400d030710b07007051911100c1d402180f0b120100000c0c0b1141e400102c0200c08e91404554400000001510084814101034101e010f5442c0012071280c20544a204001d910601881507a0302e80010300e982d1940c1140414010002481160740f6610881d1069030000182c01d00041094a1601060840d005030b080500942c1c050403803a1013003140391940364010400250342a076040d01c2404032040c0c4403500e11951144112140114041107100d0101c0304030291 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 870528597 1250 870527347 870527369
    0x40303081e070c140105150102160e011518090b09070f0806010315030b07031407031a040c210507020c120c010c0f150b1513050f060c0307060b19080705060a09 70
    0x18140c0642440001c3c40c14464054458410f0104020ac070700039041f81152854105241e03139078640001e980000060320081e10402010100c0e4030b2104c0314810895016119a810015103007024109020714040068601010710102000c400740399a80800d05581c070280c2840e01240e0000044002c801002907608001e0480d0702e09420002c0040c0d0540c0182c0703102d610301050102a2b1030740b1a040e42141c50084052800902c103a045e1803207410541c0005140715054903140c0384020b0702c8901c1074810110b0b00d8810021689820078001c5099042220240c094001c4940307103160a450b030031540c0c0c2c62055249681c1400000d4010b9010b0113034200950006640003403208014034880ca403804d00a0201640c080c0c803560400403ea0080642001a0b40000741115100c0341c4881c00c0108000c80f01c0d0f50b42c0740c0d140d4098810010361a4540060018181c0070b84030701400329010034444208140030f44200c00b903101441f0641c0c0100881140040c80348101d56083d1500c0780c0d01c0620403000c035000e8100d40c000d000401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 870529847 1250 870528597 870528601
    0x40e01090506150108040f061e09140c030309011e051603080108122a010e0a0807060501090207050a060209030c0603010e0f01080d120e0f01050c040303081e070c140105 74
    0x2040204145100712041c0380e03e541120741e66001521100740039107000d00991226440000007908070313800301c009100c80e4a420041040188545002c2d907400c100c084400140e94003400e400c486040040e0795111204078042c6041c841d1410008011140c1000513a030a16680111a000c3c14001e808488a41c2404401c205900c0c5803420043c2c03070080c0030b20914280344512180d14221641c1c0308191032a80c0400c00c3c2050400680d840407100003a0703145911080c035507841c04110000c6100b00070f105d0a0070f1040400076141d08107420030004550050f402401003d0040200d4400540045200d81015900182c01601c6400350380c00300785050241000b55070070880002c00810110210310210f031151400c402d030400b050381c840241c1502e41080403600c40c00726102c0c01046030300515a4108100c0407110400b1640b4860030103200c2825074205440d008500240080c041c002e059100c0d140543c80504042d01100f05840c9201c2c444002c08001c1a41d4208032107840305204000e41c14241c402d0310351540c00203005078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 870531097 1250 870529847 870529853
    0x2041503050d0903120309031701091a030105040503092205040c0504051303091403031309050906150102031606021204080c0c190e06120714040f02031302010e040e0109 74
    0x100014081034030706200e44452100b00910905010058990082c440304e075103031440d10141c0191440c070b807048080c810203486040e6107030640c8284d80c0c02042104e401013400c2c03841e01035151020494106c468020b03418401004041440001142d00b00c040c01d445031402c0d8606940b0408251040c214100708540c1484280f2040c0401016180c1c1070340c0086900308502e0b00d88c85107800e400303401c40c840213012030034651040110310450031406100103c080e0a9916010b840c2035a40c84006040e0400000c10387c0d94410301030f14440402001c4c4e88203e4800702030401d0040007002039600e01a0588035900030f010950100304001c10307501030f00d4800b8448241d840309410f00b0301d414592034000304060899445030540d24000303480d0829030b811000c00e41d03180c5000401c0c140341c1e40c1d0100c008000c00c81e503004200c4482c0343e4000101004100000e0100c211110340503c510010441640c04041480748068018414807046240010740680c2d41942401e0584030500310303802007400780c06003ca540c405541703072804090038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 870532347 1250 870531097 870531131
    0x2060a320d1820010903050a1b083705100b01020d0318020f28080c060403080a03090615090510080609070b160b091014011802090d0204 60
    0x71520510148120900002d588000c0112001c02410202403a4005983c54140d031141c0d04625030185000c2c44c00765203a4a500d86001f0341e100b8116140082248040b442c03030104040e0070003a108078405002142441c201b070303a0f50085140100c40d4008003001690ba4003501c0203c2008035603038403005458141c1c981800c04c030000c03c1103941d41405801003006185110303100c1c1c401c0024001890403a00f1881c01c1c181c00344803600b005074007040d40003c1c03038011940c5680d031000700c00c1560401c914007180c00340c1d003040d01c0e980c2442c001e59200390181c001480180006510a01170390303400c800741d140014441200d400c101c800f038401d010f050700f0350019000d004078071450680c001034424408400121400303070361200350301da94050071070f04a80590064241402400301c81001403c0020f051100040c03911210780341c0d030f04041010b0310b03544016400700e8443d4001d14154025240c3d2a803901d190382c01c4a61501804202081d0145040c1c00c00b0f99002684248650727840840703680300c640280040100c09003c4c50035001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 870533597 1250 870532347 870532357
    0x91e060d050a18210201020306181f0e160804020d062310080c100207060819050c030a1404030f05070204061a1e03070c11040207051507090801060302060a32 69
    0x15480c1304000c14441402d0050089034007800c00039004482c03010900030344005044d00074000c400c0070140c0001c50552030351485030805c05020f2010011902e8100002d00f114001041d03081101400035500400c8096950303020761725503003900000040303514401d4841407075090040700b140d440141c01103010301040d9280040c9100540b00c0c003004035101107401e601000700400d00c5802013001039110b03800c02d00c9481d1143e025950059030a82d2800680810311805205881c0c0071100c010240801000b005811f500c0d0b406171304680424214603c0250801340c5009040301c280c1102c1e4400e001000820804546843c0d0201c4000c0200c01a0701c0e00d00501c0500c01000b680c012a07883c0d01030000310901608110010702180d0003081c2c80d89600407940443d90710200c2c1d02c4101021194440e50900c61040403940c00d0108044040030a08481aa031a10030301c02307003081005420101803030380b50030300600050300c0c3c020440364801c0182c1058203d40c842400801c000b032403100510b03400402c0c0703280c008d8001c00810000e80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 870534847 1250 870533597 870533633
    0x91e010b0f0904080a0f110109060b040c050c121606050f1602060f0604090c0314071707060c112103041818110102120708091e060d050a18 61
    0x3001c0078010a0401ca9900d000ba580540740d1401081001446400303800c08072035035403c43c2004807028022006140c21511900c07015030b0302d6610f07222084114035080c0708800380c0150504005040c2409000301c1950f66040d40c031042c03403515000501518800451400410302070303001505001614103400c520041b10750a442d511080094182800d15590000c80c0c4980300f1941d01848054039a9045c04020180c82d28540a40c1d82d0b0195920100205440d07139011030b610805640244450351821454015280c1090380c0340e01d858221751028413906070700800101e009038000c1e0034240c11921100000310303241d00400903003124144a4040140d01d080c0070020304220b5402540700c0d04c25a03600318000043e00c01e2007010645a019029195001992510543d500c011041c811034088031035440741c80e0b4441d40048400d5469140101d840071052501404484201c0449042006c08000660110740103000d400d0052a0954454001401c0c041295101d0304400c821041c0c0d240712400c450500c201e11648001207e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 870536097 1250 870534847 870534859
    0x31305010305061e061c1e11040b0706020c031c0e010b0d0308070c0b010f1a0c03070b04060212070e0f09060a090e15011d1005011205091e010b 63
    0x21a9800380c0320312481418080c0807a4104250152411410120307004416480b101c24002c9281c030414460b03410b0320781401c4003400100146048000c15a0001c0c095802e130905081004a80c0040c50f4981a1421960103402c0070343c440c829031408101a0007002c402145500c0080750b204228410f24072000501e0042c02e9003080444200500d0a00340c440844266400001106d9000f0000c1d1140700d030641e20020f00c1c40c2c036202240c465565540100d00a03400040301044c0010113200c404030359074100c1c0503d09031001c954a0020a83c54640d1280102040540124800ca0000c0c040c8005901241c0080c600051402400e1404a038082e1006017442c0055000b82c2d0300f503140c2d15242c1001580315015460082406041c10b00d4401c10b00090041043c0d2000036000324203041b0491030a0418003030291210001100140c0c055903240a034588008101d0720b0607500c0d0880030032180e6007021036884a0081c22101240c903690342c0d11100c1c0740840f0304501001140c8420380800101301d040d0300003107226100b01c034070b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 870537347 1250 870536097 870536099
    0x90604170c330f1003020d05010e070f210c060c02151909050306040b04060b04240501170f07030c0c0b040c03020405070207031502070c080708010218150a0c060209120313 75
    0x11083c0c0b16400c80d501c54102c001004280058a072001445140d10f11030b000204e8a620104041c50502030664400b1000344130704c0c1da06000861038040302490301e8500e5007884400071701d80e84644540004034814001404141d48050041d501c1e2406448000d842060029994a2094100301e40b42c50b121a007404c0020041e060109182c0b42c0030076650b0159800051480745603d0300c0c0c1b10b90004110140003181d10039500e0741c454442d1542154018805094110420b45003440e010000d0074500c049011020441c00c1c080c1003040c01c070301602c0715642118172845c0005941614100a60b003186414030050306007030305c0104000411100e0190402034a00c207036030034082c545501c0d900740da40e2080780c0402000d901c90960b0410100881380e0280c90618007600d00c18440303e545409080c00d20b010307074204011a940000340310000030a40588c0c681e00d5041500e2221a044028090260902603681c00c882040419482413061286079010350701d1240d0001e0042000e1120464401d6507a0702800081e0550020610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 870538597 1250 870537347 870537361
    0xa050304081606020d0f0302091008010305010b0f0901060e01140c0a030e061603030e0304090615020d170a1505090a020705070911030c0a020708011a0108090604170c33 74
    0x4070b000c0031108207800504040816010544004141c4124a42099801e0150410304d41e2044200084101c16443e041442c1d4111300f000c07400d5800c400116401a0106034441240391920310049044030a0380c0342c090a002c240000407201d160801450318440c0101151003031030780102013100d4400d28420b448100003d1044401e04c0000c0c061034815000c2c201440c4c0c0301c030002c82e0203900700e19002d000720800c0e40d103401e0b03d4603a407000319000380d000201e1260140312200100f42c1c0401c0000c00c18003050501204103d2451a80441e605d070040c0802c09407034544903c01c031020001d459903005010010001042440c05a4a00d00290458003060724288200100025803e40d1881821485103080300c845145660b204010350542d844000078804510908100054514082c1b01e81016040010750300c0744207540380000140b0b4050302405009140d08210144400255511008040380c609040303819128058510030a0405042d4060a042c1c081c0c20b03003034410401141004080912001c0715042110f4071881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870539847 1250 870538597 870538633
    0x72001110708030a051309060902040f0803030f130201050904050c270a031b0803160b060306091510051c06181203021804090f0b07020a03020a1407080a05030408 71
    0x1204003030300c0b81c00030004d810086100d000208080386180c001d061942d9a1910781c0e404885442d4880500685d01180c2442040c0b070580c1c2202c02082500c0096065091824000d5543c24001d004402040741002d102e00459005005890f080d843c014000c01c043c0c50402c6084000303500800c1d07212980d01d101e001d4080303400d030f4082c3c4125038004040c04408c8418210380d035202d010100c0414242c454081d40c0f9001400d0b00e400c1004111521101000b400341d40042e180888101034068803062090304010104032110600042e01604201920318440d00b0307031209004282030003060340080341c01488900f00c0c585a90070031068424043d00c21036003000801d01c0c030001603000d5942040000e10035280b401c101d00d0346d90312030b4010700381d09581084000c040c081c40ca00050211000c100040310105407002e600c41c240075078211300560143c814005003001c441e403a50000d4981307141000080c62660a401201d540b100f00304000300150200c0700032101180d07070900303205a480d0028450800148128170000c04000703581c5c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870541097 1250 870539847 870539849
    0x90812190e06010e04050304030803010b040504110304020102030720030706050c100b03151f0303120f1509021303080c0a1202030f0a111006060507111c02090c0720011107 75
    0x201e014001c26420012000415a009801507400c0d1000384004804187e000d0021402000c80b50a0240c1e2945030505110076a0007078810076101c500280208000340c2d80100454001e2a4010a05103001401c00b0f200e0714120f80000b4a15010f104100c40400c185e41c1000042204a030084101c4d9003c1d40f810045100b40d44484480c80e030503030810003404040c41e8100042640041c1403820341d02891030300f48a0148543e00d9a40150001444200d2826003032040303103d031034490440e5070014480c8000341031001c0c46d0345080307106411f4195800540800d241c58200082d0300503503440424995a0352140f4200c03030352400a80300c265202d192030b00c891190140004102c0b00c0018003082c1403820144141d00030758004d0101680382e48c013405071300b202c4200205284130305030240641d5150651244035070f08100300c0c100ca8200b416801380152452030001c1b81c480c038006050b440c0e41159580010755844c01420f8403406501e00040a110000044080c0007144480315001e1000030303600d10807030800d04a16284d907070744c103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870542347 1250 870541097 870541121
    0xe130609020d0902011704031e050d0c1e020f1e0a0204020d09021207060e0906040914101415060307050d1404030e0103050f0a2d02030f06010c051f09081219 69
    0x9c12031704c0031700b09080c600e01309503110703c141045402c1070700001d00c08068030321400000c3e0009098a40f4040d90880d9042c01d1100760040b440100b2020040c510074507030310041c3e8440000c011030b0580100c29900401c100c030031501a400340041d5201c100c0c8122070009801e14040491082d1000201260509800a01c441c00c4a81c180d4840d0416107040c82030252000d0084c10031600130307860300c40000c04030305000222000c04070a0300040c800000028500d0044901b000301c00610100d990050014a083c00c1c0014006102c0c101c030f8141c0d90791604101614103100c1c141008400354142407020744002000d480c0d0a2017240203485559110100304011822140c0c1200d182950201140214440003e070343c0c441c070510440002c80043c4580346030a046109000c008404011680020800c06040a031401d6550410402e080505002c00143d80c3c0c0c5442c0c9034486260241e902251410303a0a41e149078003d4802150003c406035650111100c07444003e200440c0d0100c2d5480500e8101c03850a07505102d04c00c14400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870543597 1250 870542347 870542357
    0xd050304030516021c050d20120c0309031204030b070c0f060c020c030115080f1f0203060303070c060e090106050f04032909061005100e130609020d090201170403 71
    0x9540b900003449140f15400340e8011180d0078000d5a8185c11074004000c2c00e026400034030020300444001041c1c41300b546110403141816002c008840540001c0700010580e081d07085c144c8030301038181103c2c0343d405804807440c0c0c5445081804061800880b00410540b80143e259100c1039455107001e8425280744000200f02c1003a11a2003008540290310010000d070141c4107031446079030395000081c00c0d14040d400c045801e42c1040d80c10000203004020b002c100a107010007900d00c82050403600b0354864100e0703182c5001c941d00040007905907941032003114041c0c4d600a8a00000c5916510b00500c0b0b1201b001215010f07001c21400410b0a42c021816125082040200313940381a045544810030501c1c0e40b810718450002940c00f05040c284000e4085100d042d0032401082c26113000301581d004446258040c0d8080c8150203c0303c0c1c2102e0344040f01c600ba840040d504904040e000e0340c0c00c0001480e050780090405c52010492044050340364104e1021107000340d8410003407151283c002580c445d0180d9000700498 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870544847 1250 870543597 870543607
    0x2030c0d2a1a0c0106150306080f0109030c1e02181e06031c0c08070b06030613020a05220f02030a1a0a030209040c08030c010b1c170c16080307050d0503040305 70
    0x1c9119004002c110050f1001241581e86c590b100f08070000c0c5a0360580100c0e8a07444c003804400c0c8104811540c0341620300080c0701e00d044c0c0391000740201421240183c56540b68040d070b00c0c61707810308103036040c4550f07070240c08000402d03045a92400d01c80025100d16400020380d45000325210701050407a401400700602030010380c0d8491100105620204442000740203e5100d1007010910032000741240d280201558101450003800301420325030f0044c01c2065249480e5100000340e1140b140800c1500d00954006043d02c08441c0d160b8080b40301010b110f0708090030060811b1a10146401644c0201070782201400142d00d03c203c901e6101464050580e04a001108200050301d444000b060b000350060408003089602d84030201d0460b803000b50341c032030160344a281658581c2440505400e00c401241080c0d14503404d0f640d145036451004040f00e169000c0041003240c00324100f40400741d182488154440100c9940d50003690301c9401c110f42c16112405841107141da45402901101e200307941c142d036902e2a207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870546097 1250 870544847 870544889
    0x306062503091205070e1e0412090b040605040b0304021203031602010c09050312031305150403090e0f060d03020c0402040f05120109050706052524110d020702030c0d2a 74
    0x3c40000340f030012a504c0c01a05805000c003207c00c3c4500070f0740684080b840707007922448080d017880c00540c07055415060821041020b241d101003510107649082c20030582d81e4071140001510100d02c40c0d0a035405020000c103003c1c06082c681132080700c5806da600284925140464261150380052041507010b400c4111400490f02505000b190b120a052004581201c0f0503111503183ca10305d031900c03001c04038420060005140d007040d000b0380145440050603039580b03031040d4800d8070702c403010307101c01d0043c54034804a40c01c160080c0b02c510f50284000e00215240e9640700d0022188003454400c4501609005130442d61440c4103018000210380c000d8020202c15141210440782540007044441194048078582504801c1d07a920490100d4014910901d40ca0218040e5000c44000d010341110107902c1d16014030404100802915000a8441c10050300ca45e50360000c01d040088100076190700007111070b1074204000c442c03c0d031802c42c400d1070781079040301c103c04010145a001c00c6010710018918045416211 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870547347 1250 870546097 870546119
    0x4020a1205040c0e01030308040308013203070306051009050633120a0e0d03060e011809050303130510180809010c0c180c051e030606250309120507 65
    0x10b103d14269908140c0d96180d00c012180300b038200714001900d4509110506602a030180d01601040088103501102c1105040e8960400c030054602c071000e40002450300d0350240700040045070000c0c401c1c059131814145110f0208298040c002d1240d00c0c003030100e8202e0070104804032690b26000802c0c11010301c0c8125070307049509800410102c08504200c4041171049a9070b8150140008000c04500d02098650325410702608032498001c240c1340c0304003000301201802030b044c11600740622404c00f0303141d4050042c001c0d00002d0009845880000240711000c0c565850b4240d4040c0641c0c01c0c0c41c0ea81003902501c07020799a030703401d1404504254485040100344d0b07070401449042c0050608400301a00e99464446c409075682c403043da104850300c1d403542e41000310700501c0791004183c40c0084ca403410300a00e05464444004072200c0007040440042d4030382d11400122504030140d900c5900c402d007403001201124940003041280050502c400004902420700243c403060355000c400743c00100c0c03c0149040c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870548597 1250 870547347 870547351
    0x19120603051f022119022208031e09010201020409291e060a05190c021c032c0a0306061a0f03150a091a0907051c0f09060f09020a0504020a1205 63
    0x10980660280d9400f02000744020a400c0003a1400e12074040203007d9119070818042e030283c801600100250020b403400c10386004042c181c243c0c0b070300391101000310040b030082c0115000645070700d20b42039484071510660b0741d0103000c1c11101c0000a02c1c4038044010b00c50181c187c1041210b525a0400d8003c5031031401c0409090341c00500d1a06504000800c05c1c0c0320301c20003014070f011000c82d103100c0c1008203506011415050f4500840c5004d80241400c1d5030040c00c502e640c0e80d020304030b4100c04481c584e90a150300c0d1541078003400246000e2113503447e414501c00a042c035220f1015500246e40202c020403603c07100380e90a4200e102c48050071947c7d0320b004004014600408d0692240d07040501007451101485118019244148074080d007003007000501c4504039010786a0800e000c0140a07040c4030b0036501000311600c4642c0d10022448c1c0400d4003042c009060b85600090106090007800c02088940d035100b0b4540f640201c17446190b466807501400100c0c4105071a20340040c1d0005900c0100158a40003a9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870549847 1250 870548597 870548611
    0x1090c080d020325020d0f11100f1809021b0f07030f0605040c170708062203140705011e2d0e0c03010614010215010b19120603051f0221 60
    0xc02e901c0c4250340054600070f0640002c49408010342c0010b408e0045103014200701810680c2c03541448403c01c44003501ca10b860182d01810041e22444c11100c4402e8240744c8002050001d00540d20780903440c0e07203d089200c100011011921401c600f80c50081e1000131440102c94110110024488103a01c071000a0140240183e9220006001c0024044910303410900150070700405070201a040002d1242040300c00b4000045c400366002101030701501c520820a202e6602d030501032060f00c99403038980841e00519502034015480c1c4400342c040407074500e980109000002ca03080043c60300c90300051000c0f000010342c6000d25202c5c004012040742d8203904c1801c4602c01c085c1214030140c010b40020342900d903035400044c02240307850101d100d81c0d41c041040303c8882e643c0d07120040481d0304042c0c0d418200e000e011081c0c0042c0090010403090140501036030b00000782c40030401d001154482c100181e075802241c8041090080411500f09288024800d48154414411429500c4003114146c0741c3d03031f01c0025003c0303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870551097 1250 870549847 870549907
    0x2030a0231051210050915010806010501200d0e01020c04090c09060e0108030904150e09150705040e040609020a08160312050408031b071701090c080d0203 68
    0xe008000c03500090202046025618209421030000300d144085103900c014041c401d00c42c03800310b100d10041048240384c680d041c400140b55840050741454525107000c21180f0301c0d0741d8000416094004144181039940a8039503400ba41e2110720b141c2c10540361101c844489400072020940c895100305050410090148111600d840400300000e0480d11540000c4034000040041000b0f0b28409018840080c4416160360015615204a8584a1150064151081e541c1c0c0e090a00f0315000200d20b5000380454684141c1c1500c0c04445c90340e03485400000700c000c01e41164002034242d03403059048a00b564050115180b250f112039941e040036103640003080380d01c14462080032422035001c0004410910b0a2403003801c01500d10b00784a4100d950100044e810000b0800051005880000031240f40e1910301c000c5480c1052086101410b100300303900801d070801d0552800001c142d50540000d10380c42d000301c4503000000c2c1d8580702d0a541d6005c0840020150300203101c52282d4041c8010745042031b80d40c00c01c072 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870552347 1250 870551097 870551107
    0x1c0302030a0e220f18030f0c06060f0801020306010e100c020f0d06050709140a060905060714030307050705100903020a2603010609150207060813061808270d0602030a02 74
    0x3a100000f1440b240c58408940e500802103040d80c3c42d0007600e01d40c9400800f24405070650b0703240100407840c08404c2c40148003600307004100300109607200100034602c0216241501d900c88030a98040c0d40181d64450019034225808161460000002109109180c43e4442d205a0607400e2004c0c03003800742e0046500401100740b80c1d0110340c07140941e51040d125a9618041c5900307104d044020f00049600c00340c001d883c2000103000c2d0301e401041030419900700311801621428030341341185017006007801d01c064600002c8248122140c121000c1c1c4883c1d131154055038000240b50003408100c41c00f4407000b81c0164000c030710302d00124140c400d03a0950b0380700001c110180103040c1440401503602c06ea000500250500b042040399014480107100f140310ba52002d456454a80f1100a02c010f4000d406201b0030740c1c00260700310800c0056881132030004001c3d8110780c2d01e400c160810001903000014800059805040c401d00b84d52982ca0b80d01c5801c02c0024a8160002c440e901c5000c000c1d0002080d24852390341c2004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870553597 1250 870552347 870552379
    0x204180506102a03020c12121b0a0c0e0720060a02030705130b03010f09021c0209130513140a0b0c071a0405010e010f0b010e060f040b16021c0302030a0e 67
    0xa0200f5800b40280c00800a000058040c0141c191280c04409115040030440040001a44e42105d00d9507101c0040007581c000004030341c500b0001c1c0e02d00c1c01008862403140c00611140714190030b51040c002d0340c45040c0d1b10300c1e880c01304039210448044994400c0c0c01410008121280a90245404c411203103080ca040007400403260390000aa5042107990000100040042d500481c0c41d0384060600b41c030f410760821030b030720080c801c0a101c0c000c0305030009a00840c01d81ca9a441c1c01d85020162028071105205a042800c1e080da40c0d00142d10040e02d0004e164491002016000074040f81b100f50701c01140710076603071b500300140100d411050707080b1000b03505407450305c0b0240840c050b0f0074047c41c000d40000650b040d043c41070350708580c081c2890100c018104090480144e801c540c0f141d80e9042c1c140c803015500c2e02c11030002c141c2d500c42c030b4200403a409070100c0c4c1c4500400402d160840414401c1c2c4010310800ca00054610445845950041c0182c0c020442040c041d440780403603d1311300d07001808480380748003401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870554847 1250 870553597 870553667
    0x2060a0315030f022704110127090b06040b0f030910060617070813030305180307080d0608032b0605120d031112011e1206020418050610 60
    0x1034400e540b21100200d0705000d624044071003c010301005c0ca4034100c420250451a48007030801800500f01740071403044c03180346900411210021020b0000d449030b10802402c0d0328110000ca600a0481d030619008401e00c090408a045031b040d01c56000303045061504912119085610041c519980c50054900f10300b2030340010b025903c0603045607110031000b0038084600300b0400d90007c1035482084544000c3c00070003604000f1614842c0c0e01480d011039a0f950340b00d84000c402152003192202484009808014002c2c0c0340003400060304005428031802e5a5450740755664014101d003000400007406880a01100f44000517800c0e010445021408030782d2540040d034082c0000b003115015402c42540302c0c0c2819418401c07500c41005131140309080120100b00018070601c14024003640c4402e4140030314110020915410082200b80c02c0144111284d19010300650080e1054546110402e90038490200c841d001e032034810784003e011030211040240c01204d10b4030f130315550198220070a2082c009000c0c811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870556097 1250 870554847 870554849
    0x3021212063a060b100e06072108040b0c03010b0a05092d100512040201030b01020f060702031c0e0d080a0207170304022b02040507140307090e1503060402060a0315 72
    0x500b00c007100b8030030340341440750664000c02c000d50b10521038280507511080d000341e003000505009450407900c50f202e5241030030031351a40030986c6000b0700560100c00072050340080e42c24812031142a440720390345c44038000342401d40401e0280c44403820062100100c82c6120b04040d181d43c400003001d09501e41000d00c020a54540d10b600012445046881074204d5824130b00703802119140325141c1140340c004225036000314000c018200904141d10707a4404d840c1c0e43c0c42040483c401d104684151703001401c103140d02a42d00d07030184403030000e44215411458000c8502c2d10070038180d00880809409071481c1c080040705c0b0304d41c0060480b010b90740d00340010008504c60f400d903031055401c64801c603a40e03814140100500e184080018518080528909041c1110180541900c5503030580f0089000d8071000819204d0307540316281d050800c0c00200c10410350390350220b00c650403103001d20780c030000e9a04d40500600300c084540c10001d41540c4518003190050501c20000d000040251400142c0c15440007945400001070b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870557347 1250 870556097 870556189
    0x2031314163516060e15090a081f0501060305160f1b03110606060f07110a05041406010e0906010c0b191103040c1d010501030b030a0203030d090302121206 68
    0xc070f1440703603001001240749400750100d410043c100d030722101c1c0003403596800f922407501800c10100310000365172501e52030356002c2d14021081c2c0d0281c400d44004490850000c0c000c000380c00b070030b11000150f076501034403c090050000c04566a070102a184095a09080440f040001c1207000105010724400c0710588400722032096959840390a105000c2625040c1c0140c4840d00c610300410030404412411002c6414030b0742d0006281c0c1c84011410005129101143d02007a009820f210345407008035903030b036a918491341c2c1c00d0305ca07504140c0030301c1c1c00c5c0044a14115a807a000c181c041111801241381500055485039031001c07a89040390140501405843d9000d020040c40940030051208001e85485000060088151020801c9440f00c51210382510103105850525503a1150707144075440900401d0440340d0050100c030b90f14148071440707100902d240704058006000303c40000030701031503d0b0200c583c40b001418170018203485c0d0130204500072010b034044a6114001c0d400002804002c4200564202c0c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870558597 1250 870557347 870557353
    0x70503061806090102030114011d040501060309051005010506031f030c06050307091a0a052203050f0c0909370b01180b0d110112020313141635 63
    0x710326003000e441c0c004040c10b400007a900500043c0106054490030402c1c468091030701030365955040e00703060180c80c507180845401c14240800841d405416401c42030704030784500200c608459281c0600340c201d800c01e00400398040020004100c00d1140c03c00c0500c6015600004a010103035a80d50318512802240e000002040001c8100030599030015030f408006c007510703414503006a00c0c5942560300c0e0b1095507100420321002055892558950b4002e00001004030a2071400b035907120704180d0351f10688000d012280d0705c00d0507500c0d41142047c07070405001708407900003071a6030011001103201030340484640c101d420058035200d05003140c80c41241e00c4034034019452040c0b5075040110707680180c181380d51031030140e500300410609107444507142d41020030781005800d41443c500d070004980400e4104001e4034002d0000c42032103000b4075011980154140315003011291502800c1c9081e0f128072402550301f4600ca6a03c108000842106420322a44000039015440000c424026240020240d00800304154 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870559847 1250 870558597 870558631
    0xc0118060b030601080a12050315060a02070f060239030d05032202010c061512060522050303043804150501080309121005191b05041202010207050306 66
    0x1060500000740034110210140c401b000c0e0645482481144c00d0003504100440000080d4185e504030041c203441d408000d03da00d645290b1035400960f2560740f402055110010300c180040e040c0e0001941d0310301d1410120203c44075400110502689210b00c042070340800810040e240a242d03000d1154035000241c9817151a128108504030031183c0c08041900130042c5c030b6003224078004d0307070b0040000409a40d0004011032001681914401700d0b200c01d512401d540c40c4071080000c1048030380c1d00300d6480b9040d44126a004908401b080c64040340b0080d002620b1a041080403178049100001301c051490580c000044403900d0260424440e414a15002d100e5541110305000c20401c0204400c1500040a40c040c0807650600740c1894030380c0306144010f031240440c1c1d07c8018403008103002e40e003410708946034100401c1c07605818403103240c1960b40351540403503d0180e001c50780c080c10700006004123401d551010b0403d03003072051002d4040e030003060030b0f811340c40340301780c0041c080d41c0030413403140b20360300350355940c2159 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870561097 1250 870559847 870559849
    0x601120c0504180f050703140307110402030114010f090b040f0824130c030b0a050709080a0b060103052a1c27030512090109020f010c020a0302060c0118060b 69
    0x840d5504501e00c41c604011600c00c1c0c07003407042080e40b4520b402c42d007802c1444086240407803820200c0d40c40100001d2881e00013030740052005c409000b4990060428a4503000060200b104900c424000c0403000d0310103e0290481c0d5201c2d449445030fa25582c10429665501c81c00945500d400c0303030380f02c10010b108080c000d01c01c0c02024040390400c00ca0456030440b002419035200b10642c00c0c001c0200345a42c9065034080180042c0000010045d80c00403020282070510181102c09480111417074030200309456000550000001100a00d203a00b02c255100703683c9500004401508010f0718640d00d00048000721441c03460081e40d0711281d07865010141e9a80c4241403442202e000f0a03181401d4890302d0411204145001000d03031000d900c0150003d1031010005107410b484501510300094140b40e0a0810808003078815440354411500031a81c0200d10034070507004480c000300790100203411101910b81000142440006071028414200000ca032150401d502e62030b0031240c5070002e6911540f035503808101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870562347 1250 870561097 870561113
    0x18080a12080402090a0b040f091a011203091401030605061909090b03071401030905030c1b090106170c0c0d0203090a09090308130201121122050a030311010905060112 73
    0x540e44080c1050060391816400080740388100070008081e8584807440b807051540c07150b0100e00030790f6078240108010b22172410050001c0d041454160523604040001140d0305000c07103510000e90781e1540e500c032022811f083e8581d40f82000007421505054036614040b8240e07440750080c1203a54104c42d611040e0300f5910200400e05511984103549662600c1083c507001c0d20041074440580382e100d040a8260801440100d0080c0030420001e00b0324040451544442007000c03c181000040607096603145481c2c1500300b000e4554288078040104803441e0300c045201039100200b40d070048018050034140841c4407145418106440003210040c1c20004501d07040307262a4905101800452404010402281d9006815010003800710038200064103105011a849004800c4c03500b60080ca0500c50003a0800c046941c80c1c0000304110424200040190520b04c070840f50001200c000400700308115144d5203003500c02d001000d00750740c0295202e280305400315000704103d50080c030302c42064000150340c5040040c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870563597 1250 870562347 870562373
    0x1912060e0915010f0f17251d0c03040609170a091802161e020a0605030f130b06240301170d021501031707230c010216031218080a 57
    0x1144c146600b8003440740e4008250312100740c0d41c0c0800f00c2d803480612141942d10300700014541448111104c0c1d102e0000740190385a10080b142600f00030055001d5010300d01c4184042250545080d032400e00014010503680d8000b9074245002d86440710654034200320004507980503400305408521442420407820340448030075a008680c01c0e0b01141800105880c1c0707a001100c0d54009407070503990300c07800700803504801c220103030f55507000300f1103086942d40d610050201d410841e4030020b80134901c80000c40505d0502940b0304403660100c50086955284002c106004500c0c1c031206808065a0180c401d00c40c1c0340070001d50180504100c0d402c0c61001800e1501e140171004109a01150440402003440c480245801c60640b036200101110700e0000603038918039030044083c0a000f2000078900c8415220100e41030b00750501c0d040054a07041c000c00c000699483c0d480d2145075001050b000001c00100301246200b039070100c01342ca4481c09103078083e025450203075078030740100301240c1102900d60100294516400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870564847 1250 870563597 870563609
    0x7050f07061106100b1c0c0c03030f02030402031c11030d0608070f0b0d09140316020103060f0e1906150e030d0e01050313060b060a050c0c010201021912060e091501 72
    0xa031868004c036500c804000920451040b0400070442081c1c17428011601610322081d40d10070005802c540710300500808800b2001d0300400d00c4c0c404100752040300e030b0080301d104940144c000e00952041d0340000c0450320f0707005042000c10a20703000c5048140400d100804000d0400c10010501c2d50604c0303d001c1c2004401d601025070051242c100304204070310355050b514404040707100020410245d080c000410401c921107606103010005801c813030f00c4069184001494004c1ea400c010b03294a80755441c0d0f004519014003004c1048c00c3c40000c0583c0c1d0b0104c402c0700320381141d40001c1382c000e0b0754510f840e83c000e640050b803001050f84c4049080c2142010401c2e0000c180103441d00600d141094000030740f042c48044c00b000f800d103030300402110034030086401210014070080c1000b0395a0f1850400103117150441d60844010380607062070103a242d031050080e101d04015000c00b02001d00c01000094550b400319a860030b503801d84440c000900041d043c1c01143c442c20801000d081e041d98030304020201100160841c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870566097 1250 870564847 870564853
    0x9090c030b070c050d0c03020705090408030a15080a150605150c01110307090b030403021c0e03120405011718100e0c01112d0703080a1b1703040807050f070611 70
    0xc0010480c00140c0045d5040d55050122440105040c00c0f070a0a599411442d0002c04200c244002c0000c908002e502c200150131040202030305881c881040e03405030340300b04d0030710758040300301c80300401c48506440400b000344107000500207540e100415200e003484d08501c0c0c035103000803030044a0311100b8040d4000104490404614600c2d110f140030f01030a0340b0b4006c001c0150400b10005040600810003440300c010318050546e07940d1003044008292001a44150340680a50440d01180641e81d0058500740c60f0161292508820141c01c203c110b45002000e2000c0e0b220100380c0000081028860340d03800003428070b00450388a40c0f440b0851b04c1d110a03c07400c24100b00c0b4050541c20217180100f1030240c0c011503c10204442070040780140355005013201c450002c1d005240c000820001c840c001030000000b66154442c2c800500c03003204d601e4010f41600680326126006c0407204c90301e80c000066038814800c016441c00c3c050141c440f80c0c504440c0940340c0c04207602000d003d00030660404c0c2c90103500300300d100007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870567347 1250 870566097 870566117
    0xe0712020c10020c030c07140a0b180103020a05070b09010501050906030604030c0314130b030105191a36120c01020a02041a1f0f1e081009090c030b07 66
    0x70040e500e100b0903090b068155400304075402000014005c40d802241d10004a40243d07440d505000400103411020605c1511a044c00061180c4058107a80441048031003041d140002040150003035031100b000314041003030800101000410003042c05014102d1400001410340c100030038030402c000c2c041c184600c05d501070010040026031200f000c41c40030341d051814003000402228014018096030722101c002e4440c403900401c00d00c281201542c1242c00c2203501d001c94442170a028054060640590441195074004004044241c800200860420000511105d44c0f42c0d6a14050040c13900e40d0b001250312604080c62000d107031040c8080c00a852107005411088244070000c5c0d41c810000000900542d29000311024550002405c0700700e00501402c60098480c000f218081884500003011000c40d10400d0700640c2d540c13081c2c034900c502c80d03906451030590f170b54910000d80c1c4101000300343c188181c07802103020808816900612001078401d11074860031500310714244140100090160f4104010516 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870568597 1250 870567347 870567367
    0x604080607022a0d020f060c030909070c020a03030c0320030304060c051c050a020c0a050a050610050904020409060b0a0803040e06060a0503040b0a0204230f0907020d030b040b0a0e071202 82
    0x2041032950b0f50115292204040d9604c0442c000e0038042c41d0311030b400704020a0f07907100c1d440c0c04002000010400c17500603100d0790b1040c2c015951030811040294002182c11001d10001e4001c51a0900c3d09000713042030302c110124455003a0a10300b0111803001d50350808401d10003000300a0081050454032820f00b0740c10108000b9020001c0650000103c0101d5201c002141070302c94258101d03a02c0b0740180341a900701c810176003802640c444001408940500c00c1e240041ca607644103c000303c0071340701c00800c00f407095107a07502088060088190281c1d403403035441202644664034a072501000b8510075000d10b0320303540b80041d201c0b207440b4000c21060294104000403c441d41c3c0c000102c9500c2680008510516142d880303c802c024003942d0420503030486545c180180000707080c004100404011900d00d950710700303964248008450151112000350f070001c2c0700d41c2200e5009400141184002034000603079880700344000f6504060700d9000b50703060542d060621050942c0b002076580a2002c0c20829454511091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870569847 1250 870568597 870568663
    0x215010f0b0705102c34090c0c03170106080601080601030f050702060901150b070807031202041d0109140423030d050708010501090303050d0b0607060e1b120c0409030509060408060702 81
    0x90368128958100151b58030b071030032801c6840c0c2c014180307800c02002001c04054028015010000041c0d003c2203c10710303086460b00c0d8648829060741c1003695a500c082d00c03541c00543d00c540f800b50247d418192503045410700d6040503c2802c0c402c040c2c40d4014589401e04000040c2105c0d282602660039404405040c0000240e010031102c01c190302113040369884c1d16505049072814000c0c04c06140d4140001000943c0580c042403040c061440c9203503103856039a031445410211203144d0f2441301000342a40000780416211115031400001040580d41c405076803110315400e6910041007a003501d030350344042c05086036004400c41d02504007801e002c0360b1030781151409482801003050404545845600c000320395181d040603140c142d41d103c030061051807112030a203078640b5850320013100b040d82c802c2d02803491441d0000b4000090004c040141040721404014007018084483c000d405000c2c080109a0b1643c9032800240020320f41c11000e0075890615100090900024400c40c41247d1500d81c4465a045010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870571097 1250 870569847 870569893
    0xb04021e1e01091a09040f0501080a02040e071511150912030405010209090405030c1618020309010905030a0914030303070906030b21010c0215010f0b0705102c 70
    0x14001d00c0410140a001220b40c802d0070f4020740003038540c0e802c0004c01113286001801d0045000c0f00c0611030040010141c2c801c0fa542480717019000c0d4402c12030305001d0304287e4805850b01c1e4040c0c0a884102e52030f4556401e0740a1507018003400540303098151030380d5010a0002100e02501ca0b00c0e90051030131300d010781c0c07941c41034080d685400d1000c1c0040803404018007541140c51620000e0b0421403507141a04140344c82e90407007940502d0078010310075400000c920503c400380685000b2030f071740c1c020305042e50004402500014086407a42d940d440c0030001082d0700300040e08101700e16545400255080940310080780d1200801d060282d8002c2c400d014417660401d00c5401030b541280380009185078003400064880226030311310700049840010a2007400010340080c0f100030296000c07130781c989105000700515a10244201003001280c040309120085802c4002e01c0f0441c002c2040b1200203c014011a0440714021100364284000e100c60309010b826000318000708a02d020090205411440001030004043d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870572347 1250 870571097 870571129
    0x1e0e0603090109051b030d030c050f09060412060b18041e03020c15030925030609020d0803130b1e04170c0f030d060503070f151b0b04021e 61
    0x40300080d00c51400b584140300719600001100e4030f00c06201c09100c10080c900d1101400703802031108950255009004001c050b01450343c810346810140005090260803460385140c0c0114100070006211f400b0404400c0741502840e40051001c0c05c4404000c0800b00808008405803101401c2101003407943c40403040380305c040354040c0c0d00b842103860128203025035009070a80c0025a98940707110200920b0285100b01014021500410205c2d01c416090000002c4074140c000c00c001c4080c80000c42d960440c41241d44044c100c52042c44c0160f8032804150411550a202c90000e52041404d200d083c1d080c0c0e9411944042921202c0c20303424503010b004d014014070240030103000c10310380112a06000c04440841c1d6012042c1c0b440c3e80310340007135540c4075405444008061390609802060614002c03820b94219142005284c1209103024005514a1003504104042c021450340f200041283c000d00c61b654580704810098a0380303030601c10000704a03003086802c030451409400401d40d076240c19034610b6000207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870573597 1250 870572347 870572359
    0xb0703090c03140a05160f090f020c0307061e0501050d060504140a08030907060e010801030b060105070f03020d030f02190e0f032a03030315041a0915011e0e 69
    0x82400c040500d0078490b800240704000340701c007024103032801050200c0110310502c203460030600f00c00c1900a03110f03294001c2e0204903103600d50070001c0551aa010080594000304090300b00160070700c03210b082d07400c0300b0000ea51103601d410480200e00c1030385484040c01d0300171610411040d4106404a8088080400d00030941c0d030b40e0302d01180a000c0066203810f0f48080810880b58000024608500179800c1645c6140e11445601c00110349d5138000d05000d500c03a9010380d2a0b00e001da18546a1266480028100c0c606020341004604042100006660500c80c009d400a140d82d48000400400711410a440040c2340b600c18032131107180707401c5d043c0c0c5205080c9441c581455030040351030008000ca062450503551510407002203540a40c1e0406d48110480b20220344081040350740c070141602c030b200403a001c11035032181d0312008001d850550f000c071081d80152110b40d200c4507100c4010500d2240207a50418500001002500040da0701044220410101440c107002c129000c0c3c0c0040c2483d032200070400c0c8a11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870574847 1250 870573597 870573611
    0x20f0609060c07031d090703060509060301050f06060a0c0804120506090105190e1204150f020f0a12020a050a060501080106050a0506040b070201140d050a0b0603090604030807020f060c04150c0b0703 87
    0x4120752296808200060680581f41021100603006104900c07400f030203807016100041c0d040c030341845824851070550300e41c5401552030208220055111440c2002400a4551108040340e2070350050400303400448d10485420800b400c120f4030f08030005166140680c10b000030450019031070211254040310042340440c028140d203078007504200909003003265200020600103007a4401440010714040136031605503121140c1e000c12611442d89404142903988011030300c900143c100900030504804601c10740e402d056680c0c0d591410600f0301c00f41a1599500c40005001d103c10a01c500c3d00148811514181224607042c040360359405140300341c190341c0101080140c1564001c07883c900e244485007007515134452181c0d03046001880c00303031018030101e40b0b05540c8016505000c42100d010f0700d20b4400810665986980445030003400808080840c06400c1d50522000000c00110340240c0780100100c1e243c0d07003040c1d0001c2c104c080030a122410454200b00020120b28240b400d00d801100b2454085046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870576097 1250 870574847 870574877
    0x12060b0f03150c12040609260306060f12180c030307020310020c010e0a05070608010512060412030f020c0703292217130801020c100b031507020f0609060c0703 70
    0x1401038040305100b04c00003c04000804c04564030035810540b0a000c03034100f40401150541c2001c8950060b41907940c400c1011858610f000700203004103110340d4194510300b00c2d02c40d02c41840d108e01900d03c3c40c236070b842c0c80c0040080d860080c02400640c020030381c02113040c00343e40d4000940d01e40869030300786402640080c0342603100e0029080740388210000012a0b003411403900d01180e0302d0102e80316100008805500210340c500d014038002c148030b00c51030000d00300d640b00c0380c680c00c100000714015401410350307070122554400d0450010740107400100d00501001da195041c5020701e003001a01489040b15541c203000310102c034400010b600110721070384a4140b5007943c61920740e10809500094428200e4426031203c00c40b4040040150614040b030b8015429555203c02c3c2c281d00400c62001c010350005090a001880564024803401000804803001c0c03903002d10800c0b0810b0b038192480001604000300c9820741c50320801c00345800c141580d000b40f00900d0b046284a07024010b01c1801420802307403031914020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870577347 1250 870576097 870576121
    0x2031e07020f1008150406060e12070306060b091323071701030606080c030c01092304023007020606010507020627270402060318060112060b0f0315 65
    0x2c0b0b0540985480e458202d03004014141d4078080720400c2512008642c0c086040c105030003210120b41aa40340c030b00d06080b121007004151841100400d07110322400400001217005402000c0082c800c0403c0ca40c1d0b18404103090041c1030441041142d902030038440044103a68804040f9030503080814412807075501d80110460384529040c00c000c1001403a00e001000f400303d264401c0007220316a004456500c00c0340414543c4074a40c560b103040c0802d281c3c035810055100d0911007064190240380d00d1040c51440c01d000901240c00c29418100b20500f212643d20400b05076100074044108200b050429514007884001d5850200418090400c5008900001151213180581c0e0401c440900d5140c0c225000c5c1d43c05003140f4200081300c84c400c210001380c410444106040d007807102c5040e91190602039480750207108440d4802381c4003468140c0d401c100c03120200014400103001e005112007020395840c080c00c01e4803c1c0d40760f01c40c84134410360b01c8001000050340c000078814021400d917143c844256450100c5008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870578597 1250 870577347 870577369
    0xe010308090a150201290a09050c0f160317250e06030a0903020c0105071502030705190c03260402040905101806060b09010f0c0602070816020406050102031e0702 71
    0x20582800c400940094064008050a5200d0354006d100b0041504d441c2402c0070340c40500075046810b20000703000d00d680b5900260707408030005800500e08402c2154121441e88118202c2d6003800c60484031100301684800880c070950700c100d00c200d400341000090606513012801c0350380d104000e480c8000f482c8a020300c16007045484010000c689030301e040c01000d40a0035050100b03c1c0113001e807040c0401c06c0c0d8043d800fa0350f00c1d80d8210b5805140052450a40c01c000d5101070001e8052160030f000301c100925034100b900b024441031741e441c01b110041034500541080014100360701180506040030340701c0d82c4c820220036441901113030003181c444264101117050000740c40d80504418141001100d401c6442d59440110304d00c904001c00c44139588074040304481c0108041340340000e1a001c0050403142c820a07202013124081c0070300503d4491240c0d1030402d41d41c4645561043c150f94100308509514041c8034070001001e0030f0010314542010bc1803240c549090000a103c5004404140349040d034480e507016403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870579847 1250 870578597 870578609
    0x306010c020607060b090a0c27030b010b0d0e03090907080a09020303160b1602061314060a290a12060618090b01080d0f3204060905010206010e010308090a 68
    0x5075104504c0c10802c0252083c814454003030440c8102054050031503128060062800784d0f605607000d00101e02c49a825040074210148441080902201191130352848600030301c0c03100345140d0381e040700e5880308080c2c2c0c1c0d004c11019000d400c1880518441d881d01e91030079602227130782c2c46d0000140d0340e55003200000b851403c2010350180701c00b02d12803503540c50140d030070504d190258001c600d6607940c005400194810f500402001a005000400c24006c5003034040400c0c2803060300c05401110080d0f04491508408480f10314000340c9404070380b42c10004603040ba10a00a02001118544141c0c0003c074166600c0d5105031101102800c040d5402d0001c50b91294000c1c0c1498180345060803080d401c030802500000c10140c94030000d010000490400c005604c0501c80b031107407203d6071903a42000c0140e41038010b40c060034900400316007155959840210380b148408100b00046501d69003010001810381011f600f000341594413100c014488100960021070440b039100018681e24126100400c1601c11554044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870581097 1250 870579847 870579859
    0x30a050d0503060103060f12060504080d09030305070e090420130203010801060609080a0c0501210905060103050d0212030606071b090b04110406050901030e011503080c070f05150306010c02 83
    0x410081d500034000c501032982603806104c0b040c0c80310a45c0c91081014400c20340d0740800e101000b00041c01582100d64001e0042200608010468001000703840c140b0908030002581e520400c240c807a0031a110407250b04040c1c6030030300d40b403415655490078244622920101015120300140315552007a00c0c04a0f0405403040954403943e5650107140039040c640601000300302e040c2c2001c00c045d0000180140d060380c002c032030020305a02e044019664846041d2030100c643d00001000d00c0d542100d8041ca241031881240241000e61460901c2402d00314151258021500b00c6032480021000540076240c0000088807082c1d55800285001c2da0304c00c00503c0b0000c10040a254000b0700b0011355400b803400d40400b170741c050107030214a1940d054a4850ba006480c04114240309402c200d500c6903220300710396019000000390744012400c1d20b148082c19035000701c800550024940441603014007940000b000c040c011074051900b0140000d0010aa6841c0720003044004000901c1981c826100e444c0d5858001e007034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870582347 1250 870581097 870581113
    0x40618031706220e0c0d020907030b010c08040b0a08070f090303050c07030506010f030c090203061005070c03021f02010609150e09030f0703090929041107140106082415030a05 77
    0x21200a4440103180e48050300030601c05d0300035810100310031603080340d008188030101d41d64504150f00070b142c0086030a0412441c802d000d00040d0000c4010006845801865600c0c4c50320090000d054100040501c1e0401c0303080c0703030200b441035003004087c0203403a410304107203880d100f10709078982c500005940301502910580d4000070b4450300010b421800e8178060b51484046585951011041e07100503550103403c0840b014096003010321500c007405030280b08404001300280e5980002e05688411704045550181900d15000c0654091080307000a151640060100c0b00d0382c43d1003044e2200780d6100b400030f07400c000c100007031120100b40110340800b0056801c964403403460f8140242000c0c103e00400681514000000603200d801c1c902054114015910041021300398005000240c41102d100700940312003030001c0070009001a20701d003800204075000041c030501d0940071034a4140e42d402150300b0342945401e5040510488900b00e58030170011000380c10320b42403103c00b091030320138503400242c81c501030385130 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870583597 1250 870582347 870582409
    0xe010b041a120303010312201f0e061302060f1b0303060a06030510150e030312060405060109061202130b0c0105010e01230f0f06030f040618031706 65
    0x1910603828106039a61002e40a41c2000c0719034034030080c04054190f94510700308960140c0301c0c004402e200c2441d510f88079200c401000501c1d1070f102c50a4150a03014100382c2c142200354020b44508000c074405032000340b44d581040e07601441d400c1c3c10000301030700035600010b00754100d480c010301321542c145080507084080c61521304829180d030000c2e03a42c1880360101d0701d40062201d10a004842c0030395400c02c4402c0e095494054000501c0d50070302022000c0c040801480302042d40c044c409045000f001c46101000d9140641c2008222903005213038a040c004c90710000d0010300d9000381e0b44980e001d00030f00f0040e9135a0030840b240014000b240e025000d824000902060310a8040d040030b0304035610360f42115041e0b41c803034214800d44005034207502003080040054840070310700400c001d42c0e41d21010308201202e1613060081602035000320703003e0008861b00303014042003007014447c0d031001c1203c41221607096902940d00030400c0c0421000d5888004240000c1a0180d03a4205c1c010000402c944007030243c0d003c60b030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870584847 1250 870583597 870583631
    0x109030b13050601140906090103031d01030e030f07020301060515030708100e0114040c030c0c0201180e0124051e0d1d1b030606060406051e040e0405060a110901030e010b04 76
    0x10b80e00503030455007c81e806040c00000c1070b0680398140c0380e030301e012031b510b0342c02001c510800c46240d410161103801c450002030052000301100b0452440090351400746006140c00c0d83c40340d90107140a0307104074140c4d604030311500701541d03040406031401c80c0c0c098a99034503200c80000c40d60028010115000300005410441241c004101142924240a601901e000540444010042d8800881c0511000400662184542c01c00039504003a40c85d010720f40751070550140040980113080000e600d00429507c1041d5501c0b1121884000e00d0018076003290404040c031031880907502c00141c0d01010545400c0c40615400c0019400240104542d03280c12a151442d03441002d06003001d42c943d002101c83c10746007030104845110350809002d141c50145004000c0b81c2560010900040040000e80c001241ca510b040081008000a211040d002c0c106030401e03d081030405040b0000540ca042c051312070781e002e80d00954400c1442400c0020b01c03007807000d000d00e000d440081c0d1010b82c020b00d80004199500c1c185c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870586097 1250 870584847 870584879
    0x10e03120f060d0503090d060204030b0c040315022a0a0516140105030618090f0604030f0f18150207090f050a1b1b02011e11120403020109030b13050601 67
    0x900000d078a15141d600c280700e0036885950014080d504100404516410913030081a4600c5c0724200c010300c1c0990302d0301c0c0c5110120b01035032064030b081c030300050030000d000581401000d10315000c0340461a02d5070300800c0610340d114000003c481d904400300182a031100c103012400120380c100044d10095165500d10b4546004036004030070001d112900e111215501c6041501c1c465803003d0308480d811101c40c1e20b402c1c1c0002005000480a00ca0544c3c5008100c0043c40482c0c0618401d4030f071140400c0c0078420161003211820403400401800c8500c0314120388040d404c070300446680403003440382d02c10260070480c02c050301c07600201c0f944c2e030904105c02c00c0c40001e940300500c900803a601c10825070045807450500754683c3e25016001454510320748038010031410010404c28414144008104007080c0402004440c8030951804120111800007d81100703000e10514865042d070361924003800c2d680060700c105842d0002501c19150800001c1d80107050450541c050780c1c100c41100c1203503942e030320302e4030800710a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870587347 1250 870586097 870586111
    0x50f0a0206040606060e01020604170f0a021c03230a06260f07030b041e14030d060f06050a051e1b010c091a16380108070b0a02010e0312 60
    0x60424006817581c81641c0148081105901600300e548441d20f5403015500035580d20b5240382d10400c03d580c01c00340e03180b00410a54016401401d40302114011a0a01030a62a105020315007804c0120001000704e64070403010721061b1100e40d4898482c010850000c2019400080c07200d4140c1c002c0742c0e40c05000308810089495024100c400011201480e01c1d101e4405100090a9216042c00320300021001d4404006030f0801007a00c0000041545507003102e07015070081008213800000c0d42102800305801028060812156144e903004e02d1b180e40104144506420402000300125080c2c501c80d103107101c11901415042c9135561103007410000c2c5070882d060a02408011344ca8082040d50703080c012080354003140c2650003040c00c0b0002d031104a1107c0d60200f04010003001014641e00006001b9625516070380e098680c2090607500715060000c412100c0c0402c4241520201c0010013000000180640c15120503170f40c000d880d01484807080e4054a000c40015001d404089000000e401610101d00d1041d0b00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870588597 1250 870587347 870587351
    0x4061d0a080c0a44030f0702120109020112020a09050d0b0f01080109080901210515010311032403030d060305030a09150215060d05100c2a12050f0a02060406 69
    0x107520001d80000131039150f070000040c081601d00007009144c8451300c0c12800e10101d11429804103150a8a0440d0701061004014002c0410500d0542c1007500070100350060f041d008018002060300040c0545003404403d091081e000207005c11401e1040c045503006150242c40032600c00218a080b92007a001202ca0080c0501e503000000b0350a9414050030180a0700000030518207100c0500464008800b0081d00f10b442d004031004080f00b00091041c00c3c03203100c0106030b800c80240c3c007800050540b00480a0340e2800300d0140103103c0b800d01000008280402185040c030000e1482401080c19406000b480d9034080740351800001c18000080003d0240321805e580b200b080c00c4c0c4904154082c1e0707811800c0480107901045140c1c0b02070b010401c503e6009107009040c00054005a500d05142016500c0c40b280c20035152017140c6a825040b00210056007500200020006c952407540084401c3c4208050000c007070544900040134002e00480e14146501c118040d640d942d0400069583d4074103590480700e141c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870589847 1250 870588597 870588599
    0x27010e1f0605040320090a0903030b0a050a050409140a0305130b041d0910020a020102130603060e040305160b0106110f0d02030d09050f0a29040804061d0a080c0a 71
    0x840000c20340d000303603000c0ba260541098156100d44003800b02c0798490440311000c21000320304582d9060034030b510894204101044007509031070010705a030011000180981d8030758006101c1c1e591030030725100c01e6507826200040d0b4075019042c0f5884d11500300c1a0760303955009101d51136050540c4075005001304502c041000c0c034840c0d40c6080c0002e00e48214440e0311041031901c05104110380181d034015401c200684112990300014600d00c030102c0e400560900e0150b0740c00100c3c942034060a003201001411a410104442464200c0350b000c2070400402c003c1c10414002160307651094003000841c98650040500800c0d982c40d01c80260000b20f2240d0a54130912601050610305400000c4480c1848500d50245d0b0074010f010300140041c2c810307a9401c442c0ca020310786038170680c20f0042050084450061440071058003a2410030981141e00c003000140d00140034042102045c04d110440b400c370f42140c505000700010803007407440c441c01c09480e055403041c464100022020b00000d005da24009003100c21064807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870591097 1250 870589847 870589891
    0x30b04080403050613150203070e1908011406100804030201090819021005090c0d0519030e120106051e0402070f060501061106010f0b070c171b03060f0627010e 70
    0x241e0558000300100c1d40c00c141d506c4c184026030051500510315003040e44c5400881c1e00040c401020202e0b403020020005001081240c009000380700b803280c1e505040d01c078030713003041c1c00031598039901e881c000030502006502080405100b54062035445411103800354441c000303040030400f500d050b440310b80018420b540340140031041070b108190180c403181c80108650301614083c0094a6180300c01610741d4043c80c88103c1c544041480140e20316807080d5901003204108000b0840b0200400c402150310380e1500406119645400404e440311401c1080c01242000c0341c0030000c0c3c047e00c01d0103030041001c011055100c1c104140da81102d81a00c00c1e544072555070343c05160120381e54500910130340c100541d820f40e0070080c031801c0383d00a010030360007920441d0a840c1c42d007501d0f510044801201e11046e078071841d19912282c046402e201d9041d002100581068101310b182e112503800040e00f80c51140401c0803004210000031940ba03200d113203070100481401d41c0d45a46040440104403900c0304544801d9522902d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870592347 1250 870591097 870591121
    0x12121b030507030239010f06031e0b01140609030109060b030705061303080c0f0f0a210806120313030503180a0605040303030b040212130201030f02040503030d15030b040804030506 79
    0x203103103040700141584e160001d40c409040d600b0034400c40c061020017070100032121007801440031540303c020011035081d183d49004011000c22046034025891645a5a0005400b422030581100c42c0c9030b090080b40140a00000c443c1d11400d0711940e4150702c0d0048a408014041e00803c081c0c000403415500ca56640b401400500d00c07400c142c10240e44040841800020401c1001d01640c40b0a8011200311080e01210350b481d001408442c1209035108181e800108100b00340e040c04410942d03201e4080d0341c212400003401d03c2d1030160015219040c40035840314208410015504400c1c110320300168401c1d928240183c59130302c80d6a81c480c4143c0e00180070492401c0002c240700c01c450703103592090700e40f6103581c03011001809580c4030a540301e1b408101880c10700c00361082d05809060b8090100b1003003035281c80054101d91020680421035030050108100b02d48c0c010080d602958400c42000c00c5140c040c0c0941007001e41030b508010021600002800107101102c40a0b0090740d118504460786c6da161521030002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870593597 1250 870592347 870592357
    0x30209010f11010f02130e06060721020c13020a02010605101e090b0706020301080f0c0a060c14030f09120102090904080d021204060507030b15040312121b0305070302 73
    0x408511280d0040300350511540500b01400c041c0720000480814004a42045ea40140c0611500e01800c0c24248100381840c50440e4128100316041450b04000340c2e50380d24201003240e00315501a0280c0003c5034518024011030805020040070b40705007521200c500c40007074010000240c019881d014010230030b41080c0d0b101002003a10354940d1002800b94001d80b03410f007020900386030f00700f000000000403811150b0740a003601d680300e000c0258581d81000700d040c5c075103400c2c1c01041050350b125019003049900d0310810301059849914048030450494100b00f03003050410f940c0200b652000050301211140000c01802281e0700451f24041e0150b8000b811b0f034281c0c00b682d06003992208218001c1000106400e00400c0d4440a403a0302508000c030028428001c400704640c1543c005456204000300e603541441141a030800c01c94806001c4240800030b0080c0c0e004a0100900b00c1d003038019411344060042c0d4214246114688041c001d110302c1041e0110403296080c11003004ca070401c00072070301040c02802030314 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870594847 1250 870593597 870593599
    0x312090a0504020f071b21081914070b1905040b2e08010504021c032f0d0210180c0b1809070c0317150d0c0b07032303010503030a03020a090b2107030209 67
    0xb43c00d00a10010125102d8000c441400c12b000c0300088642840988001822109001e0a100c2c034051a040030703101f60200160035010b492901e070500300400901d515041682064056a122080c0f4440300d4092200320303820041450800b1a12800145900b4150407a61190344246d6111210306904c81d041244882a0a002000b10f0a01d810021041500003c6c25800185c2c44981d0a50102803980860409100032440801a0400d40070f41203200340501400342d00c0003144411040308030071511090b18101c43c60141c0c0e031061030005419200c95681c032440400085c4014094140c2d8104088040e099140503041200410000803040485080700c04e60b81d03210303013071a04c50202080d400004100404000b80002c652048000401103030340c0340c10201401d0400d200e619400c1c01d4007445080400c2c0414080d1062108990410040c0000d440210a40c0d00c0240c15050143c0c03503115040b0240d95000094211003803212001c1044103139680d160044020145662420301000c1d180c2c0c03c4220144d1181000076 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870596097 1250 870594847 870594863
    0x52b060801140a23040303020d0b0a23040f020c07060e1f0e12070b0406091418090102070609060207030f081026100b0312090a0504020f071b21 63
    0x165141c8041c0c00090601c5408a180d0001c140744c940760070440402a101580041c4c3e010451645261551042502078030044484102c02850503803400d030030070b80d03503506100203406007444030007280c030b81ba044854030b0003100c0429500c03220ba40c00303602d0740c64031a84141070014480c0e801c40030f800e090402106150035000340e038440150a4400068440c1640c2e0146d4640040f0710458448500c0340500100f40580100f410180d5075170b04d46280180110400e40100241d001c1c1540b800d01c0641d51170030160004c4007460040b007010791b2082d001c1c50090140c100041d0000341401e0b1741c0020032120358002c2103006c1c46030315500d02c0502d040c60102c543d007204541040720550124418041c1950b60a984a40344200c0400800011801c0f81083d003030406003100840034644038203280702140390030710a000c104880700200a04180c080390010300b6610052150b00d000302d80c00034491030b0080c151801c84c3e8055030081d42c10b1044101116952445244034440d0701821504100c200c6c100c04200c24960318401c0c1c0000f01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870597347 1250 870596097 870596101
    0x1050303030c180406060e0102100618150315050a050a0e210421050106081216021f0e0909150610030b090712050a0e0d030c052b06080114 61
    0x1540455001c03601c0c203c41c0c880000d03080049a0b030b07140100c501901030303036540b0031a00e500c800c0068508540003012800c0e031414100d0601400c60b600f900602007203600c0a000c1541d074641c6400d000d00050a400c003410b28601e03664460303c080c80f02d4000340c1c001d85412400300525529071208008607004441c2601c01c0380c0120304c60340341901003100038100b140260fa00c802d03e010740da5491074203008405003011080c025800c00203000d002d800c1c800ca1000b801180080d0003501c007241c0300c4101510079154401501101102e900d010354480e034421380a14420528051004078490070003403d90300070901080d106020308000648000c1c4041518003001000b4400c581040d111842040a1654080d804004041d0b0302c100fa1040e603030f0340c3c0d2a214040c2415841b0840113502520044e0240c1300b00a020f40a800e0401103400100e040018541c00000d0003071130001007540080030100e900384140400072054044403018803c4486403000041505200c1030810061160b071003200a0a941d6070101150003203002d200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870598597 1250 870597347 870597361
    0x608070323040c0f030c09050c040302030a030807090e010801052707050108040f023d0c0b1008030f040603061514031302060a030c081302090c0f07050109050a05150105030303 77
    0x40c081d0003511624000314111385540381d8207900c9025034019a290b0081c0181009413420310310034241c2040300080b01e24034050560300031a55900440c08020204003000700051240c9119004040183c20124040c0381c280d41d403585010b004c0d003002c0e52080110070514060114181c00400d240540301c0e50030003d8254249400e0064450000050090300d1704ca480340c22250050303880f41c400c141c04120100c28400c0c91010040e1140001e01081d2419800341030164588400a41140782585001c0d448601041503070b64088060100c0b0b000c591118280e8440414910030f0f80701c00030094000c0e15031a0ba010007000b9660034554000d4046413111030041403500700d65400c035403001d0740259405100d5282c002158001c2c0e0380410a168410b0b1400c40c0001d9880c11540c03202940000c003281c1048080800b29039040194000a07030083d409002c03c800b40e00b0005144e044900c481054a109a8022000704122400c0d030400a46449600030121124040c0710008c1c0c42c0900046400d038141c0b100900294196a6418 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870599847 1250 870598597 870598661
    0x8100611030714060f2d18010510060f030605060a0c0203280c05010503060108180f0f07030b0912070809210705120a21170103080406080703 62
    0xc0aa650140000c00055003c82c20b5091000081a1118001c0011749400400032440180c058101c850840403026404006081010104d005424020380f00704e13951902941c551803100740c0b4024241c50b500341010480001c00045044048a96031386414040e402d1500c2c0450032180140652a40110709001ca1180c43d0f124404078050140301508407014000c0008404080a000c0b0580c28800b03400180c1071001c11000da65140001c01c001c1c00d0075401d5091802c0041e04c018001841d90704030030905191010709810030810501e9408990003600c000d40a01c000c040d441d807107180000d686100d4010089036003048009981d500f40c0343c940482c1400e00d4007603a01c000480d4003c51402d40d0110b16182c0b405840182940c0e0b01d060034403580020710b00707949070500303009159062140f04403950f04400c00c000080307281408862240c8000224905410034007402c10f448030104812032961410750308001000b003120fa60f008005540c0103840d090fa0300e80e100c000840503244500300071505a01d1241c0b6000c1c060402e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870601097 1250 870599847 870599867
    0xd09051c02010c08031008070e091525020622081e040f090b12010c0e060708070503030f01030c0b0f0414030a1e02010801050612011a07020a12050d081006 68
    0x51410f0000c0d50b00760303215130046420585807148071600b480010040b5203000c000840050569125040081ca0030b540e8454644c429000b008011010110009440440990728608680410720048600342988a802503030349a0803904070000141e8801c8039090b0b0040d405803040b1030f6070f209140c1490728145400a072082c84154114086249080c84080307003c0302c03120b200c403002d000306440008139880b000c41002074051a5050f444001c3e45040e50300307140140e120300a0216144c0640e0401d41c0e0381042e2800555601c1001c502a204c3d00005c0107000c10360300c8100050f0b040324004c2710300d890110345846a01c40701e4412002d84440d586d030100002c000c101000349a092070790034000c050300d00b65241e40d02c0703a803c2004d00210418211580240c3e074021580c10084040c0980741c02e0710741d541070520022848000200601440350380b0403140101103400ca1910040b11007440e0302038a65984180d0b5807070140761710003034000102c030a801095030381c0300c42500c110000c2c0c2c4039103a1585041c0e28a071030202c0960f030380c00310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870602347 1250 870601097 870601099
    0x1050f0706050f0402091602060624031f0b090907111609020a02070801051501030207020d1a04110f0a140a08070e0f07020f0a110406260d09051c02 65
    0x1003806040e010a010744034640c4903d00650b203a0302e83d49410700c10450030310300040510121101000140c8a0f887c1e0000c0c100c7d5100d0b40030744540c8103081418030703035465503810340e014558101c50000800c02406040e04078038540408502d140c00c015619560461080e0042415241d001014172002030441807140b05400c042c1250002078444413400064407400a030010b0308a886003940000708036800c0d030340c100914001003800da00200300c18144501d0020211b0f00e4060303144e0425801042c1501559100c0c036071201c8040d40003032185201d1000b628200200b803c00c803002d0b03e80c180203140030316442c03c062142402d40718000f4141c000041c24850043c5c032301c4c064201c5c01504000301c0140490001c3d0104250800b400104019070001d1800c4c41259620000c020100c50440d00040001fa41780140003c01d225203e90001b9210030b00d06600010400a018640c0184540607260800c3c5d14460008016040307845070700c5e000d86028048101090303510f205280301390741c0c001049030010115200d20071503080074184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870603597 1250 870602347 870602377
    0x306090402040902043e07060f0209120a060612031b0302070b0d0b0a0b0712080a0b130207052b0e0424082b120615020a060501051c020105 61
    0x1183e50041011900b800300060410074030121446101c0058804104201c40544151241d050b024510081d2500031810300409154071801c601940031400d4058414500028003942100000c045000c1c0c0c0d0fa060010059410600e002d4011030204050200480d41c16096117416005441901c1c0d4080c010f11a01c1080c1c003140207880011400800300401071110240106003c100240c4910402c001046107500c0808400300030000c1e0341c0000c1045c0c00000700565181809a25599001705001c0a00760000380c0a0303111030346002c090b04102c142ea01074010207025808071620030000010021481e842900468011780882d52580d450a100795000300c11481702400105030b000c0c105600d2000c3c800e144004500740c602d191402e000005003000a00c0d0703030041d611180221401c1100504444581400c000c0341008110244400c40c1e80e61500807000404040300c140402c03050014000751501c02d080c42c1102c81d18203001c00029a85400040c0703030b507001003400c4103130b00c101c20070350040d03031150700c40e2081c5401c0302 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870604847 1250 870603597 870603611
    0x3030c020a08010c0507170301050f06071e06050a1a01140a03060308040f06020d020a021e0f0d110418080306061617030f061f0f200703050708030f030609040204 71
    0xc02c0a0240707070240c020f20744421351542c040c2d01d050340211040f60108030682e4001d03c01041240d8a90031a292000c4054070a1030392461941804411100b4480303a80654030303001c00300341c400c0041e558001c5100701180340c3e041001d00200b022001d003244000f241c6c940010300c4584051010144c200040a54101d203042c005052a5240e54003111900544e0019220440390103042109a030180030340c00e02d0419a00c00341c00416815800500c8041d000f02c2c41074814403401c1d0700c2d441140c840b1100c803050f01c3c1c00281304140003011841c000c1000c620808410b4040c40c02c0029101c01d45170540300d02c001050740800c0700360560340c07003406028030394005031441d16029250641d807201207241d0b98001000b80e0149485140d07289049082440618405014140030700e19090181e10494180f42d003200034600d4603d80000d00d40080c12089070700e0004484608401d10320003106003840c01d000100002101e2080d0181c0c0d2800f56218055501c90050807078026001c82d08200250f070a2130a021040d03030092000f007001500e031b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870606097 1250 870604847 870604859
    0x90b01050118121a010522050411090f0a0c0509090a050907180603030e0d2301020c01020c070f0f03050709180c031a150a120218040c0e0702030406080103030c020a 72
    0x40e0b14031a0251113000c0400032520381e520240c1209070151809880500b030350041480512047d90310140817050240d59540030800301704445503131a15440e0003c11201180c00c0101c3c4050031141d0035070324440228038080700003521034041c4040e207440756030080050000b6501c0c4071f41a4041d0800621800c0c09005010021a200f04001144045642c0000c80010783c07508514004d411075280d60081441200c40c041c00340000f9400801200c1c2201b2805004510701207810a00c2d80a80512400044c85500101c0ca0002110f0700003281822141500000001642d03958240032a000c11404054410b8101c000140b12400441c4c02c540501d8040481041c15102c00792549a0724010b2030b04103d9428403480c07600511481800301c05604401e4500310b0324205803003980003c549c882d1a115428060302c100c1c414406540d14400306031749211003510820200d00c0d240c03406070031540c098000e074058a0005404074602c94400000e41c0c094400d16101c82003546d0850b20180e556a0710840c0c100d81c4581524004546 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870607347 1250 870606097 870606119
    0x18060f05030c0103092618010c02060405100309020618030105151f0c0b16030b010e0f040f0605040218092a07063908160e0d052e090b01050118 63
    0x128045c14891b2600c0b900c9800b03049901d00f0901200504000060341c841005d41d0316501140c04440e0101c40319442801c91a60680191114450103907000202240c412010300e20691440e420761021802000203603121055440c9044820300300c01c2d001046003404601c458000c1d04013100c8080702c1e0030180f803003900c04d903510100c8420880f450b2240c810800d140c0d0501c95014015100b1060f800d080c00360b1409050300211700d949018450f66840b4039160b020500c00c0a43e103074401000361801a005558a001d02e01401c1c40d04807903200794500465408000500800c50b16202144005049540c1101000c554242580c1504000001e0f00d6070340c0d0b0303071055240740c07840414011407035040c1c0741c40400012000051201030b04a031025080500c0280400c00006c01d00c1048100318403121030a10603441c1480e0300102d4002c90441d00d00030702c14429110140840306042040e500d445000c11852041316071840b03004000d4480e0384000602c01400c00b00144840c1d0b009504446500d07401c4480740c010640c1e030b0360096503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870608597 1250 870607347 870607403
    0x1b0b120105220e070f1409071b15020a020d1704080702010e04020d1515020c0904030216031b050a0b270a0e010e09010e03071e0b0118060f05030c010309 67
    0xe0544c0c0002c2c0108490070440040c3d400608000c0300400e950f10f501e0000c0f900300400100490200005001e0b01100203d260007086a034682107103203000c1d00401c080d210780003540241c00c0003001d8801c98040100440c411a2a00c001d06100c42a00c80291102d94440d80ca9401c0008200e0500c8038224160115031a1b03407014190041c400c0300086032384080b43c500c40d12468051b800500780c20700000c001c0000c040e00003c034a04401400e40d01426a0369031410100c0c00c0401d001010000003403480800814070a6155810020314035000c070000965a84004106950303e06d441407404104080c01308040c0300384d0100d0b003d201c11040320701d014110b04040002a2601c00241c2022480429010041c0200e409819040781d020080000030000c0582814006aaa0080d0100200003034000302c00004c0346a40c2607080d0f40c2d500d41c03004010038070f0350310346201c1c0c1091184140f10444036844c00300300240e50369071a41004101d0308003501034802000c0c06401140030700b01c8904150b6010701c01444e0700c807403401301420003a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870609847 1250 870608597 870608621
    0xd020d08060d080d020703030608030a05041211040c02060906010914070309020109030c060521090601171c1e0c0b0c0f19030b010f0c1e1a041b0b12010522 68
    0x1a03480360030b40f50290440742c1542114ac20380d0300502c0040225900700c4125410703114800c030780c50001d440030f1600b40e40062540303010980107824480442c680940000340a4094206e030303070944810340e80701c03031410080307826446040070984c2c0744c4c40100d0411070203a801100c0c628010300d4540d45075030312526a01000301c801d520800c0024000190b1809040e01408a0300300c050200700d00e400c503802e00e81036503079489a040c0504800203a0f050b0f01c508418a04209e000307031401d007c20340901030300340d500000791110200300007000c3e0041d40071854070032841c890030b0012480c6520094030307126600c4c0c650311807456411400b43d000070004104088200c00702920810850200142e602180c5070100c1c0b0001020001622290700a0103080140c110003d00140c000d02180c9083e9114024017a0079030030301e65020b0380581e01c00c4404150f11002e03c01030161025500d1004c800544110008a43d500d41c026040d2080221121900d11018010b115614080707240d18050108140e4804030308503c400410210b4400070928 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870611097 1250 870609847 870609851
    0x313080607030f05101401021c0806091e0f07050f0d06050a0527150d0b040203011d0c0609060c0304090b03010b0a080c0d0c2111030d020d08060d080d 66
    0x1001896240c02081001d4400f00410702a03820100d10728808002c6038041c0c24800103841441c5c040c1c5074800c002d0b103408100f4911101d407a1030140400034101d0003056903840d00441e010800941c00c1d1403010a10700c40c501e9036103016089907442c04600300c40541d01814400c10007000b007050049103861240035012214184c1400510f9a2401c810000e007400b45902150240c14403e0800024000c4200c4050520081000b6006299600901402c0b00f9854802071540b1801400c0c100c800c2c458110b0940c1c3c880c9102360001c0010516050f600304412444082818107503224240f414518101034015101c5080301405190616880d107180f54291b810a03001940b681e550b440420906203024014100c0130b0384c080c0c17010305c07440b03007070004681e00c1c1c0004540c00c6000d680400f80d0001003000070005403000b846411000e513502c459900341c01c840d0000e1481d087d28294128000d81c03206140114800518400d84c0e00209000e0015000035540302d07500501540e444501280e0b00300c041780444009046414500b180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870612347 1250 870611097 870611101
    0x1020331060207081e070306020a030209060318010c030e0d0c15140907060804110613050402040603021305030c091314030f1207171302040e0f0a03080f16030e03130806 74
    0x1395602d003040c0322200700041c9100c5802807210b40c1d000303d0300382e0560750048070141c1c4c1d500c883e00094000c1d2203800e403a140c11580000c03c00000b01300005882189002c0342000303000c50104100110242c0d01c0d4103e00c15225044441242c01c10b81c091206c4c54000e030b00c1000c401784000000400041100c1152101c680c0000300c800c02c05c004410180000d40280405041444990405440d07882d800d0694107180d034040c1c1d000080728803041040241070300080c00c00034015543c894480c01d0040c085e4001c03005180303102c0f004600101d180d10307020503226001500900070040c55916078501c0e0302a07841c1c4a42c02c0e2030000150411b1020031006000520f1150500c5060940c1d421a044032141c040700018114410005100d659210081640c0034040d040080e000c00c14505e0985030000400400000c2d9100e00745100f000b0072558040004a03003000742c1406500c59200a666040100790740290403180f0124186101d480160a903000b03078000400351000b0000c480c00c100030200b9040c9151100d4000100703991002e02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870613597 1250 870612347 870612359
    0x50f04170a09090b010c1209090b030102041a0f0c15060901080d200304050d060f0b091306051003080705070e0c0703120f11030c041d0601020331060207 67
    0xd80300148140c014280e4a00340c1c0c4054001d00c2e024003405a0034189413641c6640a09a20a51001c90501e1304155401c007410b40d40038003d80580c007230f88503c1200e0303401c103482000285018425901212102d050041e03e41007103200492999000c8907020381501400d11000184038000c008401c0740650018400542d81031800801c01700c004140d2100d0800c0d4010044241110b510500000c0b00c1108200c1c44559000b0100e90141140101d0b00601c4d0460705864880703040c45001d4006025160301281c2c100142115441441441c0c035003212001400c0c900d00500b41c00244165100650211614148030180d139200d917650b1a1070350200000765450361042c00c090028141040001da0800e51404569140454a507005002a203140c201c21034242e0390303a0038a4101242c5600222288011084500e960f464040000241500203014070400c41c502c070310380c0442c000f980b443e49034000c500c160011401c2a00348074200e46500b0720342000d2840000c034410308100341c081c0281410041d10182e0090b10385142804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870614847 1250 870613597 870613613
    0xe01080703150c020a030e130c0503041101082206020708030a020d0b0307050d0615050d12110325020414070f1d0604030308090a05075102010f050f04 66
    0x5189410070780740032080c05070303182c00058101160358142060300305480e0441c0001c83c50318423040c00704201c07030034040c00410013035004004521039442080840903200214004550b0740350115036001d900010b241c0c0440d80802043c00c40000c1511031329002d07241c1015907598410035001558110541034000c41d161800c44900e0013403c050a0381a07000700442031501000460160101001800180d52040581407010146a484016000141c24034411012501e009100304d01c107183c1000c0012401d6406103840704001c8221100803c07425044180500810480360041203200b0b4200c2c1d00695440b83d94603211805030005100c4c0b402602d03840c0d0390034203102c4080c01010450820118500e418103090b20b082d55104181e4040d6a01840d02111580d03490032180d1401da8000c80140003031041ca0700000f500e050542c2e0f03a200d100c94111145480e45901c03000c070a00c2030707598002c181d81c0001d03505841406c01215094116144030520012808150450a01c400c0746c0701607071900034000c1e0500412040c04211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870616097 1250 870614847 870614873
    0x32402071704061d0616050a020406032604140402180d0303021b0102190818030c010c09090e150a0b041109011b110d11030f0c0109050604080c060901090e01080703 72
    0x5552042040404d20000815505c5404003034418509000100800d00c10200301810100354080e20402034281c507418824084207821a51030120050300d08545a04401d040950f01240e40030b40c10444985800c40800002c1d403c40b42141c021505403036200300e290f645100140b5282ca000341c90060780c40508203c4101039018a4661411b00da00410004161800030b05685130400c1e02850072554030b807119140401c041c14650b002d807140344400b080c080307900d20301035022201801c1c0036110b202440d0340d15040c041c25a02c801140c4d07c1d00750006110789220280c1c1d90300031a40500c41c404002001c5040000003801c4a441040d80c0c500050080b40340a21960045d240490402c00f020104501d64520740c2c40064003205445c4003030184183c003210004005440d90401c80319100107042d03890040069044503521002c02c040306001542e0301c1400192810903004440a40b09442c0c003900b0814460300c24003031603900103c5214108904000001906401201068040d0150a016165003459400c08a10303940302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870617347 1250 870616097 870616127
    0x708010603080d020c03041d0a0501060e0d02041d191401090803010308070f02132003011815080f06150609090703090614070903050f0703240207170406 67
    0x2610000384045000300050364403240c100c083c0940e49401074080c260035070082c0ea122038141d101d1829100041d211004480d845104010010056a81d80700021104600b01803000c0d03800241e800c00c40e0025083c15040019185a8001c0390010702540e2403040c0d1070072103245a601902c00c4013180c10010010480180c40380b440c1e001c0000c0c802d180594403070f100a440184030051420400150000401066480300c0d00429001840b21200030903141c0120003400010711141101d00200e800300000c4d02d0740c0025281078516030304900801500c202950710051810b84080c0c5a00c225406000031f072454100704d10f20680e20300401405050a001d84001042e96020400c1131003114140800103050301c1e04259103602126034900485c0c8503003203050007001082c02c0c0004051310030251040114103030304540d6100c1240c0c030801c02c44042840c000e104ca51904250b010080040d0214071748007055201d58809c100250010080052400e0403030346c4e8222514000c2c4d01901e0009002280400125400844031412401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870618597 1250 870617347 870617351
    0xb090a09020c0616020705041e0c02060132060a09150309050c0d0305120a0c020d051201030b0c0c060709050f030312042607050631030e0103092102070801 68
    0x5410602ca465480050480ca808481005034241041c400c01c250030082c00f014004200b550350040c030210140c0c1c9a84500303880307507040001000d6a14400181075040760040c81c0403580c00c48c0c5100c4001c1c03075051031960010314034042c0241500141d450f40000c1007150703055280d0008040c0b130320455001465000000c10185807403c3c5040e070104002041004030900c040710703080105007041c030781a5580e018100808105000640400c201e4a02c21781c445030022400784c08441c3c40011500c4c0807a494030491840c05c00dd40308840040001a03000200190041c5003402c001c0e05241990700e1280c40c203841250408002030b00500d04100318280b0b92280e00d880041036010303500d8403840c00e0040d124150060310080c4008802c00304010001c800e1400d640200c000316461607912072050034034994602d800d44505100749000c0100a003407110814151064120b410070084180441d500c2c180c482071007245d14036040c0f54a03080d00d0700c006000c0b01a2a030615100c1183d03003200c503444400c000d1a03c0442e8102c01407680c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870619847 1250 870618597 870618607
    0x1805010f0605030408030a06090507020a020f0a053f100b1c030e060904020d06051003090b010303082d07090902030108070b0304170f1c0b091305160b090a0902 70
    0x10303448411079601c50740000d1174664035181d956000008046690004203d10b2912082c0041150302044112443e4003c540c0305403000c000d08200400803a02e44169940841018007180d01c030003c440000441c1900a03414404002048554601ca80740210f51003940307410500980841c40654030450700da01c02c054507812004140060100c43c64a0005009000e2050100b510328190f60b0388c0c421291074001c060825511640031010b1000502140d00404e449107a4850f44202582d1103440303401301641c0c200b0007041141e46144c506941003900a0f110901082071081014104810aa42c0143c0c00c0c081c0f1701c440d8520b15060400400d010155040603015600400040048203400280c0b40207941041d40e0541d5a62964602030b0a106400508441d40007008664020b00c070005501900321507070400340008540051100c880b0443d0b44102d5042d42c445208808a031070081d00c140e0214911348250102d4040d090b90040030303809078143d648400d13a9590006a48070309400d1020160004180b250825070402c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870621097 1250 870619847 870619859
    0x150e0c10050310030503040f14030c01051905040b030f010302041a03060a0c0203210601020f0102070201050f0a122c030403050c060a200a140c091b040f1805010f 71
    0x2041031005940030000d02101190324a00b0b2a03160383d00441c2d0003011281e07a5503aa00042007881c100e40f25007038a0055192844403d800d0100d00c603032075880141d407020320b42014454000041c07281e40c031610b01001b100740000304480c2d042000440c0500c100c2122081c40c0c2d8514810030090b05c82c0c1ca418070061700c00030603c82455403800a02c10340c0100400e00040350305141d001c001ca03d580112100c54004000c82c020107241e0401c52448140034000070f81c2540c20154030301801a00f42d20844000900040007000804214138032140a401c14065900d02103c0150b814196441520440303103050240d110010351000e0550b0f0a000241c81205184020390305140c074540341c10303803101415800741d03020f48400140380c0c1c1d659100d110a0400318000b0700002d04058840200a03617200c1810310101d48840448000c0d58001d80001040e10701c0c010021314000b1695224031018810007002120008504800e000c0400d146480b0410303c8040e0100f1100540f0308a050701e128015200103a1226841d01c0c0800c0041c020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870622347 1250 870621097 870621109
    0xc01020910050a1e02010b030102032403030309030715020c030c1b180103080702030f060702010e101a3021031b1c0515040e06062812150e0c 62
    0x83e40c2101d070880380540d038091340a9001d0f0500d005021780c507520000400c881120941c16803480300e198030507030000008400003815580d11056640c3c01003648240505070000e40c880742000100000c030314015042500d00b1500910350707001401083c04580050a11101c1084609443c00701e01100301ca42d01544c07800005c40314003000e818000a0400c02c0009800d0007503407001c020820784a0f000508036016460440c2009000700080344002c8880d0140360240400d510b10342c001d204e50441440c0780c40c8610080d500c100b06140b180040d00b114141a0310fa500001300e001c0719960004240d079800074052940380d081e50707030f000007120544007450010180144403d040f10301e042e6584223b090b0806550300c040c2c038002d0200c0520b00a060800c007504040c20040d0b04c401618003044040c10556040c84070072801c44c0c40b581c070b40c101103d0341c41c0c000300c041c00c04e42203094400841119964240b0400000030f40c4074070440c8089080001c09941740c40c1c91660038000d00801c0c3c8251280d040300480a130201d071500c00000b440c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870623597 1250 870622347 870622367
    0x90303041b0605040512070e0c12071403010501030b030f01020d1e0c02030a0c0317040f02040b0f030d180906170708060402010806010c060b18220f020d030908030c01020910050a 78
    0x4000d4541551b18914808200300d1480500380a0540a025140484c913494051340000d00e443c00c29080c50001c02c5d003090140c650303d4500395149000714216070074000110020002c2e40e10301039141c400c804041045ea0030a1005101c109003d11000c035035007500c29420500510559001c410032407034140d00b119600da000c000d554103415a031400e8044000f9604003161566000c0980d00080000c01083c042001218443d0800151003a00c043c001d81c9441e004109800d5510000c17140c054028450354030a403841062000b00000a00b1444410192511009000c68590340c01c55000c0c10401d811108844204000c64001015400001c0409152a5000812140025001c2814001c40b04c803000b080140035040380601d5800641003520403547c940d0141013010702611200d40140b8003402c21b01c0307904002c080c241034254020b13555003080c011541c00e1005a80f4020303400da0811010f0b49010403d81c60a2005001c2c14481d07600158407a2110b0081000101840c00d450f010f21104004203414580c11041c021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870624847 1250 870623597 870623599
    0x91b0626011e0b0a0c0c170d0e0111010203040c0f0b130e071e0c0b0c2502060909090d081005010f0f02030c0d03020c0c0103050f0429090303041b06050405 68
    0x842c1d841c50280481c1032a0030701d411510086001094400c0060343c0300141d4075503e400f030109520180e9403051050b6401104d804600d02070f8000c09030b0700d005a4040d43c42e507000c040040c58150f040300701c20062182240c10a0300c0407991100c24040030441000e03042c00c124007a01c03128000c00c1c13401328403101c0c80410940b02c0c402d1003000d5100c640087c50441c081c00140031a04240d035003410b400124014001e20f81e110003c02100d08480c000042010502d2010541d100102d60300b0043c503001004650111000141000481e480801007040700c0554449188081c0a054268000c0c04e001004440c080d10507100101040c1c002610031902b00490383e801400c1c051041e4590405032080030525008a04600c6920540405481031110032449164554014400340200105407a08108000d00440c141c1e102070314148100b08103800854003040d0b040003008019040c2400303001c409120300d14103c5502104039500385040d0004000c0201344100030500ca10707415843e0800180310f0741011001b40081c0902d0042c030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870626097 1250 870624847 870624869
    0x4090f1a0105041a0910120c0908070b1b0a080325210e011a0f0d020d03050c15010b0c010509010c120f0e1b130b13050a091b062601 58
    0x4c2004480d100301c95402c10080d001e004c0780340360740c0300c080c294944030880444a186800070b640d190354801c601c1d403401c0d107290101501c0201c2c41c140201d06103800c505590b0f4900380300384d03220201c0ba07041000461810792203280895164508441c900c1c009400340d22170061152031501c116075202e0307070100000c11035466050340c0e031100c03803c0310584078014082100103030041d42c40c00b900b4030410481c003040c941c0156811104144900c81c0300b001e00c5015810094001e4004c3c100011940001c2e001d0005048036554503012120314560403101403e091078282c1c04920303090030000b500e000b445801c0c050651311030a4400280010090700b02c000f0800701c006070f020400d0380d81e66040c6c520a8110b076007041413500381200444444803020340b1141d40050b5205d040701e11036503180c9414030308003000c0d0240c260100001001005c01c01e0009040c0360141000030003d5002c29590841400080d81d1010001d00710035800c0410303003505003440406071400700c0c52011610581e1072070070141400c514205010b410b4501242203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870627347 1250 870626097 870626129
    0x5090127061d0a0e06040b130f0b16020304031208130b040b010f050d11010e0d0b090303010609060219060c030f0504030809390a03050a0303020d06240f09050604090f1a010504 77
    0x500d180c3c0c100515002070031041446589c074180159041c1c00c5010b400400141c0b0701c1001080700699603071040388401412000b0b45030b00160414005e0350415808220300c014124041001d5561440109040354103e510540b0080107000d011421a41d0b800501402d81d00d0008202541d1264000b080806100604001003000c1d0211030340c4560b410102c29a51180d541c40c1c641c24101d240d9600d030742003402072100080920600007149440040d2040003840c01218603041e0015640348d42c2d024143c010b0041c418561130b04507440601c05c051288500c5240070b641e81c014982402002941008070584010401c80701005e00300441002d50044640004071280324546004541008101c040200e41e2000c0c1c401d000e840188414541c0540041203040440d0004005054883e410050400506003004c0003d007200d11280b00c01c0343c041c06044804040a040c14684256034000280e6154801c0c4c219103e02a140d580174100c03580c290180300820407900d0040c00c15409003a0008140d40154401ca030560042118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870628597 1250 870627347 870627361
    0xd0b04060504060603060302100f230f0c061e0705040b07050c06040308070b0106020d050a0c0309090c020109020307080606090f0a020f0304030306051905090127061d0a0e06040b 78
    0x40840d00910028000380b1080d9a180c82c054010a501c1c801130340070f40300b894485034440e40715240b44883e2101d20745030b485654040d9118048924005041030004000400c2809035600781d080140040541c0f83c40100424900515052200103401c20382400246140c000c0c0554160060191410344150303240050725a0f01ca03040c5a0314000070004015000000001e02105204501004041079809140300e0b15581e40d0b2044100d03550322400f006e1074000760003444071440c400d200b95a9220254000e240007111103880740e142500f1107040e43d00600160395643c11110271400c007480500010320b0b4410140400c0c0c034250002c01c1481100800286600d22000f00192208404e6815116114050442c01da2280342600e0f0103401040356005062143d50220100c950401c06030906005880f005080c030240c59203003c8805180171082c03000c01c001074510500c0c042001e801c1e482021300403c95420001c48101c20342d5418216158041d10415110381068181041d0ba8000180b403a0031a601008850702aa1155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870629847 1250 870628597 870628601
    0x180306042d050c120109020a0303080711060601050306040902040e1c020709060b03011205030d050c0909010909050a08250803010e16020a083406050c0c060112030e0613140604030203030d0b04 84
    0x20000030350202340000c002c411305502100880c0b003004951103c118440c01c01d907400d6900e0070221402c0f400258100002286820300d504008200c61000e04046110350030950f0181c00c1c05402d50038000403039080d103251519140d0400c5100020103481c801040b10030305010070403030f213840305018035510060480b00c0340c0108441041294041e41400340108120b00f440740141041d540009605403003071b4004000810340c60820f12070341c096507600c02e000303000c542001d554446554100c4c2d2071b0080125140001a80c0070085000781ca044244210011b5a8035030600c1c09007410020003a1110030b005114810705002c2c070f500020503605150f00620055100c076111203d00350f0754054900b43c10102203181c2000c501000c6100100211180b0518081c8103958500811500b203010b0009600c1180d40a5001080000d40120122103c0707406850b103680d00001d0040482c540740d002080c10174500c01041000c12143c2480c9603d000a03240803101c052030140b81d900003c0d941c1c0100c03203200c141c02c1d0b80d440b0641061381e50380e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870631097 1250 870629847 870629861
    0xf04050a12030501060f050f09091f1205010e010513060905030d0906020d0c23030603030f2101060f0f08060301060512010f0f050606040b180306042d050c1201 70
    0x300c8059888480740008019100a100d0742d004611400000c0322280d02810550350742c2c0201c040c030b035400d0a106900708040410081c00c038890b1034a071000700000c046440c2201402a1450000802c0c41d02928544507003140c040e651602041c0e4900b6044c040d40d940d900d07003410b040c40e40101000c030799641c0504000f400c0d031141c8840b003102980b8100c105810000e55801800361040300d203174104543c2e0300d0840c042e00d5030980e00395681e4050310340000703082c0c5840309100955081603015084900703000e06000c440c50a54003c0c214044101ca0480034502e4914140709914050156407520b80f802000624015188400313481e01c10382880340f000000380064070300358041e2004180050000f0541c40c04040054000d01c00060400e005600300841040e49211900800740110320242c2414030703051820410030a2074001c08104952052400440c3e0050f0390200000e0b0300481c043e2115902c0c2c00040e544c440a038001c00e240b003036241849a2901404a60302203500741440000b0b440030005558043c10080c0100f00c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870632347 1250 870631097 870631103
    0x3030b041b1701080d031e050c04080d11060a0203181e151b030402010c060204150e0409050d0e0a050d060606030c11060106120207020603040f061a090f04050a 70
    0x3902242a44088440845030850711040c1caa10a03000194120304030002024044d180c190307409218800b250364840d9005650320480c032103011030180d8142e0180001e0703030815104180c1e10a800f24060200102c18402d1056801d51030514030405400d60041c15107829005212000050703001c000520b9903030100c0003001d41140b4500903205406280e02c030500c02c25039102e032070102c544140700303610503d54280000c00d0b0265050031041c4c140352158010145c842d920080c02207041224a0442800241c06400648054007d80c0c2010203c079010803001000e5054411040e480343d41003000200100e240820030000340c0002d07150090082c010240422520185980300c9030308000601880c00034040c05500000660704650b40c18040c102e800c1070200c64111244c901050701d50001001000300b070f07008420549030608890000b500704540754000600356001101e007920303044030140807402002107610a1812841c8503581310b80522030800d0100d00400c10040c112803290312824003150500504000c0c20004540c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870633597 1250 870632347 870632351
    0xc0f0c0503030a021f230a0e0a0311150606030a1d1005010f0608010f0b0a020118080d1d0d1d060712090503070b0a0c0201030e03040902120a090201051603030b04 71
    0xb0740f0703600c000d40d5071108202041c0802d1280d8400501641030b40a000090185510b06002c61945180a0502c1550190507444006e51b64003080e40145024400010f006000b03032920b070400423140480d0313810021400d110994140c0d000701003001c141e882009880e048000d81e45e00040c9407200000072400c505040000044601c035071140c28204009a4101c1c0341070b03a0440710042c2d210317551140190398034402801040d802c07040b111010302110201c140a40011800c43c800420030501c040820b034103060121506540310000010040c4168006000d90b102c03203c03c00c03186000c45068481480e840f06040d080040c100700040c5075101e5050140c0440d0b055800005001541e6000180381210800b01254003060204410180019980c80d01042d0142220600032503240b03400101b6800326000d11075a40c049041c569510181c0d44090700410140002e40034480e0300507038841b5486501c0a00d8031f0001d09140c110750500a5074801030f40c0c05000d4500f0302c0441c0390800200d1040f40f8050780508004a25070350864 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870634847 1250 870633597 870633607
    0x903120d061d01091a090a150e13021c121205070804050319020733140729010f05030c030a0203070e070c12021c0e01080c0306040e0f07090b060a0c0f0c050303 70
    0x103103040e0b201403094440024030741c400c80d82d502582844036008495825204d450ad801c0000903080954004103001c0596009850050322543c0e004006007003403030030a0004010110f204500c030181d103d903c0e004031080c00d00982c14170b0241ea4245d0349100d50720340e0700249044c50103522222402085210080d000007503103041100e0140d08080040071005c41030380510140c502d2007405442c01618006201003051005500d4201c05840d030329440888154287d00c89010401100c440290350710800b4042d09014100141507881e110030103240c00d2640701c0d91f030712940108c140c08006903800a1480d0454049862004103555240c42c2a070b070356140702c070018203010b90002d04044170607800702e2080303640d511805040201d60300768042128011140091180801e0710311000c00d122003402000b459000710300401c08030302d4856028442c0d040051541031040740d036010001c140800391032030148085001042e20740d1414a4a4504006c1a80c1e001d400003800341640c00912900f80140310703803100094030000c2c0c2100e03a00c3c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870636097 1250 870634847 870634861
    0x60d06020f090a0902220608160c050a03080609091212070c02060a05090114040e0f0406110d0e150c0a0f031b0c020f0a06020a0b0c0903120d061d01091a09 68
    0x44d60101c0500da490354000d601b200480f80e60b4504100a41d41940d582014580c0ea540064606a00c4507410038140200d40c0e0b89000003580420105c0c4000e03110f5607455030300b401c041c1c00340044081c02030420f20054100c40c042c224121002021340365090146100c0154980324010191049034003814046c3d04484000b4015000c15048801002c0c604020380c0c0c3d00e043c1040a200400f094043c40c00307407907134407549840403d01c400c414144440c1c20078060b100004504c100c0d2940701c3c0c61940001d4030403004540358080b280016a0500c600343d10b000c014031440714140341101581e4a82d104100000e01403044030350060948a00c81d0b448240b12107a0000307110030400c7c03400c20152552a45501c22841040e0900890f6a14100303044003a0403113803103030020b041149141e529100c441c61300030310854200f042806080400e6404112142d21300300e02900c1290354034803426200040c3e4a4079005203542440249101c41a00242084a0704503500e005001424500c0c0d4078001d04040401c9003410b80c40035014080c0300c58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870637347 1250 870636097 870636101
    0x11206080a0b010e0609040f061a040e010b0102071d070819020a050d0b1212090609151b160512161512050c0901050f0d020d0f060e060d06020f090a09 66
    0x42c1c0e45150313103030001661484100700040c00100c03001404400130b0300c0e0071000070707a541d0010f40208520760902e9417007425003c041811a605001100b03810b82d1590045213a55030180150341c0940708903181140c042c030080809018502e4043d14120030400d2141c00508401881c046040303910300d60031015580d84075040c10040c825048039821300040c81c980405c544440c82c00c410341c9146c10602e90090003c50148015090090304402c0d98550000000c221f840700310b60b00e40565012080a62049079100d0210321000d9071209034268040717040343d00c41d6140031110925035100c401140c004990003e0441480210b42e402c282d602591303900d100c410104085810080d608071b640246220760f4824017181c400c45c20720000d6420940f40031400314800c0000003219407181e4020032403444000951440c00c4400c6c3c80440c226402005159103181d603500040c4200800fa0061000030050420040158200100043d10002580f44000d2049500140601702007504406560394030b200241003d000036900e01c070441c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870638597 1250 870637347 870637349
    0x5030d02120402330a141617041223030a09210b01120201020304080a06020301140f13090204150b0309010e01110703030c0c230d1d011206080a0b01 65
    0xc4200401a0045001c03502c0540d80e40340e001d1440c084a0307040c0c120213405102c6034000003c0e681040b5600d0184401d407024540100308800b03081081d5030b21291107090901154444c0042d240040408010070000e01c4003000b8a050159003150405041015403810324040880898504c0790358040420045542c41d00440d40c201240c00001400407010043c0c0003940240801e00c000411300711128005020080890081411032441801220714064982545514020300e00c2030440300240c0010040c00041c0e03441c8265240c0304002e031114905c1c0c03820040041d0844480300c2031076410b680d4400244081d9030703840d000f552141850f03420344031625498000b1fa4049a2085070028240c0d8200342210701e482c03005109500c2468807020110f41031003a16a0100e029001c2c0da003003a002c11502d9802c285c00f16070b400305c0304010074400d9a087ca459645201040707080c041112080e000388039400c1403e0166201c6400d001d0aa00024030741945040c100c400d117400140b141760401000c0b44100710714103080000c401b05040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870639847 1250 870638597 870638599
    0x90b0108010c11010203060a0306180209011716050a1e1503020406030e070f0e0903120123010e100c06021b150a09020d0303050405100f02040f09052205030d02120402 73
    0x49120000c280d103c6080c0d10080d1a450303046018024100049031503130344240307020b00b0312110714041500031b43c0020701c4414007a007004180b4494101140c05850040101581343d102655400ea489440e040010302e840c20746114a8514241f03040f00c0103034440540302c015001d4541070703401088980011800078002d4000d409410042441c115407070b003001d10002411400c4681754440f141c080349c00d04591900341980500f42d020284010703c10041c100881304a13050103400c00388a03c1481000e030400d51b03240000805000c4d410300c0507110401c0e46540360701d041c018680485080c11a2464898685480244901c20811800442c12600d0030852030300401d00b04541103070426066800c0c1c454080c50400c03aa945200254030070400000310b0b002901030740085500500600c10303500100484c42021003950800c07100384458660000e8280101008401c030300000e0040e0500400c540d01e0801014440710301d80300c9418650308000d01405040090402c202d4001200c030341c10035522031440c1d4032410850b010603a012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 870641097 1250 870639847 870639857
    0x90f0303060f060c0507050f1201090f1e05070905060d0b0f0a051803032d09060f010b18061e070f0512030601080601030522051e070324090b0108010c 66
    0x42e00c1c0d0321404440c04d5458010010303150280c644000c11421040b203184031030b0405003075a8103414502080c4100c405c014090b280005d0215000c1c94070028206528068060b022542692040854000039083c402e4441c100000249038450780e00043c500c00700040003c01801c14141002048910000210b00818952505101a80300c3d0790907a00c3d10f0342e00b0900800213920078070000b06092400048043c40e001805c5440300d1160300c006403054024800c0f01c80180035403040301441034110640286900402780000054100806000c1c1a0300d00381071200c0c034074031660700440d03d910340c0407910080f80242c1c40e681440710365030402171600301c018184e1400140c070070b400380c0d03aa5940034202c090200c03845404142d4074a0217903540c020055000301009040300082404651070f40c8100300350401030117181c0d8001c41c0100890009055000e502c7c45440403001c41d1a00f04010410005000709034800da10191b00324091040143c1c1007401008204019000d414402c0710b6000040d00101075100801d4065140e4407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 870642347 1250 870641097 870641099
    0xe04060303050c0705040b1305060a05130507020606010503093c0a050114010b03220204020a051c1503140c1509100f0813151d070609060c110301090f0303060f 70
    0x2088119441060a01c4e000b49100720b05503181c0008d90b10050f8441401000400b100d5107a84c003203070010745041c2140005540d24402d102c4c0c3c00c1d40400c801c40d8019400d1030018910328040c21519121900b8041080881001c0c4844450301c01e40204d55510196030004025151058000416a107860201040c3c0d001d503e81650b0b10000204418202c0c1a15030791101249036886100c604408403030b06240c224941101c0c0715000340103945a000511008445580711922003d0f603600142ca00c8074914518010340b1b1610f800040070303072200e0f001e48048a0704000396008a10070012581c2c18000c2420300340794000545807054003a14180c20150090318800d40b080140900200b0003603035481250301c10300010401001c00103000741c0010340700601030b502c42c3c1941e15600301b1402c80181176a9041102d07030440d18004500d40c600d103804001d203038020521840d088414510b811000341084030f44103030161809011007900b02054609420400486a1200d05160080600d090082c010802405408646036881c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 870643597 1250 870642347 870642349
    0x3090c0a06030917030612070801060501120509190206070c060504030b0903030f1f05031504020418080304020105090a0305031b01390e090f0406050717070e010e04060303050c0705 79
    0x301c2c031030703841d82d1104c640c40304408000d00380c15a41d00002e045592250320b40403440d0b40d03040181b10302001030002030000f1480f2400c10300090214102800780440706440c1c202080021100001e452801c0d038403101340481c072080c150000c0780c40e502c950040600b4286d42407000180b40ca60102c014022680104200d03482511840b01d035030749a00c010f903614500354450802180700c47d000c007130307001c00254100e07141c4561555880300131074142140124201c0b40c80842d54104815030403e40602c8020981d08030340b0440503481a0354189480c040a80042d0400602091901aa4984a9040c00610b80107006c898881034254900401c20f621a01c11083c0c40d42441c0d241c480281d0400f10350111408950341c03c20030111407040002c4400b00c040d0400c3c003003000700d0000d030b003858446004c22070050703014003044170309868541030841c140e4001a1280003080122000e5001b44040741080c541c005401e4038001c66881e0310140103c0d64200c0302e00d0060f52007841c040002080681000080c0003040082d0191000c29607250 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 870644847 1250 870643597 870643601
    0x111f0219030f1404090f27030203030103030e060d140402030705040c14070c053007240306090f0c0207080309012f071404180c05130905010203090c0a0603 68
    0x200c001c0106110001e0700c01c00c6800740001d840f0070707220090002d0805030394099030405c0d500f21070491130407075590311178042d00320070304145414900310f001048641c3c00016170b030000d560784414400a0200301c0395591f80301d03e55a5800443d08172001078103042c05038080b9030300d80a028100940c0d04074828400d4400005650409002e4040c09903507645036444003400040505003203a0248401b01c4950402d6a8003041a03540e445a1040140e44c65008681060317000c01e40d0801c50000c0d88035050740340d000b6002000180c044881c0a0010212000440d08d02503d04805502030800760700700214103410005840103003c000d50000a00c06800e80c201c82801d5030320400182c40c3c1c407500c900b82e400503080994001c4081d03064015410b2847e1070309103060000040100b503e06046840d00075041903250201c40744030524190140180ca902081d820501072a429515910001090720a0b40e014181070101d032051402c02d0340c4041c030070701d80040095542e403426043d51521030b003020034258442c008400010134014464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 870646097 1250 870644847 870644893
    0x816150224072723030601060c0b090708030a14090d261204030f020f031314060313060e03040b071b060203070f0f0c050d051b010512060d111f02 64
    0x2045606203000e00708000c40f50010056003a504c51000c0ea40001241901c3c20007600f0700a110325038a82c0c0491000c0e1400c1c196003040505048040c5e0b010900500c0340c00d402208032100040b81d400d0490b504c400b8a00d0006050250350f4450345d02c03903407105100c8140203214007511030f03840440c0300c001ca2150701021568928041c940d0203001e000000000580081d000b1308440d03c111209004403001c040051082c035245600c00d17401100b2500903da020451445030b00c00c10581c51208490b110300314548490340302c8011100c00405030100352200e000074251102402294090004030991030b030346090340e0030b0541700c46444045842312485841700004042d40701205076491260b001d410070251181c3d81e01c40781002c0c2c21160041d03c0b000c81a1400141543d5001e4180c0303070301c5104402801401c020400c682204118030b800c60390501c02d041001520040055220607445131044880034040b03d0b041c01e1548024000386051508468007009480d000c00300180c44220251540d42150072520000c0c610401034071706 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 870647347 1250 870646097 870646157
    0x2e0507023004090504060b0a03110108060909030313170d09021512151f0c0b160c0b0a060302101106010918080a020a021009030507081615022407 64
    0x244000c0c0f084603038035041150002d002d5000030030191615030003d9610015944111401821000c01c0003035540c00201c0300d0783c000c0c0c00711103108840c90002070168603403100500030110600c1c0114503208005d80c5800f60000280004540c0b41c540425080b5000100091002a445681c201d4540c0c02010b107200102c0d82c240b10034001340032050312000420547c0304c031010030729940030341c00210008003105456084214440c1682d01d9030301025840c140f07170482c030030f01426a6207420601100b004000381c100d900c04c10f0351507100c0e60740c09a690381c4020180c02428150002940440119100b1032119440b500650405840c0810380700d0a907600d1048400722034800520800403003200800c1c0c0049904403014013420039060040e1403442150390300003080c2c99001403d110120307800b4441401440030400106021b094488020a505a00351150010440503807180d00103502c2c100ca00880028803e00c14441c00c070000c42004641491410b02d10024a0001c07100c800026459202c0070380407415500b41c03402071640c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 870648597 1250 870647347 870647443
    0xa14030a14030c27040f0504060b041b230304030306030b090601050d080a05090406290711040e0a05070303021c0e09010501180509040f030216082e050702 68
    0xd408860486129001269014130300d030582202d8103035115030040c640c40103d80c0300c001900b8685850040308507500d101d52103005a20b0600c6621414032010b424070501881814140c0f065014071100c1d120680007000050103000001c403d100425030190083ca0a50344510070381d50042d038030040150b0782d500302440b840390b100203150080d002083c100740060220600341c0c0340440c54984902c0c040740a0340c0711540143d0440035211039150328038240c1c0001d04c00014107484424680240c3c0e40310f0080d6920b65480082c0f0a0380e584141c801d07040d00400003110328680c0f04040e100c021390b613801d0103520352102d8161800861148083c2180540c824a402e030f0890300001c140c080300740d09142c011038403407110318070200400b903d100021035541c0d24100c0380b80c491403050411040c25016403500030f050401c41c242c022118038440405000126000c6444100c40001120b01c85403c489003818600c60156500740314a446d28001c144142e03164003240ca20142d4144040c190f800030f0701c465211101c00d401c401103c04c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 870649847 1250 870648597 870648607
    0xa0803071a0c040b0d060b0c0c01021b090f1302090c12070e0105070b0c040801060b0c01060b040513050a0b0d030e01022b0c02030a05010c0c1104060303080c07050a14030a14030c 78
    0x3412a2020308030300d03a1700351000104a5180d9808043e1680640303000c5015620504100803250380c104444020303036498220b0286002c48840c04101c4501340a80707a10014500c0c0c000141210900e104599803094008145420030b0802400d010000c0c2c2c041e5641e82c0700001c05400007100503004080200c0b50f030301d06a40e51480d01c50b09465145101c07202604801440b031041000003040b00d0240240b801a20505c0200d50380c0c1c0854203940c0f03003142d045038440407101c0d100380070410055441505d1062071240c80800454181d85034280c10005048400c00d4a90002c440318644040c19400359a22000001c20707022105601d801e80d020064503d182c10b18001d001e1112032068000358483c40a020a03144050110340310b000090341c0e101d0a40b403012482800150a425039081401014030f02d42c0205003003a40c041004a05580b4010240e41d00248000f012400c00540b44003004410002d140247c1d40212309400000701d1030720015129400200c46200140c60107170f80030798656040080761b004042c1030005034a45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 870651097 1250 870649847 870649859
    0x30102040b1614030d06170a0c0608040f02041127060a11030913020306151303020d02061306200610171e010b01030e030c10050603030403020a0803071a0c04 69
    0x8901e01c18102c0720348032a004070300d0140c10f080001c0d1089841c0200041446400d001d100880003100c0b5044161030380c050740c00400850b21850041c000d6400721710341841d8595903410104800040494025001482c1805c00e43d100c0c000f0380041c282c001e08040c0c4644007122407045503500400000340044d44100308012a407000c40c000d00120300c1c0e21035014140d9050116030000520190300e800400b80341c083d000000c000e070380d181403280380c3d4a50103405c1c8802c0c10000403c41540c2101c00e5808000c1c012000c1c5001c00e001e541d1075109a1f5001840c0c0040d8485440d00e501d0020018070041c10b13a092100410504040751403c041350007440745030030008022038103251031642e14001040c0d60a0718850b00460020001c84500000e400e894112110000301e44441c82000060880f4256a80c08041ea0400d00c0300648140000c01d481c41d49041d101008141d5841f00b80009065101d20740c03000354004464900040c41d00c10210140100e98055803c0d100c1c84817841b090010380c0c3c0703c215036210066004010038451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 870652347 1250 870651097 870651127
    0x7050307120203100305011b110d080406050604020f0c0d080a140f061c03020d0909230a0209031b0a090504020109120c03120e122802150a120b030102040b 68
    0x1302c942294001e5512aa032038039418212030f007a0080c4081d003890810304240a5030401c181c40a070000c038400404507016040b000410000000d8402045d05413a280400d00c01e6440e9010b8403042c03448c0e444529902d50700101450b55400c0811200c0c030116034a03000144220440303103e0040402090743ea00441c03550b0301140109848030080110b98881d0101036041079460928202c1c05145100741c004014614102c0c1024180810b01d9024035031050800003145000702c81540e00750491454200a110075499003860100a4001c208401e42c161183d0b4046400030116800a176200a00982d11400195166107a501c1074070400c84000c1e0203e840c0303110800440f034400c0240031800d8025a0300400d8243c41e40c0c2e0700d11030702101200c1e0400060345080d109489150454a00042c00b40100090005181d408100d00c1d041ca402003241c100307010b040400740c1c29900c928000c0e0320150440081c8a03a41e07500b10f04080c2a52a0a0000c014903602c7c0ca5507541150805100f145c0945281e50a2716051010311024264 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 870653597 1250 870652347 870652351
    0x5010c061116051018060c0903200103050c0a0c02100e1306080d020f0712140106260304083c0c130b0609060708130807030b07050307120203 62
    0x14005988405003445032154102038110b140314480d403208000010305080b403034424030310440075005207802c2041c5440003410206100d065400400451517107031017907041d00c1c2c0d400c19034401b070040702020000388000502d481e900710860000340c800b0025501e459503006401e0045040e0380022582d2000c90074054901710505012484283c0303080d2050b40c201e000815154038031700c0c1d2103403190741d01d8000074000340758140050103808174035100815103d98440e440b581d540138903126411002c0c016102a00c10b214200a54240c04000f003070013406415503d800510754014400040490540507041e5107000d903601000310380c1152040801400c41103d06030602c0c001001d042182c400170800c01428225150b90200c0083e502200301c00079107a1500e24200f0b002c0c5c07c0c0740b100142090a440c002280b4202d94a0006039040040700340e03152030300c840840c034180c500b910443c0b08071803528a00c8040011680f0000600e5800d036442181c5030340081e150390300142c4480c0820340c0d1100100e59001c580802c444030301c0d40036603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870654847 1250 870653597 870653603
    0xa14030a0503190807030902030c09150603010f1a0403121b02040c08010509010b071a070201180b19020a08160311040f030c05030606061c0902060c0f0f0705030705010c 74
    0x950045100c0d640c052465000c800020300f00c043d40d0251505103608140720541c458010b06050081820302d500003a110a00c010000307104107003080c04602c0250070303168001c1d404900902000d0b62561203103015207071034500e481045400702c0350170080e00402c080c010555048030f13489014040080d02e0400305541e528505000a85401c403003016000141c2c3d141e0290003c03c000b151101c00840d41000103012a241050700040480b0100300440d10000ea49218076402c50700c5074046c0f080041d195018128090250dc3da03041d01b804200b040f8210501c5410710056000704030000821101c603104902d290240c2c09200c080307a0114807960b000903568041c100c0310900044251500050005426004c4e407865003254100c0c1250521650b8140200040a86590042c1200f103004049526003140098254440c0700c1c1d82425101d00c5440301c1022800315000f420f03240e64014201a107910156034165920200842680224855803d58003032170140400c1d000142e46025008e0401c4c3c1d0300304001510004041c9a040f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 870656097 1250 870654847 870654853
    0x4090f0c0503070318060f020a08070f0504060e1c080307020c030c09040803100b03010603020405150f0a200d0309030206060405010303023004060504030b0f0f181c0206011e050a1403 80
    0x440006541482161007022001c2d1005841d4904009c000b080d028004001c0c100f03004c02c0741000420150044141c80c00c5505ea0f02d0700c860f400381d115010030341c104118010710482c0214000c01900300403101000c0d6109100c10b500300d41030100200201683d030710426507030302e420411b50300200c0c3c04903101800466121007110200c0d410709a84000650040d4030076402240001d0b404241071002349003130034240c034014507a90552402c103070040da589103191140312024000e02c9402c00e00308007520002e001c111010641e01040d210b43c400301c1c00018000e0155504110010b02409000070304915181c400c00f81a03940603401402c0300e202140103400c1405030090082c2102d5010719000020031960380042002e000c1c0d070741d50700b500c0b2882c5140074500e80c2809003014561205180030021a0030300d040301981c1c0201c100651400c40a142c243c0c02c0d003044010700018440d030a0748403901c2009900000c40e07504a80f0445140302d072449282c407011000c0c00060103000e500c4414440200550700c024407103507498140050176 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 870657347 1250 870656097 870656141
    0x2100c0201051909150903110d0c080106030804050918060a050606090a030f0b1614160203032b0612080c07211109192f04090f0c05030703 61
    0x3d040110340030280c80c000b5122010034801c0b80e804c156884920340d4241014580d40e4110f9072190000030741c0e001d4441c01001c891006800303200b20550840001c000141c020000c03070b45c603410856a1548540a4503008a00ca9404510580700d02003600f802c00c42e00c04007400e41510b551000c4006808098946944582c043c803030b17440955a404c1d440c0000f14464001040c000080d0b1808450301400200041710401000703103610202c035040010b805071a05107402c0c0e80d03611140500348045903020120302a4040c400800c00e03009151050040280760038040342c440d2410f0540d034200d4015034905000da81c03081e80c2c0d060062000100c3d648041d00c40d82c4142425182c0d01520ac948288002c001c407030a500480801e40303034007400e10058010041e800030701903d00320054600640c200384030301c40303000380610300311742ea0f1b10101605c2102100001c800484c803010200e0713400c40300e18a80c1240e0810b000d06200c0d40e10304035441071382c1e000e81c0c400c0c0316100607a80c940c5030075a86c0d010b600b90001c002081da80c181c41500c046d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 870658597 1250 870657347 870657367
    0x1a010f0c03051e0d0f0c170a090c0806190507050d020f070501090b1801200c1203160305010f0311090703060504020706050420060f13210506100302100c020105 70
    0x141d10f40310300c40700c142c0385500c84007100c1055080c0d800000c1503990852401600640e103a40c00880108034007526600b0150f11703183c40c100c1304000c000b076040c080d0180800c40c00c042840000858141e006a110600100f129000b006c2c04600300e804c00c0c2d4a00020840802201710404000d802500380114418005da0038002d0b192105030039103c1011b000c8405c401030408000c808000a48003900150b000c0e4020080303481c1984980c0c00c0030b0341e0803400304a00c000105401451700c900304003691a05a010b41b107680c586c280002e1410120000d01c540303202081c1800004980034900342d01c0d0604503904480a9032081480400380010210040d00d000e0405403079500c041800c0c0c4803400201684c51003542e000509140c54200b402c000725032003101c10180c0030901d058014a546400c161548201c1c02d100c101c2da5955001001c00c000c0046034060301d4444e20005820504504031480c9044071801407041c3c030f0096a5054040d0790101040c08000e6103c000640d50030495031241a4000c41c0d248107041051038039800b81 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 870659847 1250 870658597 870658627
    0x1f0b1801031b0b033601090516080609120c03070c06210b0102060406180c09092d12140c16080a0c0e060303040b030a0e011a010f0c0305 60
    0x40c0060340c0e04a0b140c180302c2d07401c40034004100000d0101800c01e41c19810b100065210140880a0841d008103c1d60710002040c000880fa6400c0e603801d2500821035005c480c0307002d0b91600c0503a05003d1640c08c10b208006928100407031618819580b007005000110407094070000c031707a0003030000380c0c14520041c4071410000f09078071001c00c080c1c4603544510700c007560300c0c2d031480c0c100481401110f41000e0400912100030303600041c0c1c140d0850b0b80f080c00803807202c50300322249280000103140a8010300000c000000c07810314070351000c1c4856004a001e1114030303240050000701041e130000da00300b00034074202062002c0761007030140e5010400c6a240ca85002910458619903503080089090703070640214000350040d0380754080d401c00601c0000003400300c4840c9521030314000045442021841a00000080c1d0981e070140212400b030142040e1194990406031f40410051440950100c3c19618104909280c000e0560000380305a4059441c1881950808002c854041166000710180002440100f075054048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 870661097 1250 870659847 870659849
    0x110c0d0213060f080f01061512050921070b060405090d18051002010e070915090209030f030304030c0309052409011e0329030c0d051204030f02030c031f0b1801 70
    0x880050803611108000c05d42160340c990b125480050b6024110404c054205480d202e101d1420b150004030303130341caa104241c00e141122418061808200e04510b2383d03483c070b0314003422140d405120003254071b0f40d401c02803000b129001d940b881380300c1d40202c0340300340c4140c401c0303030b081c020500c5201c4460040366a65000c15500c1507924484009030751581d0300542d542000300b081038000c7c01e1001c0e0a100396584d1500080188410b400390071200b58000982d07500310b44003040b008820a6407101143d03a80c1c546400e00400801d40300c041200040c14410000800e850200044080303400d9108541d211a907041c1c046540382d905c10000e042c140200707950000080b0400f001300050000c40c6480214215030f0a091040140715100396205052100940500d000e480c0010344030015142912800d11749100c031b040061820b4040701c5102003070000098048100001d405003130a07894402d4084510607042c81081640301c07010000308200802900c2c02400d4038190b25002902001400390401d42c1500ca0380f49607a400d6482 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 870662347 1250 870661097 870661109
    0x1a070c212d0b160e012712030306081515060c0c03100e011401120204150b03040c030c090b03151003080304080a0e0d0b06060d1404050a03110c0d0213060f 68
    0x54004024080da51503405043c08181131811003801411a000a8004d4021b41c4241041444842500c0a503580c01d585200180c458403548510005e480d1a0080117080140a094100e0003425184e104075400120624001d407101c0c80a80400e41c01c40c010700003160440541c3c86060700c20301d00c2c400c5d0551000d0000c1050150315041c04030751262032032003090945003407210310f100031741d26100104030040358040d04001140d8121000714802d6842c0c0c401e110002404e4010041c201c01c0001407000b000684c500c0c520460740f040034490290790b070b035a400c00101c40410808940540210402c3c01d9900340d810016a80207490b0551300356500d0300c903114043e0a410882d01103514400c00101c40d01f105400840b083c0a0304811500031050b8000384c3d94402d25000007501c010701a07440842c9481c0d100c0d095401142c0115a02804903040389028109a9a05c8460301c130182c02080084818600c1034070b011418040024018000d031560108a40c241302142e4092149542142d9841801003804e1070400254002004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 870663597 1250 870662347 870662363
    0x604110703030c09170606060706021210081b0f0d05030d020c061008060403020d08072604030f050c03040612140906090c0d030e06090a1a070c212d 65
    0x321200c000c2c007018420317086416130501c00c0d80010404400001d032568072410948803103484528034500740000c2d00805040d00448460b034400c00c080009504004400c640440040703c40110b58203403c140e0480c4003403048c2d90440090300c00e0383c540f070910210480c181840b031402c81c0c0c5800c0d42e5104000403604100d0741100c82c1d800040c05c0c0190030120b48074640c043c02d10607014010600f826940655191981001c8034140111131000882e582d0280448840d44102c030504850b0700881d0901d1100c00714000c0b58210040b45030818242801446003081d100800c41101c001e516003410300c0425101242c4010180b6a525100c9241c1542c6d00150580180208c0d0342ca4010705050501840301801c111000186600940300380d41c00d0070100354481e1100d80030310804d80d00250354511800c0491084100ba800000c4204448140c0041c031715206401441083d0003000d08070314160316080d00700348000c22000c1c2c90205d4202840f521b008900300c0303003604203c002c8403003001417242d54011005594080150090744e0b00c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 870664847 1250 870663597 870663611
    0x6060c0c05093106140a05070f082d152b0327180e0703121202160b2202031504020d0c0f05031209030a0b07050c0f0c010e040c0207060806040204090f02071a10030b060411070303 78
    0x1050103030203101030480c0c51810108209240c143e0028880302c83cde0028041240c0c000e510002d0310003442c550b80320300380c07442c61009450344c462240241c08640700001c0d4090b13a02e00b40c80150700d5900465400d0070781ea030141c1002d102d103030001c400300e40110106020105403613080080d14041501d440d14103010300c0c403e0150a403a4608030056007040500d4038914064883c28202040040c2d601048411644505000104490f1a28004218807030400385005012403580040880c0c0d141943c070f010000c41e0f008500305d800701c80803513007241c2d4580a421002900b682c041c0295100140c0b060600d140d02c41a5171510394207010b41071204501d4650f2a480c0300d1010b41201900400c59640054201241c60090ba024400a00c582100070b56070f82c450700c507030010001941302045503540c0d940c040310014030f01208280080b100010101001b0361202400310b0303c80010121428498615000143c401c010140f1380380360591450300c990203508002860b050784941d5810f4214001405000900b04490080c0d800003800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 870666097 1250 870664847 870664849
    0x80a050f0d020601031106030711060f012313020d180308090d030b03031204050f0114061003090b0c0a030f06060c0c05093106140a05070f082d15 64
    0x4140c09000785411508510014408a03484990b940e810b29010b5071801d590340c6d2044400c84416100f403030321200500690003072000c8200000c4020b4107a13103441d650b003212108801032490149051403615900700c48881c0c500341400a440c5c1c09402d8840c3e2140000c04c480c44501180289980e0244044000c03c84171300c140700804c5c2080100004480c168141040100302d1200040c1d50380c0540c448000d03a803046400000d007002821310042a54050f014003d000501000c001e00440b644112081030040c2e64010a2400c60f510902410034055001092200142c0350302020a42035400401e0040505848003c0181c2c6608a846028024034142e40c840c50034620700c0c581008000045d62100c2d1080360a10140700d45400b14038240381a80e104c0801540380c080e40b2090000701c03010b000c040a0203003403605601e07280020315008664891842c1d00c42c2081031fa521010280c0d07284414068000002e00034800080381400f107556000e80008101c00859800044003084503032901d8105d403117050306c0e10034075054401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 870667347 1250 870666097 870666103
    0xa031202060f1017010b130b0f0306060a03120c0206030721110d0b010e03010f09050d0306030515091606022d0a0b1909050303040b0a0c020a02040f06080a050f 70
    0x1080600080d0500780c02c080c02250b1030700d03003d801040b003001d4809001d480303006400d604c40200c0c0000a082044007406000030403008001d03e00405000f011100600707480da24010490a01c0717484000c0042000c1421901d54200b1469a1078010301445946801d42001d60780715400703144151180d60342c1141c000403040d410200c911450800e08031060030104011405112002910440c201c0e04900188010076040101c0d4604034500c4490341551920b4200c3d031200305250441c44000e401102181c007085c2e1140c0b01241251050702c005803041c1c214080b80013280e04181040c940104808013181c0042c0c80c2510301d081044415030283d00541d1080d4100380c240c550f28041060103a0803a110401c0c0e48108021701600c69242e40360050640002000242c1c040700e10039116600651502c07802c10130720055141c00c1b542c90b807003030b0380540700640c5420000d45209501e0080989910140d800380c8851543c550900000d416181003400c441601c605002c07801c25010000003032064080c2d0700800316a540c031192641 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 870668597 1250 870667347 870667351
    0x1103040309050f030a060c1b0b1e0f070507210207060206180c0d020a0e040605010306150510030b040b12100509011b0c05070506040e1b03190902040b0a03120206 71
    0x40500060f00601246980210380c0c425046d41054000c2000720529404540501c0c03581102c0281030950441c14040c071880007401740c4645202e02c01c03600e41e18010401c480403003600322410105100600b0000e8011351246018007203c03481000e81001030140d148000074080c0240303505800603400504200b100c00e40c108050303a000072203000654401c1065442c01c07074036482281d4009000d003803507004c0070f0110b4540c07064220040c040c4e81400101e5082c54908100079003000c2c0700944800f424241c4000044a518040100300d40300103114442050408000364041c03c0c40c0c60505500950300e180184150b01c5a00d080482840080c01070011101c00c14050700031103401402c64081a0b140042484000002040440d40c90919080c0a4a0301d14545096881c1404a822480c2c00c0540810001090720b45500d950f8012007000b005c01800d9829080885001d0100301d40707500c0c803100e01c01039107801c003001944889100d41c0040e00c007240c06000d0101003040d9480c42c0e841281c40740042c500d07a5020a5040c4041c903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 870669847 1250 870668597 870668599
    0x41404030201060614070b090709050403020d0f0207050f0906010306051302040503152208041d0612390628090e041205120406020d0b01030506061e0d110304030905 72
    0x1c91044c414100031061030049100003400c1f9500d61001c546465002c000c880b00510b40aa07051065140600c2e00a407038030307006060704001c04c03588101204041c1c0007041140c1a42c90103804044c55000e003c0030000707085009003001c1d05241d618580400c1d1501e50310300c0c3c91a050560701c00540d07510f00e0a000c1c54940a101d10483d2940c103a001c003032000a001c1c41c240c8076040b65150b1881c10350f600e003908020700d03d40301e0350740561b0240780521b21b01000101e42c0ba00e15442450700301d030074001d0020941d05094891003044000e0741008920310311704800e015415100b00e1701120f2480340c8081800c030320000c43d100354000f2002c1e03440b01403124107102e0340c0d4005180c07140348286207180901100345080250368039120040e1005200c0c100c128100b00616100c0e2082e20540c0c02c0340c204012a500781410464000e50000d040700b1040d13802e064034001e83d5402406018042ca8000e400175151034651341f00e0040103d000402256099820006040310002034055104141840300119650342842c0c90b0241c6040c419900c40d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 870671097 1250 870669847 870669857
    0x106050a0902030c1207140307080115020115171612061503031202091c0c05010810060e0d0602090a0603060f0905090307121b03090e0c091c0807020414040302010606 73
    0x2c40d000391071360155a115005c084220b6035989541006488104907501040c180340f1010080102566224040318100c1c0c030f44420100744804c902400300c0c00e075128031510001050030a44100100070016200340d21404070542650801000103400b030415401c00e50000d00d2151014212605100a03486120500001000d40a131058035554000d0140707100c0804020000354003140140340381e10b6030313421001010401d181c403c400b47c0c824505034075416002e00030305000800000006040310342c8012220709544080e100c07001c403e92140200030a0711260031084402d59002c4c0014041c5865884500307016107401c1d1004900c9a0400e240c0001f0036083d90b018a004506010900c0004040401120182604054403500030000a2003e69100403000052800c01103414010014141d11440801c01e440380480c1c0001540c803160316010789400380e90340c6e0a901c40104094000e07140d1101f483e0010107071081e0380745070a00455800003412500808042d00700d403000343c4200002c266081c0700304005000d240c140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 870672347 1250 870671097 870671101
    0x30109020a06080c0d06030f120504050f09060406080f1c03060312030207060b09011d100303050a1808100c020607020622140a080406300c0e0a080106050a090203 71
    0x1e00c01140502c1468288140320300418100c8900c2000c9a40c1088100410300c1110b54034941440940c02200d410749000c41c0c0c101c080b00c1c1642c80b4400721380403210000e000d44018040301040040000000e8612584203030b558400081220b03040c0480c2e400d881d03003403014001e1407130742070003231110f003041d00f40381808142c5001d500b8070004112110001800104c1d190050b00c43c0e1440c90807900620781c91000c1075000d090207000245180c001000f0003151480c1408054580e1910300031058854040c0c0030003070100f42d050150242c59440b540002c50340c0c80c1c07485488540b49a4a02c0003c2c201605101c054100139290384014540c140c0400099400c905144010212031404150720b80e402e4402c0515004200d4205041d030b801d001030240b2030011080703240d041e21074040d41440c001007654024400c045c08120142c01c050310307414031002642c0700c241c403082010070a560550700f41401040c2c080040e0003440700c6892880920344880780c078800680403a000020303500d824441081202d242781c6c0e112076415401041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 870673597 1250 870672347 870672349
    0x108031e071e0212031207030209040f050901020405040f2901020715021633020a050102040b040f05061c0b010908030a12051f031e0f0b04021e032a04021803070503010902 75
    0x10696024107d0700d0f0058540ca10100003a001d8581da00c0c507440400e04240c144800c1d21010360080044990450b4200840342c4a0282d0300144c0b03075040c01601c245811552a220440450006918813890510640f0112503d0750301c0a007003034888240005c016031140c40d00000ba00c5084a81030060102c03030b00746901e03c580c0083c0e00004030900c4002403001c0ca10078000014045e000b0080b0240c0700707074010001c0d0f4640f91201030103205e41d00944251300e15804500b0001405042c0380d4200c0349170000001008c5200b017400003107035020380f0080f06821b0401186110019005070180050406016140d40315000058000c40c0c50003a0760000d0070700c1c1800384038818514000160b800d10541182d40c0b00e1f03a121002d815001c1c0c070404100a000010700031010382000d11042241040c0704d540305a00c2200c202c9241c40c004941da040841001035043d0700b503400580c6100c0c0c1c039195400203100700700300c07030f10404500c0d2180c5000c01c0c00e03030700080c0d200c03480042c440c0c2124920f4903040c84200044c3c4410340003001760341c22b0342d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 870674847 1250 870673597 870673627
    0x30c030c030623151f1d040c270b040e090106050102010522080408060c1905040302151b030c0109060b03062a07020d03120b090108031e071e021203 65
    0xa05070a9071030120090026050710b906225001e46502c5280c054100720b8481001b0381a40301004588180303000801c1c440c83d6500d042e2041950602d0f646c0d407442210b80081c1a403d800c0007182c80704154180e15070f00b0000321010510018000b43c51480030062342030410560150079520f250b040181964105410022000e18600c0e8003004800c0d01c4154012402a60800c030003144a0303908081654050130b42001091130000b401094104000e40c00100684d511b60421904c500070341c08000d51040d5008032420015101002800306801c030341944610354550304186034a507500c1405465a240d454403030580a00405129441f04224150080e01146c90010400c038100c6070200001c40c54482d08100800440300b00074241d5007015130290002035000d5050401400d980350340c828001c0601c3c02d000c0c00284038203020581604a40f207030030040d0b080101da48005845034001c0c4d03c0750b4a58140a111480c01301e4410381110040035040107110210409900502100f114031100700429039004100143c1516440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 870676097 1250 870674847 870674851
    0x1030201140a09080f07080d0306050a091a041e140f041202070b1314030f0705120322140d0308040b1302040c080a0608280c030c030c030623 62
    0x81c000341592081008001e842c0380c801c80d00044500d200300e521046200800086074001d9034125401c54404640402c400c9055503400c3c050150407626145041260f030302d01d03030000d941d4840048500c005524001c0040740445411a90039408803500c1c00c20100b0100c5175101e070204440d0106c4052615240c524007210b446900600000c2000039002d4281040620902640000d40f0f036858189503600c4480ca52004041982d014940180d840d0a00c0b5143c2e6240000322002801104800f502c0c0007031600e0100000328030728405c0000d180c000bc00400d50f9102141ca24214203070100500b51304658180f0203080940c07108285282d000b04a440031240102c0d400c0007007140d0050340b2403242c5043d80d2300d1f1669040e0700024042c00941044c240041c44201d141c015170014841c12140d9404c000003a603c0c00da61341d44241c80007800f07540400358400310103a015010101144503024644101c06960b0360b039a11008001c4541c800d441c114400d590500070801c46000d071040d00c00741101c0381c58005401a41e00c030040400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 870677347 1250 870676097 870676127
    0x61e031e090303180c1e080a0f12260a060506041d060103020901170a09061803020d020712030e030307020d14010b15030c070303150815010b2803060807180e0601030201 74
    0xc00528a25403040d4106030000384c2940f0307058400d070640701d1078481011f0300316103001c8071101c0180700d218201920bc0c282c0012124484001c01240d501040f28441240001800e0064a55180c07440800d4645403840100010841e8122080c01c0081c4082c81e080040d0010300b000381054010040c00c8030070380e0b01400c0d00b030034100c99000044194481d0a880001840c3c8500000c040c00d040030041420016040754080689000341c094030080b5010b0034040741c8030700c41d902803019102c80c8a4181d00110744150307000c224150000e01105d1034a03549170000b03821f81038002c1003110007600800c1540c00c030f61000e01480c0162002500e5440d42e519a10b40c3c480b0700b501004000c100c180c500492180705040c4680c01c041e04030000c440d6101002d940b9424840e440b040300d9450003207525244000021802069021544900e1740080da074142c4001203550300e261f0100040e03c1d50101500d40d40082035815040c4003100081040c40840d10394054803115440545a100d20040d0b101c0d00200010401340c0d07000512a0380c034403030f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 870678597 1250 870677347 870677369
    0x5010e0906160c060c0306031406091c0c020306040c1805100e130204061401170907030201030905150705040e061c08030a0f1508010b030601061e031e090303180c 71
    0x345000b10380b60f4900001c09482c01c3e04190200c605250554000000d4038040c62030400360312440003030207980304810f9425003095801252050140030203404c02d140004e00b00c0c80c00301c0341c078419600003c4c0ba05205840a80e510030f54010100404800319002e60303880c2003043c1c01800036142011844441c1d8125210b424008152600050090004a5002e03092305038002c03c02c00100b074450306c10018000c46c034000f143c00714200031030015004001c1b080729071180078000000d2a10030309690044000c0c0ca5283d008032110300c07815180110441803d40e016100301c010755034042d2180d1400100b940c0c140170180c0350602401c08010015940d5104005151800781c0040e62569651075405c0a2001400110703140307821503150100343c400406020940b41c0807544004000d10034482240d0805450354002e21075500031464280c54000700c4001d0103421a0012002d00f400145400c56481d540c00607001c00c6a00403c190351036211808141d00340c401c000e5810000f01012110f0002540c411484507007601961107a64 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 870679847 1250 870678597 870678631
    0x80d05130803132111010e0705130c0516050f07050111030a2a11040b0a0806040b060414130c170d031d0d020a17070807061a03010c0f0305010e0906 65
    0x1c076524040d030307120561001052041000d854005c0134071500f405031298a50030b2080661103800001619029140000e103000780e007003503418202000340700c0412403800b4040c040c044014640d0007560000e601501800140240038032074082c240c00c00c006a0803407410300c0600e11800405100001c15180ba4003078500307000c49072035502881c200141175007441110305401c481240707004211040d0480e045c9241e0580d801d00240071064100300040c90303079004801d85940301500040108010382100c136040321010b0b000203030700c2c01c1034140c88602900c01c54415030060003001080e0100203640d9082001002c20700301000843e01000c4040b0f4640460840450402d034030b580d8600d5400041d65200c02c3e40c2500c0c0c40807035481c007180c1c5001a44a0305a03450903035800307020801410341d43c0c100d01f007101c0380e455100411500e46080342d610900100345000c03005514400001c89a406910700b440340c69070034051a19926004101001c00a0556005070090040594803a0034804680000a100303a000b01910100d0801c4c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 870681097 1250 870679847 870679853
    0x919060b030a02100f0e030d02121c0f0506030c10080109090203071e05090109020a0e130e06010305071809020d0f080706020406441f03080d0513080313 67
    0x2140c07102e540a0341c0118500342811480d034010701c1000c0c070301010340c841950303443d045000c15850b02c0d007500500380582c00c07103115480000c903900018800442a400d07000f0400441e450b50f034044441d951030803c115503588e014800340380340401084081c40e074200d5020b1034107022581c000780084418440e00416546070946501155014407002d030280031860035003508109113400c50b807001141d51094501907140c2e20004142c0202d01c0c0202c401c618400d864180d1210340c580180160344030f401d80706c188500c4c1e40d03034a4000841c90501c405802503000d44e00a10b089401c4c800101803480c07806255040b054034201000d0016221684c107080c1107074200044002c05140d5080c0700449201d40d41009001c10310009021a8071900b048a45011094072500501d842501c0c40c1e000d1091389001c981d96082407104e01c20040c80d1801030428aa01c21101c500200d06503c3e001100c0c0013034802c9820407030741d00b01e01049400c0070240c10f109403544014450529851222140c4400b2102d03c800303050540d1003c081d820180034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 870682347 1250 870681097 870681103
    0x70c0b0f040306050121140a0212031306020304030f0b100503100902130b0d060216080406081e0c090f0f0415090b06040f090c020c09040803100b09100c02150307080f0919060b03 78
    0xf42e03030013510102403191464802600e03507215283300d2001021503940030408504c000306a4050300d0340250050586a56038441d0115004018500c1030f5048201d0004291514280105091100b43e81d03c0030583e55a18410411006065194403103054640ba000c0c1041e0f5039403062216031660415001699040b606a180d544c000303402c28058244000018000303042540302800702c4c858100036904c80300b2254454404800c44505645006880300203000c601c400b4079010020b44022440100002111001d50303001c6016148403800207461403200c00000c0005090341e009902403030404a40c1e29150604058900c440c03c40c0303a024a030340d03555481c0c0c0761413401e5000b008500c1801400804004d880d02e490724000f0060740c01240d0b54402002850700001d0440348100955075a840000c01c0301d6081c460741441105e013045050416030340003007002d00700c00c500c0740c9140042d4015142580ca0030500e1410140700203841c6009004455298005000c620a000d00050034150090b408103000c81c02065240010346 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 870683453 1106 870682347 870682363
    0x60212031509100801111803030705061911040902210f07050f1b0a140f10020f070215030a06061112070c0b0f04030605012114 56
    0x1005203441d6441c15800303a0040a1400f0142d510701d061400d4035140300140850342400181449503520030190540d207100190002c500e0070300c00c1c4d603130542e550400030140c6903040018a40110a07580341d4001840e018238121030311b51100d440d484044000e40c0490380400c035062891804c030300c004100840c101d203d0070000c01f48020b682d40700141030303640b40e001b403021941c40081080051703c5e100d00c03604520a05e250300c10060104200c6440e10450000e118181c404c0c3c0da52190301c40000b0314030002204024900d00001c09030b12603e6010154466001e1a08000e6002c0e94194042000c00010406103100e01103d603400c2c043c540c2c1e030342400d9440500090801c0400d4010000d4051004499002000000e100ea110f070aa13055031141d001d02e450b00100b1450841031400101042070000a014142c050324014110031038020381d02010501e07914542200506079195944440542c403014070240e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 870503597 870683453 := by
  have h0 := BRFrame.cov_init 870503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 870503597 ≤ n) (h2 : n < 870683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
