-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1648
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:02:49.335999+00:00
-- url     : https://prove2.me/submissions/66c91336-bb57-47d1-9c10-bb6a3e8474ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 296223021 ≤ n < 296402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 296224271 1250 296223021 296223041
    0x3050618070b0703030219121112060d1401090b1812030114040b0616060c050c0d1d1f030507030501051809150a1d0f0303010512031210090e01 63
    0x6000944100220310409020b810f01c24028200549844418100b00d1700c19240b06400c1c00c08a0408803244120325030318881c0071002402c40040c545400085400c04400070780081c049403242208000350410884103d4440c01600200b0f0000e11142100c3d141c9004c0350081110035040280302d401001c40c44031000203e80c0380c10f0061072a0640b4507400c2c42d10070000603140b003c2887d001a11040503190649460000348510500c41601700040d12403031030100c007513403c00c1c00c6010410006104203241907078080b403101c0150056040078003104400c501405003030014400b00341d90000c10003205420849124511030000c0030160350801c80340d95030070005da040300c0e020b0141c1900600c01d68500b4a040310b00d040943e4121a9a5040300d2114451018100c02101c0888440301c81c141c545600c0060001940620a1040d0054001e0f03c4140c950365600341c1d030780c0014407032144203051900f600140c51000f8400c6646843c1c500c41d0880b02d074034201801030a1000c691142c800460300d003448800100c28184a03201c912 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 296225521 1250 296224271 296224273
    0x20f07030b010506070302120a05040302040f0605090106200a0f020a090c05310b180604031e0804030f0305040e0711060c03060307081606020c0904080a0302160602030406050103050618 81
    0x1070f42480107011198010741000c80a42c4948600201c1d210020300c041c0c00ca400c62903480302e555034150f2040c0004d6458182c2402c3c000c40c1000ba042c806640c40100080c15500246441900b0700204400d90210034500c5d2a0903003c0d01031203d00b2020300c0031100401002078020b50784681a1070380c44401c0c1c0c084030407180c0c00ea000a04c0905c01c92292a50300603440654117a1b03030203400c0c185601c2c00051180c60032503070320909041c90300056044208080610fa0300d000c9004a81d1142400c0c07445d141c8000010441e82e00544414203c00800c04001c01403094802441d003100404c6600400780c540940703694040d0182800103503481c2d0020f4415481441443c08011443e00909142d44a69000c2c404640015015540c1400f030b112000c14140b1003009410542da0003014407103103052500c04042d080450041040307029990f107004110220f00309900301c8541548600d001aaa52001051510041c2c082907000b0225030000040c0400e10610ba089181078074014015502141c0303d054007424400c00b03520b0b140c526 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 296226771 1250 296225521 296225543
    0x1505060d14280b07030c05070219090c2f07440c01030c0201110d141b0414190306140619050f0639031303110a0e0901020703020f0703 59
    0x21136031080c1c001030305409260400e40c2c100340c0194000f6540d0a03480c1680040c0c074501101c104125011402005000740c0b8a051440050031000d81680418442405048601d07000c0203035441280001c00500c8002e040c8038129010b0201040b4031420b80c0c410490b0f082c0c034900544911945442020154108401c0e0f0540c02485909180070065010f40064201c42096542c1c49401e050300700710302070081240c2180703041e0001d07041c202c04140545000003d0f086403150f0713041002e0140e4441482c0c049609850341d90780c044c1c0044203840c0005480e903a4888034000014010000002000034607000001c242e400401c10414640e184401d014504000d0442c2c2c07c201d02c080e0500b008030b0704141046c0810b50701e000c3c0880740f42440c40b405100c2c0452085541007140c0c0031408240148490400c070130b44c3c880320010069458074003100c200e83c44840c040c0c040500031030941d903058039250340d6005502000700f41800000941e1700d80181c80c94005d41100c5010b8001d405003d0360b6200c0c030304d40801e400082c7c035405421692 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 296228021 1250 296226771 296226781
    0x3011109010c0606030204060801020d050a06030b040212010204090603080a0f1d060a030e010908070b13021318211202070206030703020309030f03091f091505060d14280b 75
    0x1035a2859520706540940c0e03613880100c0036840300e0003001c3c0503000350b04c00560398900d00d40b600821510010040354861389098410f0002079100541c15822a404580c081d001c9920381541e140280f05030352058400f94a8030303000108014080000d4101d0000e1070301c502c102040701500544900c2a440c282050711042c070381100c016442c104025011103407540c500000d0b080003000e8880d0850742030b00c900355403950011515000304004614502c1e4442503e01803042c22050a502265894101480019070a5140c81c00300c0f140328614110210a2038101c99402680b07800d026403890880c9040e0341c020300103041822164040300c0075000f110503d50740581143d146589041c400c5000b5040038010301541e020411800c24022034100c0514020b440740006014124044c011002c1079030300100016001a06004108020904c03402c01e505251040c1d42c80441c0d241d445500061001c5400c560090004100801d6907140341d10000e048004952030700e00d00303941d2a400071420f034008000780100610384004100011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 296229271 1250 296228021 296228027
    0x1911040e010e071e1a030603160e04021c08030f090c030a08070807060b0d050601090c08070e19180f0e03040503060103030c080d02042d060f14040b0a02030301030c050301110901 78
    0x20340030501c201d00960f85500c40c04d00c514000c2501704000a10100442800b00500d4140f122800082481d00f4000c0201c0c5040c420051043e00104040e03c2643d1150a1480f4081000c0c5040c0226500252865a83c5008001c18000708020b40709200b0600c1a4040d200c500d0a0009030b102d815a004045c42d0305008140c1e80d51034203588581c40854a0603100c0340c05105c0c44d00d40c81c240e0300c04d00e489034001d0046503041080e40d500712030303034044503204111010060200700d540000802d505075000713582c1c00c612407001b440e00400a01c9182c0c81000c0c0030905010350301040b8000ea1069100d1103c08609028080c4d004103819900e002e03034058647d15800040042000078090340c0c0302e80e1342c14803e115070342c04c2040329003154040360015400302c1001c0038900d0a88050364080c1902c95250034000c0e00500100e800c004004000d01d6500a0070010701c0380d010110f030444d81221086c5da0041c030b40360a00075a03400405000070748940080c801124006003a200210b03445c40c0602a600d140045419400c0c10054000011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 296230521 1250 296229271 296229299
    0x201e031902063c100611011404120c1506060e1f0f020a060c050301050906010309050706030b130c021f110d050a0b1306061b020307050d051911040e010e07 68
    0x103c103881c0002c65200b03109128401070511510f0100c4a0301c20b850710340308004d071903126130780b810010340e9142415580f50b40d001c4034045c40e0441e81040445400789c0f00d03135005540d00c0b2000580903001c110442d10080000c1840d420000c10b560255031080241043d00e8140310044141512144001445480c0c80c186188140402c000c2420301e44119004890b50f0b40b514411140c4040310100007480c000010b0141c0e0400c03a00403600f1031002c0c642003000046540f14a44c48039010301814007050b445000c00e404965905036080300003540442c003000105002e41000c0e50310407501c00540f201c040c08040c041014941d51181c2c001080783d8030503642c82d010b003c00850b030051100800f8154913941c0e665010901da19040c4111903c403804041c000b502505180c00942003101c03c030351424080e5100322003500107842c0401c0c210203c5405440c440381e00000d81c9022803e2950044000c1081c84441030701e070091150303902100d06058030070340d81001401d00103640e1500b070765603101d411100e5a10140040064074000c0c1c142d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 296231771 1250 296230521 296230591
    0xb0c091c08070809190806010e090a03020706080a020d05090a11150a0e0109030f05010b01080c090102030f091c030f030f02070302150403050c07090b0f010201020901201e03190206 79
    0x16030005030400503110745ca200081d0009816603000c8001404101079a4078990b030400300b80c90040204030487d5600a60b51903241c0610020003216002099020710b458054a203079a620714401d2012385000d0b4940c1c6d82d03541e028407084d20040b040120900c080e050442c1909100041d1242ca103103415450102034803500001500203040207514000003010603510340b03a050741e0364854000803c00d4201f1200041c11440060807946a01ca01007000300920b81c0c00004803210807a41c1c64071507448075041c40015200183c4040b00402c04190441080d040640c1308424001c0700404c4e4804021032401912a9030483c065000f000300940d00403c004400c1192001c22a91b002d03100745042460003400c88921418103481da48000322184c5c44e0201000d40303240440810319002c0c801c1c4000c40c00d003050800001c0c4503e4a07040c5815400319401ca24000904013840396051004000c0707940c45001d0300580c0d500d55a070380107000c030011803a140c0d00001c5040e4800308a1600a4000b024540303010341010780098600592420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 296233021 1250 296231771 296231779
    0x9030f02180c0a0e06030c18040f0e0303070201050f19050a0e190c0b0f1b120703170906040b0a0213090905030703020d080714160b0c091c08070809 65
    0x20100d112650754801248070b941e441400d241ca4820f800d90144c03402052954440c411007050003081795154601080d5118500229041c68810340c83c031003c86c00904984413101000c0e801e005031a0a040c000000860003144240e008103e50341d1000421b20a028041e1484900900407244010b610b0303410303030000c0350010541c6074006140d500b5003400034030300640c816190060700f0700c61000c00e040c17180d0010950028110013104a02d081c9030f001461070203201e52000000c001c2100041c41076540780402a0740c0101c0b0350f02601d541d4070046410040c10481d80c1ca60700390341509810000130f42e00c203000b041c124019617100744c5001080e1901150140030b5000504c0c902103d103015040041c0c001310318058065014040c901a650701d68003070400038100f86148190070180103240090240e001c2e403007454184070071203031407003107071640f03001e00005042541ca114040c1611141c801401000b8840000514583c0350840e8516201e0204550300d583e1440d042c003000d032469005221020114000c1c10040c80020700c024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 296234271 1250 296233021 296233039
    0x201020d0501150905010c1e03090f0308030f22200319050d09151808150a0c020a020a09020309070b07030e0420270d03031e0c09030f02 60
    0x40d003281219026405007801010541c0310080c8543c22207914009483c2c203191201c02c058041c2c8039041d1580310550580c940102c040d000b4014944200300754400b510010945080e6103591341040c0410303801c00e4480c0d5082040c1000420f00c100105002e446080a1440d901d440b095499265609031040381345400e04210100020311015980500c0010200c800150503030381c0c1d502a5042c00c40c544040c1c1240d000a00400500070311065290301d091720220401d52400c084150080e15015035649801d900010b01d0380306400d500403454070780c064940d1080244071000c1003103030040e450483e61603104000107900024074010901c4031180d250021544410038400f01c91075540c5d20360024600f51301900003540000c40302c49180f4894549030081c0c00f4080c03407100da00c10350998901500d10592240c1d582158494681445101c03140c0c2110b02c1004400070003c01d001e440c51602d08018001d0300303200c48102c0f100441d0900c0000b07020079a10909168951781d42c0c407915058255915811080ba121001741e038004024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 296235521 1250 296234271 296234287
    0xa0602060714130306020c0613211403150f030d0f0305060307030203030f071505280902040608031315050a050c010e0a0f060c03050108030313060b090106030c020723060307020102 79
    0x19601c20780c0210710a0000680e1003d030510b01f00d0610102822039101c840035440740030b0210b1040e4280e0048005426031801715040d000e030050f06e03203212450f00000c0c043da021081003005401258402800d040655865080d21000410540c807011101000004204403500c0d03540107070f12a07400b29030300c204050201c8404541f2900028915044003640401841e00040e2900421840e100c0106600f200d6007024001d07410900d100310541400910302d11a28419101c00344103c40d07250f04404c005d1078001c0c00400034591640261600d940c4045c5190301d9840c80700c00b000820020310340c1d1142d10821282c0d58075080c803200c010201c6079503200c0c8100300400d640301d4140c241c40145c24020745028030711442940e04441c3c0745d0b10704071080d5901401ea0b1400e061410b00100000c1001004913517001b400313074980c2c482054041c50044020b100842140742c000d0001d1001184090b0154013812900c143d035021600c403561f81e420722502141e8031200c110078030f1030380d04a92041d40c1400c0c40616080a82800050305000d07a07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 296236771 1250 296235521 296235547
    0x9090c03021305060a06020a030c020402090402090a030c140a05031c050d060b1314030a150e061f0e040f0602071e050c100203130302090702030c0a080c06060a0602060714 75
    0x8807100166141d0b9076100f40700b51885c24aa41c9002407001d030003d011101c8003520044c0c03015501241c06805a90001140281030f0743e558116140c0300c0c03001340760805650322418034107840001b40c0a5100214078401203507c1a2921201800403600000e0060511903a50085460100381c01d001d10810b000f0306002c0700710110303414080c88018181a030441070702d42e000d00c0140c0d24a500e084d4010703402010390400703c5005403004640c520f025500440e000b200440a0b01c601c20040100b02440741040c0103000030712015044012040d9503401100e5a140c00e03064a03000412070056007990003c00a03500307148020001405034003d40003c502401385010014856410100c03110501a000c5445801503003002500b8502003642c0008c0d00c0301c510095081005407501c04840d40c80b1400003a109203c0035000800d458400c10480b41c00e0521441a2004540b03685824480c5800030044900740340a400c000030a01d0411802540c00c03243c0b15801801a61514002940c441c00e201201418103101006410740b60342c2c0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 296238021 1250 296236771 296236789
    0xb18150c0607080919080a0f05040f141203120a0b030a141005070813080c0c03070f0f061b060c0903051e0c04110f030703150b27090109090c0302 64
    0x6194603a640b4a1030014401c82c10884920a801903944c0d1000c20407006c1010716040c3e41c0422810b0600c06110b01c43c0110507503a03805140e011004891280e00e010924001c0c4d0110b80f031048000f03807520050901c0c2d01c0d841684900900000031042c0c0b8060b00051100c02281d0402c2d1319180e0301409a0b403211206464a08102c0b0f110718180205070301c0303c900e002c21926a840703600e9210f2210300e404517080c24074182014481d00035101c0600340603070200d8521840d40c420b01c6050b03544013008049401a035900c1c1000c1c0b44540851040046242c1d030108000740e00c0d8002c189407071502d110720515114204403503580d4030003428a50894010048020f8011000032020000350582044043c0007100e20a4204103a502d420796020500e80254140700400401070702c00025038100030b16000e0419203c4d942d0710030440003004401444048920741c86000114552410014000581449000c8640d120700c604001103403600c400c4125003100190004101302c840b00c0d40818206485131100c0303503030300d556a000115900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 296239271 1250 296238021 296238031
    0x30c03100e011202010206070e0108181002040f170d0804020909100504060203220c0b0703140f04030204050606070209150a0315051e0906040b0a06051809070b18150c06 74
    0x1828940c03c0d2801d541e01000b0013a032181440c5005080c1d2100400000c00000c800791400d0200e058001841d4892403040c814581016058001103441c0c583c4c440c587d1100c440248140c05594100110440540300013041451040e220f58807900311035200d55007404400e0400600700e1080340118242d00e5800e045601801d170195000e01c5016032681828928540d00310004800303e031002c0d1075544602c0001d81c500c881502100c02d40189c050b04c440d41400d054813000d808144c40d403803107500000e2000d074500f00180603006890007070340c041100c3ea6401040c0013441c459040082d5102208070002084010b0700ca00c2901610380c080c01080302941e4980d591414060f00c1c2e00383e02c07141501d07403040202c00700303004010a1440811003044551030030302c2e003101620344101900107401c80710740400040741c1105503002580284005410403040c45488006071105120030f4a03081e8150240d080001030340600070054403a410080d0158423801000308007009000d022000b8001d5800c02c0c18410b0300b80320074052040b03900ca4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 296240521 1250 296239271 296239289
    0x50109060b010306270e030408150f0115020a14120d060503010e0607211b0f0f0f0f05090d06020705072c06010305070c020a090b01020c03030a05030c03100e01 70
    0x18041040050103840980d005807560320030717040b02448000e44540d810441c1c0080c0300700019a10510841c0b15046d4481c3d138000c1740c441d10407000e06a902d80340c4085400e00c91804022400c0d81c90741c8a43d03401e0346c0e17691100c001c000168083c2d2203120204e90081e583c05800407a0301c00b02e5a10204501c1d0f0001d40c0d4000102e03804c002c1380e03a0102003040f070a0a0103201120300e03201000d001540341059014002c101070b910400c03228901006120300d205580d5202c01e5032100d0700c452800e100302008200902010383c0340340c040b000403000312024002074003603040400401801d81303401601300c5807001c0850312900003210f400c0e448103038500c022021924510080c1012802400500308440c2060320740c1c0300d400c0b1004003064a20107050903c000c0745103034900c5203400000910380860b594444210807103400414030f00195012503020b00024845019611113203420400f078094904004882c0e040644a02801581d0004601d0400010340c1d060b031160300a50f07000b504820750189854a40c00303141501c2c0000d070892000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 296241771 1250 296240521 296240531
    0x2072a03050106150e040204050a1a04030f060f0b180109110d021810051608090f1504150507081803070b0a09030c05040506030a0213090203030d05150618060d02040305010906 77
    0x665001120914000c4161400c7d4078041c904000300e91100000d200d640d0401c41b40c0c40e010300d07500c14003200701c2d4011a04650030042d041418202030f4001c0001e540c0c60040145001f00c030180b2403d1107640c009030f0003c0015aa40107a10740241000900807404c051500410100001111160301b4409012070410740e064031f0341c881860f107041c0070410151210300400d001c012300070910b185000a090320b00c0d050b803165409469030741c2440410305d0809024000c69014260703c811301595500c507800360044400c01c60800c2c4034403028480c103031800e01c100712014051080800c984030220f18065a04c021038207000c0d0440e0034841d03039111101001d40201242c01d000803903000d402c02c01d10009400b100c0103814200ca0401460425100180d0390303069200c0000c0c06074610700307208000c00b820341d44907500340f6030040d0691790f4403015081c0c3c1030014a800c90380030700e20041480ca540f51904081d82034640c0889003401c0c3c3c400b000601f504111058100c0752031424056001c100102c00201c0a0140000440c450100458 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 296243021 1250 296241771 296241809
    0x40e0a08090909030315150909071e0e09180c0a030506190e1c0513080c0a1403030d180602040801020c12250c090207050609060a02072a03050106 64
    0x42c40250142030300d883c59000f401400782c1e0410000c9800d2182c042103441140000346816a01403a006115070a07900590090402c40350303940080c0e1000842c840c0d9136180d0000c0016000948110703a40004198004602c1b20010f4000c06010400e8403840410208a034411292500080e12f101d1568004035401d400910134482110340c034070083e801d8140c21260a0148020448500741d5038440d070780d42c903111454110600b0021038055400c070b440c18022a00680c8038107803124245581c4081c1207101c10b010f0720101c0310018184501481c03107414030f80c000b00514940214503220701c01600c2007240e82d4940011101d00c56000840b00c2c030041000b0240100090386940d04040e54600340740010f504040c0400c01044070001314800152600c0c401c442180c1800d0f413a142c6804c040b80000b11a8004030b9105100180b43c80903c030300010301d01e200d0407841701100e0b030320703555101c541c41607015200c40100409403170b140c0001d40e485403460782941c000ca8400c90003c078a039640c41c3c42d1300390317106a1310100f202020880c107a2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 296244271 1250 296243021 296243029
    0xb04210b18150c09010309060f060603020903060105030102161203020405090a0504122f011503080c0706090b0a0f0e0a060e0a0e040c1a0c0102040306050618070c030806040e0a0809 79
    0xb2641050034950900510b00072401000c0f41c840c3d01901d40c101030380c4101e8007003044400e900c40c040004090004102c502e07142d0780054000c1d030103056141e00c00c0c4030b81d800004442c03405000f01d49426141205080c4008040e42d2811050314084110b00300b40f607000c1c0004103650b02d44480152041d03850240110301030032702d07042c102c0d03060104050601c1003160247e6905d11a18150050314452034010080010380b41e191141240145150440f0074107005022100000348907100014100c3c44208009880304242d0301c0400380c9941e0071510070150b1020301440400b00031b60241c03100302002c501c2414002003081070300340014003c148541019000c01d40e0000040703d0fa0506080260180407214106040707820301d9101c0300740010140c865905e08041d84002200f44013101070541d126001c031040295222a00c0b450851b0180c2000c0394003900032040c1c50802d004401e241a9101e000e4802a21008401c0c105038070210b030404d100070002a0099202e81540b03000100030000c0e00400c81c008c8100c0d40d11410040100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 296245521 1250 296244271 296244283
    0x7031d03070308150a030c150f050310090c03141014040207020609121504110310090818120a0819050301030302250b0d02030702010b0105040b04210b18 67
    0xa401a603000703000030070020f03800440054110319404810075441100d080010780880c40c2d07070001404d10280300300001da000100003000b001d03c4c45984030300f044d1030766410084800c0e010031100103070400038550301000000c0b1164068120f200b0a031034003182100000481580c0b462058901700b8200106000410048040c49004000d2810807242540303040042c1e00000d44038002c440607240b10f00c1d2503410300c00b1000d40170012040f5159448140241d0b600e02810801c09007036551405d02c0c024050728074080c20b002d01034402c0b021025403207400d850621001980d015089843c010300c551f041801c150031480c1c20f10041041004030340c0b00e103459550311940c000c0007241c0c03000c03000414000c1c00414401800000c3d000309040c954255400302c0b0010706540030300c803240b680740103500c011201d07280082e441560080d5500258862181c0b600240600d281d91001125148a43d114603610410700b48020f20259058a46641c0181103030041002004850b8403840b440c26029903c241d0358040d441e0380407807051414030139 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 296246771 1250 296245521 296245571
    0x50a02150406140d1d03040e060a030c060503150a1413180f050a20280b09010212030c03041505010302061219140109150b181302030703 60
    0x40c0904141c41c0080103044803900007140c801002004c60840c00a0300d0b281c0c003080c2d00c400ca0082c0445c014246402e00794681e8082c0c040c0720940420000000c030141003144004044950059680318040e241c42d1044030181c002500d2100c000148001401450b600d01c0c20500103840400a5041480c0b034103020004140b204007043c911080c180044940581c0b5035800100c3c40c0d54000d81005000c000c0c52030454140243c80c14001c1140c0d0465034000100104440218000d400540c0c1101540750308250303251030303000100d5280480d40f29892003400785140410107440c0031001030044a04030720340d140c00101c883d001102c41d440d59a0700032041006100386110040d0030b40000307000402543d410364011505500c691003241522211100214040924412815402c0100c06c00100a42c0a1031400000317803920a10840d48070074182210b802d409145c0d61040c81c11608012165450081e070038049200086201d0540341d80309291007104021140a4001503202e05203541d0002034454414801c00030b0005034541c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 296248021 1250 296246771 296246809
    0xe160201090c0905040c0e0906010f081606030b0102030f180306010b040f0b0a051209150903120f0a02040b13062a030e04020405040606020307060506030604020a03120203090d050a02 80
    0x5400200340d00354916800d681240c0c0c00824161781c0d03420101c604e00440d90140e45010b5460041044080380030454030306032002003401042940d43da2405958880f07460381d081c40350428141e400c012490213070f03108200710581030050300d003040d441902c0705801c1c0e0420080c00016032038800154005140c2400070502500e0200c0c86a4200303410919040c10408403800b41000f0410002003064140e4014015184244080301942c101c5107086044941c6600c00205212412080c680c040b411061020003562003e294110b1500700507500c00200c885001806010118015400c10020803021192402000080030b50111000002e2600354010040b40d69010b454240650003009515243c4035003148541a80c1c040c500391182040c184005002417085901250f44940b81002c00038a0a4002c006000c00c680100c0741004107640f500145502e840040310000d41c4440070702400d00000d41d0403009510700c1503881c070440e42060004404902c6822908805940e2030303102c421107070210300d0204600c0014040c102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 296249271 1250 296248021 296248031
    0x30c070b0c0604110a1a090a0f1d04230a1a2202121b01030b0a060206010509041a070503192a02030705030301030c03150902030c060d0b03070e160201 66
    0x3084030b52941d5003e0001800c00707040e03952480441d620304101e0805855102c810500510740715440814a40c03010710114040c4040c071200040382ca82d801c96020440703d00c1d440480c0d04400c8103101c1104000003c04c1102c10041e04601d24001c0c1c60314903c4040b0261200d4020301245c1c610341003241e00c50440115403400001030b202040040413501191078451039809107007480a01e614400102d10390b05800000b900761180c0102c211000a0624401c42001001c3c4c801f080304030a46024004805003038041c400141e070040d0700400c9641080720303185500c2406000800c04009140454a1003084295944000540044140580308036140001d03044a07040b410100f02d96046c010110282654040c8182c05e00d082c201d1100440c00e00034011200030551010030380e80c0c1c1c0c3da12032400b03024000c3c40340020b0344d41c2c0061444c0f4002d040120710401102d160002c004280c48010b800400295600880078540510340758a0607000d9031b00c08010040c054181100301740003900d8038410300745151031800220700c1168104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 296250521 1250 296249271 296249287
    0x120203070b0c15070e030d0206072d0f0519020c040b120d050901120509060411010206040c03020906040b0d0501090605060a0321031503030f081e0a1e02070302030c070b 74
    0x90001444040d42d45000c0181d5079600c416105045e003641070503014002c07407070032014003940030518904c178a04c80d840d103001c86074482200100c41400c0c00400316280b09242c403040506402101d00c40200009480c3c180e242026900140040741e003480040c1c0056484480c003c8801e18190081c031420b5002543d056080980414200360340f040000d405805000700002c84036842d0344218402060340442541c00d01441c01c0450301c25540d130004450a440c41d80110241894030b41c40030450f103010710b4105052504c0c0307078110f030200010090041c2195521a42d1088000b940d0303120901d591303d40c280203a000103040101c904142e03054a82c01802c2078400c1c444603000b40b001642014058009403040d05521424905a010940003040f0344610030080780b031000c07800020180e000c401c1d03103030280095480091a07112050f01c41c403102001084400b80b44100310010b07444040c40e510440d01d4210009500090010903901082240c0c060381050780160400501001e03140020401d00b402001c030003004a01d01441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 296251771 1250 296250521 296250523
    0x60f040e010e0f0a050f0d23070b090c09090c10080405030d06081e06010609060c06090b0a0e070e09061303031116030318080409020a021204120203070b0c 68
    0x440105108594400380c80e003600c1402d50000c1000311081e801c444a80c20040781807680c070310310300d00d088805200b8842c00e0300d0400c1c4003003481441d80101d510340d0160701030420a80742c0284080149a01010000c0c42050040340c401040580500f000c0070244c14214540307000e0140444c0b001708595102d503c103034528055600d03455000c0b5420328007468510700580700c83c9089070035441090718a03000743d801c0a1001c9042400170482e0040842211041d800102d00408580c0c1c98440c01d105400104040c02c0c42048020f000b0310500843c0c43c401c1c840001c0e03041e43c1c4d0341c80c091040c006503000e61005a503200544d8806038100041300281c60308610a4031141380c100e4000d0351b243c02c000c2689849000c041010000c0500070f03013015126052242005071580602416200003002d4000181e00103403d04d410741c2e4280c0b881c810441d000541140c01c191400c0c3c141001c1e070002c0e600c207501000c03c6204001e5100f410900407000341000e000314072460094452070307004240c507122954212850492003001581c000c07440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 296253021 1250 296251771 296251789
    0xc04060f0e090c0d02130608010510030606091a0706060602010c0f020a120507020d0501050c0a03060603090209162304060e09010f1a0409020a080615070302101503020a15090e06 78
    0x1014652140d6a020043d20100c043c3c01080000b8458218081000c80e0f400e81049041d4141c4102f40c03200090340c5c0a0043c2201035810301e118074008120320311418000020415064401c00041e021094640318040e9545411501142d02c220300603590740e4103a002069220007480390ba034003e88010f100340070868848050030407003440903e0a001c1d00040d11380440d2107828031107001c2c9801000800ca07034a030007480016640d101c11101b20009141010200340305000e072007510a50b41d0058001506552082c4160501c9101c0640c090306000948909808988107007a003003144407040c640b100d4543d881e201c0c025100901a0050b540700b2181c0d10014401d1007600181101201c031000c950f46020050040a07400030301c80d9030040000980001840b01c40560803070701c100d020b0001600ca401070449452260101d9005118000300140c00c003041441318200c0301c0d08844582d046c0d00060725445035407540040c1c01880e0903841040d260f90102c08001e0216003200c082c40040410b0071004e24546850000501015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 296254271 1250 296253021 296253031
    0x32508011a040207020307120b07260f0c0910020a14060105131107150905060c160b090712050703030305100501140c01091e020f03030a020a0b09150c04060f0e09 71
    0xb50303004c01d0305810b42d5020046000100300d002540001944a810a940d501c0012074410303000c298200b038200a00c0d00024000c0045120140c001d403071a8071001e00348118240302030074680d090f203408c0c0010300665586500c512010300c01900180880304031460b01c2c200703240c510344181c282e41d0005801002103458446000720b4403500788000052002071528000c40a00424030042c00110440b2072201010b00c1c940d00c01562640514100d442c59900c0350f61800c2a03124030803c0c182c6082000410100040c1c83d8161550814803140a84801a8481a0a190f0007000260548280c1e120140400625400d0b00c12141c100300c035440d03403180031030501001038001003901e0045040b0a0000840032665038082d4070010b0800d41c00302c0baa12a01e00d1300d0064280186449200f6486845001c01c41c0240307281c0042220819801d40e006881e24856907141e8401c44403009100c1c201c14000c044512180c8004200404d01c5071039010640381d107480c1012001002010070b03400384014001495085070b010703501e03188440e0340a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 296255521 1250 296254271 296254279
    0x70905060301020c0d081906151707050f1810020303190603020a03030c05030d091212020412060513050102070c060e090601140c030f18030111031009090f02032508011a 74
    0x548030005a1300e000800000358041842c505100802c0c115000c09c02c28001301010b595180d0002c400300300440e00d841e41900d4460106108104010b01505001d01500005150301c41040041e60500046132006040c002c1040c0140c00010400c10408d0912080b15065118180104551070a66012038040c02c260f01010f8107001d842805181000310410899003961003a101c2401000d489140c031520420300801c2e008003181c183d44e02c1402001180c401e8408841c00604c82802c4801c1c1511050018200501201d000c640303018054400f060090004005240c4103880c00200a840c00e840106041c2415850790302c218105014007505a1380305103000c242d003041d48003480c1c0d03848150198620390310540d90f42a0100e03002180411400080c0320001d1178800080d4004c1c41030384204111029140300850750410480c000900c00d01c05001950300110100e882400c0400e00c04c0402d400080c90444940c00c10503205640380d050540c020300301e140c0f0b400148040341c000e01540c010301e009060305080038400c240c09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 296256771 1250 296255521 296255537
    0xd093002061902220509090d080105040b180112060506150d0b03251802030405071512020d020a090503030901020705090c120108030d0608030403020a0510110708070905060301020c0d 80
    0x10714041da0468601000c0c140444d40300700032007040b51400c08083c1c13103520b1148200300000783d110360001c1503007240311025640f90380183c1c0c208400c1100a1805010380f03900046075103200d1001880312501c2c140a48540b100390001c1d401c25240210513908000c0c1070b580688a82d090b8249030450303c006a4a480081342d90128500034144c0c0401e103451082d50641000a0030407000c0b01c00b0040c0d4030310740020f841d4281ca013515031034541c580c0340050384030503580145194803589007040581000010032000c162240b4100d45000a10354038030f020780c0c005c030b074074203010590000e12507410b40d4100c803040c8001c25041c0c025606245107000040d4840b42c10b4412980100103600005100b4100502181c00310070032a0160422940c6a500352076036034004152000c4801d107811800300e014940041030368200c9a0007040c0000040c10031041c8403142d10303428a450240b0072089a00703501e0b0f11082c4580d00c0600300070310003001110f24011101e015104041c103030700c0c0282d01c10003104244000116102803400c440f818440c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 296258021 1250 296256771 296256811
    0x11403060d050f01111209060115050a02010204080106090b01110604111210020a0f1409091b07050d030213060318030503040f051c0f0809100b03030d09300206 70
    0x1041886803d68035205510305081c003d01d8503282d80150183c21280d40c072014081d900c904603666120401c0c014605040c00d0300d801c91402c03e10850007810301a280d03100150406c0d0307456030380c02c0c2507848541080454a132a0302002d001e42d6803007149030517804d0b941001000c40c0e040640742c02650200c05ca00040c0256045070f511541414104440740034042072450442d502d030541e48e030040110032030b4150030001500a0203444a42e02c0b05105030b641c6814018050940c3c2d46810f00c80d41c1000441550004c8004400d10040e0b020032003d020300149003581d6100580d5410b102c14400040071000e8100300c00b41071600c2d015150b503001c0c6400340c803441c40c0d041c101140d0340c0d00ea600b01000b0007544805d005090b407181c0c5103042603641404500000303a0482c0d4584140041e128602030703c002c901240d40c5086540100034500031840c842e0401c120544000d420f0380e241903030410019082c3c1d40054015034801400511121b51a508a560b40c1021140c83d2030440c1c3d042b180000094503228054003226642c0103480c840e038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 296259271 1250 296258021 296258023
    0x9151305150403050304120209070801150c021c050106060e04020427112205060f0a031a0d0317060d050d1206051e010206070305061507050109080406080103050c011403060d05 77
    0x28043c540080440791200da50b94203248400a001504902440032000800d003050f0194040034144c1d1180401e94104103007110003100d000f4203451050303900420b508598008004a801d01d0403009000303900114095052010143c6002d4807010b1550040d8410841040800c800c65041101019000014040c07103071562583c401800d00038504514116000440428806114609500050b9603005404000d035841c001c001e01c9001e10130405404010401412601c284a0360165180342c0c4400020340e0301180c0100810075000161208070b01240c02d60405080d00c40d07900c94250740c8403100310f81c0481000104d9032a6616041303118508024000490175280309c4265030f4204c075014110260510b40c03910300501c0d991144110410010340036004007400b040c0d0080c07003802a01d01c1a0000b80c044203200d01003903210241030b4040a0150f425559510001700001ca0100081c001001030355900a21035056090907030600c0c3c2c8200c085414440d06500c0a40040400d406981c4e0000044803c05c014000a0801c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 296260521 1250 296259271 296259277
    0x60603071703090411070510060b0706150b0d0b0925180812090907080f060105090f0306010e090d03020406090509130b090d030609060e16091a0915130515 68
    0xb5407040c00c00040307400100c1c17008043c0000c00e0142c0111103000f69403500b0340302201c800740608803540000304848400b0030750b9501300c20b2414040e001c00030314003541d80d4030124050b040306603011101603da0000c2030140ca4151925a041000d844102d40c400da603a5020442090207907011905004246030480c0341c3e841d0a09508009182020503148046d1511080900582c80720303250a1082010038081070b800b510070b05070180316000d80d9101940d076880c0c0e100159400e400c1901403590205ca00c040740c0703025403810b0140354000c11502034480d20300d08120040d5418800407180ca0020540305202c01c00c941f44d40080e90030110b074426100da104548070802d580045101066000e00130009001c18499034090000c0d2403544021b4a60f000c01c080740d02d46034000180c1d03803140310f040c10f05021840403440c2044007801501c100b5585003050003c0507910f24005280107114901ca00c5189408103180e09a03081035114409001c03040d6805601e4107034900072a4661542c075015450148440c4161280e08190103411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 296261771 1250 296260521 296260537
    0x60d0b030f0703030804060e0c010207090b0a09021b060906041e031106040b0105040e070e040209072c150702100c02030f0f0604020a05030d0504141c030305090c03060603071703 78
    0x2d99a00540303e050141c1011800d5400303c50062400388903460055000c40c05a180013816406030440b94038004c1e503040a440c2c069021980141e840000242c808036520050851880c08030000d0107030440700010030300300300c1c005051900c190808010000000c1d42d62a5030001c400900ca122010083c46007812110b044691881840b240b007102d06000502524561650413248201c40500500d43d584200c2d40d1940d50030b12980b007685403240089401843e02c095880e9000141e0324102100c1f5000c0c42e907501514082101040381c81c107071512004400e0a1054034203100103407011030b13989095401e6000c202d8030f01d00d5024440800065078841811550140a03101c0614029005c440c00000a640e8850300d405061b60124072800c0113103000150b5040110b5108a004c109813a040d060501d0030403404c4005502102140c0e02c08031008155201c0d0907030322100c00d0694040e1b5400109442c6c0781c11958501406511528445e5124004010980d42c0000d201d0707040d80c4205120301c1070220f182c83d6a501e14025502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 296263021 1250 296261771 296261773
    0x20702060d091a130203010c0216061101020705030703172809060b0306100609080a05030f0a03021c06032319030e040c020c0108010605031003021c0209040c140f060d0b030f 76
    0x400c0c013001010755400b00314154002c50007041051000202a03076215a241c0700200c0c80f0002200410000d4090382e02c4103076903801c140000d460030041e0b50314241941e016003004c401254400d9403e165203000e10070155071260f1100200c40350b01c0450042c03002e46032103043c0c007280c44030340761110203003045035035001804400d60103011603044c0d04100c90103000303483e580c0c001e400006404140c0003c20007000151450400d8001c4040c61401c021040c6c2c901d100d900006c41c04080c55001c00c4501c0800c40b0348007601a1040302c8107400140c0900b10324242a800039480008208400d0717801047d010790308081340460000712a060803030112031075403906540c68007808040c1c540c01458200c040701c2c115004624107100340000d07030f52000280c0e02c41205441c07902080d10b00380d10b25030001809100506200c907041003030103404140204c000b800780c1e001a603500700031031b411199520301314010804400f22210459590303030103e130079101d50350102002c143d0380d000350103200f400c80b62918100c591649040c484201c035491488 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 296264271 1250 296263021 296263073
    0x1e02120f13080709200412050304120602030709060507211101050f0601080708091f140a0902040f0c020613020d050d170114060702010c140a14070603020702060d09 72
    0x4000700e0f112074a074030503018400d082403610000c094200d010343c28120f14243c0c4ca00d00703050801c81e150302e45c1c500340c80040b2403d02c0200070205801120460f0501c4240c8070790340160b502d140c1404000c040b05410391200040c428284803681c00512038588615072807240c01c0d0100c08803241e9880890320102d8200091045510700001c0c4650308080b809114800c0e01c1c03e803149801921050000c40700e580c02101c40f0384e1240c0114203590114034851075a03003905c640b542000b16074505054a42c3c90262802c0e2007074030500d56200c1100c802c5052501607094031a90f0b014042106c4074043c2d10194540d800100443d620b440294031b400219604c240301c0f94110f0350481c0031101500007400000d404805900618800c0c0718288000080716010000e000c208a28090121400d2098550064400c000d0340c59080342c8440703030041c409800200420001c03c085009070540442c007645c2101c0340341062860b401900800d80100070200143e1964011141c011030702020019080740745003040c41e405005100c0c000100ca260b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 296265521 1250 296264271 296264279
    0x100b01020319020307111507030c0615120c09050c04060c020d080307080712090c031407090c05120117060105060a030b060f0d0e150604090302011b0f1e02120f13 71
    0x101900c0546d104046501c0c000d00d0300c008105003017810703001018200d0380400c00f100c0020f1003815030303144051050102045000f10590304041300b0719950002d041074490320b140e060500011a08030320051015100c100700c1410020f00c1c640d0380780706074003401003440708240c298011525183c003c58030554000847d5602c070705103411300805a1200b43c0341d40c2d001403801045d070400c0315082d2180c00321066210585a403c2403941da10041c210070207410640b8180585c22000072806030301d01680315003e4486e581c07035a8820712401c5044e400c0006030803101d0150071480c040d01b2080c1d00015150305544023103503165160748101204078007a00d41084402c0d000764010801c2a02e00303002c0d60140844003000c800500c001c0403800816070369410540d12160340b8070501303c04524a030070681e0200050034001c2c800400d0707294003412106003c60340c482c00c0100141d0b10000c103d4a0b80d0b030200100d0a42c0e90f141181c08034038010303858001e5541c2e80d1102030b240c5075107001030b01c07420602e911400c840c0c1920400012010265039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 296266771 1250 296265521 296265523
    0xf120603031e05090d0f0305090a030503030603150108060612030408010c050a030b010e01020607030b040b0604080d0305100b1e0405031006170118060c09081006090b01080108100b0102031902 84
    0x5503800036162201200c40c40d02e45036010308251003030900302403c10100c020b000c2e11115141c91000c24250284403041024007800e840300103e110103580180000c1d80d8034144031060514004c2d4000c8004c0d020035015005029180d80420980d40100b011900d4007040d0080d006614110710486d484110350b0340c82d10f802030301d015400c4005040c080b21107482c01c0014024802c01552015240c0c850b043c010b0b001440020b050718040e81c0090a0103101400000350181100042840c607401904054056440f100c1c4d051040380c0c0c50301403240d020301501c1c0f2085015151800c1000c680c083c00d510301c4104a0703956400c1040340c14400541740100300040c1114125541800801c0c010202d902600c0c01e454001642046158414029460324010f5020302011174011070702d0f4000145030103003081e001c2015040000550040810181c2000740001d07900080182c0341120740404c8a01101640d818084000f004110f145004210282e0041c114000441c866025070300407419441407032000c0414003a508040403100c0d40c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 296268021 1250 296266771 296266787
    0x4030609020609131b0804030503060415050a080a020909010b010503010e130b01030b07030e0c032107050607080f01050a060c0209071e020109110405160c0503040f15120b0a05010f12060303 83
    0x40d280c03a6821700d0b043c0c2c1724044809490803900640400c8040010944600b072550101e020b0100b1052260010b584800001d9a030007240d5005075135503401240408250300d00303800f04c9071f04120200d008001480190380040c26900051080001c2003407068005101405a2410410b5107030380310810400542e1640b80c0740000d02c0b001d07039040c0c0000349400d204003803260380003031100c00182d0000e00501000318501c00b0410018107901c10a6540001405114002402040018000e5138903441c0d081d90703072421261400f00c6440583c40b15114104503101013107920f8101c0b101e1803d8035010f484504555640140a54402c0c1008080c8551236421079076004910b54103611171204075200341e000354480480281044207568064a441140700709102c0d44000035401384900c828038910420039282066a034404141c51401c6c207901c10ba10380b48402100c1c11276a40d00031811980100181c104001c965481c1c4045048007410380034960604c0101032010400350701400405003c2d00105000784400c64a034a0002c004403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 296269271 1250 296268021 296268041
    0x71e0311033001050a0b0912060a02070203160b0409051f03210804080409090c090615030b091b031506072a0617180d09050f0a05060403060902060913 66
    0x11420040d0003004032001c500b42e040b00c900811007460303181003142c40e0b80a41c1c4014007442d480842507003424105030007442124400d01d9085401601d80505005050030310034003503501c0313101402c1048207000e012403440540b07083d50800e020003c4c60356075120801c03000441c04a070003c070341c952044002041104801096450120900324104110340449003500c0040040c1c800400b2803d007808140000b2038160b00820840d070049040418090b900c15031681150010780100540b002c1d4840d541e03200503014040d06980d0b590a0394446030901d00850112950007214000c800300c3c4c2d1002011454240d81e4840d001c541c88002400160f0b01c00c0ea91800625074042041c150050031800c3c009901c816481041c048100e91058480c09103c0c00300e05200100040c000784180c03410610b10542d03994030201004080e8119441c0e807585002582400200000d4200c4074a809100d49203102050016072508000c2d9421607500000c0401c800c1c00c0d82c40010310340c1c040c500380301350411080841c004101c1c200c0d0f04414211 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 296270521 1250 296269271 296269327
    0x20d0b131e180b041110050a081803190306090216060b010206070807050310030b01081b030c010f12020d02070f120503150d0312150812071e031103 65
    0xa915107103207607055500184880000c0c1c40c2803404100800d00018549038010311510400d00015070080c00101220009209a40040c0020520780c0d00c840d040320302e00d078004806d200107080c0754030001411943d078401ea458900b400100540084034481c02a08110060030b4010029900d07000140e80744650000c07051019280b071410702d100034259500105046000e8070301c580d0f554030656680582503406600107059082d100d2101d210000110b61084035090180520101511400c444076040310b50400061040c40d200340c100d09010580717a0b0700300c1100c491814040c14100c4640300c1524042d4000d0060f203121021550002443c141006141326504413200d110307100d0440145128082200c1a0200301c030454600c0c0041c4a0070070142c50080390190b61107110b451701d031030b40000d01584202942d15032808140e246203521800c1c03007000001d110102e001a942004641408240d4452090040c0c00d600048411030340713100e08009042c468485484060000d0f81120781e02d001420710104400c0c800581c400d06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 296271771 1250 296270521 296270561
    0x411e0f09031002160201050c03070c0b0c010e070b0a0c030203090d03030b010216210f020d080414010e031002090d0f0f02091806190b1c02150f0d020d0b13 68
    0x60702c9064400e40710100581c41e101c1440da01151700564056111020380001c2d07100c107015080c0007441c5003904001900703003400403035201d9469201950030740d1101400300003140c000c07100502c501c1d02c00c07206071401c1400c00d250840715400c0c14101030b41548100080580c02c8a034100c5038400341501604807a0503480c0a03070880d03540002000c0d1030021003070203011700c81045649201175064006900fa202500a000b200500c4c5918003e50009003003060b003403000c070307110900418200070075070794446140000c0c10282481e162902100d00000e0300c03180a161f001e0802680858514540d444810304540003543c0140300c2200400c290034620310034800d5501c200d1240100c000081c03010411030380070105d2099410300801994407071101010b00d90b6070701004403106a6990040c10260703504d040000c0c3c01c0c0211150411000403050042c01040c00c01c4142ca9001301070200114868603800c1c100322411402030507001a16240d11051100251180c2d00949500c40303007111700100c20740e08035840b49a2203101c50410000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 296273021 1250 296271771 296271793
    0x1d120a0b01060f02061306141512010917031f081b101205090c1e090105010e100e060d02030c0903010e0c030304091515411e0f0903 58
    0x81c2c443c01c500030b2200607004600441d440c031080213154080544150000700d001515046c02020142040740c2d00a01d00951950300700341401c150304610f901000c81d60080c400203103241c6a0490641c1031042004284078004000303185040701080446580c4c43c4400c201040c40d66600f00e00d940c4010b0301c143c01001184c540030002030341c50700d03064a02e404030306034642c0250240ca071610000204401003c41e803150140301008042c0e079656450048440c4084c401601140300c0c40018000511016000356051041c5564003c1d00d50392624083c40d44140c407403030701180d00c502441c0443c85c107000c0d0170305400b1000d00100502806a0900001d051881c200350020400703d4161241d0f223694081c5d507020103405800410040c002074885800442804000e002c00820386c540c4d8080600800201016420001e41c007801281806c681c00c0580d59032140e04481512220a0480780b10780b03404202c400d028440b0000060100300c282e5a2649605045100000c21f50b01c64441400c0c09503641d01c60130020380b1a00413100b07002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 296274271 1250 296273021 296273027
    0x40b0310050109030f06020304050c0603010603150909030c02060304060905120d390c050a03030504032616030905070303080907060809030d02090319060b0103060e06010804031d120a0b0106 83
    0x240c200ea1700103001002d0000c4544a04c002544040c202303942c28000e244082d12961101d0000b0742c02060550b400140d10b9902a461540e4003110740c0040c5105c07802d107000b90000c00d070310036181104c141d01110540c0d900c2d2118909a0020050b01d14020b0203809203449182d003984100c030141108010b050000c2c070a04200c40382220001c0394280818100c200380600c2075102000242904800c07036460300304064132006a890f92442c1000d02c03402100000d464074100010507511410301c98a030101e424074208a11510b44250408041c014841c1c1022011504408c50642c4682c000040c2583c0003000c0d20007254403803c0042c00c10030110740b408550711035034100040c504c2c403030314615203e007100c0742c0514100100e07031400501a5000060581d41403040c0345d40d640e4014001d134075028041e8071803000040c0303605420b00050182c0b11141c0c000813001c0400800c101080e600401d40075802a4980303460804260802500a80180b013054603540003010f81c500c101d0700c0c040006248450b5401540d1800d0503070b903201c0c030803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 296275521 1250 296274271 296274287
    0x120109050f01350a0b010b0a02070b030c07020f0a090e0109120c030206010509150a0f0503010b0103020408030d0506041104060806040e0705030d0503100e07020606190b040e09010f02040b03100501 86
    0x560714900e180e02100301000f41a00560001c5003940a50301d80c0441a02d40c91070b07640080e00800c00003080041c80b44100340e010008280100458004035040d450b04280c5100c0c1801141000b0f809004484218030199a54102d0751010300030403c000c00c282049a4035443c000c0580c80c7d011a004116844261030085c040c66645070b110350305a00a25a50b801e140c14400703512070150004200301c444440454a130b83d505800e4802030441c03800021032051812042500790b4118003071090605204000c18409000d003c03040380c1c109a9500000705035921503502050003054551014054807101180102c1d840e640b105882c0e008200c00c8909110780b0f40440344094443c402071140591682c4651200e80d512400303540995032106102c4060100300355100016844410103c0781d00d40142c1080d001c211941ca00800818815503403000030703200c0c2a0034a000d0058a101b43e0280d0560b4500041c0043c0380d040d425000b10008003081c050540d140c6645000c00302154000f0f84140300c2400044101003200d520030703065 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 296276771 1250 296275521 296275559
    0xa120f0204030812090105060f12010b101d060901200709020f040501090e060a0e090a05010501032a060207060e041506080106090b03090a031202071703100b04050a050f0303120109050f01 82
    0x12751039441e000d1400700305811506030704441e19075407501c0c0000300700d54818403407038200205521070248005011008042d00c24440100d43d1250b0f00030b0203100b84613640204480c0003001d03903c2151480d4100310070f003030386000455800390442500000e15079040c195540e000d071007203603401e803201c050040c0c44a100c05841c44040b640c0b03580000d141c00040000061207003000d41c101d10780a0540324026002e407200d03429100c090300241e03040001074128a02070740050310300c401c00401c442400c4003000d0034103400944555051250758104201b610548400d507889a01c40c890440c0c0c0351051114203035899101500040d000d22425010038220300b00021282c2803081180e200d080024040d01c00b421890398266a2089200c081d050b01a600788100c83c00507200110384800100c414807007a40724074284441c1d842c00045074100840070f000610081140791101d64488003620f8044035071081c44040c8070042445e60040d201c0c1c03580580110000090101d001d58400d07401960a07106d03c5010744e8803070701003410a80d10628 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 296278021 1250 296276771 296276779
    0x60c0219110d150e01090209060103050702070302210f0607080c07211103070303240815180d09030c06030501060e19050d031106070c02060a120f020403081209010506 73
    0x1e450202e1804400900c003481c0310b500219070003108001c80504407110b400c4481c55981d502c102000640c41c0030920294000001d19041c00649002d24000b900c1751000e2000a020310f0002900b98807010034140b06441041c0c0450444013010000c0d082d041e5140c2050b02c060011840c03190110f01402e10030000c4501540d049100d41400c00c0340074614440d0090400300c00c0e010441044180705a1000c1880100f00303490003a9004501d08841c8641070b54041402c080070030201c01803070410450804003007200c1624002040c2c0c28405a074641e00c103030300502d41d20440c4032b080c0e0107905001d862142d0000d201506a900070341e200a126620380b0025012184280503400200f080b6485100180c42d00040c4002d02500313041c2c0f8180380c1e95450003c9960448600b80440c08107880032032a6444c402c08200e07440e07125100349004e25002c07047d6004201c051186100c51010041c1c01954030055200603007040080000c0d2560442d07855980c3c1c201402160800c0c0100c54030b0200b80702c00f01d002d24030140103042c000c00c4028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 296279271 1250 296278021 296278043
    0x31005090c0714280c0f05100c0f0204051806010503031201150e03030f120a0603030504230a0e2a221503060305061b030601080919060c0219 62
    0x1c3c445810044116150700d40604c9016450b9035113030741d0100d081000300302d007a840800c2c070300f6a841c01c49403d00c0e44e50481090581d40c210100450f45d03071450b10707000d0394003282010284401503052441411008a030060341003400e013802e1041300080c4440e82071103400c1d2403080da841640c03640304051b03d071b108821002c2529259a40180100000180112443c42060071b0965041e050b006c0400d0075500000d40c03601180d00003003580020940344190032a846034000d402004142d040da42c0240842c082e50044204040240c01c1c40511040f143d0b02400c04101d0081805594035503401640340240c46c00c0740c84d21218008041001d500344d04a203030803041e82c803194209900b0b040c0f000c2c0451110310a0038032000722010b258000001d040c08070007910792807070130319903000300744c030350850030020314001010340044001c8031182c1c00e40d041c15102d2420f59400039800d2a0410140c0c5901071102d02e0071038064081320384c50300182d02c2e00c02000300315800041105256029180c03280c40880d0080400e19020318068981c01c1a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 296280521 1250 296279271 296279273
    0x70506220e012c0414150a06091107050a12120e03180301020705060105010f03022203050d2a06060803030a0b0a080d050f0a09180b03120a1b02041808031005090c07 72
    0x3902c1e10070700c6082c8a1044886c4030801c804c00800d103c0c400e582d03c81c2c00e0350307035580c1c02d0001280328050340c4000701e8081c0d000340c6085001c0d13481300c1c0d881042d01e0025101d8020102803221807032050040b05489040840d0500c40640001d84003500ea920458036031440d001c40400c1e07000141418001d40302002d400c0400780c4000d07071801c0c005607510500d0580c1344003015401c010083e020034a4102d000e14402800304543d981600b5860030918040c0001a90003e0082a03024068100381525201c006010708541011140f442403030004c0142c9001e82269030140004070401a100071031ba4007035001e0540031500b80c2075565507103511548403444448400c00042d0100103600412010f42d006000390307006450303d00c0f8403e9881c220800c02040c0c450320b000b1240c0d16014074950501e0b04200c80344608100c1e5200350703d0194802e070040c040452440441c1c405507103940000066507900c1e84420243c400390485128035441a1501c0d114551045500480c0c220105501051900384914118490400e2500c41450041c407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 296281771 1250 296280521 296280533
    0x9130e0c09090f01020d09120309080a140405060c06041b050102030d090203031614010c0e010816090812091801062a41070506220e012c04 61
    0x100810302c0b58548180d03034514088610920041c022031070030035000900342c9541d00e8140c2d0911010705000c010582030607001d40100e1090300c01c4914440e002d0600002200881c41e031844140250b46c4150340c40000410034482108000c40d100c2d2186106d00c0700f080704500c02c00310140001701c02d4013407140164018840d030032000645507c1201030b039000504076410708070004864134215230180000c0701c050408164990245109015801e400c1c81030381852000d0040c4200000d066000046c41e1340c520007011092810316a000c0d16095000e40040400d5441004040350254010742c41240d019000d4040302110704284016940d20714140c860341d94030134250090340006103900034a0714903200944d10310365040350001260000b50b03030381c00c8480d0004a41c0106034412404049a1804480c0d0380881150000c1807102a01082500a455040303c0d103c1e00c1d40480102e50740c0c0d04840c00c6d000c02404e500010049040d14054a0701c40c1211710346444403468030080c40c5401006c02860300c0c40503807602c1c3c51b00443d0020712 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 296283021 1250 296281771 296281789
    0x12030a09020607170a0210020304030e10180b03011e14042a020d1704020d02090a020c100603050c0312091512040303090605070507170903031303060209130e0c 70
    0x10000b003241d81030840c035031925440ca65a01c108002060380c0002d58658054052000ea595200d00c81c4003182940b8240e00d0180210491103c0184101c00c4035658620041c00b8259001e08003000d1040e0514541c0ca551082640340e00a0080512100003010f00d51107112400050005540c3e20444017440c201e500c3c401e000c060700346030410040390050034500c6c1445002c0d1109000082e00340d540141003000312260302400c02c0c000210f146035800c40c2d00f42000003688402e54451380e8554140e0300c613a01507856800b503000900400d4070360f448c0da00640c03030b0150b01c1d883d20350000b205a034055000d47c3c054000709010190759100305d00100501c40002d204004003845c00c101c002e4400d0016511443c07901d000c042c801c0a203284103c404030082981c410007078090100c0ca01c82c469120078141403043c070303000494842d840a0340d00d010a82000880c0043d6250282c4c806005448900614001401e201500e138640400a504001c5846000f14009550280355030201d0090f184402d440801501d00b10f02942c0034448528 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 296284271 1250 296283021 296283023
    0x709090903021509151f0f03020913020126010513050610050d02040f060c05150112150e030f03040525121a0c12060f0a12050a050a200312030a09 64
    0x10061044149000c2c184914940c4251032215546c03c25400c0c0c00c03281c900061305504030508220030030314188010307126140f04940040001201584140440c80122016070115103c051a8044418189841580c1e400c81606891049503510310000c8142246004c0380d50403540b42d03600c2846101302000d038500a500808070040283d0025140c107480c0c84100039108143d074042000200010350b803034184401032000510320107007459954100d5141c140d242e004502e52035809403000e240340c80b06240b00381c0b05a000c14500c8484209880c3c5421000005440703d80081710182e840d405449003109082d002c11807500040441360300640b07012800c04000302c643d140082c404a070f007015003d109084041600e6400c1c1e1081100800450b83c2d26810340314000c9100c00030745064020311400f21421050740c0c9a9024a0a5948920140c4d20442e12804e00c60f00d02303a0981c00c007070414000c94181800b03000c01c5542c14510701c801c002d102050800044140b60340c40a810030042c02d01c1000f4000f0031090429504030070545 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 296285521 1250 296284271 296284273
    0x120c0307031b0306180318050105220305010504030c0317130b070e040515030111030c03130c03080708040f0806130b0702010605151812120a030f0c03050709090903021509 75
    0xb99460f940d401c0c00b2501c0503840b0144e107a02c180c2c004800c042d840b8580e00034074a0070004c0c01100a1a00e00007920500501180b41e1002e05071007070001c101d03441c071410b82e4021600000280100e050900300600140400310040c2c0000d1482e02c0c81034403248181260f00e004084841ca06881900300340c1781d451a203440540300c6010407401120b080c0e120360350790250300c0c0101c6101100c030019000200806084230729009107100d030680144100300921744180c058a500421071440c81ca81716055180078021484070340c0004003070700004103003042404100300240003075031004100103940c01d480e1402946c2e19102103a01c400000130100284000941820683c0d4200c1120300001c1105d546410029814404c41440701c459020301042c503043d460003941e418444850103176061180c0c1d44280f2a6591a05001d00d00b18504210006015003841d101ea802001c0b0901810001c00c54400c8410004003e49415036100000a803405004074010000c0e2141e1145c00d0383c5074005180403032121081040d08003004013240380e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 296286771 1250 296285521 296285573
    0xe03160e04020f0907020c0a080d020712030e13060317030402060702131512050d0c0f06020309031c020901030509061608040c0801060e0a0609060303090605090f040614120c030703 79
    0x4541c40310b2000500030305d000c1d00a40072840c003080a01902c0d0300c06074401c3c00c0e6a8000b15059844030b4010138814296400c0c1c0c1400007040f0303028102542e2100075400e4181e00100015005029094a039015101b81d9100382210040414045541071160200b0799010354000c40c20010000145000c240341048160300040200e80084602260b07283c0c242e9541c4244c2141d401381c100311017004018003114025980604007070600d03416585030307103d00f215180402040341e50700002040d40d00c0c8082050b181c0c1c04080f401450310460503030740500003030740164440034027203814140450b13440d241c0070074168480c182104c021034440c452400d044031350550203002a601d03d41b80210200e6484400c0c09040050704804403000300c0c0d42031617111441204c00395400020618030302182480001d5001c07030130030304403092071820710380300d4050000040e15003507180944c42e032251401d20f0020701ca0b2090440302000702d4049814400098103280d110740c0343c000424499516030411001400040c0221480d002860703010f40318040c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 296288021 1250 296286771 296286799
    0x106200d080c39010b33040902040b070b07020706050d0b040b03030c0618070501080a020a030e3301030c050d08070f05010b0907020a0c0b0c010f0906020403030e03160e0402 76
    0xf000e9014030f014400c500041443c81e0950701c40900032182081001c0e54030529051506921915045030055002d461815a0000c0140c84014105031400342007c40320031940c0d25034540ca07070b05071a40150401c842041d5444005600d1600104120301203030030302d07101c89251900b58030200004000d060103043c4d00950f2008400201d4900f0000350a2051200c40148031504080003d0390380300c800d1404181481d40454001e02459a02c0b60903a60030400195004da294032071f142c0d081d00070301700480010f0118801c580288074007481201c01038881d4440c0c410720506022040280f0b41007080c00340409440700d00d0400c000c209904001d08034419107801101d04605110080d0360b1404e08402c0c180068449a456070000303049072401251507a08058070740002c02c03440c0c031161b40d1220740342490700c0303441101c00d408250240310200039000599502c440781005c00072402d40340b91400c002c0d040342c001a0001a032a6010401900b40014900514440d101c20115141d14000c3d030b0314021f020081c03040341c0000401078480707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 296289271 1250 296288021 296288077
    0x806090a06021303151a090108030f0706060b030708100b0901091802040e04080301150309020d0b0402010e0d0323130e0604090b0118050a020a090308130e0106200d080c 74
    0x2289040e070505021901b0b00c03088045401904060b90910301c00c00303941d0010003403a030001044a50350344200124a865900c0d0342070040003003050b50b0010702c5202c000003c014000ea4030200b502d124130022940107030789a440d05030300300c8103004003001507020816120342130000003140400a0901403016501610b410b480d50300ba040162000d0710216000d41d0040014860f140018108000c1c0c0b510302e150802032054a034000800c0d88130b80c032501400004420000c0f60669204140410001c3c4000c2c01e05e10844140d40f44c010504030086800c503084039000040c0f019001034040450b00486282c04844111a05202e0b1140e4940400f41c04030340d001d5502d00040c8005400c035651640200b038503222050704003036500c9428040d210020704015016104019145906410884013000d481d000140785888d0003082005281031021a004400540b046000018580d0740c0411003180c030458800d409580140060100d0355110002c11290000c6410b41d000140720b03030700640180040b41214441e060b135841c40413030380c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 296290521 1250 296289271 296289293
    0x30309080c0313030b0717010e0405070b03151c0302120d09060f06050f042007030e040905010b0312040303140d180606050103180c0e06031c02160806090a06021303 72
    0x4441a0b81001070030403d10000940061b404519401c1c01000c401020301c80c0980303903005005000000c003100b804502488010031081001c0e0504440c1240d480c200021102899218900b105125100409180002e040004069004164980c004124500f144407280080d90003141160080a50712413140c2e001c6280c2d40102c0c03640e0040f03c100011403e0805c1306000d0b0484050254034041c070305000002c0b40710183d0f081a80307402072502002a844417140c1c68201d9403603201c5042507502c14140f54510080c0001980940c481d800100c080760f000000f900e81c800c4083c000da100180100c1d9141c030700d00610900c95401040f150455000000e1540145400e004107108024801d840300c2d41d50360018411541c0521950f0042801c00030700b181a00007079030351340c51400f805020b034802202e89240400c410340c804009403c2c400010300b0000c04d103510001002580d8960700b03036007042c0c1640c1402c00050307641000700e510b45c0a200d20001074101d180480e240d0700301039030010071000c1e906185401c00101180380c408007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 296291771 1250 296290521 296290537
    0x30e0a0609090f02071a06150a050d0c180302040c0c021504090605030a051018051c020f120316090308030a090308060603041128061e141602040906020304080304031107050607030309080c03 83
    0x511912201c00e1601720044330329030000101480110444e10101900d030034940c030120799045a0104030307151052400c490700f4280040081d0820f600b00640543d034028031000c0d0080da85921010040d080d503075000c040e502ca105400c05030498120a05000d0000b4094201c51000410103000c3e548200c503643d04d052a007000b20804c2c03510503101d030004520f01d42d03040c0118506000181c0041082c0001056814894480982446404d04c1c6101030303205202e008011741c0004503085084241c4030314141c030f41c10000d4100c14400f2000074564000180e5285090401c0d40e00981d0010480403203102d40406000280040d2076065900d0000d00c000b2000040b06045035034040c01c0181e0710107000d032a0b42006996440429080c210600440c00c80c41d62010280e141660040f0700319404442c0d00701c81a001280041042c10310103070a0600000801003800721500041d405a8840c2c0c0d1004c02296001080d2505c40a95000d5998131003020441d083c0803d00c0b030f4100f801098041d40085180c9201003000a18561000070b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 296293021 1250 296291771 296291777
    0x14011b05041d092515180b18041508060901141603020f070303090b06030109080415020709061d0a110313030e0a0609090f02071a06150a 60
    0x4100a081121411020440001414101d003810b00701040ca03109800c1640c41032260000c140c002032070311031080000e030340010301041a00344806611003030015501103074002c401c82c26800805440c090f6204501088505201c8800c011496080024008081d403245014041c0e5481023822281a03903124455001c4020754a060800c4507898003000c503003803080042903407a160345000c1031205c04220404125a028038014100700c6035800e000c4080d0024054903c0f42d401141001c15050704060709640040c80c45405040d8440e034030303030303641c03040601b6a8444500142108030a000422604250854000c1075100318010341c0e100c55111840e020449940c0d0340488a41d050018107103c4089511501a4000146030000e0045d102410703180903c0348809000451000d02d000b0195080c148601600658550010104035070159182e400820f0390790030340566509285400c0021308084845e108650005621003400c09540c0030051017502d1650b0020300940c1c010400e602c4003c01c0088900c020040c0b100151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 296294271 1250 296293021 296293031
    0x20d0e010516020a05030a030e030d0c05040504050c0a091a0403200f1903020603060a0e16140406120e0312010305010507030506010f080f0403030b03010c03091a0106090b090d1401 79
    0x41c88500c0b0340c295450000303642204243d0408204040100c0308085502e00b00444d440b0803441e035581c61441032001c4410b2a03494051200340341c50380180108125a01100e00f40a2512100710f600e400380700740d10580b004540407000c108a146840400113200c20402000300d801c0c00d50b01c3c1c0f00e074511041c0007910070004002c410010803492074020800080480f0a441900010701281501100d11149000281c451000400040c20740e84e0f41034641000f40c0425060341c1041c0c144168400c242d01c0c030440b0314030b000c109404d1101c9040c007a08800c1e2801c0f0f41190792682503425035855064000c2c0415030003a166400108044130240084000443c0290702c1140005414503100c280101210380c0a8140c904222044415146403540a105a0781184550408178000d844600d400d0f0010282a5991768242d42000d204501282c0c05178402003100340126456060341a03071001c115103400090062500ac210f2010b01880b68445042c0581040300018000e450511500d0b118010242c054841d0b8004d641e4443c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 296295521 1250 296294271 296294281
    0xc0606090a020f030106110a0c060206041208070e090c0c030a05070c08060610052a030c0106080705030a0f03030b0306010f05101d060a140318060702030f040302011101020d0e0105 79
    0x38585500c001d403181c04500b07103800c074042800c1d18401803081c042007280c40100b06280341d00a00000c1c82260b030015800007145e9a414001c0e484002c05c13101514119800804101410701911401780318246580d1181100d0f4005401c10261744070150003805020404d2000d40b49461041004000403080b944800303890b900149800071003840f1a4108081030740100040c0031071502d4001246072041422304009481d600e0b880500004124400340d200203880ca21031910100543c048020181c1c00c0340080240150380e00c9207a110f54a040603c1200e81503804a02104007143c455290701340ba141c400e20380490480c12140c0000c2c50440c00307030460300502109000030440c61078011800101c00788241401003280c600315413020304030901c0700303c0741f8010500020911801ca104107054451041590741c01d0703450341810a1036850031075074085860542e100f2074001c10b0300d1600001c142c85049420303586043c9441c1c1075a004481c800307440240442591740a00040000081c5030044840800010000103194509 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 296296771 1250 296295521 296295529
    0x903110709021c0506040f060608090c19030201050c070306050a0c030f050717060a0306180224040302010311040e2404090c05090601090305030d0501050406060e10080604020f0c0606 80
    0x22a911100c19544100440034025a141181c40100c000e860b00000c1c0c5903403504040b4000e0200300100c14a00c62030800003103190750f040180c09020381d02f00c00c125080f0703404140a200031035204240399080028011010030040d0312410046c01c150340b41c002901c206650303035601c52080e6502650fa145a294507214000f40b09a49845547e00c1221401003c1c0641e0615450152034011050103140d030220300e40780091540d44542034100c00640e4410410040c0a119003030317031060001100403c078403e140d01850071111152a0f068900b010061150292a003071550f8015801050308803600c182144051100003900200d040a2510030032041e4044840e04c2c01c480a454119206102e000381305618045100f03011807981030b48007043c0e803425151580e590311104c006a900d02055400180030348800120310b005100603030406412944123175018003000e9141c12041d9806210f03021802c2c0c011007041642075120b44a462440e1700110302900c01407614000d68010300980d4800d5181958a40c0070100b40112818 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 296298021 1250 296296771 296296783
    0x402161203051509070815010905030d021605060c030a11070e04030f020f1c0302070602070c030c1d04030503040b06011724040204051026040f061407090504110d090311 74
    0x1141c0b07643c550314213040040c6c51400054003165003c10600c00703801880e4001c1a11001900d0000c0480b4007986500100a6503008450300d03001680001c000d001070709003024000e482c102802c1002860030314021354811900e410100448400305d02c510400002e0399030303010101a026074000c1c1e0300c000000c040064080d02d00b080c8401281e02da58820070019800441100100340340501616003d41e0b1800b80b4100704003e4001d1041c090001e0079100800000c205d11420351000700e0305400c0b4441001c00e603440c688000d0000441d00980811001c10028000485400c00143e219005040030790244086500da03008900080b03d1103004481e0401b1900082c4800d54481c03403600c04100c03401c1d4a00341c200800b145501c0d43c030800d00303030a0142e18480d441e08071070003840a04200c2214005a4104c2c9090f0820207007000b8030075020744807946005081500501c2c1010502d00c18490354030b42c1108145410140303c01412400031040a26405109920280b5124001e10a801e4040e0b52030540020f40f0140c1c80e81040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 296299271 1250 296298021 296298061
    0xc1505090c010c0b1303020f010e1e03030601020309010c210201022d07020405042607020a060206040b1b09030615090708011802032701091b0311040216120305 70
    0x109000f000c0004110964840d80501c02040580010602e440c00fa8a41030349410381d12000e50034080361108540c40015030036500300035513104a00d40080383d48030503100c0c403003a950180181c204203d58002540210b5000c10788a1140300d81200f000100290b801d07900f400b0258040c0142d40000304418160141c84a03100900c1701046e803140c0442084203102d90b10b214460009019a481c7d4000509000c8034004a03e40c03048000d060f41c0391032164616803001a44a41c0c822403050580401c04543c6074400501c042c4112741c0500001596110301001c4021011102032000d00e01d04200070b4520326440601ca03090003a07540d4500c104002032000104003101d44000c03c884e0030400340724010081142c050070420301d140356140006a030707a140c0c807910070307403c0b81c5503204200510090340c9002c00e003140543c00342c0940c84c042c0e075088a14070a00518820000c0044c0b00182007800f9400040f0460701e02903005000c0710aa50010501c0c40c0660751710300345501c40b90300844000c00e80c1e81c0c0030028031419841a0315565 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 296300521 1250 296299271 296299277
    0xd030b03030405010c02040c020307050a08090306010f06050d0e1f02030f090a03021c17040b04031112040311060706050f100602032a1002030c0c16140603070c1505090c01 75
    0x7083c01d02d0002007030000c00150182c40346441d8114100150300a20850b0712440d000000d580d0144c00600307000c400d81e407220031414040d10800000103100300d0356a901d5802c0d10700580e10140340451408420000c1c2c92612902001ea006000a41e20000a840303880340c4520542d000240c0c072441e08407002004040014a14521600f004c0104800030703034049400d0402c1060000c2c02003c001d00084100c52017841340782c01402d0408050144020300c4a00c0071702034490751080d62900b413010b03a8005a1515800341c012600300000b0b0034401800014007203052102051005482c0e03500304103064075100181d400946403051501c0c1060240704c1d03e4040c15400d0b501401080c00114640441018a101c6102d05421242440c60160500159451003807024004028a4a5082d502c03410103000d62a00350348042d1440d8111b00c1a4035038081380c07203469100d2130200d40350000701c0103803007104a081c03107020760000f458401000f0003680c0040c0028807590b41e0424540302020002082d290001c140b0749421030b1803a1947c14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 296301771 1250 296300521 296300527
    0xf320301230a0501200111040e0a0f060807062a03030917040b030c090f09070315060809060c0a090314010b0108061c080d020705150708180c040504030e060c0d030b0303 74
    0x7030b07917001640300e581c3d502038a084003841891441401d005005842c2c0c000000c140c0002c00090072251050221f0040c105c080701000540c90000b44201181c0040c400e442060b08a50000c1040c507000d98a0310114a01c0c80030781c0c60003450340140c003c50100840c9011400311f540c90851354140915282c84181c0450241351840c641807c040e040040703808020300d0b42e000194001255070030380d22086100c4502101c060854515800c0c202400340141008820300b10000b04100000141039101c2e0714524050a40e8201401c40c1e900c07440041d10b00c66100039815024414001000400103402041202d0512840000015070f40300c43c400041043c803010385200e2192040828640d50103010241040000f0750241000d1781d24840750603808080e01411501504078010998044009501854031600c610415542c8500c10303514414990a01c0302d612001c0c2e17603a540b14070102c2d4520300703190744842d07006402414841600c259071000903c9551180e8421803503508502c901c1c562860301401036180c9150300700c0c01303141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 296303021 1250 296301771 296301779
    0x3010f1a07080904020702030d0c0b070903021309030e0a030602120a0c05220b040b120f130605060117010b0c0706030c0f0c1502120708070f320301230a 67
    0x3280101c88010303000100001e0107a0311a500ca504880c15030b5030203003c0e13800c44914900060034620b02500195098104180010740c0d20b842040340d078003034aa00924802401d4940c41244d0300034820810110180848101403c00940e40c140d20f0700000d40c0301d12009641d442d0b010440d00c0b070500c0085c0c075100940c0d0a164150401c0c580100135203503200e02295440b482c402252400ea07c21582d180e1107105c0c0c1001c00035011403044ca25800421400000c005102450380b50002441a480c4040b00c00b8240300320061501000034184e500081e4000d101413400074031015a000c01c0ca00c800f8800e900c50100a0000030b00c00c100d01d04103110600041049040403c0010711a1078060b2050040d114050308000c01010860300308003071146100310090000e00110b440e45040107002d580010280d9515001c500140001102c05204a5008080064903550516050b2020104920f20a40b0b00405880104421240ca00103c0303090082d60080c0200481803041c40d01402202d082c000541450b07a00903840904180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 296304271 1250 296303021 296303069
    0x190503220b0405150705040b0a090902040b0406020705242b0e0c0f060a03150308220b03040c030f052406010e0303071101081e13140a0b0105010302030a15080303010f 73
    0x7804c845503c0c00c22651030207081d0301142c2e2b0000301d030000040306201007000310360a80000007400548003103808903080700382c48000300042d80859500b080e035180c410308001000b50b140d0320003901207121510100400340100100001d24900541514503040d65a002d00d0b03221504200b08070751351454240d440f03580027640440403451314810403541b20309154445c4070204003020b030b90108100568102c00c3c00e548070300a0070b0380c44400d000049c44030040100c05c0f210200c0c800c1c503910112400b856110091a980300d18507507640c1741c4151064400c1d42c0d6030007044500d00c903040000d45510040c0841c3d407400f0040c0c0c6880c1d070002d8040099185030902a038010f002c030304000303441c2e0011b034490007000b42800308896540c1c42c1d0419206404541c43e40a07070360b42206101c24090b5140e02850128400c1c65410500c0b0340104015a4a9414000240615440f032004000700d500a500550300031180b42c20100d201050f4031201d40d000c04c81da5000c40a00d51002004000310704030120322402a20f04e0083c3c2409050901c1c03800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 296305521 1250 296304271 296304277
    0x300c0c0d180302030304030605070e0604120609020423040507080c06030a0b0f10050d0b01140306040903050f1606050a06050918010912110111190503220b0405150705 73
    0xa803051010041102041803881d000c00401194010112640d80c3d48900c0c01d02e000c0c0c10241c1d43c50010507d408032100c01032404600360790a680d100d1440503281505901e81c0c1c00605050704040e0781180d42c42800076801c100d0340c840600000004010034165040500e0070510346815984100c1e100d400c900800745680c2d43d1401243e400c12003191340440c410080c100010685c100b071001031a841000c141c1400140354212024190401c4405d2007081985018401035480080280305c90038164410000140030340b40c5603011950060084c5000d034144603030768003654900d900c28020b07200c4030718a01850340700304a01409070300e600c0b1784c3c04072050011030300d03202c00700300c00c51809404000343c1044034014000100c400d500c5000303daa00449044007034000c040002d070640300d82c0d4480d40b40c41e50a02151803d001501780c2140d40d0b02d40103402122601c3e02103082150240c001502080c100d200120300c01c03808400e5586640d004d280550000000c1341400c1ca403a9281610011518950789006010410215008019 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 296306771 1250 296305521 296305543
    0x102120a0c0b0a1d070f0f05180711030c0c0a0b041a2101090c23180112141e04080301050d02040f15150801081e03300c0c 54
    0x2240c942c0381c43d0714558401034800802e501c0d1003542e0070760035001103040c0041d0000440d8080c030441e1030000c4e150056007844202c140201034201c00580c0a5503100d007960210907034003a41d81d2070001e429050303030b5188500710fa001802d600c00c00d42c46507545444a1601e291501c000340080c0c1403603031515103000002005192542c0c82103910b250041406d02d1130702440311104d0816240598030600c03035a11012120007c0c5440c0d88403400044da100411050940181e20203c0e0381c4034004120341c14013400034060a0300c0c0504200880c10010702022054000b98940113040c41c03460b840300a00e4441c0381c0340b020001c51504946000f0a00301540c400c1c000420301900c00c0304e06450090340e01072003046090011401a180102100380c0e66071a0503015401000e00d100050103594a5040d182601c1c0c0045c070080361406070078086c0e010141c104046040303010000da007400c00c060f000c0d117007540d01f440b15000c4100190459803440781058a5162806500c1100d6034141d25484140984840d0900350014441c555403c0c1400c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 296308021 1250 296306771 296306783
    0x9030a1e0c06020106062c060a18030609060501060806010926060c090909030a090b03060d080324040204030b0105090702010e100e100203040f200a06020c090622020304080409050408090102120a0c 86
    0x2002c20465200f220f0418013007102b1604828500d0b42c80c41c00c0c2c0c00402d0018401c1c2c4142d40744c40300104596200d0342c01c003401644c0503500e0141080c20420300c0301c0640044181000c0b60013280040f442c44400501c282c5111342007030207081d601e450407a020300100c640001d0a082039034000b048042d08440d0003c0c0103c1c1038a00c5a51020f841c0c0e501c00000c48c800380c41148001d42600804030420030000d84030f007881c000340320746280b5208654404a0904c030903401503000003004d240301e540040c0b045081065115507c0400c91001007100803020134100e091000301d1520701c01a0340c80c0e040c002c8101104005511102c40e6181d000c61441c81e0075160203901035408040144040b41c440c4001d1b5002c8500c000141c200c54001304103103041c40d07482e480030b50b40d4400404020300417508000002c0d00392601c0e900c10340701d090500c3e41c044803c15000d12100001c0d403000b08101c0d42000c007480b02240805441c81894400c03841850107543d1102414000f80c40c110200d4a40c4800c00000c01411a0707203036012a4241000303501c80c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 296309271 1250 296308021 296308027
    0x9180503120c0421020a090203060f040207061103040506101a0306060c15010816080303010302030a0b180d052208190201050c0109060603140309030a1e0c06020106062c06 75
    0x303070705500b10780300b160310034582c5501c00d000c10032441000003080c0018604c201c52a07041310369251400c00980c00201d5022b98070000a4003c20224103082c2c00401c42103203e05070028080002c500cc80100ea0003c1d5000e4036036074000c500704080d114404203c0006015560355642074101041c00c0d044180c0301c01042c035402102c0220b4106d0b04c0420030804813100414900c01d00c0324660310384140b143d8070300f6246501c540d0020350f0040010115408421281640d4016000d42104440c03512802c01103000507084040300c010000300c001d00780d80144140b05901540d55101541c0d034980c1c00b03c2411011a2000700c404050142008205424000500801c0e011070310035588441d005500040c1c3ea41d010ba0401c000241d420316440030104840b81e8008001d903403080311b04071061843c1000580d070700c0c001c480c40c1c241c240c4e0009400b070000c1070128103000d03540701180384d07040550343d95640c80c032568079115413202025030346908042c4646030b00081c00301c520042e2248411064898254882d0140c5070704a0741c0c42c041c1c1e00c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 296310521 1250 296309271 296309281
    0x4030c05150109021801030204050a0302061615051e07020a1b0b120901061e060c02041d0105160c11060d14070f020d0503010302010503061003020405040903020102040918050312 78
    0x140020741c1c0c0032041841c89401980c1d54240440658000c4410040481e0000c0341c080b0598060300c02c0d0303000d8032005000c0e107501e01c2c2583c1c2030100071341c070503410400d20b940808007444c0051801c1c0002c1d040360100b014045990f041010841c4500e401d1440d036403c0010981c410000c500d90f0005011200d542c102c1c20103622203c81042e04030b403034030050700007803900e2000043c032001c132014403501a402401d000b030080003415a60110035400f640d00403926204a1580d42e401c20440b4401c0510390348490004000180101180d0007100000150135194030382031f5199400c004a0385031000300101041b943e800d01500503d0195240522000e28242940c401e9101007803501d50f4660b154440c100c0320002c0d03062110141064034018140220b140740c0714005101c0d002c4418640e40c490000e0701c6c1241e6060311450305640380d100402420955203810113082650034040054266260700500e0360081c021303000117036a00e086c842200140c4085060b030b44960b0141a120b03000191000080710017202003400c0c000300c0e079121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 296311771 1250 296310521 296310523
    0x11116060506010e211903050d050604060f0e04060f0606051215030a0f0b090c0927060a02091903080313050a02060d0c030b0301051015051e0a1106060904030c05 71
    0x2814100d801c80d90340712004001411720130b800c4041c0010f080c11282c000030880c207070f0705103050b9000700100081d10a028544440030030f50050380d0041001040414180d448040001c0080c616034070500c030f80d80c22101808144070051044c0340c1001c201e258280300301401c20724040c00d28400c10505111008180307001440c540903c000f0726544500c001d054840000b0541441440f005028600b034400000c079a022074044d05001030342895404e0054000702c02503842ca024072140b0b4240c2c0c8088250805c031001c00401004003402014492600742000503100e00c808424400176047c41d071022070441c00c0c400700900229040c01c003a20f8ac450340080b584800c18a1601c0d10a04003049010000d400040c04601403080e01c05641248001400c1c0c0e07681000340c060303070504241c00d88105454803070b4260700b51407041c408070000d2403024441d19000d0400324030f400c03c100220310810742910140c8031100801304105180c0c9030310044425041003404010708280c101000029064440604003c0034400307066990340802034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 296313021 1250 296311771 296311787
    0x706021b040e0604240b030c150705010c0908010b040509060a200f031801050f07120b1306030b0709030317150909060615070803180f0a050f01111606050601 69
    0x10b81c2030181c0e5607504003450407074035420b0303500f84c4030584507011100f414111440388142c80c80c1810050050444800010500ca00041d6013009000c022108011050200e6800d0281d402c1009640c0e9402000754a450091400c41d207802100a1040d42042c1c144001d05500190940d00103450040010700912211000c2101c0382082041d58903074140480c1c2a0311070307590a0003851040e20b07000620095880c002c0112400c03640b0891700201d040d8501008542a1446180c80c0c01c41740c62600c0d4001a1220341e000005d02554021061440464554030b040c0200880e681034079410041c9800c0010300f01e8115600684003a80860001c45070048850002e2281c4950400c4d1904000020300740ca000e0f4101440c0c0d0740c2d1545000c84880e4082c150101c4d6010f010f089081c11180c00c10703001100c060554940d5800609441d0385030b0036440051186260142482c2814058130062510a10081045003002c003001400c1d1481070782d61081c00ca500380000e405103e0700980c40800113a01141c0058590b64502c0140c4100c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 296314271 1250 296313021 296313041
    0xb0303040e090714040912080a1508100c0201060e0c090102031c1d06130602090301060e0106020f060a0506010e060307032a02011a0d02010c051507050a030b01020706021b04 76
    0x182241482036002d4081201e1080e60101040109040105403d020075540032a00040158562185a02e001e512540849030402028000880c01c1030503030b0300d401d101c00c5080d042803905801210b04407a032140c0c9841100d4008001380001d10200b41360000b00b0300001c1c0c008007441d060800c0010030241c6a0b1081c01150140050400364a0088072a03e0340f02006000b0700c0481d50750010b03d400d401044480c00204a48500390310040105521182d50340c103030203034124001e00b580540d280d0002044c10510035892901800b1958010070070151502d44180c9060f0000e040c0c1300c840c5161006000103a41d02c20300b070081440c81561031360382d00c1c3c440b19400c0f401007111000c2004c01d6002181b10103003503810541c0d20341103030341c5035070090009902c009603180e05050303080b541981c0700302d070341e0202d0005500481801030039a00038000d0700c00006904010080c2d40c071003154880000703400020b494000c95058410110100f40a01c02030406504001002e544e50001a4840040d024072303541ca0a030725a1641c001c0300d417003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 296315521 1250 296314271 296314289
    0x5010f02030d0f020403031808030a2f010b24030106030203040312050414070501091206050402130c0309031103030402030d0809030705120717070804051c0503120403141c0b030304 79
    0xf65603402d024001d4000e80421070000c4c04001031070041280e00c401d9103040d181c103280654501801500e054030509000304007a448071800c051440c40d9900803600d21440c525130040040b891900480800c0700c0c01d084000d054826107108008842100707406d9003030348c3c15180b15090041c0d99455505041d5988800c0020300d00034603040504000030800104611014101e003802112445601c43c401035820303045138040c508104945191001c040342c095007104d504180050b00702034400b040c943c0c0c8181902c0c01c00c01d602000c0380c1c58408020805038814801389040d030010020b541103043caa0300083e1140c04480300341d0104800300d00441d50b260000e1084801055001003125000b009003140040c1c1a008200700756070450041010070006c054000071144155406200c040c0342034100420040d241c05d400a411035000c5580b1810030002d00c01700b005000d66042c089030200e092806142c02032800e04011101ca110502c144100102c0e40c451000603400c401c00c0c880c0120b48050f4490110b407460141c0c1e8444ca0007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 296316771 1250 296315521 296315531
    0x60d050109030c030201050c0a0206041b03150204080c0105040e0a09030318030801031122020c03040f080105190c020307111503280c05030402040902120d0207230a05010f02030d 78
    0x405400140c0310110f2031003a002400391350788403c104032850060205000258024a002500040c070079140c050003030214808401300f4544940702c0c0c070a095141818007206907400202403103521400c000c3e40c130800c1000d1814519241c100780340d488500b2005021007808540b0707045050100341c000d030040c039080c050303034190f4180502d05800d00805028081c40196107100010340300d5211402c00711130162034180f860389018000181c40500a00940c01208045520b000c01c0c000070603803400040c001c100070581440041101d0034807181040c180048161030f48442440e00c1c0001e0803507038000c401e942c0100d4101c0d000c14962080c0c000070030001d0b0410f1012106420000003008003074084112074207038010300400a0044000300003861401c88002190b6000842d400b40000340044c503107a040b84503a94400341042001407044d120311880e15000700820f00240c0c11000d414004812246600c100c881c001944411f0364221240c089030310701089002c1c83d410400d02d0303043c030078056000700200c66802d030410000700b003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 296318021 1250 296316771 296316773
    0xc14120f0a030509060408090603150a1404050609040201120b0301090807050a050d0e15031312020105070f09050f150c0a110f090709140301060b0c0303100f060206040b060d050109 79
    0x39156100a01c103001091800300800e180d035000041c030302c0c482c03940080c1c04d51500d81500d0400006401c010040c00842540a616446036124052080002d20722085908082c1100380b0410043e903000070b003600c3c0969006001c00c00540c0e07000c841c041c60040c40c01c01c001120103401001c01d024000080b8090461000010b610040103030016400081e05d01400541d02c2c3d05802841c00c0380c2400340f0480180c1d000c164200295260704900004680181c0b426044a103403000580d10848002603090a03000543d6603001007100700c5410001c48080a003070303803408120707050824000940d4268000b100c00e001d08120740400c6986000f0004440350444140202d6003c2da401f4601110605001020355000b51000e0560b149107003022100c0300d01428844e180c110301982003490705071404121840240c0c2c550740b036100c0040c0d810350250081030703030703d505101070345c0c1d2842c00000e0080d00c82c040f94003410074501034080c1040b541381c0c082035803070b0041e5008107144000c0d101c0000155032040b80e05800303071070b5520b0400050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 296319271 1250 296318021 296318047
    0x30d21051801060e0114100c0f03110607030605030703080705070b0d0c03180203340e060f060703020a0f030905060a0c060c05090d030e0d0b01080a030e0406060c1412 73
    0x715100030303000788410398640d0b4090151903002c1c4150419442d50b00080101c0b032030500d840c40f520079110b24001504460540390400b502441540660201d020f07600c0a569401c014000140c0c04042d0707085c18408246000d002c00e555254921000e001100c0100b46641000000d02005006000000d440c68544070f6021409004158000c8020003081ca459240304075805d00c0003003000c007160000c010303000650b079111551a040480e21078070704200c2c1610f14002c010100148180f005400f055004010300d182076002e01c10081c06100c0b04070f104100c00c3c003100c00040e600044600030707954410485189985985403d4503104001c3d00440d50008000c5513602c03981e54080c10094445000c0c83d01885040101403042c0e07072921a0111241c2c00450b040c1c0c03100d000c40d019403540c801c0b1071005401040d010246440e030001c10f06080e08052400e400c0b0304019400d040d480783c5000c0100f00200d5003002a9440c0c1500a0403100380107034010710440c000c1a0b4402445030901c943c5039414680c00841d03945401c10368501c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 296320521 1250 296319271 296319301
    0x207050f0a0c060206010801060509150f03031c2007081c0f02090f09010b030115050c0303010f0609060201050f060f0d021203040f090209030606040902060c15041202010209030d2105 80
    0x3c1c0f0061085400001c0c0c03c1c44c050091004039079018000701981c0e110703e4100c145441c11b1240c1c05030003249a00215915480420042070141114000e00c50880e9a51062606440040c80d01c030480900b01c0182000507950399045a0f0b010b9031004500ea903030203800e420301c1c640300100311a914500e1f00d440303589100d404050f002494004011540c0c0e010581071942040803505080c020031b1106003080c001845001e002a003850b002803010308159080182264100780b95070f00076001204001c05004e020052a6000503522018108a0000b403002e4905000160301c0c5040c0200024030890070b50310020303160b40f223405030a010b0540192002211030102c055199a0380c3c0140b041e021811410100096500707502d01c262101000c005000c1c180b2602d40404010140845410580c0d00c03400c104114400e03824200b06624000c0c441100b40120fa10303042c1001100300006122b00b03c296401000f592948c0d41d80454503040150850030600302d040c100251a640078600350440c0c0d51030300d160406020151100c0d13005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 296321771 1250 296320521 296320529
    0xc030c141605030307030e090a0204090207050703060e0a0b0402010c0c0e041a1303091202040b10080412172712040510090302130b0d200a0e0606040302040207050f0a0c 74
    0x56900826918401d00d1355030b101d00400540050f06120307034100a403030609602604030020142c05400d007500c035a444400ca90061908491540c4461010410001700b0301512050000f00c6008e00141d03c16130316400e91143e002000207040040c0200d8003810000c203d0791000103880c0880c0c000140703181c18034003440c10300700d19000408582045000900385100001007051141c3d41a1340b144810b500c0c1c503035106084070b2a04002c990094803001d002c03081d51184c00120308061040d0303075180c0180c00c0a091582000e101016840708025220b4880c001d40702c442c088081c1c00600f801c3c2c2031f813090714000f09450040c201d1100310801324001c0303540e10b0102c43c0c80007001c1c1054810482d5288600d41c4107403026036140c0c0b2148002500020840e0a40c00700183c1d40c0d1000b12561000390040301c0b64450b42d501e551580840100c00031100b18164403102d65130509401d140b02415101d4074010355030410070000b4005008511009110780d400094103000c01000b030050b914030701644001c03105840032600e080702000e803550017 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 296323021 1250 296321771 296321803
    0x203040302060c040f030611192303010f0513090c060e1314070f090302030d030614033c07060e010807032a030212040b151206070c030c14 61
    0x1011846207640f0104503001c0355118084958070368070756a00c81000c0c000101003000c0c0d950703042c001640c000380c52680200c2c01000d00da84001c0d070080c903221404a0403800042c241c6440c04103000600258949006800941c0e0b0219401d00402d110744c210700c8040e00e51003d00030600b0310188000a600751300040d205600e060215088264203504500c14800c940002125440c0e002070b07140412900350190315107103407540c030034584000d4040c2c0725008030386407541c6105e0703d4000030b42c0c80a04108000c81e03055131500f182c900b107019003c410b0400c202c0040c2000e084109000102c8082503440345000c1c7c07044801401c500e258217840c040390303480f0b0700a010513100c001070394041585500004d00680c4a841107440401240e080c00100030b00780b19032503020303961115001051640c07c0001518082001040e144158820382c0000e8907441c1c02c10741d07201e0401c44d00342300340e000b960000341c0100c0811b00444c1e016804100c901e0405508134440c10100d42654010102070300b104000414603c04440c080380021608040701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 296324271 1250 296323021 296323033
    0x3112110050d120f0207090504080306010908031801180e0405030a030c0203030702060c030c2b06080a1703220506040219080c09070201060f080a0b010506040608010b1c020a02010203040302 83
    0xc1c061002a2541d00001000c41c120b80140d0040f103400340c2c0c2c0d2603801203071502c100c800c0c29499900d8070341103410548050790922310201c02c0240d69a400314204000c0c080318405542072002c5900c9510440b101079058a050041d00c41d0303803443e208940c00461004001310f0704d8070300e00740c28141400d83d129030104150100090420f02c80c030150900004c1120701980d41030380100742d1540e40e905090b2080d0009006c008035080c042280c60020074503004000213100c14160100b0a1260260307d1608403030f0142e01206154010314640400f107140d030042e0811102402107034654990b6806102c0d019680f0b200c0080e108021034080c004d00340400000c44500c95403007540c5131542c2e001e61711a014a02c01a40c458120745501c900448100e606000300c0664000d0601d00000c0342071521200815184080c41d004690550311898544040c48540000305006010544005180034281040140141c0050140c004000c0d03000601d460903020092401a022213284011511114010b000034003075070099405070f0041c8124 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 296325521 1250 296324271 296324279
    0x2070303061a030402030a06090609064706030603030d150303032304060209011e0f12052703040b0a090305010c2c011107091b0305100603112110 64
    0x11104413405070350020000c004480381680d4410242614481c104c0c2c105407200300e8400000c01a0107807001e0031264030700305d00d1713081ea05141c62088d9501900186403052042d440100d00721000444681480720140d031180e5580c0c0d22000802d00d1031240c000c0903020395103014400c032014071200005400740e0348a65010311059142181d810714000c510840d0340925030215010a0011700c26900078010480c040c11f286441100c000c1045c2c2ca0482c00d54520408075106c1e02d400412940c0c0301d074030f000c2d680d10001d00030801801d20100c010040c2e9450104994120b612507032200b840301e01003041c2c40090518003501c0303030384a01a031030040c4902000d2000700d40541c2851170650b041790003400340280c01d03142c031458052151000c0c60790038891100410500d05116044910103424079051083c000079004194000c1812085203110004071700820341c0190425103040706000c02c100c0c030024500200d901500d8082850101d845d006d40da02d10400490400071407400004811042e00f08000303900c03070008241034160386981c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 296326771 1250 296325521 296325569
    0x4110c07090b09071715040e01060f060e0a08071502070806090109060b03010216030806040209030f0c0a06021504060c091701060906120f0f0c0509070509090c07030f0e030c040207030306 82
    0x1d00c420031948485000280c1c0305c1c0030746d04c501c60303104802003004c600068480559401c480c41500a0303101610304140601019804c82400f98a6200c1903414082c85480c01102e0380c0c0382d14090142a000a510b0482c1080d494070801845d400f40c030a0102f03980046c10a40c950764002d11812404032203450510740440c02d01d29042c42034030900c03a06440b40300c44804440d90111406940105a00c2d44507130700340a51019614100006c2113400040d1009240d54100c040c00c02c071510754558080c030115440381505071051030544030740300e030460740c003100201d10b81c0c0030031100303075185822138025148024030070760b041c030092805400c050200c1f200c400040000b181c8642070364001d50380002014101d068000c40d51b41c0081c4406680000090054103094800e50301d81c8005544030000fa00d0714000240c0100c0c88030b4032490a11046500092500e84280c54201c882d60054640300080e0080c43c00e1103440c544081c543c0c0c40a00c051400e03400c0c02042150380388011f01e4081d0040241e8091f0b01225100d81c0168403013500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 296328021 1250 296326771 296326787
    0xf050a03030e0d0819030609050a020310060c030302070b040b0a0507231b30071e02040b09010602010c12110405130204050603010e0103050c0d0b0604110c07090b0907 73
    0x10701a56080c408a9620b018440b11460403d0f007100e2142003081003241e00c92022000904d001c250b942c002c03a12501d80708814040e14005814070107500c1c410420301480c0c290190301182242c2090401140548543c04c0560090080405c00761024110008000410944c050542d12806002c2c408101a0300c620b0781c12504507039030300c01e00305080c8841001150300b55030010191100e0440040d0b44480311004089050a1016070701e82511002c6a05a0300b030900981e014020001a00d141103160500c010398513850900125038202210901c038440c030308000d54985402001c0003c8007e441c00b4807a5a40d540d0080c002e0a40b07040020000b0040d400c400ca0112440c0140c490f94416141c1413401d00b401d003000c1115100140301340b103010740c1c0e007003100040d2520341c2c00c0550b0003401040100c075081c1d03141d402d0440c240741e1a0441a44100c000268200029045070302450300148180e40c0014008841c5440c40d03054452907240d42c3d010300c01c000c800a180c540310781200d0b004442c04c0d500a0b10a0310b0300a02078131442 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 296329271 1250 296328021 296328023
    0x804031a0103120c0507080f010603170307020721020918070905060d061e1803171014060403230f032106060415030f15030812070c050607090f050a03 66
    0x820004401e80100b132140c850864440c0c000c0c4242d408103603540902e00e1416034409803208040e5101d00303041090110a1a84619101d00c81681e68550f10700703c03900945440301c6019807001214000154520403001220070340f40c0310350244c42e407050b50402c03100101070450b048210580301c1c030070407501103050410340c014103000346030260100c4c20110103a1f90344d802401080700102000e90125107070360881e039018000c402d0f481d1400a8440900c0c030140c1401041844104240d01510408500707104101c0b1483c0d50000840b07030007403c1d43c050881100f001851500c601d500190007402000b843c400c0a240c0283e482180c00000412641d111403481c020a80341d019404120002c0f800060b484800e0350792622030182c0c001001482e1074a001d84400c86841c0e0b1601031519100040d0f0380304c203042408159807081c9400c240c800054a610703d40303140e5a60009219050240c410092100085880780340a0700141140703e6002c401d8503031a190010300140000c0f090b200d0802c081c1c8130700200060310b0a204054506803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 296330521 1250 296329271 296329283
    0xd02010512040f020307030c030b1b0a030b01050c030d05091b0105070f02040b06030c0c0c01180302120a1e0606090b06180d0210020c011d010c03120f090804031a0103 73
    0xc038071070384a41c41a00052050710401c2003400c83d04010707a070a02204010b9445003161590f038a09500305054a036100400e8a200951403d200818000c81c11050f588803e0442c40d000c90326000c00001240c881c043c00302401c942c2c2c030010940003009140350308040e01c2038030804100c903548001511000303120056440c20300e0115104206550115980c2302c41100641d0016001041042040004c40e41c00c1d481207400d0244113201040401ca0124140001c400c2401c0c246014207035006400c1c812904200d552000078400c131340c40f9002001840040c443c6501d00c40d00302c503104490000c0c9205c0940b2160088004507059850200e003c1003a02807841160f55081014101300c0c10504e0010245580c0e104141c89180e000300f105804000582e03c003001801c00b800700f9030140c404018050005403204400d1007203114420460b011600c007590340300d510388820340c1c1c241ca05925905011405c480040c04c10000850825003045088018804090010802c491089400600c00d80d0012003a01840e0b000380002001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 296331771 1250 296330521 296330527
    0x1218150703050306130204031a090d020a030210020c01060506030a0b190f0902070204090b0c0a021603020622030507031a07050304022422030311120306010309030302071a01140d020105 81
    0x13042c201000412607010a60b00c0051500387c032a120100d1032005880707408260b0314850104840c25a083c800021180d2040c00181450601558041d480750040c4040c600b045601066002000c0800d401030401040041d00060347c030b00703010000f000a040911501e5004074402400c1e50050b9042181c50000c403001e05c894030f01c40505010100e40a58080041680c0c419154050140840d0070841c0302c0e4001c2c0d03104c040032507454100d2080a400c2c0002c2da0414401d03451503c00400240e1182011a4a5052001100125001540402000d015081c0c0000d01984180309010040103140c02829040c001e0240c8000c4003613840034401c841900c0210740c001d401c6402049811914902d0309407030b9101100c0800850f0030f013061440d1080100c070081a107002e28401301d1000b0002d1680000011402c80c55010140404800700452041c0c2448003401e00c0341056034840050701807520a50555114681c40f0440360454030912001d00035112080c01600c0c0b40c03034550142c2c0441c43c07400008010301c0950603180c00741 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 296333021 1250 296331771 296331781
    0xf0301030f030c061d0105060607033903020303040b240f03031b0106090b0402070f140a15050702011d1908090904050d110304140d020312181507030503 67
    0x72800e10034812810301c40c0c40302c241c50002d40140101c0004002c1120100440e20b0050f080c1420354070083d201c18000c80040040d40c011130f07440700c251108101c107214801c00710300011741140c0d0100b020401c200d10020b5070403000f104143d4040700075801f99002c1c4004610544a55950700488020400002d50710122006034003264103200c070300178000703410040660341802e4010303071000800b00380e010000c06240d40d140b0050140100b83c1c031032036102c2c01c029503045050131400c0e550448a0a400000942a03006002c42011180010030043c0344596006a549840c408660407881c017800003510100017650820215450081c54441028820068200103140444042042009015040320242e40c0b42804002021840d00c0303290322240601d02c45c10003030000d103480310801400c4550807100d4447c0d80c1c204100070420039040e00c0304468501c03030489081d0445159071001034509038039410302c0c40e0720302e8020903100b090003d1400400c481090076214603400c40e4914145107814801c5102c0100402d10500200d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 296334271 1250 296333021 296333033
    0x100608040311030310050a090b090609090703081801030c14040b090310060b03041208010b070b0703020d0507030c12020309030a0509010207081f1a10030b03011d0606150f030103 78
    0x5030098000c0c14442c100d41c05840105045502c122103401a00c110540100640d04088101c000102804913041145410a00000e0328802019202d98403441110010035400442842104001e59000342d2040c0c2c0c6074238190b000700c01011103000030b9021038644214038540902903140c4800000540036524901410004000030581148003a5a098400e50701c0200b1150058031583c4042c0c0955001241c5074034140c6000c0005003007001404080141600040001c41e803043d0a50300401d5004000740d03159510300400324001d000b40d03041119201d00b04002d0044468041c0d2020502800a55400300c1c0104032103107040c01d034442524131001640c01000000300c22445000940440070f030500c195503159690710b001601d01440000c0d02d00030070035061546c080462980c400c1c03400341c0d4030079454080506801000030720700c02c619185940a05884403e881e080d541c0a52185a14036991400c00e1081c1600e8026070382e5401d001ca41c1203000740c02c0541c40590304080c00090b10881d20701000041d185a085507202 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 296335521 1250 296334271 296334287
    0x61306141e2205060a05090307031e03022a0706030b060d0902030f03030108070f05040c020a031815020106090e010608073b0703060504060f03061505030a0308100e1006 74
    0x5142188010500c55202c620044108039000340624000d207010f06040c20780e18100c3c0c0d00a004809254410402500000c3c1c22011301000071100390301d00ba04d05503217424281c010340300b850855680c1000201120300300345161784140507110203000480e0346050316a8010b034202d80e401c2c40d00030341c0601c01303102c2440c48030b619400030600c6510150035188580f5440c5059480d41e04207800c045150b802c99102484180c0d050f400c3e4000901c001c48040c1700009001030042e440c0c91030408050200f040c5070081002074441d03241c0d4080180707000303216190305402400c002030081420f8003403401214201030707604078171030414000c039401d8030004409001114941620740050498400034024815075002c12aa440345104a9586000710390710501c175a1442c1c081d400904940054002c00e205529160052141c101b1184111041d207912481c00a102e0520403400c980001090b8481d40e8140f054000100806500100b840d002c3d800780c2c818100841e446900c2c203203031108103d03603000c0040d200c040104200ca10034464 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 296336771 1250 296335521 296335531
    0x1920010806011416050a0b091203040309090507020a0c090608060c18010f141917040510020901020f0604050a14010b131d0a030915050c06130212061306141e 69
    0x8203d84d0943daa140e061801d4900d040d101366040c0c0c03003004030200040c000d03110710031244141c1c940395145c9641c010303240140038040c0f465080c0e80d40002416030341c005c01a000c951070f0000d00002c506a50f41d040c2c0d4015003460300031640340c4e02819000c140c21891180c15100744510070390182448108540c011240c076561300f070840702008090368442080c0b4000c07800030711602c01200105528214180c1000d022226a4103403000001d180300c0800010400c041040648000f004d100540d68061460040341740c284082264a0079004100c1400100800002e0500180388100100d99000f9401250b0500f2298102100c540061215005448104480c3d01c9006804840040d0322130020302c105e41c0f1407424888050880204010003400e01541c1100c0711001e280009c0b614180c0e25000c0c91446d681d4030380d40041c220242c0c20400750307050403c6584010700c0003404415002100c19030314002e0300d902900c0490740c00c10303546280741503d60004c2920000e21a8840c1a003140e80c400079034090411403c00c0310300104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 296338021 1250 296336771 296336797
    0x60518040c0306060b0901030e030a0905010f09050909060f01080f032b021201030201030522080703090305030313060b0108060303030609040206040503030c030c150108120a0219200108060114 84
    0x1d40800020180c2c400c0700060040518410f844203000707800501155400100f8415503030080c000308005940c00106041035600a04c0e00d00e6042c1400c4402f41c4401550790421684030800d202002418500012031501c42d8035820018082030f41e90b81c140540742e801d820720203c0284c104100a0084404c14000b070305038003d4040283c80b90481a84080080f82c0140e0b140d58280c020001c0100709541e818010590807803151000380340c0b009440c19016044000404000707201c2e00d00403c5143c2818000d8410000454008050742d680b0b14000f80504525103401c04e040b0b49a0b483c0c000980b0495200f090254030030718010303000b503103541c40e52001c00036a0440204101c0c1c0c003410130400400e50b91800e001800f14841807600a50b103800d564914070303041112024040c010201c8141c01004100400190000381c40110340440740d8800700382d01c040b03003000c0b14000450712012070600b041080100c80c08900d040d200301703109281d0210706980011902414248e85807400a001011200d5020304000c00920741078182d90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 296339271 1250 296338021 296338043
    0x510201210051003090203011118041e14010305071203050f1606020a1d030f060610020a050604031205071d060a021f061d24010c0c090c1206051804 65
    0x74168501e90080b400019403035040341c5c01107080074010401f100ba030203100308e8140780e05030310125080b040c1c0150503440b41341c0781c081940103607002d01e2814141c091010824003014100c504000c4422200380720865003032159103c00100120132104110071300ba490307030720360785040c0b404084032620390400c1c43c5201d00034400c1e07660100003482c40c2c4010079542045403100b107001c101c031400e0741c100544469036881c083d4010003c104080000826855032003c012070390340ca6842503000c0100d242600025004106201d03c40900042c5500303e441140350384040e14082c440380e42d8949041340c19200e50464140d405058041d18901880c0c00c40183c000021948115050020041143c0d402d2000254018602e10741c0c8a01c107001c00d2401c00c050004450410061048a040a01580c04240c1803c21100c0402d20000314459940c0c0c850030503040101e0b04404110803107921090790700014403a030342004003c1007020000e900b005a50b0b00aa20072120001e028482c520380c3d90790380701d010050041c0101d03132645100d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 296340521 1250 296339271 296339279
    0x40c231806190323010b151308030304030305011401030b01020a080307110312090c09012102060910080601020d260a02090306010f0504050f01052101060506070510201210 75
    0x200700d050000314041d608140b6810310709000d20b0b400132880c102d001e5040c0d051000070b03009a00c2e07a00c2d60324a118000c24a9543da02d080b1040d041201d01980c0081e0118000002444103140d4180c10003816501b1201440101610640040d41111a00045640580c002d0f10050020130720290240d81e200302107041c2100d5201035800c00c1030865001c0d4940c082c24403100c81c1402496481000361402c4001c055035143c0c240d5041404101e620004401d8080b10800d1204650341151541002d0700c91312100074045415074030140354054a5001c1c100c07030f05401440388520442031300344601722081d845000d680861012122040468000c81c200510400400e9000c024031b17001030b00e0030000c0354024448100008440c2d403d010030002503c60140113880800119001413003e43e0361000c45900c0b485904a880300c2000d001e030001400b41c0010350260b035101c02c002c01c403d020b00078007003070020062200300c0080040040030030070100711512000c0e0a0492503810b0180d80041c02e100c8403120b401001e240940408280e80d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 296341771 1250 296340521 296340559
    0x909110f120a060e060601053105060408010515091915330806090a0f1103010b04050f040c02062205160e060406050102100b040f05040c231806 63
    0x180e408100c980f99902c2c081c001c0c0d0500d0500c80303203801c07080902e84245000d9410100749281020200340b100b414445c0c0b2a101c442180c50400e07100100005019251103507070310002c0030b0003088206c416803683d0700841e905140303524014000900c122440140100c44940c81030101004050140710081e650720001004110960100307a1030740201c07003a031510160000d01c1d03208882ea9000c01001d04d0148103c10080c4903041d507650034160b6001c0300066001540c411000d010790007504002c030003651b5101c0000004120001d10307200403c243e880503181060344001400074801115000182100103800500205020040c02940c1c44110780003249850003039049030700c0381818814600d0110000c4030074064100044440c010045a22500854003040800d01e00b000103502c5a01003022178469645e11085281603654a42c0000201c0000150070041f0349024034180e00750741514040c852004c1e03050755290340e0000580c5c1c00c52042c1d10b0060198004c0c401800000c011029000e441c0992114040b0b640081002d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 296343021 1250 296341771 296341783
    0x41a040314010203041b060815130f020a140403080315060d02030c0304110d030806010302030717010b0a0206010e04170d0e0118020406050a031703151206010602070909110f12 77
    0x1007401c00069907801c003490610130740c007060303040c1c56029042011b003001420340000925500414080722418070342e581d01c0010f07011800c102030341d0300d0603031904500380410016a800350400c1c0150391620700c00712440301007a18050082c2c1c400100303c0b070400c0000803103d0165014000709000c0240805040c4103007031034203005a80084454450940300030007080140560008801d440b00320541c3c00100c0c2c030748551001031040e14020710b076506041d00000454941c42c0715030b401c05101d1451103419503065840301040380042d400030603584014401e840001c200001800055405168000b01c0b9206038070410842c1141904080301c1c149410351b42c2c4030841250002801a108111260411140c1c101c0786807042100b1200c650700004d0041310102001d10008500c0c0c81c05d8240e0070502a00c0740d07120342c0c503800c51503900c0410601032074000c00700840300501c0c8000084c0c514181ca1141d02500c03d002d0f200c0d010301c41114400c080160a4228007204900c281c2001903081010700070181091010022505090745803135 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 296344271 1250 296343021 296343053
    0xd0c0b0a030b090606070203060a0905030910050403150506061b150a0e01050108011b05070c03080a080a0608190212100e2a010f08070507020409030302180a0b041a0403 74
    0xb6101d112032100c5141c10416240c1c0040102d83c000d041c060346402003951084000c204900141d61410a0424040100b0039030f01042d2009018912020205800400d5030700103220844176401820390401046815014052040e140640310909110400044400840001e04042d5060142d02443c140340d4000c00b880741c1c41240002c2c004962116a40802c500f1910164445c5e01603924000b003505048158081d5000341ca525850400d031120160300300006180c0c4164001410f0420002e504400550000e24251107540c1c480f2042001c15643c0b42c1542d151418030f00440c0e441a640006400189403000c4460316520004d0700311010060440046401c0311f2103001c9015940e4403540d21101c0d0203000d000b01ca48a2030301c1c2c4001c0e42d00600f200002801700c003000e00610050200480000d1012441442690210340d00280f050103005210306000c0c1c002c0d40800303000c0741c00f05907903419501c4d14100b004490040300c803000c40151505d40351041c8d45400b00340300000c22848180812002002c00d025106121000b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 296345521 1250 296344271 296344277
    0xc01020a030506120a0305040b07020316030b0f0f010617041e3e060c1009080304060615200115080607030b0118030f03120c0305330d0c0b0a 62
    0x2d410303c202040b450070444018140182d1048103850002907100003501c2c00c9940c1000b5583d00c0c0d6205100107403d00d82d03810002416080915800802e1081891196020b442445203203856a29180d0756103600400134003a00010450f090001c07000303500e030203c407035921a0040c220f50f0fa55500100050405034091001078840141c003040075401c1080a4050011402040c44600c40d1281d0804e60035400d4590b00c00480c0c429440402d201440f50002c3c0084402091565020006455185002c4405406c113840c255007480c98441301292291000304c0c4c0c550100b4007521001c2e03401c41a14107140449800f950600724075500c814079003450746003840340704003c0c00ac0e50b0080d14480c5880c40c00107045600d0b03c2159410440803803102401d03010f00240500540c0d41000c2c815448540300d0400380c5070b840d00c4241c2207541902c0d2103400040a649948881e01031328400e11440e0441c607003600c00c00e40e00e404091001584a40f0404260b000f03141c94200c2e450490f00c1140c071b1440c200da48121541c0240c20500c1c4034804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 296346771 1250 296345521 296345531
    0xf0f060e010b0d060b03031903060e0a090f0204270b0a0c0201060f0b0f0909090609010b030c0f0108100f0308031609030b16031401091e0203150907050c01020a03 71
    0x20412503000e9102805038500c002c0202012550000e118041544805070066648000080745924288101c80c000780001014040d03156501d08010010034036072107007480c00701d100d10100e01d141800303018036004640c00c4003c0a90860307050b02004001c028503c0582c0030b44048040c1600c074a04414140481180190071542f00c030320f080c40b0710f281900d00020212007164540303402445807405d00c01c0e05c141902d502e00b4449458401c0c0c40e0b50920544074800e4495406490300080005d06000000c00d01c0c07140d40800d0091048003905018156a2402a00304581c040103481c040d10aa510403c1042d038401090400fa15100b9034940361a02c0c1c2058940050704c2450340041081402280c6260080d0001e045240591a280c0b960301c0b0201c80c034401500b146200e410a0241d00c141c103120b038101400d508006078541010f96515094038004108010241d860540103402c40b0104100500c240c0707200e1440ca91504905111305d40810403030690007820101406818441c08544070350074809010810301c41d40b40021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 296348021 1250 296346771 296346773
    0xa1e0e010213080705060a0f0909020706230f0c0a0c0209070507020a08060f0403030c030213242607020f19020f04150b1803010e0109020a0807030302071a070f0f 71
    0x2c00d50403241c000f004154441c10040040351100003c58103942810700d04000010100f0f007088400503410392040c0314050010885c1800c0c040c0340e038054810b010f4022400c40c0900d09851000410740c50441c0d01c50841c61103100000d4407100000000c110020403803402c075500610075400174007402c0051343c2e0a000140301107003000071400c014034440007806030752000307103064602900c0c0001e20000040006040545800740c0480351070080c1c0550b410410440c00e14003417552601d004048038442c0f40341c010300200240c10711201c10f9001e4407148079441010304881d0010301170f4481d040d191060103404e4408502c601441c0071042507090180c4a075038003018600c0f20101445d40100300594107038429042c459450f01810704c0071400f45020010480f040008581c0c1c41d82a158221001c02400707020a03905542400d40a805282c01035102e98059071089541c0381c9110340303e1070030301e0740ca60b480e02000707016034440c00061241e01c40061207800702500c12041c0914000496035007246000d2003503021501c441d0305d145808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 296349271 1250 296348021 296348047
    0x70e0f190803070605010f06050408030f0d0603050a050f010c050a0c080a020c0904060203060a0905091b15070c080d03020406050412111206270a1103030c01060b0a1b0206030a1e0e0102 81
    0x21f8010403580c0303001400d160801d01100d449210f5440b001e15030510005904504242c036070000c50046410505903181d45c0c80608089480d80d9120b400006c0d5035103003030701540d00c150084042e294000c060350f45181d50405203543e48401680880c21000079071190301d4078441b941d95140f100301d2145229000141c0c403420960b050001c4181c20390040c0f0a80d90410081102c40100018141d21424124603003034418941c3e540440c24081d010844070000321000035480003804000324200d000c0799808001c40303151940c5118102d0481c06140200f10025400300b004001c501008500d00020500610640d2480c041d407100081c4e03403a480c00108000c5401003002c0007041910240702c0100000c042c5d45100c1c1c40c99004040a071500c03504100107001c01a810042482a01e0410503144481c104200810407291111501c07102a0450240080050b60080600c880c00c00a4410114850b601500f22400c58864038a594003030080816500f031020451345100044404074040d1010f0030100038001651025202554 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 296350521 1250 296349271 296349299
    0x19060210090501110a0c03260f040f0b0a0603021c0804060809070b0d0b010e0a080606040c171005030d03020f0412020301150f0f080c0d08030903161208070e0f19080307060501 77
    0x4a0751040e0f85070200e180c105048c032080d50300041085880103690f6440c5004400410700180181181d2110000c100602c2115800041620b00860344074000031201c0101142d040305845004101c454140f00c2000030f42d000b03c181d40d0f000080e40007a2445542c80c2c5d900c4080c160001c02d80302c60b05503112070071800c1075600803050810b006030a0300d840b400d0307605010440e540c0b8000900304038003541c1e07188204121503116203402d545d03c454904015491f407d007120450506841c5000c1c26203e03000d00d01c01402814001d100b11144215141080c44c140b41c9030a0052140c0c40792103500380d0b019500ca42c01d00c440c0c20b0070b01d071005000d001034812400c04d160400313440c02403001071034010802c2030303002e8112882d46a03181e00b100c84405a1182c0e07002d41d070382e0f600c04000d4150b000e000c0d180000200f650491f44104180340313082c0e60190210b0355400d03045503203800c0116804a00041d200c1e4200d83e0345160700715a030030b081c0a40e00c020500e00140d804000e5482d031469185a1103182c040e6181075940d03005000c0b0004078505 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 296351771 1250 296350521 296350547
    0x1b0a02100f02211209061005010e060702060408030a02060c1809100503030d0f050c0c030f03040305131202010e09010e1306060807090504171201061209020a09090219060210090501110a0c03 83
    0x20229494200d81c62907c44c000780c060541070020100c08a552075075a041101c1ca401c0c0d0140c6844d0b2101d6075008060707900c1d000052010094060700340020902c414903000d0354405541d00e200b200107000c001052001e5402d0107407030005402c500b90400702d02c1c1d071410002003465245915001a1031000003114004944014000c60000c880c1000803205030f100001c165944585454511540d0707481d5072800b6182e902c0f0301801401e05c14221000000c0002c40550301d02403944c000c1c1c0354000d507201040304103e50780b40c3c240601c2d021034102e18003050707a1110040b1502030307480c818440040d05c40d132106421468a0000e81c49a0407154446042008000c030204440f600341101d95a00c506100c954441b0905180050081104100400056500c2500d40380c0110340c06035000303800d41822a07185c0451002400c201082640141000c50f543c0800707168000c0040100c60f415409403c40e0218144c0e07510107060003c0083d0b400b5074032107114a003041402401004500100e40750034030304e052285005402e00c03807400e40e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 296353021 1250 296351771 296351773
    0xb070c110a060c080d0b150c0c04110708092107080f070b03060603041509060515030601030302120a030204030506010608011d01060801151e051b0a02100f02211209 72
    0xb08402504580084012a44100001c2d140c0480c400c601c402440c010984551004500c501d072105007110100400070482c0d068140d4100b11807540502040d504100703840200380c0c6081200c0380100d0080e5002d050a46d07070060420b0300f40401091800b008150040c59030581d41c1018600b040000c00410a0b141d039451030f00c0240011502c0c0c00c4c500c90700307070100500090103500e00100050801c240303025461004507010408001078a407030300b071000050000300c44000d41e60002da0b0341c081c0d0a14001801c581240c0c1c3c11383c0140030310700d411020600f10307412110036141131680a0102000080c0c040c00618007070401c940d80c000b800d40c940440c581c0840e80f8404c3d140b24150640d8014424070317502c481c5440c1952545040c00001000d502030403115514402c1c40708882c400c3e4040c11a144d294404028064100e908000281075403032145416158126504001e6102c116501002c08140c0a400c00f0a0926182d0040d00c100c6d89000601001920041e030b4003801951000031801412007007003503210b82103000c4030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 296354271 1250 296353021 296353039
    0x60c2705040f1104031704080f0303071b0b04061e06080f011103010f06080c0f220f08030711031c030e1605060d0504050c0a0603330306020c03070b070c11 68
    0x403600c0d201901c11400098980fa840040c1c0301402011001101d00501c2200c08490049d600007800603229001640c5801c00601b03030b458480a902c00900d01c0001045d0040e44000c0e03171307843d0340c2d480000a00a011000b50000a180f200308501c4416104290041c440240a001d40d1100d9440c5142114481e0a180c4070304035061006200c8a08444034003000d66840341849842502c1b15100c82c032850140d840a800d00400c00207107513041c200041c81070110102100707026607001da211508003071114054051070100303620600c130a101040300c2e24011560000b0140558129540482d02c1181c0030f0680480500402d8849050090304d071002c00c144000700309007404c030007003681c20a00080d4142c410700134005005501e480100742482024030900d1503044009040c4440d06940d4800a0080d191000b642086103030b0700400b039200103c0104034419503821501021024508644d2440000c0d040112b00030002d1106002000009040109190055090380c0395452540504e24141140d10740680c680f9000741084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 296355521 1250 296354271 296354291
    0x1d01061d07140d022206020706020d12020405040e03070b060a030b07080a0617070602100203010506070f060204030b0a1b02010b01360f03030f030c020703060c2705040f 74
    0x30511464025015103024441c4982e001c4500c00240910200c10701040c0c8001404c200d0280810100e0741400e028881e488840c83e5180d00503038070f42510f4805c40d80560008032112501c0c40c4074550f01d4049220b40d9000604164984000c5800c0b03d0365419000013561002603007100303102041491035440b160859001c6441c9066986e680c2d04040060014010301c0340c11004076040c485250044d40c0901003910203400550958061144c1d03c8445200b0400035028a001001408155008480c140c880160255150494641d9080500b03038034020151140d42d400d00c008400030310440c038000e0180500050108400401c01c43e481c00321060b00f4116015a0b14040c10b903501a42c01007003100101c09050309c80d019984409020121003002d180d1820241808154003040f48095600b046082e40c0c000d90b030f01c001c10a401031064003180c0b2804448800350f8004001000003606503001550388402d10b140025540c0784069040d804001c40001e5103a21a080c0718003400320b8103291180c0c04249922100a204100308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 296356771 1250 296355521 296355569
    0x5070206130f080313140705010e0102010b180c1e091f0905190902030c0c01180302060f1005060c0d11010b0f060702011403040c050a050628121d0106 66
    0x50014003d001880c04000541080780300c5040490b0709030071500310744401d40341e41c1041c3e4540070030f0300a80e0b02145888482c21040e5205100303040c83e1040192040000007444071040102e0040201411090f51007084210440b18540468070b01581c01924007586030040e8000700320101010f032501d200c2e407500c0341224041c440d50051224040b600b05641ea00e40f680e45281c80a24803010705d0b004406164000024407105210707040c024450a070b0641c0c020410115184103c1050a049a10103070050f803001c80820381c154010202583c11042c1040000c21b441d44d5000403541540101507007070160b800c10051644155084100e4001c0c2c1c0207980003c002c00c0010000240780641e0704683c180c082c040104101d001c590284804012001500e1909034884c589031900c042c1000326400317041e0150b10030740703000682414808282c0d101018020728180300b01c0f190b0311a003104440ca103170792482040300c000040b041d0864240b00c1c1d1546040718036005080d04207060209420f40b05c00d6408191440d07406850250400b02e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 296358021 1250 296356771 296356793
    0x3121e301509070921021c0302070b0315120307020a060912080c01020906030f150a06080a0207020a1a0408010501211e060501090504030314060108070c050717010507020613 76
    0x601290740c40d0141c0c80c0d483c800ca5054406402c801e000448501c00c41000500307020462907032600c219041001400800c1d00f100c185032048030010051b81c00010244031030309510f4051640305002d10360059101800000052100c5005501003c40b5000010070b02c040d41040020600a4921070500c594200e1500900c050b1b50203903800041d100d060027282c40d481448081d0111103110703400504071034581c2084000c800915409907584c030007000000240702d8250034035990140440c3c5039070715000501d40e51256200042d60021004a80c881c80d0407102150100910901c0c00000500440071a2640d0400c08201e00b10341042e04145c43c24414000844404d180d174039610000c9592190390480c9a4201c02d01c4600b001d41843c1000b1700c02d40c203040021418400c5079008034400c502136507041c0180c03c242c410b0490043c02c1030725040d00003035a000026282d24020b40c52100e00511900440300b000d80ea522402000c8001040d480d6040d9460300c0912400a504010315a005072804c0f0a981704d444017a80c0d102581c403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 296359271 1250 296358021 296358061
    0xa03051e01020c0d1e03060303050306040203040609050a1113111b03040b0a02010f061d1b0d0e01050106030b120a0b0a02092205010b0903121e30 64
    0x1403600c00000c5000d00a4043c1c0303142954680c00c58041010303021003d00813202c6110140c045140d56a40207640030b100f400365400f201d400d52641d07032441d03c03800c040c0300107944000d10965910352541c283e000011801c207c003d413028091504080054400410451410b194950810b29a402e00000b000d905100d80c04658101c6101c80351025804090319040c0c2c1140180e03070040624460219200040326019003020294452911040180315110340200d201c003411840c450009a540783c001941c1c0304410f401042354099590707884c5061201021401e000d0b00d1425000e0301c600e0351114010029150103000d42040221300f121508416132010100580d41c192407000905402440c1c000b04640480d907030b040f5100140003070524030010140080d44180c3e01d10782280e580301c3e00d10b03080000600282840640e140402c00401614090703000e5100554503401000076400700a5699003d00842d0000400030492040507030b03445c85440111400103500d80428065907500c0d000e00c1c004000440c181130380c4828002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296360521 1250 296359271 296359303
    0x311160f060e16171608030c01060f06020d36030b06180a02090a050909032206120f020f040e0a1107030e0d0c05060301060e0913050601030b0c07051603050c0a0305 72
    0x6680d51013030300d0030301464140d4403500500c00b40801e00d441c000c0300074021410900c00900c050359031240c0e2503000030381c3c3d0320031070005810103034072408030b280326400000d114517404c000742409409440005c0c0c0d003200f040f184035004400d5000c08008106404003c258030a030201d44210603508020310215445800030510100c1c0340c3d00040121041c0c0d5890090320142201401000c00d0745030210340550349511512000c0c1c2c2000b003004c074003c16999031a14000640d00c0e20707601d0f04510009540d520b4042e000c0720000d00034044d028440c0c501c070400b144d400380005011484080405040c0500780500300c035501c032159581c0800402003640400c1e00b041100d1500c140980705c0256800c141c2c1044071250100c0c3e003240364004000400010585c2c1c0c481440c0c00084422161400071743c131802012001c003d40d00f40010000e800c80b50041012032a543c07a10b50340901801011450001c15075075041c1461903645000c04541214501802400000c0194604444068858490040c01c6803140d42d502e034000410710107030f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296361771 1250 296360521 296360549
    0x3280b04140a0f0213050402030706050c071e0e090a020a030b0a0216060606030b010e030a0b0c13060504030303111303021c060911100c11010311160f060e16 69
    0x30080000300c1c01030024249416035a095181c0d1602c2c001a010605044e8414102510002c50102c4a48111400750b40c0c020010b0012034584801910150021909a10b40b80500e013800071340f4035821031490045100c01001a5203503030801941c0703000c03884041d20945490340000010001130b03c4029004040d80d401a0403800240e0b01d0401c02c4011f81720b00c8011124017402d002c0300800304802600490191607440e102401031406090044030401c000c0e051050345070340320210200c0491600000301d50885004103200385801100e8100348203140583d440240011000074041051561500c942201d104440300064034020182c6c0d0010444030183c0406403252840c0b0800c1d48231412502400155268003500520400d415400c1001e001d1500e80ca0580c000e4480200140144c0e1080340341e08a20750703001c2c1d252400300c0c40c904011402040d9845089030f2880041000c00c039003040303440d1800641031188502c40040c83e2186403144c02d81d6945030b402c03a400c2e4800004c0c502c460001c90419020b81e004140310b640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296363021 1250 296361771 296361773
    0x11040c0906120f18030c12030c051b0114010f090f05010315111308030912010c050307030e1509010e100b03030d0b06040506030906040308060916180b0a02010b03280b04 74
    0xf008040130300c00b055403a440102c94500301a048032800000d9401f079160816680f190341815415941c803221260009402000305e0800e00d1128106c0d034544d804d840b00006000c01c0090070140c140142078010400440201004202c09a000c0c001e8055050f40482e040c4a0381d451559044411003640c840075440c0d0b80c40d14052100d2040d84400c5d2000e10103c00c0c5400c603015941c96000362680c0c080c10350540a14501e012000900105020fa000c00c0401903441510315600d1a42c120000c151138050300b0f919018414006030b03030041d0305480f640251180030001070303541c5000c07000e140303052201e10312003602605100b100200c903036010080d6955202e01c4000883c58181d440005111881503810031a8070100100c1406191100007070b0b000d1007a442601c0745003503a100c40b020002d0080e03048444401040d1090203009000d413140d4450701d686e0f1a442d00c03440300d1765125550510541c0109128000507907444111604a10f8204002a15480c00c90350100c02d101d00d40000360081040610050072540c04100410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296364271 1250 296363021 296363051
    0x602150103021e090a1e06030b010b30180f060126030a0809102a05070c03030305061009030803070c02120105010306290108061201090f11040c090612 66
    0x60f841c010061410015192000081004000403411800f15103400991080c24103010321400c8280c0740c11041d08845a841e208072001154010004100011024580311081600174172a0003410408030aa85055140403010070546049060200050741d0141030322189046021564a0554500480c1e403000703850079600c0000e8040c25901954000d22000074a040b100758003903600760140c407800c0290341070f03034040d050503000b40c0300c003510200d070840c1c400a01c14107041c442005460b100b400314140700d401c107010754031a0250b4072515841031700841e8a8808001d01032034065418013922440e81800542c01d400e5450f4a1401d000040c40e800a004c03200c0505800e55a40d4002055407800c0c5000034400c560f120b150140183c20102c0910b407540005402103908000f0700340c0f40b40b0410034181e44204050342c03041c00f000f0309900d8888030504a5540c400315640444e002651b40925213000b4400040ca040646081c0300480b03040d08000c070100115443e09020150b84116880d00709030b103408011a00854840d201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296365521 1250 296364271 296364319
    0x7081302060307021608010c0e01020f07060e010c0209100305060601110a060506061c0b01140f071209090e060609070c03020d051c0c08042013090c03061410060215010302 75
    0x112041c408117800000d20f06c1c405402601030a243d40e0380f504041304019006a0ba00e035101008001c03150025601409554425492284019014500090285595000b04a0390f07101a202180c554150304402e206001007080056040300b02031901c580b100040410254550f030880304010101754450021405507034a21058403503c2c0d69a50150b01c502041c03100040c0140108916503003c280751106118003014034206a4400c80d031401c40b29450a4095501d100b45034422905010500c95051008103105520b4424050009900b800420b49402c05000b00060340000034018420005414110f000082e808290503e8400d4141031441d1604030005401080888119200540510700808183c0280d48038080c01d004130f014880c03940d80950b40c848509c1c00141d1040c070064009c601482c071005501c40e10781c8698090782c000c0c106000040d449540d0b8009440070801c440780c01c5000710050040304801d00c199900180240d0008000d90300881c42c2c840c1d0300020502c00684201d9402c5a2121110101954 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296366771 1250 296365521 296365543
    0x81b090603090c03011805010c0e012f1605040f060f051509190e071106070e0a050306090d08010819080f090a080708100e060103020d0f120806090708130206030702 72
    0x240a51440d04160001044034030400303a5241d0300780b511034409e690080340c000c203142e401070707460102c503941c01c02041990105c6141c00e1094100c54008107804e0440070711524041d000d0031030440c01c070a468142040300740d810302d03480e00c0804c5150175010011603410072006802c0701c200b980d00d440c143d03d0b0380079209c0050294031405c64025050134072000802103007090f10020b03900c110b6000e144940700c40d001100d113400c1c0c0300d0000312a503000c80042180e050055041b0140c1c3c580c001d040b41401d41d22030002c20304010007612001c0c500ea0118100c10210364106d0000c034090f009a1000300450200a842001001c11507035000e000c90030700043d10411071584500701e504158014080c907420a035200500da684072168480c0d0142c0340509100c04880051501070303508207105d414010101c990950f001c02064070800300089980d06032401c0742800165006600d05041d0580b615407098502d04901400600d000c024041d10400c100041002b180c0c4605240004c016901034813903681725543c03400241d19040d40010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296368021 1250 296366771 296366773
    0x60705160b07030f0b061329070f0605010902031014120f0705030607050708030c130306020304030909051f170a200a051008190b03071814040b04120e0a08010c081b090603090c03 78
    0x49d540c0d0902c081004140c1d441032060b407081019030f9843e00200100e00081d504000141c01c00c0b41e0802000301c044a550526078001002c3c0c56980d100c4000d0580b42074403040c41807000750400c80d800c00441c6030030300c0710691002103424041c1c07600d05140e0300c200b601d1000a02c0e40249003000700e00080f060b503d00010740041c50f40318100715640c2c200382c1000b0704140038074460030140a0030200001c41d1450b0b60f000b18019001c0c480b5074450001e0034003400d800702901c1c804e00c0d100b861058501d41c5000c2429003169a40317031143c05440c01d2070400344205020115403682c1115014607150076110340044d078400702c400d90092403040d0f801c0c0c003d0f2280042038040c1c0b070608011513051242c10382c0410700040100031455100d40b100f07000c001b903d003411060310743c404044501400c110f1441c0c1c00540441c06002c038110514a161030075044004910001440c3d1100b182c02440c0160355a02c070400041d904410f0051300000e80f4035072800034145e007140b802c031280300300034495001340300110200d602503000304014081014020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296369271 1250 296368021 296368027
    0x1206020309061008070902030a020919140301020f0a030e07081b011b05030901050c0304030512040e07090807140a09141e09060705160b07030f0b061329 67
    0x10500101940040e40d800485000320300c0415400c10803441d0040c2110340060103002101d207811881002908014200030220380c007045800c0d05907481c00703013890350070508000d0000c02500344400b00403805a0981c409000ba0f00c1040f080c1c4403013051600b662464031081c90082803074411905c14500f0001301d1740c040d94851040e450501c62440e18000060603c44003a0f943c4d106000c031680214480340400324010344150000c001012055129100400c460151041100d00e41030b5030381d0b01c0354905107401c0100b0010346008a0180b080e803a0b17104000307400c2075440c034001a001e400c24401d1601c1d082e29100da40e1030000561844085a02c5602403070001b003540a40c03c1080c02903009614507030007022103800700c1c003400900610000c58201240503015081d40c0e0000c00c180c1c1c3e07030707800306407030603486040c50300641c4541c941ca02c030004406101c0c09204003030b580d40109a20880c0e090030b500740c036100e0100381e100344801c1c00400d20444070300720804112032068514507002d540040f4000c21201c0804045032240c4400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296370521 1250 296369271 296369273
    0x1c0203010903031d0a0b130309030b0f0a0c051315030906060b03090705091902030c040506160c0f0308071205040f0f18020a1d030f0d03050a050702060106230412 71
    0x10703400f44802c0000d00781d40c206000c01520358a0740300c0400d45c0009026020396008500d620301c80781100282d2034441d0400225280d280e898020340c81da0300725000206000d42108000c40010f690080d404074481c13170b0900d103080c03010007201c118002800d030107150300016580000130b0031903100b40c20000005401c07140c2001080e40ba00d105020710750040300c04500700e03c54a1800102d80c240000d00611408002107191442040c0721604e0f000f80d400544416a0900305020100362680c840000300b1507605d1119070020003d5561074003c540640c6548070200c4406000c4d0108040780c0440300300d074041c940c45441c000b030100c114031003664103019035002040036070100100400c0c003140c5501410140d413040440345607203d0250403c075090780f03c1e05159900003103e1347d03220a04155100b103001c81203030006068410b0034070040502883c00b01c0503d17040300080d88075810701040a24600ca03c2e90000204e2001c3c00c0c4540c140000900100482c0c0f40125483c9a8000007010446c80c000607900502030745c40c0300481d05905 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296371771 1250 296370521 296370527
    0x9020609121506031c080615040605090901090e030a03020906070b09030403051006050105160c030213091104020405091f0e01061d0a1a2506020403120305040b061c0203010903 77
    0x70310460300c545007000c2c0410b4441c0760018265900410b00608817500c200312003812500c0210190030141c0200c42c0c59200f070b0b00120400043c1c4050401030b030316561918841c40810228101c10b9110300303201e5142c0340d144031010b030001c0200e501c4c08040d41400759940c0e00720004030384244201940600f4044a01c0148082c00c10003000a2084a000308204c503c042c150380d0140044803264072507a07000c02c00402c201e09050504503a1152184e00585001200d16500d030045802624140d0052a400703540b94080d0701000201d40484c407101c507003a1400c500b41400e01020440701507016140400c001c002e00c9209104c12400381c522009840040107903000f6503590140980038004203d09024040511410307807205040000707201045920310b506015035000015140d03281c039802041420481da8688100000b50962007074141c210a101396401a41c0f1843d41c1001c0c3c0d051550788110004042c100f100307000110700320000864201c0c804840302c2800882018985504c0e034107108009425508005800c424036030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296373021 1250 296371771 296371783
    0x3080c0303090f03210405010e010e032106030606041d0f160e091f020f042405030f010b0d060503100b0a060f050d0c140706021312150902060912 64
    0x31080c1d049454803400000a04d499001d507803000f03d1810100c0e40b42c0640030b80c0174200c0940050161000003000f14207200da003825140149503036600317a440011024407070501c4000c0d80c0d00e480444550740607a8140400000d481e0a406440d4500c1517889110300b1490b0a1121113000742c91458104560500203141c0003a41ca91408500d241c0d0f103215051000155029141e80051041581502429060044600e07554880c03142125151202d035090014141001c0c03004010406002d00640000c2110000303041611038004000070700041200500c180311140141d0582c8038192030303001f00e03481d07100d481c0243c6ca400144002c0e40100e5140c81a581e10402034180780e0b200b07034000203003034403040c985546400041d00e510400e050080001102009911f500f0f500642c4034241e28003a914003040c0c81072490748a4511a0001a01aa8a40d42c0080c0801c5d513035090300824002880c40c400c0307a6040100c00d84070340e8440010035081186040d141c002010441d036401048079015031000344140140302004184540da41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296374271 1250 296373021 296373031
    0x30a0306050a0905040203031e0903011d01150806070e010c08030408090a0504020a05070206070f0c0f080c0a0b04050103050912030108070503010506120a14031606270308011e03080c0303 82
    0x890714140030603030a0301801900d10031703070f000ba0013149450401c1e41e011000f29001b9907c0c01048605000d030104544d000c1c0120700c104800c41401c1090040810307071007070842d0307081041013800a000320b400f000702003030209019503c80c0c1141060005a028040140c49020540500a2064000004001c01c11000c02d002d8440c6840a40d0358102d42501c0d20140404ca00c5039071141c0000c60400e215400051500d0b4000b4159a881158a06a80600c0381d64041c40020607821551780c0c0d4000840c244080ea100b0800c1b02c1c00d0442c12130319942018601030302101d0a00c01c9016680c10541c58100050200408008001001d0341810702d0660b40e42c1c1d190000b689840ca80e001d094440c0d4282000701d000341c074104800d4401a001c0b03074050040c404240c0c4e510440300408c0111a60140010f0040c014000c48c5050b054080c0d601840c40070a40c031005807a80c40c01a5005103110419a27041d100315004664409000c506503051602d51b42c0303903d00000424094907402c1d80c00200b8900c0e0019095101c0100800918020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296375521 1250 296374271 296374279
    0x1c05070801080d17010b0702040f020414011d010504120305090310020a030f1512020a0e090c180f010b090a0b04090c2003070b0a0f0c02160602160e0711030a030605 72
    0x40c0600705001c40e002c2138200802c14031380d10210014040f83d00034070003c01d5006d200400005503103a20130140000e0360803507409545212817041da146100c1d600f1039078908040300312807030784070000500f100041c0641c0101e001d00302c40140c03c0da0003401058007680444844600c014200e0f00500a49841007020b0740c0405941d4000900b0000c40000c02011800390f0b412124140d0011501c1034104030350601e12005c01c1e1410f903406150124000f4800400c402c01c1405040408007402e0f0203060f0300180480404044000011003400c1401c100200940c035005605440d05000c6d1a50b07144900c500180303294409410081b020f400c00100000c1011140e48100c04a01907601c501d40318008660583c403150001c4001d04030f260300100000b400280e151090b190b80030005500010b4002072246d440f40071100d0228600000d40d21140c0742c64140292142008001e020300e1004194407a103a64403150068aa0312030384400e040c1d1900400d0200d4000e01d904031a04292031b0450b0b440c1c40c3d20b014011701401c0c6a102c4c81d80030b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296376771 1250 296375521 296375533
    0xb091513061212020102070b101a0a0c0b070224010806010816091e060b180306061003271a0c09010f121b03090302100203090c01051c0507080108 64
    0x30490203009000448288030342c03115004440e51600c00301a54885005030844d50300300040c10003c4c96010305107004000301135800b00340c1070511007440100b04800300c95220010080c4008070b649680300705e00501d00c942c07002c0e180c040e41e1501d10381a46044490081c403503a66014113105507191110001030ba040315000d00444510b80d03618502a5112012194070308070081c0000d1041c041c258441e0866030b03c0b2940d140845404050680c001021540203802205007054002072403400c003501d0380b5901c140e070a0701310083c0c141814130030001924070801000042c2855120350113107000d034680782c41414618950810541441e90356251610312203401001b011002c041b50000310b10600a0902910100401a141c004003868256410343c0c0b000c807003101c043e08681e00c0d213080394090300c01d14898581c00d64250310085044803080c035010b41420316000d45449030a105100300803405000141300e82d107151003800e2841d035800b940700900c0d9203099401440040035007000c042c420517940c0030800310304880d00c82040c2c0d51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296378021 1250 296376771 296376799
    0x12010c17100815101509030501051e0114040b040203040501020c07080c060403030e0316031103011a060702040b060d0501082410090c0203070501060806100f060f120b0915 75
    0x20304681d1901815900f64005408159080402c500d1144c1080070301c2103a6211603910742c91200842600580c0ca0001000c4000402c1085230901035140c000d01848429a080c2c50704081505800344148074985085d12200c1400b41b0f40c4c0c40e164402000800060020366030b030305d02703810260702035401918036442e64824180009180040814010148079000f007051386464074548040f24410000448542c1c1070294440c07000808010010343c000452284010281c185403003010036003107030a5109107030300ea58446000742005a4031301d01141c0320140d04843c00240010100003062060042d8044410f94500c0d18002140075075000468404c0140b455503188a612400009644203050685801241c1c00300380c02c041c44404025040948204200e104490800c0840c0d110903094600e16131059840c1c0c0c0004050102130581060f001020348551055010000e20300000100000c0c0c0b2800c201e81002280c40ca68012000c007604030030003d280040003032546060402500c4000c0e498038080310310441341131428003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296379271 1250 296378021 296378041
    0x1005060414040914100504030e030316021203090a0e0103170a0813110a06050c010b040204080307060c0c0609060b040b0a1401080a0912120e0a020901050f12010c17 72
    0x15059030003052074200e04542010500000e0000f00030212110600d0150211091000300880104040c2d040c502150302d080509000d49403000c02e0620724041c0d0010001441010101c8007a0006140e064950184960482000e03500314081d00000f658800d5028070700044a01c0d41342500e0b41601e00a01c2540104410400900118414101000041401900000c4020703106a840324001c50203200300c2e0b4120300f075003800110120119000403001c9070020624400b2501e007407091810500341940d0844c50a0f0074044030590300e0150010080c41c464132003010480b0544a001c03031107400340d0f000c0824041c2482c00e00c1c00304050440840442e009900e018940c1000e40340100c1184221044070368900000700e070000045440c2840100700d0810203803140d10a00c0010b140700200003400d8800e917103885c035000010b401c8400b610036030b252240055000d540c2034070260740c868420034110f81c01120007800030fa80c2da401055480c5000604c541e01383d440c0ca1490070886803c032903014030401d0b06c034019400c140c0c0e03040f17007113 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296380521 1250 296379271 296379277
    0x20d0504140f030a06020d1a0f0916030e150103151b0c02120d090602070e190e1f021b061303030b0118030c170f0a0204020d02040302040f0203100506 66
    0x492070324015204460050910300044003180030090207440401c201903c850742a40e019144040c0419a60609961015100d54100d03104081c2100c0400782d01c485100050080c140103420005041601a0302c600018001d500168030182101c003900d199503d02c80030001e03000401d200540d110f408941140c1500c2c250741c4500300030300c2e0404502c0703032404016950031140d00512000c02c80c0c00c440c00326045440c41c6000c1102c491889403640d5079400483c20810000d00b4551740e40d02544600ca0664188080c0078090045410a240c2420740040c0118070701c00044e113006108840030811040c82040d040d10200c0d150000c103240780218650a54034043d40907240d030b0710703902190785001900c100c5240700000781c030035084001d001c0d030149010180702440040206240c2c510f0340c02250610701900c4200074903100000c100003150296400b07030030304504141100c0c2d00d0f0412230740000e115590028072806405000d6040d03402860b0003400030070a281001400c3c81c0203500c00e070780c0d5900200750203600041924242d011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296381771 1250 296380521 296380529
    0x103050304301101090b070605010807060f0c02040519020c06061f0905060306040e030a030c08130210081f06030509010605030d0210050a09330b010207050d05010f020a0c03020d0504 80
    0x82925034010030f07182c00c180e5805240c882e50422100b039200180d0b40c50140e0107401d4444c001ca81c00100d07545400801c52401045601071014000100b02020405401c00180ca101a0301520041900e5540d6800e10000c0013110141c000d1103403011844020150740060500e100d000e0030358109003007801c02c0c9425900c012208201a0009402800902107030501030065501304070058804101e29034641500c2c2d095400c80c00c000000240d4980325000441d6200b00ca45810000d01d150181c0b0200e000d4000c5020502618400760a00c80300e8408501d40d4548009000005c0c04040240c03008a904c0e018000c0140809071403510540d0700f401e00101d46031601140c2010348103030507001400205c02504814000d40402486407900503a224442000300e0f021030000c21069003240c400c89010507034907044410700e501440070303481c581f0324201e014401d5036000503440003641d0049980451481c1c8a00d0500d01405d0f8030303292000d41a0010454030005a0003a0407410703554483d8080c3c070301c0c1405019084074903028603c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296383021 1250 296381771 296381849
    0x100f0228030302090f041d0706030b0d030c020f0916112d01090b040305040603050a05220501020912030301060206090313090221010e2712210103050304 67
    0x25250000034083d034010825418090f02030341e103911140c4005411160301041c4481e84104007841c4440d8464184142070180409090820203e504800841c030340c114614802024805540c02c0e020640d910b1100c1c55004000c014025900391820780e43c0c0c11107a901c107510810128551100300005a0320118203064041c0100b03e00000140c103c81070101e0030a006209044c0c2ca540e10755510380440d00b00491107210340e0207611a503580b24901f81c0010111600206480d0102c0e10b00000d00c4810305116a050109043c652061030340441d5600b03015009110b202e0080f0343c05507410241c0d0a07600f1010000d1812607425800f550301070340d038001040c0e44034400c60602c10680c0f02c0005051004a02e10340c050b146c0c11461401040101440c000b40c1d1051042c00e8024812620078a401c200c0c42240010400150b068807103001d1444d0540035108a070b9400845000d0003903410085010340c907803070b40c00b000c02c0c100400402c0182202d5030b403400c10316100c0e0311a0241e01c1c1201082e001564100c2d002c41c0701142c0d40b0780404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296384271 1250 296383021 296383093
    0x70602060f070c030c06051e090a0b070e01050904180b06030a03080105010c1a130606080109030c151e0509160506072a08010204051e0112150302100f02 67
    0x141c811a460103603c1001c40602000d2a0241c0103d03502d40308144c17040c091034480885400c404096555520402064404254000041e1800040c008038015070042850f00b801881c0c005904010380e114054a611a0b400c2031030310540300c2c0c159070200380a14005004900c55903194039650103160b200c40701c0e0341000d0081103004004002d6075100d941c540346c00c0c0d070003020400c0b004520504442c603c1c501c241e0301444d0070f80c00606c030001031142c2c034401c1c07400502626000300321074540c5a5019044440d802c0c0c001e403801c0c40c200344005d100886600210008034184c0c1c0401d01c00342080d245c08004100c01c1d12002c10506c1615048004031000f036008006881c40102500d041004d960b54070510b10940e907407207203042c03c0303009440c0341620145941c0c94064140c038030015032124104001d201c10b28005100a8282580c51407030460540d030400000e400066203080c001c41c01c0031000d50074000568890b40020342010034039201c0141c070b5a000d4104280e4031130603801c1d6401c1310001b03030403100507000545160034111f00e55 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296385521 1250 296384271 296384281
    0x160b010e060f0d080c0115030f0302100c0e01140c07030503030f011e0e0403020c032e0218010c1a070509180103020907050a020a1703040506010b04182d060503070602060f 75
    0x203072000d0208005070b600041411f403280075044010301075540c0104c52502901440c2c0c020981c041c003450007203c10b0810704200071003206a0003070503204841c0d901f9051107043c2603224200140030303044a4403500030748101e80355543e59103040c42d560703441207911403105805103001090700e030003030a042c201101a00081c3d2001c60304144e111001c81e4805417007101503208000350301c44152014000500100011103c0030024000070300d100c0c40341550507001c0d0309190301c1000151402829580310000540c406c0ca0490100c101c245485083c410070b484400e40030344c5003032040000d81948200140041e080945022610700c05021450810610a00000b0340c010098030003e900319103d60060300200240b481224003401c100e444640320755054103d030144818000082000b0311108101c12801406462580340c0b6040c50195040700780c2e004407051440264071204682000c10306600700d411580c03107004000e02501c1c1c034848020010101071042900901030f01d0340c005281c900100d00e0501c1070300340b4001c400742039440b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296386771 1250 296385521 296385533
    0x20303040b0a0b12070501030e280503120a020711010804030f03020c15010b03060f0a0311010f030e0607020c01030f09030509040b06070807051005011208071205160b010e060f0d 78
    0x4002e001c03440841d50b0340c03104407099641410020f10b100480d4003500070a4100000102917403e00004603c840d030200c19600d150614210022503075042904034007141700c003207141203400e501c030b41300c801c01c50100344800f4481496100d0303005040d864456078516480c08a4000191503c400c02c0780c014020540d4850410700f4039001e82c00400314070319010143c1d100b0152580c9900301000080e00400150701e004810440700d400c01440204541408480c552029850340d41c400040c8c0e40005061410000a032807280c4002e07019400030780e41201c1c1c800c107546852900c0b01000f5030300c1c03d00c008404e00003400d042450040480a00c84d800c4240d0301b603560f907441d207000b210900c409448442c000715040501000030401003401400600b01c094400d4000c1c00c0d02003c00c00890060303841c10303041032018005e40011603000800c14821281119404501c03200c1d002c12030030040d213682c010151008a034070406100d600c00c00280804141c10b80c0d01c14090245540c65010520a6000300c0c0342002d030700007444484510208413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296388021 1250 296386771 296386793
    0x10e06071407061119030908100203060a120b01170c1005123117070f0c0b09060702040c02250905090a021008090109061803170c0313020109080610050a080d02030304 73
    0xc0603047c0304075000d580c5c4005a14120741c0f81080c03501035a01005101d15440e018403010010600b00722000c084000036258101009070620618a84100542d20b01a00800910401c0043c090040c1a45140ca8003400c000c6c0090384100f1483c40c0000780c0c6030000d81600221040d06021800420701d4070300300d0044103146503200042041c1034078200c3c1c500900c00071354000c0380024503410b441001c0c114400f240c14688100c600e1401e8200f030203025411300a802c807035201c0005a50006030121400300701d69000103030030f82c103001d82204030310440b4a42580c84e08541a820340b0035021180400300030000707a6658052251a4200c6040003548034080c070145125091040c1c2070075410000c1a0000075071701030295900f1040ba094650403152005601040303006150300200d01900300013403000040481d10300921030b00b41920004000e4281500002c45030415648120202800390030f00d0f000b280c14604120b06907400c041c0c3e1504c24180b207400260008a940c58010070100c1a104182c2c00441c00d41d1107607610441564 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296389271 1250 296388021 296388023
    0x10061d060408010507030606021c0c080304020d060507110d09080606040c02120307031406040b1f0c08070506040c0512070905071b030801090c09080a020609010e06071407061119 78
    0x80d0240700c0400d0b02070080c032604d40220320940780010702c103241c850040d08114004181c0f034444405a9001c44809400a41c00002164080b10741980c5e65680d10000c2c4980c0c104a001030200792500c0301300804c0075000480d00b06108240c00460701c0b449000e000856440c2041c1c0900d520580204002c15603d04041d0048055111540155207032050061070b8001c254000f150224006a118000c031110000151801c03030308804d060303406102135007800002ca04040000e110b003024440591001000c05845040418466075000c1c036503581d52803071400c140f6a01c14003901c0030b0740c1d0071058140000c0c85280c2280008901450710014049140c40d001c549801480e0041c05102408075084441c11601c1c100d0090110861090701c50140355410310040c0c03012903e11414100c1403007040320050003c90f2000501039026941164681d5440f804040101e9410040382910b50300454003044010401446242a5214407585000c844000c2c0c0d031084116a514102c2d0244c403581d0f00140304e0f02c2c16180340264400c09403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296390521 1250 296389271 296389279
    0x80604181101021c050a142505031306170a021e090d08041508011a2706040b07030f020303130b090a050d02010b0418020105091009230910061d 63
    0x1801c071001e0810502031441c0540c100052000580c10b118036040348040146501c0080f050b4100a1080b04110034090090102c650741e6240c400e00c1c23420000100b00319448003403804d9001c1030459850b540904001b80c003805844900c180000000d4281ea04d6109032000303829948803807440308401050050f07495000070885904061404100d01c080b9046200800040c1560644260160801c8600038107090043c1c03c000c04900f6441d0300c0c207160f400244203448a446141806c40c04480e514403020400464a911564010a0108000803008440c00182000d54041e8440e0310160390800000c80c0c41e88000c03650119500c95402d8900e0201d41407020203540b15007074200f1140c0c003010f55101d051400e41d05014140c0141e450b1071003030b003007402c043c0148140203414121401a40381c899001914a00a40e885240554501d59607900500c2c400c020890003450700c0c074041070701c0b92615240c0305000c4036078007203041c000c6272020b0120300100c0124000d40101d4020b0740e101c441310078190051814860358903215a40c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296391771 1250 296390521 296390533
    0x608010204030b070f0e06031609080a06020403021c21110a2a242a0c060e0f01030c0e030102030109050f09030301030b0a051816030308060418110102 66
    0x5040000d1005002860090781c0001c450b00d00904020441c0203100d6240302002100c595000158072041e065075000f080700010313060606000c80c01113911080c181e01450091151501403000e000300342d40140b069a00907031780c03a00240030003100c00c6040c0840d400e0003020343d40903080110200004940036011551123140c2800c09d084000300161900c2c89480701511410208844070508042480c1c3c9580010b000c080fa6500c00c61030034001641c441c01c0b0f4182040220700440c4aa600148a000c802c5800c0d5030740074901c407510381c000c20801d82d96448000c00300c0b1b610800c204007098050081030b04107a01c50b0003c082400540300000110040c001190303802c001e00c8813081c1e0340702d002c0d5400c1c00558082c0c005004001030b289000350400b6100d280152100215070010801400460503200501f0307480b00307e2200108150311480030110204441c002c5030b0400f4040c803c008089032180340042000c07070380607640740f426030789481c8200702c2200c12083c83c0408680840c1c0f503540020b6260f090341d40c50a4814016110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296393021 1250 296391771 296391779
    0xf010605070201030c0e0d110a0807140904020d020d1212050108030d0e031b0c0406140604090c051303030216050102070810050c070803010f0806070309020109030f05120a02071703030609011806 85
    0xd07e40e5842c81c02c481c03007014248420400d04081844500900364a8000c1c14840d00d40034200d4103140c0c161552501480b0303858006801e648400ca2908840756020300803200000c12401e12134401520320b8074800001e0000700c5c0240001c1407234090306050b40c07043d0000d185401499400540280b91007030090107213000c180504188a074501e500c100e541100c00003e40302c52091001084101e0340c06800950400302c0d1400c0850b1503845040c1650262101d0100025025082c1342e000c3c1c0b014003811101284136245110040101540421140c8510201c03010540c038940d107800043e0788643e90360040303c0c0c96600c1406104004c106503007010303401c0f50442d0312640c5014025100d01c0810741c0240c00000b14007414071030410841804102a95200e03074189030810001c5d03401d0f80003d00595480c88080e1003c54007030407000a01200b03029060030105d4041441e550307800341030400707900c50070103109004540030307a09860180b064010003101c0c0300d48401000200503a0a2181e80e040c4103008802c01d0380300782d0703480307001007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296394271 1250 296393021 296393029
    0x3010c09090906060812070605010915180207120306050906150a030c0e0a060c1a0411100512070305090d1e03021308010603050114091603020f010c0204110301030b0f010605070201030c0e 82
    0x14400c5014882d111f43d80301c29604040050310010b92180310190306c1d0008140082e12403107180341c00c0e640c01903090081c3c15003002084005e8010140080c01c605c1083c6400344007941c05500004c104c96080d903010301259501410004240f800082401a094041007803405003403003030740491000c2e0207900f80b0500480d110300100e21508003c1d0025400700e1551207144c7c083c01182411645020829040c407003041c40d05130343c0c440b40d030821a81c025018910007450382441c3d5018005a9881d03003441841d07013160b4608180018090101070321008154050040320340f0542e881103034103507224400c9031421012000c10101c02c030b00035840b01031400700b030014150011600c0c60f0b003070003103000541c020300c0080b0340b1501c81c140204a200c00a040184194044803180217085000b80b000e20840303804840072100a01000010f0315016030312900298003c0c50040203038079100343c11f00914141ca0080f03081080e40d030303190300002c41c00983c00e00441011440c140603080040d8420380044541401c54030f01a403141940f04045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296395521 1250 296394271 296394283
    0x6030c08030309010e0d02031804060b07050d0e1801121e0308251b1104020a02151003052104240e0402040510120e03040608070e03010c090909060608 66
    0x40c0115410000078042040c0f001d01504c83c3d43c5070300102078041d2803882c10019680b442800c5a0102c400b403040c52004540e5925400035005259507c240341d81c07883c851502e103444120071008000491103400e4000a10f00327010904840743d0000c1001d00c40c06900b040040c6100c0e10400d24201c40300f429510b4901922000d0f0000803803020b2181d01c5206040c14110600c0401c8604c540c0c03070100314809101802d00b05a400b08030030212901e0180f80a841d4072403810560742c3e6444094080341c0090000408090050380083c06120045074007064419584440c07c10402c220110311003e0055440b60303040400e1004107258586940d034060549a140a03528541280c0c8180c94503090945088600d4613268041d0308914242241007080f030b4114941418200050b80889026014800b00140748550303450001903035200c18410740103101243e88031683c0701001410a1800c454440001300e100480383c0c624141405142e5207030111340c8640c08907608166444009090a00d0140c1c1c4164882000048a070014040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296396771 1250 296395521 296395529
    0x60b13050f210307030e1903060203060a08011e110c12030c0c0d0e1002060910020d02251b050109152003040501180b04090207330c03050403020604031206030c 70
    0x556290406810082e009006180107076004103054821100d07c0c078114043e5105480c0d00803401600d0740c413000301080652075650800140c039072a100c002c0c0f01580d200c1d02080d0704200d1040092020341145454003030306015014030fa00d80d42e8000e20020480043c00d8014550006404c50102d04050468210b5440c1c04100f1103024041a1188002c0019003800000c540d03d50407a0b00091200e030a0004000360385041a91180014560100e0244d10141054040343c0c104d65010308840c0e84110509440d500304c81c900e231421518103480200ca00316000c0e034820500c0807100161038400140d850038009840d40165000700400b00311030114403035a03c408014100c28008030030707001151a2400c100000d001e0700d10b690225440e440501da020000d841c46e0108860964000007809a151034a0340361544210104003501c103040c900180007640108118039000c4c04141c182d00e4107104224591320142e040f1075081d1000340c01a04424001400710b0b01a80315001c0404800744005402952071312440804001508 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296398021 1250 296396771 296396773
    0xd1b0e07080a1b031503020d05010b010201180b0601050706060302060d0605030c0627010504030507080105061305150409080c030d020c01060f0f09090503040905010b070501060b13050f21 82
    0x800d0000507507101115507071020020b0820400842d0a1480410f68010030786403074105a00c0710000d44000d01c0c083c0301c2e10010b6038050100c10000c40e5614040d0f0180c110b01507110b00540c070b0180b5501d28440d4405440d4900794204d105111151074034001112141e00446d0140c642039280c010020040c3c484c08000c020803541c03040001441350414082506240302c8030075031761280340c1c14026202c00c03c41d030442c0103003103c1d0a04015000d051002d00184c810380502d0b44040c2460082103030004072074a06400080c880e80003103406400900040d03403c08101c40c400d0b1101c05607200000034544039818964042c02003540a412207900700700340300806038910340c040e0360310088003900450641d50b151000d000e144050a44241030824590030b10180242085407071180c1e05007543c0380c410000c1032210520032140507192926040c4400d6850366000486540452411220f81d0720b41040080c40524460075513800c0d680e00508090458031300010002c0184408151941c07201e4886889210504128a03038550506904 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296399271 1250 296398021 296398049
    0x130816020f01090b09060c151f060201020f031f030204050c07150b010203031f03050601030f120e0a05010c060e0115030b070503070206040204020d0b09091b0409110d1b 74
    0x1106101d20822065410360500c4108001440b00340449402e891096406659a5456401950b600e5140c404400b0341c102546150302c0130b0003000440ca803202c0b220b07040460700a15105503900700c100e00700c1c4540a0790048001050011900c0d50100d018900d2544044180f884070b40c580f0381d00040d08a030829100007442800028126007002100086030f035a10588120422490001c040040c1d101c0c40024890701c111403c1814400b4400c240a20a00146410204031082580c43c3c1c90080c26121030044203031741015021030714140140c0305103040306402d4005400c410390149020015900310440c03a40403075040b61140c4015440503824813800c00e00b0300484404250051031410102d03075400014003c80104002001085407080d00001e2694205606940040c0c0e0340c04a440c807480207007500440554030a58860070301c080900b0000320140500c0c6d8040c41109400d0810040008440710f5001c000c08640b0854a50140c82c50005141102c8a0044250101d4030300e001d8000c2e901c56610f034010380e2a8520b50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296400521 1250 296399271 296399273
    0x60307050307080a06020f0c07181109010c08090d051605010906020303090604170403121706040c021024080a030909141620011b0801060512130816 65
    0x1005420000e1109a02400c4254203050400c0c3c2c98000d1a0005000c02c0e800281c10b116001115085546500c5a0010780e0b2000380c4a81c04291007145006010030040d00707003062034030080d802c00d00710340442405031100c000d043c20710b0707840112603049a4200f60b4415509241a07010440c04d002c41c2802c5460101032076001d40c1460005002c030a41c2d0781002c0d007158010320800407a906c00080072504250810340400e0b00e52000114aa454856908003e1604101c5803108002c03e80100c40035040194403159182a95504070074401140d460210340c3c001a032080b250f1101050083c0e0140b00c00400d040d03600c40e91288140e125000d0802d20344d000344003d07807104d01d03c00185540310007414003a141c103110030701400181400095209002410040a41e40885c11000708180240300f0450044040e550404001545d020820300920001e03903542d41342d8000f0046241c80a102c0c40d50a0305032044c54850504180014816000c06030008225229140000b581c06001c103114502400300004d101c0482c9000d0015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296401771 1250 296400521 296400523
    0x3030911040e061806040b070c06060b0a0503041a0c180d0f05060a050c120106120e010507030f06081c0f0e0904060e0d021b0f030c040221070c1a0408130e0603 70
    0x9800f035101d030703803c4017080c040000c002030030361130300405030346084541100281414402481740e41e224a209000000e9515001c3e81c0001c050b500c294001d50225004003101400040301b246c0840340724200341020003002007c00b0008007482c00491000c0c190703003521a19a5031340c64280400000959443d44008200038141c4164000c03e580080c2190709641442c84102c803921110304180529418400c0c8040710600c0ca0420348e1005080040040090049040001c0d015008210030b10391441614141140862003074030004420103424144290410b4540c40751078116001c4103c49807c20411032500552007540e0707101d08046020f00d000380d2000171100030707022150f440c0843c8800b001701590800302c3c11103e1500c40512600c4921400d603420480070a038000004d05150102883d0382e80b00d88003245442c2c10900f05000704961055051100c000c0c1d84407040c00f0b580b0589180030080585806000c03010180d103c1c2d442c125041440341c1c54150402d8070805004081c009260031203407002c044030301007010600e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296402877 1106 296401771 296401801
    0xf060d0f021804020c0d050304050a050d2d0c20030102040909020f0102070b07080f09030607030f06050609030312090325020301230403030911040e06 66
    0x109651500d80290085680e856100e41203080050050400e44201c0300b03803121950003040b131265661411591035000800460b680d014000000001410821540b204605a41c42d2102000700e01211071002e00038448007540441d5641b511071400c1c031f4021440d402c005801140074801d0108141c8260840402c0554254044d0b03c0018001030401d10750340f12080d80e91089844400010f0b960707004aa80301d00301e0090709285c0400300040700000c2d600500034901e40d10031000c05414213481d40002410400c2c2210130170f000c0303034a23400c5103508030109100d120003512080f20000d0501044401190b40c0e0b01a81410318031000c8600702183c4403080070001d9a803281c8580d040165180321041200400410030300e008ca0007582400354254441c020a02859040d03005100311495130350365520200c000c1d200304001544c101113640742c1c08015885601414912958200040c1101e0070b0082240a80b45 = true := by decide +kernel

theorem cover : BRFrame.Cov 296223021 296402877 := by
  have h0 := BRFrame.cov_init 296223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 296223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 296223021 ≤ n) (h2 : n < 296402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
