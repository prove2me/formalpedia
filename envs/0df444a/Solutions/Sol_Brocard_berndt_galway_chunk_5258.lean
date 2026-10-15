-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:06.998646+00:00
-- url     : https://prove2.me/submissions/65a28907-62dd-4c81-9331-c7444a004eaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 945503597 ≤ n < 945683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 945504847 1250 945503597 945503609
    0x8070f05040504031d210d02010c0503101208070f12180b040501030b220902030f03070f03080703021e09120604020a05010c06090501020c24010302090f0903090d0c 72
    0x844056258000d21064600965000780001d106440302a5103220301c800d032500440c00200700030316003103c2d0381d810640d20140700c850716881d4002042c1c1001140e0244120010860103050035401c502e021404121140c0306446600d01181e4210005401c00a0107401c80b800760383e12412a860084c42420a2807000040c0320815010891101e00303401000300c819107503005c80300750f400b5071850700e400c7c000118060201443c031241c01040c944503080441d24000c100b882c403951101c40014142c0c415004240c80d04200741104011a0010000f00c00071a0300456010341d15074050420669a49919104a000340b007180707614404201003d240618210341c510080005e600222045c040c003d4050460b1503da4106407030095100d1480c4bc4100415401002c1c0e207940317680a041c0015000c4038070745070142a0390003030380790a21641000030740c071041c030300c201e85104a280c0e002c4070810220740c11030340070814511005c1c20a081c9801e2100029040207070420888281d2640541022090200362a1420949001d07014034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 945506097 1250 945504847 945504869
    0x402041d1614030403030b240c1e060a36030807180e060103090804080601051206070215060d05190209070509010c06230705130f080a06240807 63
    0x1000c01c98407070100c075412264014072503499500c541d0340980007000306200a9800608034500c285030185450802d01c20800701400e401d41d2001c16030350550034500c80c1410080c035000d00d2500d04000000c0000c40c0c662149040f4000500100c2c0c510305c0d415021004e40655030402a907508030301c51511044404004c080c825101c0100315241d08000780c3e02004100422001c0302801441003008012808966800c00c83c107042c000b9568003507803903515051b40282c2120304c1603888800100040d040000142d050042c40101405140c18100d40081d00c4210042c040ca0200710b40d0700225546545910780b02442561100440d540c500d050740f540b581c04800010241e208200d0800021803c0d40110121030300081c1c1650f562007407814540d01c00009110174003100080c034802c0d801da14140000310851501520301c586032a5203c24017454a8510300990b50003580c00000030302c100300310780c0200107201910268000c00c007065213109101b19600b44205403091980d01c14081000080051003c2112800d0b240c1032043c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 945507347 1250 945506097 945506131
    0x161703100504142e05061201330507020a12030804050607030513080f0f0318100b0a09020c0c030316020405060d032102090613060e101b020402041d 65
    0x30a010f50030080300e08850b401900803a024121400315807412002d505001181541034079031003c14003642020110300107400e0034800501840300c4480041403001c003070300c1c3c1c404480f130344200600d52410410300c0d00d07405001d03020503850111740d25041d600000c0c003991031506078064100c0c10b0041000005482c00d44480c05007001041c0c1c030074428080e80b0322804c805d10300010000c01965034002c40d60310034036410f01171030001d01c032191200821200440c055a03000707101c80081781c0e202109030708000e0402ca60b45115494030000d040c150305c64450340c2003100d402800c01612070381789101280c02c00d402d00350065418080005c00c0c0000101103401030300c40314003e0382c0410642c0c2d04d5009024611005c048080c005c9544002d0041c0d8038111440402c0b18400170b0300025007002155000f0034215000600001c0c0703da8418101400b0b420303401250500aa0380440f41811941003a50000d0304000003200d10b010444c4400ca62a815511190101d40044c0200503d0b2200c0c21455007030741c0080c9006841d4171141080340b10b9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 945508597 1250 945507347 945507371
    0x207060c08010302090105060f070c0f06021020070201020c100203031509010b0909070903050f070302011e08060103020f09090103060204031209060206071209050a0c0303080601020d0203161703100504 88
    0x6001c0c0d05a036401741c800ca409900303041c1046002d07004010f0099a404082008100240c0d001c41210000d222540c0d9101506061102c06420300c455501c2e000c1d4111326149859101444000c07038210b01015032800c641d500d80b6030303000403401d000c0c0c01004207030802003026402c0701c07155000006602c03601030080035060540d1002c04200521500b842a2444030708240540c01c2140790000c1c02d00d40011046c00e10f03140b910340e40e9881e1030414528007080d1101d81c0200c04104107558006038450240da445000d00c541d51503014001404041000c2c00301810980d0102d03104904903161b008171a8100c0000303012402c19039507480d060b000707580705010880d07100c0584d00c20403004500410317045054507401d130042c01e2a80d5039198125205a03008280d1581161100c0c5000c010407410300c0610300341030154541105050071400d01034a021400b0b486d5504662114040321070541d400b1060307840900c81190102d80d0031440781403400d288100002c0c45800400000140180305610300e408200329030081e04e0600c5401c1043c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 945509847 1250 945508597 945508607
    0x60a0b130906170703061d0d080a0b010509030618030f0c0304090c210f0b0402040306020c0105010e0c040b130e01060f0809030f0405040209010306091a010905090702120310090f0207060c 82
    0x21201000b6600c1800240001140e41c0c00504c0c040d41055001072400b4220202c0603d0403901140a00204d1680c009007d11032b105070064a03038840c4c0c20b003003440c601f802c040013183d96140000d0410000000010007044810414411242d803070b20110b00702600e59008240c410b88a0303210b48102c076482c40c506076800002a016200300317a400d1800c06000c85400742034110b400050441035075605c80d0580e480440c3c203241c0c1e071140302400285002c0d550040c2c6451000075210f08440f0f040c2c20802d18114100100508102100100d80076281510f85050f03c4482d00641c200800d90980c001e0350540b0242d20004c20180c5c2e110400b101000b1070b0f070f80c0e098603d80301c08031040e03168400c112032000c3c1d5400801c428003032401d041c2c00501c900c540c10724001900658030300d5020102c0e0f400b9044411072039206a0582c000d5070b803000550003c1c0404a404286c6400d06010180da510010700c00811000780120001c0e84041d00400c5a5000308080f410600c602e5103e80070b100300032b61201004442c2c0c1450f0507030b1a2070841c418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 945511097 1250 945509847 945509879
    0x150127060305150a02070206040609030213060305070b0c0102070b0414250302011b05101d06090a29270a050d120605120d0f050c0604020108060a0b130906 68
    0x1c2c010305801031000c00d440c0c144180041480100c150200200001a10340d1401040180016601d0301c480c03a0840c81080f020284410b003081a0b54100360042c000305902054071030845044030406987c54200100703050190043c03d4024280301181d00c2008184421480f54a030b07402400c0d01644e201803ca000b9501c54034400441380300c0341c81d070038000520055000d4146048051000d691401803001c150b030302c40746490100300034540c0403900e84030b81e00604c0d690400c0d030885e03084c17104010340420301c0c000480c82d988d841da40760050500a0620f020310021483c810801142c0b039008150048203180ca900312844110101c01c0c1101480300d050540c212800c0d0120300c101010381e10502a01001c50001001c541e000c10300d502e4409190361320280028550350381e03031241030103401840c043d007070034111031002800904044039000306010003002446541c100c0170034a164003d509081c030460b19203030704d00450400103a9400108481900241c1d00d0100e8055a00b12011102d8501c0180b004544582010704001c860b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 945512347 1250 945511097 945511103
    0x1180b121902061b1e07030201170a0908181c030c020d0602090a0f051203040f1502030d090b0f090c060703081b0417060c0702060406030e1501270603 66
    0x280429030640040d40c0c015407038990000302210b04042490580f00e0f00401207400b030380580d40c0808076026640a04200d42148403a040004e484841c0c0ba40c0c0000e0600c0e80e80410000d48502c142c0009203080c0015801600c4c0c954020701d24949650084150a100044142c1514072400500c168000c2d11940102c94028140d415900e402610f032050303090010072208510200e52241c0c0078002000303d5210b000c4000028102040138072011460503091008060054224513100d0700108420b00c6412000c0c0d565004403988122078400801d40720700c04030705500410320385c1c1d003a1604000741c0130306001e1010044d0303020351301c1614064050348505134000c3d80c13103150009a40d0400018040600030178011402c040d408140802541352000d0b80f82510610b540c1306e40c1050780141c40b001c0751400fa20104020f000d5100801004da14985103039600000c1c66802903100d00400c250f00c1d1207011f45e69910500a6524440c048000f4907c196101c200101100100c94605440e40d011502514001b8089006880450750 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 945513597 1250 945512347 945512353
    0x904020f09040302010617070501080901050f0103020607080f0a11012313020109050306040317100f0b09060904050a0f0c05032a04080604060605041a030d030c1701180b12 75
    0x20120040c4641481d0003441076081d13559507034000404942e030b60509065a40a40c0c080c041310340c1408009000800e02a06090150b85000200039031410b80400043c1582e4044655a03161205450001c400b4800d5036211400b00102080700840c09400205041c0755000440c001e0014106441e4411031813070b482e50b10078441c90240d00c049075129501c1881d0868030760041c500800d11a4840020a10703099050300d00700d00080e00c81d03140558040403102e15542005020005c00c9000e80f82c62415921030341c4900408070080c40024105c81583e071076038201c0ea10840040c0041c405460281d005000030124686140481802d00c0c0519040c17030320405c01c42c3c0c4030f80307036031144d042081c01c0f0394194191034030542c640d46460702800c01010680c180100306051155100780301c045101e508003418003003900c40c40041c41852581115030000c580d0b80100d00102d462105103800103032400141011a2405545400c0c20300f100000301c00420416034001c8002c0000011040c2071184c08007506c14003402c25061600060340390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 945514847 1250 945513597 945513619
    0x13091515080417040803040b071e03090b21040c030501050a180b04021503090d020d05040b18030c10020c100e0315270a020a0e1b030c070b010f14090402 67
    0x5043d01403d00040b0700d8085103500701500c580b80c582c034607030042d0808a4040030204011007003001c8404080d4007020500d4030350103c14869980074168107110f00519041c804046046403200c00c0d007518400120306041f07074041c0c00c2d0810741000c081c402c03018081a1040d50801c000101700c2c9090303014411415099070384c50002d41c03e103a11074110248024200720791020740b4410120060b0010b401a40c00380b04154040c110451138040060716000b0814860011301a052004004480259041d074046404200c0403001400313031a000241041d40307410159a1007a0707403240c01000c1547c00501c49505030001d0702c01c40092036680005840c40548820b04681c1a40210b00f00704503003081e03020298101c90340c00c0890902c0321f118207000c5070702849086981e13241d80c4450f45440071340c134044002c5001006036004d40b031004c0c10f102c0444600403230107800300080c100d0b0000c01300d549035096004075000f15405ca035200c9801c0d611400360003414a40c51207814603548000c4c040b8403007031400d515024011640109030481507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 945516097 1250 945514847 945514853
    0x601140a03060b0a0306020f040f050102010504030f0e0a0510020708061807030212030904020315040b1e0d0c050d0c0510031107020f13050f07021e150408130915150804 74
    0x9058025809a00204016030002c001b0340c5a0000e08030340449114141d4075281826003801c40244664442811603044c0410f110100342c12030740700b40c0d10090318503080c0540c107049008154100250382c882070700702c18000c026200c40b0f6400324641e0252040c503802d03610326445042c0c0045030542c6104803000c3c250081d036410001885d241c500025604081010380341062400b02c0010202d0f041125902140f0400c100c0f14036a40c0303028892210604400c981d48599042c1c0c1c0a03583c00000e50b0104907138000c0961141c01014800a240d100008280003400c0d04101c403031518103d1410030462003074134081c0a100c182c141c43c04d4004e0066841000410810318100022038080004054540c01510303003224a081206902c0310740c90140310711a402148281403a8102000000e01e4400603a6890b15101c40c085e078089041d803000700d9030214001401c0c19030b440030b4603541010300075449190700b04016000c0400000400d044036402c03246601012220441602d0b55440426074041000b10307401e0006200300c0009800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 945517347 1250 945516097 945516101
    0x180a18090c090501120212011418030904150509060a030803070e040b04020a17060f030303191e09030906090b03072f01060905090129030115031101020601140a0306 72
    0x3126009201c019042a0303989a080200c410a81103000842888000303c1e082d402d05c07590780d0603103c01e2200208034552408030070000ca0340010300780d002c1c048400690714400e1101001900c2d10340790014010040d0550140e080d4a261a261140c5070050380303a00c0000321103140c03590b500000c4030b800444c00b51075a40c1d085421a40d840303904181d40e40c01541e88400c112103840d42d2020700a0300c9060b881e1520aa4080c240841140b800109101e20801c1004030f40240c80d01c0100a4030741044590400903154880024010003a000c0d49804c00c002c0c0c40040800030880505410000e0703414003d880f46009203403500f82c11103104205018007983c2c20301c2080451385092240c14401002d045c0d0000f00100c00d1140600075881c0555000c0790481a0344618040c07101d4001c0d840340a41044100b002000001504d11040010b1000c1c1c0001010281700902c054100b07071420741046401c51040c0f42c00e042c5441d01c0c0c2ca460028120411002c900522076000040344808441d640d50100703800040079070102d6031960341c070000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 945518597 1250 945517347 945517361
    0x230d0c050d0f060528120b1f14011404030605090601060801080a03080708090c090903091e0102070b2b06061707090b090d080a0c1202070b0d02030411031002180a18 72
    0x840046281c40050806d8581440c141031520960807000715007443e06a013800c400000c0745000014010a104200c03410541400030303401c68080c00c1680c9403040480c2c4c12042c0f40074a030710191a46003000d04000760f0003070201d0f850317060300c0d210b480c4c3e1221a62555400e5030b540f441d41c0d40040c04149810080349480c1d008110352a4020319003000c5585a03000c0e0b402185107101d041da01110954004290084103250002e6400d00e03c2c864a17101844030b080d20f02c0003c1d9503410910804039402d4000460f02e10200c01e540c1400c15001c203502940f003e0300109034809000340ba4602c00d91000600f24200403001112502002d4081c00300c5070f59611005013050314000890307001d040340942c44540c40c0d00c2103000503c55400341100d118039840d005070261050600420b041d0701030b46c0210843d0070a2601340302034440300040e200d240c015060016100c4d40d5525089101003846400d140d894403540031a03113898030b81500104200f8180b480b4040c4410107076070920418400501865034000070600c00150b4130140750784415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 945519847 1250 945518597 945518659
    0x12010b09010c0825060e070509270f030406050a08061c081b0609010903090506071e03030b0916090504110d020c0319020307060c0f230d0c050d0f0605 66
    0x142001c01515091aaa49540c0400b100e0080c5c44010806e8a500103001e1030b4010041a10807402d507281c41003004568940d495001440d0215900d04401d0301801004150a48450030b000c90f940c03161100c07005803058001e200700400003401480050640e042040070070f848010801401a60060b0940d954640c40e0002010440340041282d40c5c00726500702084614054044100001540d9107103040003400501c658001900030141040142c0c0010401190701c68440446807a481c513541f81482d085010b4030800d54840d6010201d002400400003d50302007204c0d016050f00c1c3c040380560b4913001e020589028101250628105121346030100d51650010140c04000009a81c94504008008031215007003910310001a03001007103c0d400c00446100d010941c01c07050030098060302e0b0b03940740223115180b680301280c800c502e0700e04988925040803040e14130740e030200c44081c00684123880006210350400b020200420303003006103009c640a03240c0f040c0c90684101424140561682c05210030059850b12000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 945521097 1250 945519847 945519877
    0xe0d0f02060d09150e120d0c12061410260c0c07080616090e01050d0309030501022d07020102190c090c0c02010216050a12030201060f06020312010b09010c08 69
    0x501d1016840f44204040180700d204070f07484c1043ca00700c1460845907000035060a5501c4071418980407079010081d19000c80c40020041200110742d5411a10490b81c2101e00c0001402c03c60f000c510042c0d40320054001032005c1c0c810040c00300c0038240c03c4424074410b140307005289103040090310102e0740103184244c0c0044000f208520308590000701501e80308940d48100d00c242c10810911000183c07100700c47d54a4036251902c00c05c05401d10380c820307a0002040c49810300c2070b074440c040401054091410034004582090003192940c04804240c070901035100b541d5407220f41403111a90031000a90192800d03280c06174010b0600c0d1130090210040c24070b9552040c1c4d00c0070200c4000003419550380c00b404241d03d0702607030f0340040000113100180ca000a9409002c40d00070112405010ba500d4880703086007100c00c021030421200b00c01c0c1c1000d03801400c035900030302c54a070007109000c00c1c4e050300080103280d4071562050404a0340c0c0d13121541405409681047c5000440c9034540c00d0114684002901e0100c41c15401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 945522347 1250 945521097 945521107
    0xa0e150f0315090d0c020603060f03190309080d09140609130c090608132a0320030d110a0f0c0815100f0303020a0f0302011e0e06070e0d0f0206 63
    0x240340409040c0b1801000500e0000c0101c0200d080c0119000070340c850400e280d43c0e000310360016256000090074030313000d400c11032000ba41c150703420009000d0410142c04c40c0c15004c10142002001407940c0d028910151203440503a03141c00b44904420401c640301141a082c018002030100301e802d80c0b0007402e0990010111610040c0242d191252010041c4070352607034841d01d481c20801400442c00102202001400203a020010540f95902030840200510001180d00b034884500000c900c0507410192004c980c450901810051a007050128110200d0450300c071854503801c2204d03c101106102d80c03154000502d0f11002a00581010041a10801e0a40c070202d4030b58071814900769503c100002842100e40038040218120895513014200c00002410700c603080d41c0300607598500c846001800c002900b50031000340341c400e6000b0701061400c060750388014140301d20007030003070311074100080d00c24010040030551141c0500e030001c092282c00307403103039500050750303114000702c070000308400d98014000f006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 945523597 1250 945522347 945522349
    0x40509040f080c0114100503030703080a060f0e0901141e040302150a0207061401050d020609190305100b0a0317031e0106120e07030f2301090b04030e0a0e150f 70
    0x103050307410741040c0001503490411501a50145c00a86058120200034005001645010048540030b0741c06040443d01c9494030a461401000315612401129103410008a0700d012450341c19401980d5a40003400002c0114200f030f1051030042ea03070054480c0c03608554080700b00c03825501d554014083d00542d21000c0f051a800d5819101c00c4503c80b04290b4000f4040c1c0270003425200e0032400130140822120190305100c0460b004620040e0043d20551010600042540d100ca41800241c840c0c0c2601c0b0441541c0d900e0181e84d0b40440f00d091a0005042c07081c80610303418100c0f240741c22a5001a19610080b25032907081d00c650784003070704549041c1341e1809500b010741e403444241d50003444159a03d030100044c40750304801311003e0010091164200d1541040880d420f030300c030743c03e01540245094101d6800c202c09100030019030019030301c2550070440100140080c0f140c9130b41c86a0700a464444140384040d00700710b028003040c06a240c41500f543c0c041003401c8903208000b0420360001e440d281d05011060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 945524847 1250 945523597 945523613
    0x303071215141206072a02040c030605010909022a031315122c10050a05040b0c2a21030709051c031d0423090a08040509040f 55
    0x82c015a0264201ca01d00c20301c103003050036503100000c0303a0350050308150038600d00007000c1c0344210052440c0006203503c49a51030b440c1c1004085200c5e8010700410400e0f500480c0500904464464180401d0310b0180024040845008031100c0111b2a2140c40c60524051003885114011400c9807002d444240180c3c804024014071a00141848810401232100d0409000f44886c00c000007800b0701c40e0421001c0c040b40c43c2082096840309907400c54505000d05929101854041d08041044071681003009020240320301781d101c0750186000b0050b01081e9524403020f801d03248102600022144524103181d1403100e80185440c20302d030b1904041d1406282d410101031001d0b2007408a50a0b1130b80c4c00014403080c550080c103e8001001c0540f001c0d5544c500000020052030324400c406000d11010080c20111998100700f105000c01e0002c0c8108848040c100e03030025618101268540c1031850130b004540d1003000010081c0e04a6485510149400d00388000c2c4416940064011201c86083c54102d0740010801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 945526097 1250 945524847 945524849
    0x911060c011a010f080c0306180c030108010b04052413060e0f1302090c0c12040308090907030515040f0b061b2b11070f08010f0614030303071215 64
    0x1400002c11104940d215001d00740d000e00480c14140490000a82d258a030842001540440107100c669100c0d541c0001160300c030303424908003000c000f20990420007900d4910020318103a4213000000c02020f40c2080910044490070b480f00030030340d441c4e510444001c489003894420310350400360020051f0030120381c50405070b42c400d40000312802c0d4403500300700d050550841c049078001c00f4001014603407015034011030f805200291103120754040002d01900120000c120020200304280f4110756107540ea410040d64070307040780709105d02c1988180041081d040c424066140a0000712314014410302202c0e0070080201424040d8599454984d40c503a00f0981d950000340041090080d403c0c0d540003042c00c10281801111221015001000c0440b1020301c0800d00384808030741d80504152100f034504242032482d00c529680014440780500e01c0206120206403c81c1c00351000028081c03007500d480b985981107901c803520055030540d1040c000258028490040900005208000060380301c00340c1c4201c0f01c0b06506 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 945527347 1250 945526097 945526117
    0x50a09170d0b060f0a0c0f050d1707090e07030207210e0319051e0a150e070f1a2104050601062d031130010807030305070204091106 58
    0xc08240c81e58898010700a2070b010310b41c102d8a10307141c820f0b808080c031058020301030031008000181c3c1c80c2d5410840207641041c0107541010450782e800c142064000c00503200030140b6204002020003090315203000340115401e074de064220303402c1256940c002c12270007500070383d0701070714000e03001400311064541451004000b250a030369580c004101500034146008000030040c0c0c0020092154480810004102007815810b002c46a030488000700340114940b1110010141c049070561200c503403081443d41c018062007034124103070f0781d07600e03a10720000002c9a010f1140c3c2c0d01850403003040301c0c6000c4984000344a0180d0080300341d840e00c41e40d9003c1800c548400c4a0440d210762050006100c510342141c030041501940328805849030a040c1601c01f920789a144014081c55181d070071100c1c1c0b401944040d1041004120004003800802ea216001ea1400d00d5201d005000d00c03001c004518101d000c5140380c10703250542c03200f0b8a0b01400c0d909200080110000542e40ca500c1640c54820310b0f501c0c00004e00d14086 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 945528597 1250 945527347 945527393
    0x70927080316030b030a02132c0f06070912060e010e160503010605010203121e070c030e04090317330a0b030c07080310050406140a0b040f03031b0219140103150504050a09 75
    0x140400c9d44910b40601e10320002129406407041064081e4004000c0060314060800c41921800303500c0c01602601850104c800103501303280c007001d034085001030700400720355103084650030032540e5209140c222800f0703010715130058100700700022440300c1c0450300c603400c2940e4800100040510340c64000d04240199402000038061203080410300d030340b265161200c090100d8042000e400c003503501602c01ca64000131142140781250000d1703403020509000304041d0310404038915120345818a080e684003602c00109102da40244000b007942d46062054078410301c08011914a040900d4481c001143c2000345004c4006414000102c0c454440b0300440f030003041d90342c1c0000c9070489402d04010701c1700c00c10303000045040300a01042201c800200c000c1c100300ea416041242c0402801c1d46004032144000720040c1d04003440308560341c400700700344500301c0880d0b0166011b4100044250300440907684180000a1101040f000c14400e07403500380d10064005001d44000a6045240d55442e214590740c4510030320002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 945529847 1250 945528597 945528671
    0xd02030a03050d230106030c020a080412021212090d0507082407180b0d0609110307020d02010c02060103060b0607060f06050a090905070927080316030b030a0213 71
    0x514138050621401c9100303084001d40e034981c4000440c6440140b10382420551030340d1000309020300a05c100415160803c040700e540326259100c6800c14240540b00300c3c0200c81d00021518484408940420b0ba5480750881c50f2a004000c0200011641500c8095403503014019000a07100400c1100001c440d8122404a070b4555041d100360410308401855034051003080e04941c19a001c40e60824070130380c3c0c8050032040e1a15481c00003e0300419403a00000074080c40c00420b40c1e20080b540c406188104c5023607007101c0c10f01d81c2e03103d0b04900784c941254180015900a00c014000110341c0e400032203034000041c084604150703680d1203103802d071001120031031086960b40a0a0101d81484800080684000f040601a0041c695a49940d070f1007944940d603955a81c84060b040b000e00390104520001c66000ca006507500d81905140b002c0354070558081c400c100d000310350b45511501900442d1084000140076003401900b903024007200141180440c400b0036500e500ca4a249003007040b0030300c1a60384a00f41e0003402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 945531097 1250 945529847 945529867
    0x60b03070b0a0f0e0907020a060e030d0203040c050f03190206160b0406150609080319090b0a02060f1b090904060e010f050916150e031e06071e1202090d02030a0305 72
    0x84d8943c8072201c3c000c482c80d20400c100e00750005100640c40394030401c00030301102a00c1d080e50030750207821401d01c0014000410301040c0304501810400341c4000316909010103042808040d5660304054480402d00c1c2c150000b08050301d03000c8003404000c04500301c1c40510010b2695000640b02084900300c4885699400480d8442d95600081c0003600d0241081c050190600d201660380c1d008620b05000d20020000051004a01c40c0072040000d1982c4a01240c071401d048601079180c0108581200c1010b4001d0001042c007a02d4840d078440b15003040819900e0000b90388103004604000800c03c0c1c0f078107a122444900500e009229107000b400c0388200c000b4480c1003115215042c0703c2c2d00342da43c03000005030b84028411031200b0000c03070034482001e0a184030754801c0440424148551705c94010800040348503207596040010a4030303445840c203075685031401064000c55400400c5800e0440e40068201400105079030031a5000704a2a00c001700b504a001c41c0c0d03680041d00d4041144811400035070041703500d05503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 945532347 1250 945531097 945531107
    0xc010b0f010212090f030708030a0f0804080f031e090309030c030a03080f1b0d0605123f0f0712020109020d02010503041b0e060120060103060b03070b0a0f 68
    0x56450403128414910030640c0003d680303103039108554901c543c00007003a49265545c68020410840c01405650801d55212030058a03904980039a0020401080e49511042c2c0b280c0e080c14031a5034021000340c20400c0201c0c0d1080030b5040140042d43c204000032804004040245180b4800c0c07144c0c20040d5695000f070000c1c98245442c2d05c1200340a40e100d0f46c0c5410010350010001e80d4840d0000b14400c41c240c0e2000481d003400309809001e43d1603c600080e0700e2a0308460380d04010300341d13a030503205903101c0f01003402050f0341c982c0d00b0701001402d010001c80184140403050501d44c031125040520303080314a986c5c80c144c00f83c3e0703001c00c0729212549800600c01017000900700c85100d20600e140000c10407024140c01150350130340c280e10020304200001001804010100b048007180c00c0c0217440b1082802d07100e48072103800c03050545015021407890800c44146c0c0580039811003000743d40901901c682e920b50f075280c401802c00ca1510642c18000c2c1c90000c1250110b55000d07000142c142ea8950450070011040940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 945533597 1250 945532347 945532361
    0xa140439090b1c081e160809010203071505060123030a050403110610140604030305160602040e0f06040b490b01031a100b07020301060909080c01 64
    0x600380328019080200d005a08044011220a07200118000c2d080030000f44180710180804840c012214182ca0203000900015000c105e201d1441c1e40301c07103030494001d1096030154134510400d605021480c41c00065080010308040041801103d003011241c0d6150800d0400c000c443c2000f0603074900400c40e00c0e41e030212254580e801c10200d1030199420f21583e20a4521009014044540c1c9480104081512070746902440c0c1c88000141c0d4441e0900c2000c03042c0660451185e83c01425900c01c1040c014a820301c1141c041300e6142c2c42c2c551612000c0c1e1111418250896829140036070709204c002498060816030364400c0001c481d0604641c600344040004031413013000081d004613902c4001c00240410302c1405032100b070400399540100c00c2c440820302d03050f403a915880c02e4070721170b42c0404c18108807200400505030303442034080b510424214080030124010444d0241c0b040f540c2c0560400030159000000e0440500240000c50200c0c7c80d941c204041d0f4400140c12641c2e50350000c0c600d80311000a1088607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 945534847 1250 945533597 945533663
    0xc0a08011a060301080706180b040806040606081f1a04020c07060f0e3001020d0207051b011407140d0c03120b0f011d04050a05040c0905010812030a1404 67
    0x19043d9414070701e000b65214001d0040105010300011424600c1591582010080003902c000d20303513450322003010365201c62080e1001c40c0c51900702280411030038070126506d14400382078900115452041087c20001d02000c80b602801e12801a1802d10341c0d841c0c5000420b05144400020311107545080c1004158a0f40d001502082000b920510300e44c0303035940c61551030441e1221040b03c859101400408405200d6150070780f00c550300c00a0590b0310751640350040e10345140104140c800c603513850380d445285a00070700340f401d00040d80c0c0c4620354803002500e009498030718002d034480c0e100282000403551034504c01d41c181c4c0003c11020f400040815a10000c10600f501031124144105100b40c070100328050741c8030000c2d0f4103009842c2010881d05004080803141510010400d2100c1d0605151540c02003900b6241521001c280c4480415170524074002d460407200928010810920015001d219503040601441400e9071584501e038180094005d03c03030f0045000d5501000035091241900382d5032b500c3c5030000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 945536097 1250 945534847 945534859
    0x31a01081623211308090103020c1024080a020d0f0b0124020f0d12090b0420100e1e031f1a03120c150c07060507080412030c020c0a08011a 61
    0x704079001c400d111201c4c901e40c4207114644135000400142d010740030340c807100e1200d4807509122a20b035020300d42100681c5184900d01c480a031080c5045032442011900510390994080160305006003090159070f0303010b5000301814200c11540c0c1d41c0c0c180011070203901640201d010b24000300c01c41ca1002c084001c6c0e02096000812001741c000c0710090316030703103801c15980070b1000704400300d03d030604944c018800c250342c17000c2c102c001072419203030a07003a101403200b0b0907000c400c141400710260b08203604070145c180e9640e10f580c45005c0c000800c0003d42908901780301040c003450b807903400e03864504000c1804160301d46201d8120b590102215001105d0321018200030200d90700d4212903c43c1c0300400c1d010700d400d841040d000da0350b0300c000c50100d18082c0781207103040c0030784460810011118110030242084c14400c1c05d043c00151116035048810450603907001d40002e004265a074041030003640311900151107801030710841c5201c48005a00d100080c3d01001545c2d4403141c0403040d0341103c403400d550218040b260 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 945537347 1250 945536097 945536101
    0x5010806010e040e0c031015060c0312020319020d09032a15020c030c100e120a0e0a030c080a02031005070509060f04091b031a0108162321 61
    0x20200e10201c2d4140c0e02071a610b00041c180c0003000d10080700c41d61809002c6420b82d032002103c1d035000345a9003900540e0b90080420104005104800000c1e405030035641c0c9690344480c41000100039031000c0c141091905103103d9244440312180003916a40c44261400143e829503805c002c0c104020100810113950244002242800d20003085a1540c50300b1801d2955407504140101c2c00a116a1800400d84e00c00031074a9400100f00281002c00e15400080c14050328802d004a20740d103000443e9184070b80b4509015448400c4c1c130501c2c1c410043c03400104050305950f40c076160200500e520380c1166070340f074202c0300011040d030608208040d03000140c40010091843c2c07a45004046000701903c1c9840b6a00001e60711000007080409d81e0302412150404002400d00e00c1c540d0440c1c1701d42807082601107410400c14001c0c0000c2c03080c0000c56040183c403001e00c11f070b0f83c00f03504d02c001c0102240c00b03130244010001509040700f0429148a1000711115926030b82d079450210050880342951660440003c5003c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 945538597 1250 945537347 945537349
    0xe4b0a0b10030b0607050f0a14010c02070902070602070b0a05100803120609040804150e040c1706010e0a0305030f0d0b060307050a26070903060e010b0a0e0402011b0c0f05010806 78
    0x1a480341c41d00500e400030f9030500f00400521140300f001e00180c07061190b0a036060001c1400326100c441da80c440d070080d507100a9480700c954213840040d50b0bc070000d40c01282c41003004490980040102c10300c604401454900b169480c00e04a80003990244200c942c0c0380c0070001527031071071080040a00001030045007810030314850100040d200a080a0084080001080402810005481c0641006c03030407954076181c0300000614114420005e00d01c69824002d9052042d80600c60741010f040e5a0b14130040c8554a00f03005444142580352002d03005440c006000000c1401800034000d19076040c0b035926540d89078032070131005a448007111148110350404c20b102a080d00f000844203218007608103042d082d000c5060200d1075860541e240c5106041e024100b00ca0144e02c2038880741500d00c1054200040c0c08a40001c038201c401c000045600142184130500000c07400107002540203105141110268034081034500030003c0c10101142c020b070000c00e0030302840541460079000b40900b8a000c031002d14000d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945539847 1250 945538597 945538609
    0x10e060414011e0f0602031206040e15040302160602160f320d0503034011101e1416020a0b190e0a0e4b0a0b 48
    0x200c214800f03a0700d04000385004081100e2500000e0400d182a40b0401c0c2d82e48402039101d5022420901d0100c50501c0001c40f02d10781880742d0990582d641c3d00030612003002005c1c00b414140b024106a0030b5200344507a0002903005031131488080d080c5507025100403002480806640012900a6200034040c420144640948030000301152500c1406402031f000210002d101c41040c9110b01d00e4000d019140104180701d4000000c60140c00e00b20124680d074292201012180c524201610000b004041c801c1618101440700c2280c02034000c08035859444503200c000f07603c503c50340c01c0700000704048031805c0d0394020400e04c6580c0d030b012103814403c103010200400c0307801c2440383c08200f1900148800d020019500c0b91468800039240f154860340e0b90700c046011b00d2034a0303001d506100e0009400401d110300300d405d10000b07601c1100e880c444a0000ca0f201e110710548408040301210100c88540c0340388104150041110020b080081c80300701c0300d0603452600b282030780800145110802410f1044114542d103410f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945541097 1250 945539847 945539849
    0x30b030615030f2b21020a080a060b0d0c110d020a0308090d0c030c080c01050114040f0603020f010f020f16031718011107030c03150c1d0d0f0f0605010e06041401 71
    0x10a10820b00344c2c02c100c1c080d10808a26200304400c0c1c0b8420000d811500c0c0158010104004145c070394020300e940301c011040c1a944d180c040c0c17104600703042c081c1c0c0101440031b810100e880010f0781803400000d6141045185090800c3c4561001607114000d80c2c428550005042da4200365040c02411022868282c081c0040c008030400034100300c19440364105000301d500030b441ca02d100c803000900040d6515201c500d041c0a500031020710580c54904030032501d80c030503c100005c0b264087d01a8554002100056501420f140000341c00e50003039610b042a4070609201850a480d81900910741150175424801c1c4061103c40031080c0b080c004006281c544c0502440301c0c3c0700030710300740381082607480f04c2c1850a080005584c801040800030f007001004010b0b80304c2011a03101443c480420801c4e6842004490644410180940041d2542c00010304d034184840000e078003502900d601600e904a590b1303000300300c0141c0c07041034400790745d92001402024008a4201c0d00320784115001c2c400500b281000b0003a071141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945542347 1250 945541097 945541153
    0x31107050c06030c0408010c0903031e080411030102130b0703030b01090608061e060c03040305010b0109052101060e040f0c0b1e0309010b040c020d08010b19030b01030b030615030f 79
    0x103c0060642d1514070100d402800c110f00003802840c0240401400c01010350201300c0114000040d8202501c040440c0100b03524115507898999440d103442c1c0030391203440c12420a42554080013145600d00504000d00010100101c1583d41c0f00141d00300181210f0607813100b5030402a11110401c1029485802650045403c03943d545c0302c21003288002181d00d00048038940c001c4008201c0100e00361011001d002207a001300002d00407108154011140d0480a00a03158890200c1c400c1420320005041640c4038070b0b005400008515032a030881404401046800f01d035504c203040e10b01410000004210f00052105002940c04c080e4813001d1400449204c21070400f106502000080450a0940004c40c00724006001003000401e02c40c40252114022424900401e500c5d4000162002803601141c0140544081d04828000b84500407406001c40c101c0060406031221880084c0356400d000540c01000c9515814007041030030130525040032189148000b076038202c450400d8002003044a081085c000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945543597 1250 945542347 945542359
    0xa0623060405252c0a03081312061a0306150f010c231e1902060702120c12060c04030f1a04081c0b130b0d0209090106030201031107050c 60
    0xe941d000c005000740b00e4581c10700c01001d0b80c3d180c0308065604094100f06804000d004041e1240b0300c8072414079040560241c05400543c0034a0400100f5076100140c09080b40045d4400300305a038540c0d03103c000100300c000565800750340310b00c02c1c2156203040c4101014100b00350050807482c40c0c9014036070094114403000328080d40d001151402c05a1040c5401400958040f0f0300d010205211084000b880c42d010060100c02c0c4a13140350140c4450041c0941c8440b500c91030018841446a00d190b810808481074040f81c203c071052044c00c005a890801e03800354282c1c0c00c00100250907000c0f00f00001103214002a201982207a001c0c0840815400c0440f42034039007181070340010051034035256074400504800114000901001c3c401085140300c01494498a100d201143c49903484002e0030440b96141001544001c0050544451407070755001801400c2009010b20680e00340e035000310300454004c40c1c03131080d1030355906400d108560f054441d859400066105850400c102030ba1026601c409003514248154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945544847 1250 945543597 945543601
    0xb090610051b0601030b0717091f0e0d0309150b13270c050f0a05030d0305060f130f11040f0b0705160305010b0907020105100605090315090a0623060405 67
    0x1180410120758900c2c0c0d8100702d03001503039281000d0b80306150603640c00c8002032820701c00700500c0c510035990302c1c0601d02c0a00a0104440704180c0b00e1304601e061850561002e8446203004003d0360103003e821008584d07900e010504001c5407a00460b016002440030181c249802c40c0d00005403500d49001c0d56260030303a0381c0003905901c06060030b5040c6c0c03695100008035503640003400c1c040000302035181003250025541801064102c408110003400e55011b49a0198007601c0e40d261700e0f5102e40c1045400030700c00341560607030b0907108004c200f036400c55030400041c080e150582000140550b128140c982e40107000490f04181c101013540180b5105445a0742148501085030414800140328085c075030320404258280c407564a19210b4040d00070080e00c640701c2c0100c880062075450040c05082d12420300310388214561810140196980d40100c201c464052042650741c80d0115100d40b48903004045c140018500c1d0007441c60301034282c5001c0e088821440c05001e4180345040214048550002c80454007c01e0035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945546097 1250 945544847 945544867
    0xd090b070c0b03180708011109011209050f0d09050a060c02010f02010213031a0912043b0907061704020d080d0c080601120e191a0115030b09061005 65
    0x1001a40c2c0156800040000034040080142d04030424500c07018000c0e02d11243d551381c451808c9400c56903100c5c41104c41000301d202d0301d611841003801990984440040d02d2245906e810b40f03008460495031180e40d000644001086812060900c010501140c101941908100c00282501c84038000241408485540e07520402d000b034041e111750a903094000a007030740d52070a28074003a80d4020380306c0e00c8100c140c4001c9081110007140201300c0c0c040000714280341615000d5207044885104640b080700e444a034021554503140d08060340414070030034030050320a040c208a200e0820f1115800070f4140b216079079100c940d54400c1c1c00302540c00b68048440b244502c003e41003410381407040f41c44001520f0300d040c070f00c049e0442d0080c041b14010a0203a03141700301c5030222740104c0c0c102c1d00000d00120059200392b40381822034410314054109a8400d04440d0204403401200c00c1c40c155003a0460900c584040760005e081a0740341c0b08032a140d0300200d40b00e036260b0a0460201c2c1801442d110141308005e0001510240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945547347 1250 945546097 945546113
    0x240c04030807210e0411130311060706110901030c020f061504020409020a0216090608060408070206070b0a050f0c03010b1803070510120e060f070c0201020a061b0f020d090b07 77
    0x1007014000e020311118400780f0090004a000b90b0940c45245000c3c0813840000c1d1260945003d20120b41d0700a206a0941d00d40c1260703400e06061030782d40010b08000031710001c1c075180100400d2070b40c00d0300000e8503190318130005001d03a080341e207070f040031584900d200e4101d140c0005402908043e28200c0310102c6641703200400e01a10894011802071400002e005460560014012000030307014416003000c20b0712074000006894041c0306036141a4040004070700881c1e1030707800400707a043c402000e207860141c0c0d90f40c1e080d81442c070440321001040d40d940c00708038034050303003482841c0d20091070390401e0b2441d810440e0b40c500c103001e0150384c140c80718003650181055072000c01026014180040600803c82c0c620040106100c1c0733441ca081079070b1402c2c0805050b8140e800a0507501802e40c100304006a07649810301180c0c1e40c91081c2c1c01707a046225401750708011404070700c6600c0111040c074a031303600d80300317031710f0001508840611081004660160f02c404104542c031000000c26101880c201c1a0f94483e9400d02d080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945548597 1250 945547347 945547373
    0x80102070f03053f0c090a1404060f03050d080603120a0305090a0507140f030a0812250f1706010801050d1a18071509050114130602240c04030807 64
    0x20b1070100c041313400c1c1c9541a0394020500000300203619404207a42d5091003824600030078a503184c201800c1d4a080c0803103041c004201d005680301400c000340e0308d5030341c5d0204690300d1102c1e030041d555034000c103404491080d800801c1e103030302400940007009402100c200000142c0b107219100b608265440340494002042171044140f195003040486803034903282d2a40805407001042914819150386805042a0801041c0d80d181960010449810404407000e141441107005142000040d1248500e0440c0051031524070555071050381c83c40c8034003034209000b83c42502c41000007407d0702d55080030041d1527a84810080d040d1101541c14a2003110301d45015940e00e10070b00c08405000744a0403c001c00c048070b0200e1006034440c2402202c8001e6510001e01004602d440d0500c000102ca10300241700c1e550248400702e04219480c2d0b005032606d400300c243c0789800d00c01030f0080d00044c0c104541d1a142c06051226441d00314110070706600c100d0130400e01c1c4030610310441c80000c07e862000b0500344c1c00d119074801005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945549847 1250 945548597 945548647
    0x3030918020f07140f06090f01180b010b0a180b0301060e01030207170c030c07031a0f010e0f100302040f0501050f040c1b11030d0c050721020d06180b10080102070f0305 74
    0x140d01b504040c400745413500da0100c51a172603986088004038050750307000307210154a9000340e00c1108a908100b561401c55204040c1c41090003181c208400034060f81c15140b100820803407030a90388a506040000788500c901c1c200960406006021050116890031142112002c0c1c000511b03556104000c07505040d4055441580341d540950b00000080c0103001c0c1044000c2d1080802c1001540d0740c1401c002c060603802c1c080e209901101c3c4001800c450700d40c460054022a00c001e030708800701c0d501c2d40005c0c10703100c1c1c42015450540e01c0b0001041142019600e140c0c2082040f04c041c000d041181e0780003400e100c00b081c2c4514000212500341024003a00104844d44414040c042e42d0845074004400b400f5410b2a01d01210301d4400d13041e0010301d003d00751819600e039030004001106101c480d60200420706c440c5010944031903660b154610302e4088582ca944440e1741c400c40c0302050500d4410f6031074801881c950b200c40300c1039004206007000a00500c000c09201c0307a00d824015180c49280c0c3d5140c5103210022444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945551097 1250 945549847 945549853
    0x3030807080f04212003040326030a090206040906060e0306070f17060402040f03050f1006031709010212191206060e091803040e161d041a03030403030918020f07140f 73
    0x208000305d00c040010001d81e0301507060319040c18404080400c040300c140081c0f2129030824800b0421a440039006800c20303500051031241410384440c4d48400725181a80440081442d50500000d5030600307001c03a90780304e402c1e400e02803888400060060441d20b4010140300b5820042c0001840c103690329030640b0b0250145028011900380c803450aa9541d0901c207401700c500b4450806101c451a01e0340c0100d10543c1d134001102d0090304400040c10320540c0000b0f1074a070560003414072062140070f5000140034a451108640d00f00c900d40d404000d00100f02c0e0404400089003009401c0c8409500903800c080d42c5142980e0030f400703d50301c4020341403040201124043c041d010009000402c1d040205902d8014410064201c40707645510009498281400030352611201c400e2001040a02c3c040d40321440546855610f01d8801d10b003480000d04503403142c0c01c101e01184042c03100303002b00030581d03681123141d951605085150800188140c0a94000e030440108007480d820f1030000340303080901490031401c0c092000c13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945552347 1250 945551097 945551147
    0x90b062503081f05100201021b1f0516051b0601140a09020a080103081b06010b120702030a090302041d0d030603020916140304031803030807080f0421 66
    0x440303105840e15942038000a0624012a4a40380b4101c0d001c00000b005440340440d940ca0407051109004103c0b54032030940d5400e1007104081d10a284aa90089803104083d140301d1286850f64245200592030b4890500d1a0508000480440e00002c0c45140600e0801d5038584800ca2240307104030780390144151160194400000b24102118190001c051084409115542d22240031a003240a40c45107c030018040500400c0441d414900034003d0b440440c0e1411008604580c005140074000c0e441409900710005400d2100302100d00019040034140c80594a81094840010510480c0d4007000c0e04c12640c444807028004034012103900c241c1041d4040d90322100c0c1203000500100a944001c0c1d00400d0b005000030142c0350fa90403158503c04054503a51601c0c0d900d03114580254200a1040701400600348040342500f6030004041c0007148aa030b2102000c0c6041c83c4001c18ec0c0c60003400030300010302070b4006d00000481c401a4032601034001554529000082441110042d5032204940e04004007414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945553597 1250 945552347 945552397
    0x150b032a0102011a0603060f0f030109030e0f0303031b0306060d05130311010b0616170304080c0c150a032d0605011e14130b0f03011e05060301090b06 66
    0x40030000241c0081001c403404900d8210b0b103940786460340d43c0c040d00800020329280b8260f0400c06000303c010b482c0c8401941c0d00c0d03001ca82160b1070284241e001c52841d41c001c81440c03030700c072103d903e1a4206a0103181103007400c203903000301e6145500f45410001c03000301c00a46035848090a40b044c1c041e40400c24081810250a4032071107030300c500d4060f400624580030074001c00d42c05018010b07013403102034440c5103880c004005821681401d042c046800711840c01c808030504e00d44401071801980500e802e01c3d03031040c10012251800c9002124240100801d540740a1110070000c2076030141849824046070111038510645407804180c4d064100290b10341c01c041c091152242d00c4501641d03402c0c2c0310a640742c09011a00c404079140c2c0701c010300004582e0890040761040c04005409003003110f03101c0201e211344403403840e41d150308003070b0810f0180100070004028614082072201c030030800306040d040c520b03401c0c080812418401401144c00e03035038a0310244010341d200c0c03c08135a4404901c050800088034039070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945554847 1250 945553597 945553663
    0x180313090501030311120306060f0403020402180916090603230907050112050c071407181a0d030c12020a1e050c09070203120a06030605040c080613150b03 68
    0x80004d40c0041c1d031800b000b5503440c1d8006072080b035215812402e035041d03641e44000c21900b64401d48900e10010011f000000041c0c8403400600b40c150215240022074064041c00e1210414000b040845005520510364080b079030814140c400347e444600d030101f007149030300ca10302c111140d15100402c4000340040410181c4070b0003040c1c40065510076aa03210301c54148254607015140140d032040320009007040071000089005c40c000150803a40b0007503845c03240d5136010098a000420520030412500c0d628041106c240c4805002041001103d00031241000c50314000c1481c0d034004c200410303203181c45040703483c0d12f4020072441d00e600d40c1c850b020b204c9540119a0004a2001406084484d803180c8003800f1481d151400d10707a4410107083d03000790305020242c0400210118060007600c01541e4400c0f000c00802c00600a40c2e104030b001e071880c030801030302d4440b20310b2400700f0040c8841c1800b04600900704c0015040e07001c442142520700d201264944540002074201450071a90030751480d012860b10350301c40900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945556097 1250 945554847 945554849
    0x10f0507051f1a0a120f0b0a020a020d08130209090106050a080c0f010801050607150b100f0e1c06020309070e070903050d0203091005030a0605060a0905190509180313090501 76
    0x3403401840001c801c031004a15000f040e8041d5640011501c0040c4581c40c0800042c1c42180e024a120707007001c040c152207001d914681a52080341c4141c000a08580d0140c0401038030318894982d2600d602207140c200008401c0a260307281c0244508800700104201c84025000f84000d0140100b05030380650751809078990b0381c031071150914000c00d6130405489480d8050400c050490b403010b0b240c186441d0095540d000c2c5500c506150901960790303100358039030540303c0840002810000f503c9050040d80325080c082d10360110241e00301e1080d1080c2080c2000801d10456445055510801c00b60b01d0340c548041050624005030400c3d10b4514056042025255000700840b08036400740c01940d04004903144200c2c1c40c1d05c60402074a4100c04201a500d50b0184128020365100b011000f0010364580c40c1d0002035000d42c05102e526000602c01c0d01d00348810301d09a4000c80c101d408007095954450b00c0c010108802810007031070344c0e00c8000c140d6070400112401b80300f229441101900f40ca00c095441d491100e00910003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945557347 1250 945556097 945556153
    0xb0606031023090a06050d0f060e07060f110129030a060f091401020301063c0302030106020d0305040c09150b070503030421020604110a1701050114150306010f050705 73
    0xf207034021130145000751044070300340c0b00c01502500341801c0503111202c00018030700d41290001e6072402e407403410b42d5050000c1400b52140d076880c9100554500b9004007001001c4c0500f2055900d040700d1003442d01c0c9042c4d1141560900240e54240605103840000d081600180740503080d40d080102c00b081d000c08552014440300c0c8207070300d12031404000c0000c0a00701e0200b40900404169240a5140380000c03405549044403885a18065044094510640091242c4000c40e000c00c2d0048010b020650701400841440c40c043e160410141c5400c0e02d80010701c47e45440764014a9584016107440b6801080428024084110040303640708403d10b00588d5a41c03048600b91809803400e000009021600c0a000048104e6903000740060345490301c4103030ba410b100706041c9034405101180090802c1100e03181503181984071000060765803500302c020700c01081002c034552003900c484046e0401d105080382900d4000c5420300e040928001c1c51a0240d8180c45082e102429500c5107050070b02c0707810000100f003c41e20301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945558597 1250 945557347 945557359
    0x2a0f0114041202030c0703061109040f09030e0d1a04061b0203040f060507081911011a040b030c01081918050f0c01052b11071b060c0b0606031023 64
    0x707031540b4100e0702e030b000e0744024150340e8210400801c0802c800f40c201100008240450915069811000408403503444400d1b425082e01c03403060341d00b41500030300004e141c12016030b1044a045642d42c5c4071090502c199816035030005101e0041010b102513984178500c44240614003900ba4810000081d41c0e90304280315449803080012004101079101d9025503032515401a0007604010781c98104541c1c40746084071070410800400481035045001340582d044103004240104c610038a03200502c41545c09081c40d46d4083e81c003159034181780d40da002d400035501c00c1c2806000003820030b074a000c2030040c0c500d01e85503448488001000301c0600c0004110100c030201d5440032038001c000b20704010b681d42e0003540c2010404d09044110000d49442126011904040600d0001820b6100100c004a603030880c44043d2114622401d0000048082605490107003c0c9401c240c03800010945d10034202580060115000d28008070201e12802c07658901c0754060700003c8284500603201c8110114955100010148a10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945559847 1250 945558597 945558623
    0xf0204030c032604140105091504170c0906010e1e090703020d141501050a0207030c0b091002010b0913021206150f0d0803070e1302030c031b2a0f011404 67
    0x88590070031181112902d40703170b424440101c2c40041d142900134003050364004142c1e0b00c1c0c4540c00c515000040c4054880c0301100c412070301e00b41c5891031820401c140b03031034003074001023003405203aa0b0014110180000c1c1103e001c000c04031403a429110101e50303002000d400c5890304061042081d01500a00b1030b0800d50841040b92542400503000030f007206407107111651051000000c0c1952240c0010203e04a80380115061503607a90703100100b442559220b600036441c0495a1030700d51916980700c00812940d84000d1100514041c0000c440c20009441c1a0003c1c203c1e000420464070f0304540041070458003c2601e00350316108100203c410076000881c1d200d01d01c0003010070344030b140007000060200d0300015010708603510248107030768140c0355034103499000780ba069000040481d030340020752241840c07071001134803820805200342c2c1c0c0f41180402868200000c1c086c002402c804a001440c00900f01c040030070000d200000e07100c3c10003120410f072056550810031014201040d071440c0c10700403441140c40031500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945561097 1250 945559847 945559913
    0xc060e0108060f010903320c090c070b0c18120f07080a1a060f06040602010b01030c050c061303030209031b03070504020a0818100507020c0906220f0204030c03 70
    0x482c044200140c003245d500e542c144042400210301c40800c03103115100c1c00c00f4014002ca9400d48400c400720840351503100c045c215401c0d06203500d90341d070000740b40682c50f030a01000d552203280c15030009103900c203240d20220b107a22607503c0d41134000c218864060700054094800c07060355601e500c084044032078517110b4654000742d910000103c038100c050304090b100510040703a41000008000c06040503500070a02d40d1502d04e43c4e03079140c00800c000e0056030000201070314002c0000d425a60484200824400300740000e220490010a035260302c41031080c5440030844031450281c00078040d180045406106403c05c082510f00c400d0415003501000324202c556066641c801c00045e4403e45412a00041c007a1000c2045840c2d40f0701c2d080509003405050301c0c140022070b17640c581101c000b2940c1c031006902c070300e07403200d424100301100c160008016244040a0596100d140c4d0103402a461610140e9a90f06550902c80021390b05441c040c60344407844000c4107070740e803c0070012160550400080030703c00400c2c1303900c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945562347 1250 945561097 945561109
    0x110606100225050312190c030e040c0c1506061223151806010f09031106090604030611120c04030c0e060d060f060f141305130c060e010806 61
    0x80c220059004180c030b280e1034505080075501140c00300000d03006241002c01c540e80c0030310203101411001c480741a190401080950b140000c004100d00c00d0281c2c080204002c00d41c003503c1c0200e805010345022951024000080700d101c01c030484090030b00c1c0860240c21042000301d030090004c80e01c05030f50390725248100000c2001107032815072507010aa480080d0900c000104040c0003a8405100007040180b0b42e80000800c21406640c8115000600208100301540d82c010100601002c0280343c40390450382540d4542c90120401d210181c41150045810040c0b0350354041158060b6a01072400d006600306121040c901c2e8009034110700d421101500000d200074404810358045039080302c0c070b403003101d854070600d95403104020782034035000b8403001000c0c400300d01c641c0656012180342c6c01c0c5c0090940d00e002981c0c10203800b190010008007105c280740d0750807940c0d4003180b940d42c1a04228001619181c42910000f0f10a504e0300007130915100490018070039404c020803141501007a215110590344400030018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945563597 1250 945562347 945562369
    0x20706020d2a020111030706050f090a32030d0510210209040830060334120c0f1706070c11030f07180c020a08090409080a110606 57
    0x38006205240402030400d0140344042d0380e00604000340e01510b69040141180d0104800b60782454482c0103100001c19828000fa5009464401410410865075950100001119a80101681009810b004802808006203c1d505e11030341240d03a2000800740380c4000d400200e0740907074181040140020b406c00c241003815a00c00000321454160311007942001207814001c1c2c0103882c0c00000740f109681030041901b040620a012400c0035500d8030401c001c1d07461a080040c101806a0420a04614040001c4070301c0c03c5100455890400040d03c140e030085180801980002070100b0610700c08024840300720200801d43c0d56800c5030074010307a00c400300301c0c15510500112000320782c808000200060300c54102400007a01c03c1100350311a00502d40000d1800443d0000e9414940041904000c090b0010000c3d111029209030188040000c00802035159240d1890140c00030f80c00080d5064641d0321130707101c0404203500038246601c1e0180d03944020940030914000400c0c6c1e216520200d80d0700d10309000c00e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945564847 1250 945563597 945563627
    0x60e070f0e48040b070f2102070306050402131d0105010914070c020a03020a080102040509091506130e010f1a0f1e0d0605090307050d0905010503070c080c0a03020706020d 75
    0x140418030140c45242d0720301d80e500030010002002d20003c81c0b2210b2000003400304a020300d191140828071800e0007a4031401786070120f201314042c10240000c140c1c000c100141100e4000da000209a900c5001241c0301031424418099070a1800c181c81014003003001400c004565801d00130010b90b070300c44131034004882400b100320148685410001d11a18450a00120120310181000049a85c1da50220303039000c11a07000300c0000d94000c9420300140c201564080ea028521000416164113002e410000b40c5401400c210701400d034001490001007440d40114940c149100300811180c3c1c880100200206a101407074000000e0300aa00c5070b803868282c20656000c0c000070005c41c001000e0100c0714001504466000307401100c1e405240002c03e00503c1418811021200910364601444c513006080141c0c06451400f4030141410500141e6404000e03a035021049080021098981d81041401130040104510701e51150803002400c07d54049a00400c0707a060303802311390090440020590b0103040c1d1095407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945566097 1250 945564847 945564931
    0x30912050c0307170c01060608330103022b091e0c09051306020f040306060503030a05190c060c020c0a0609080a0611041214061006020307060e070f0e 66
    0x2c081440e21032141200903502c4d01e00b034034200181c007205003500c180d50311480103e0984420401c50300f50400010151003d00350a000820a1039035000c2c480c0c442d01a4040e0404d035001c030381d000080408140d404c2e049081800c607030003004e5200000742c000d4100f04d941220003c410189408041b0740009081c001d4a034413a000d451142d0802c44c0503030042000900003400b1000c158504008503040e40f00610f030034444d800c034856507a82141010f80660f0f480d503103c140a9441000380345001507201c1e040d16000602c200244200f01c0c00b2940c110f0781491800005000c05150550301d0100381c0e00003800640d15502592100c51aa9555205a400200d1407207080b4094003c08880c030700040e200e910529940c40c0071449203040644a40f0a10301d14860b503034046844140d00708800c07407200c5d402c0119960080480c40c42c04845030401c0c600940b20300441d41b00034040303030b00c40c1d070b07807c3c860701b410302a10703019284400441403666500c401c2c005d4051406d0318003507440c0482d181d02402c109401346c20074084e00828042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945567347 1250 945566097 945566107
    0x30606170703050705041502030d050c0708070609080d1407080f072a230f01050114011d03010e0102130f080a03050f04080d03090311060f2d0403030912050c03 70
    0x29005460f00524000070081e04000105040644044203507032400c0300e030b00568a65640c40b9481088400182040100e030500b405042c001945641c12251103030b038409000b140c2102e4918080c0f0040c00355102c54800b107400c0101c00140b444001c00d00e80d2044549681d90a816260280216060700c402e0700da050002d04800c1050f5002e84135041584504c0c0185036950744105102d03140c1c42e030030302255101510004040c10106801d0300017004443c000700c13120b90082145524101801e0f400303240c200319590500c1079088003003000841186041e800418003800902c2810507400202d4000c2d40480001d0b00400c5007010081a10900044401d040d038080390024024008c070b94a05a4080d00400c1c084004124100408503078010b0621640702c0b29155074074040b42c0c1c0b403458580903104410401c2c044081da4800800c01100c41981e084540d002054502c414100c2c4480c924008401003103050f44100d15010304083c0400c042c0d040c1d1220a1003070040b04905828500d516048405200b5201c540d8003030390080c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945568597 1250 945567347 945567361
    0x71109040209150d021801060207090e0c151605030a11010b100c080c0a030e0406140108160306030602130f0e0f07080a06050904030c05010507051318021204110103060617 75
    0x102100783c42c20010030f01142c0e01001e0703001a42900d940382415050711101001046510780401024001d8160b014081c4070141000480e6a614090540e003288506524031500100880b03000c02c031405118402030300410101c032401d206940c0d46c45882c6480000b1a11107504e40640d4041c0b017200c0e03900000600701a0188544101200d01d030300d030002c042d00c206808000502810760200440005940301e40c442e0b65041c1c414104100844421780e00c25404800540c130003007504c3e80c0c000b034441e0344843c0c107030181c07030900b41d524600300c005001c0761308002c100360b2002489100100c40000450201c40000c7d8003112010346070030600c0082c14003502d0066260159101240685006240b6158030020111002404551f80d10001d000c005068505401140d00007030141e003403000a000d40c640c400c000d810050718010b42c0c1c600130240c60b200381c8204072010000c1e05003615100c5194045a181d1984c110740d201081c24135003024003001c04524501404a031801000007081800b03402208845030900702c2590061391421 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945569847 1250 945568597 945568621
    0xe01050f0307090b030901050105011d09040f050709180213060617090118110901060207140409050c0d030504140d021302090d05011a0906120a17090a0308071109040209 74
    0x6003031001803103d544404110031020b20055032040710351a001003541d5140c0310015044980c031100c0980020225001c00c01c1c00d854251405800940c40307040b2908116060030315074144101c0d5003140e0002030400741c0f070065020790b0f13034202031086000b21005118081100315000454000f4841c52003c2540c0301c5601103084521103c466211105000100b1400c00c685106a081c0c000b0100c110744101000400d00303014203000c00614098821800107088032130400000340402605032500742e10a5488151480400200340b0065000340d0b00078040b011418118500035005030058003654543c013100c2851082da51600300701e0316114030340280c0710300d8040c40030000c05000381d400301e4510f0f90401d00382c00c2210005202441410255914410108060030f105801c000c8903d8000c0c4c1494461240795140388450b40c0041010007660b07a000b011030020302c440c03648030b2032540202d000995110882d000c0c00030510003007400a160f5284151841d02d800b0900c0780401100b040280c1c0c000c0d401c141c05100284c5d00b081c4a03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945571097 1250 945569847 945569851
    0x1030507150c1b1d1b0d0f090f050d0f050910050c0a240e1c1403070801060e03011b0f030f020c1509060915180604061b0e01050f03 58
    0xb450b080c0380407020381d100e448408070181000003181441400030414600750300c0d18030341420000b41e2142d5140c1401da4603121800100c02d40b191080d400000d084281d00c0c140e500c490114084da540501401c022418a9030400c0d04a2405980d1802024440840f0130b202d02455405500540c030b0307190516904030284845487d4a20448040c000d04014507290524200140e249581c880d01124140c22541442d02c0144103502103065082800d2412a9508083c089410307041c81c03451800d130761107960501c2821500c0c045020020182480c0001c10b0203020b60b488030310b40313059070440d4442c01130006004062500702d40302d42d440707078051001111504051901c100d1200e402c085080c5004945003016124820482e4000307004118a40e0117040401c1062a008880c01da018801c00054070041c5840160030b610ba444104800d08943c6052000410101b2016000c02d2488450000c59403e4a01403408500801c084483c15000840546000046030320400c000010280c06a40c0d550508141441040c415000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945572347 1250 945571097 945571139
    0x102370309092c0309010917070314060402271b0c0f2406090a0b04020d09060e010b1009091d1204091401030b06060a0309152301030507 60
    0x28800c4000b0300905640200c1c0c3d0000c504000d009429482402c89a241d11100b0784203d0b810f80090003005c405030703082441c0341300722501c505100009940002c03696082c4265904014206441920b010440329030001c2c589200307134400d89148040021aa10001100410225450300740517650001105040d0075090551150031241d0b049081070500030715281060041d8a04400703a0340318a060303078406007581480d94240e10781c030302c4c6920040c18000041800c10388000c00812081e071b15550804415101d030344c11100309400a0104004401441c03a100001c1c00a401e0b10080b00d60800c07101580d10314103d41000448040c9032a10140245000c0380d101c05420b07a82d55680c00010450b452504c950002d00c01c248010b40080141980c1e1424000c0351403c884415010b1900080340c1401440012903001c00d560b08403a0884540d503c0310b01d207003012401781c0000c000007446901e008821105441e12500042e01585141c3c40c82850800f00810203504200300b440041c25990014000700003501c4c5d00e128001042c3d107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945573597 1250 945572347 945572357
    0x7050a03061415160623180624031605130c0806010f09031203020c06011e0b03060310090803010f1403060a091502030c030609091605090604020403020a0305030901023703 75
    0x80d0640320038086540c41c428446c140b60030050030100c40304c05a0341c115801101281f224500c0e48044042540c0d400d001020011104c000c02e21400e00c01e540c0d034100c200d4400b4010304036660110150201c100b0b5490f18411280035144810002c1803002c00c2d40100c420702e603980d81e601085551034070011129415950040070500c16042d41c08008140d101a0f0f000e0401125280560344000705400c0300c0c80c0000503409043c50b001075030f0a5840c82d16258852104035800000003946907180e40c40002c0c10500c0d48803080590034580f40c2e001007003245400c095070490307442a820f154007039039070a504803010701000d512681c10382002c40080c4030110702d6442007800d14050032924045541c82d0b9404c00c100d81c42910501c42041000c410401949010b1001907400801300025081a129980114885090b01c0c083e151040150301d000484603211541600d00444d0002c01080c901580c0342013060301d80c0d00a2000703500601031113005141d42c41459442070801d500c0012440045c060718840c01d950b0401c1e06e102142040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945574847 1250 945573597 945573637
    0x306150d0804030b060108100f05090a0e0a030c020a05010c0804050603070203041511011812030b03160b070605060f090103030c080909091b0a081b0301110307050a03061415 76
    0x320700390007030030140d4410202e40d003280c20850000342c00340c60000e040030f400440740340741400700c000035000f4502100e01c02e44240710710352a6040071002803e9035000c042414864a035083e800c0c10351201d44002600d0080ea101c41c00035840310b00442e0005514072001c1d2182d00304107c100a541814401150b0040e12032060341d0400d5100c0d00c51005402d43c032441c00300014000d1b007100481000a100b21100c000c54590740e50f0071702006607550040300d40d070900c1c4e250505603910f55041e0141c5051242c0a4100c240f800c00d408520345404174981ca40e004410259840d46c030b80000150319007082c4030311720786042c0d00800c03594a07686166811521004d1100c8108c810207000d11140382252200ca0820f4001c0503024064001c920030000d042c400c4d4425120010310406081c0020801c200d808214038800c1701c141d220800803c120100440c0c05809142605162194000b0402802a0f40503000d0000801d4568090026603540e000c81304580218000142d401400101444486a240f0008061000c007140d04140c4d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945576097 1250 945574847 945574853
    0xa0b0a0525020424060504030b0406090201090503070801140c090a05190902040b0a030b0d030509040b03120a020d0809010606020601090c0c051f0f090512030c040807060201021b0c0306150d 83
    0x1030f414515859a24136a142e40001080302151100f4019001c507150082c10b2900e140c075038401489010300041c11407aa0b510005055911910b64a0301038035014086a914035960041e0500070541030300b200141d201d0710004910304100401c21104170b0f07100105108034540c180010803060700510b0701c800820f907068820008a0070058009000140941c945550b12103c0c0d5100180903a030340d8034041d5205503400007024001a400005965100001340c0300080c40d4180c10011078078046242010f09180b000110b0782c0e0031240d0b0f0000b18103800303140c507541e0700ca1142c960241142c240d0300c03a1300804003d6044140140404403183c0e01044030392019140038590341c0d01075260f00e03040a424130740e00c44035104004401c0d1510012405171100180b0140c3e020068003030340383c0b0f410b80c03100a03403000c0e100305507000808a0500000141a5005021940240c1d49000c1c1e50b070700064000d520001c103141e0900318181807108240d4000c2001008244080c000e08000d03500c59250000039007001080f40e50000c600300d100408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945577347 1250 945576097 945576101
    0xf03090b04061d2e1e0b0a030803040602040503010e060702060103300e01020c120307060b012c0f120c15190306051c0f1202030909090c0a0b0a05250204 67
    0x2c03852140c44e408030352208104032400703026503450114411428071081044041904141c46101541d49000289401c01c00b40020780c90001503101400690010041c0024401d03180d005104854007240200041ca18031400f15855a50858003440540c000d48010804111404450392207a251000580354025605102c1313104c20107110140300000344510282e640751358040058810402e001c4500000240c84014425078900c20124014035035070300d44200107000d9010300302140030040c2c0700c003042002406040c0204400c52010028510980c12441c0180d61814001350001324604030601400007245410103002980c6d810300b0826a010a041020b464000600f5940d00e45028440d43c0c00f00c0c28514002c10802041c0760381006445441d041c034520400104202c420720521988070400240050075000c1c180d056006036828250010101001c000c1500d4010a46000030381c0c0481e200e10440f9140c6041340003d014072070441c408510100641429800f00c00380b03034a24608055540d01c0264500c1e404503007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945578597 1250 945577347 945577363
    0xa080c0102121008070b0d06030f0f060506060a080f1b040603150b0c19150507080106031b0e1201110f0702011d0105031305030c0105090d0f03090b04061d 68
    0x940e96012034000c2020321844a0903402181c1c60b20058502400c2001261321603100d032080c001007510004440505400a400402c000e54102d50650541051401c21a01c2c80c0c2c0404d0302110311742e00d05070001e0704619201054905004283e81c0344032003030b0b8800900d0f0f181002c2c080c1540000c030402c01c01080e0a220f000005002816607070381c9c081200600da0901180d04400c0350840c0a0100c03003400032200c000c60001d616006405c8800070b501c1c410181d424030510074491100e498001c00d0802c02000030264104204504854243d5020080e0b00e004c10b50503041c550101c03d84000003810f071008060300e85844c0000ba0800480c2000004414611008000300340e03000c0036202440c0304001c25108290340c1c0002640040391035001c900f1030000c41800c0020000e100081c48402c509000600b80814040200151240031a1200081189013403442c54503070b4802c0000442c00c0040c440c490428040c5102c0c1c0101c3c111070350300012f8042d248c2c4955032480b0191000120100c0340001030421100c0c0e404081081207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945579847 1250 945578597 945578617
    0xc0306090f07050619080c0c0a06020910032f0d0f1a031b090a02071b1701060e01030809040e070f0f0f06051b01021309020910080403020303070509030a08 68
    0x503200540d944002e06080c003940c40544149030501400b42c0c21203001070500b05e18003003890040c20701da888a4207412207019900c9269001c1c030808605004000c915130003000358040860707401282c0520340d1811021ba40070381114950344550515070000340284052000512914040f145007419441300716001101c1a2010f0303400241d071110341355280b0a44010a40000d00001d5016082c4040d441e40d05059561144040c00e0007848008006041d8140c030b6810303a07144a5100d9081c684451082181619000c05806481c40040c0243c140201c4007405104640849418880c00e04540e0b00c0c0d61141d0003030f034004a4100740c005403030303140c004010300c414418200034010007504c0701c0c0c103141003c044444102e41a08609186444001c00744138050b040b500b80c40c0040c0c40807014074000d0640004060181c040d018103c4100240007030003280e0301e080c940113892440c000f5101d400958800c80030850300f0f07200c241c5015001d07800400200749a1403240000b403010107000340031215840c0b12a6103203032840d40000003034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945581097 1250 945579847 945579853
    0x2030c01030e071a030a1404022d060d0c080a0b130f0b060406090603051e1f0e070c14121b010e0307080903010f09120f030f0e0309012a06020306030c030609 69
    0x6c440002446038128150000307009000914165000c220241003140a0b0400c1000500032030700d030008030040e00c0401c1600074040395194565094240094030301203101c0c201040e80a80040c04183c0300380f284810010000f000743d100e1145038214800100001b0b81a500703619100c803201151502c41d20001c01c0200b0301e40d41c51140e00c42c5003140003400c031000900242034090005103912083c00da40c81070346812401d0141124a41d0030341f43e0b010407084c41c46a01100d2500940300400640540141d09150858040c44403804003051a81c10a0b031540b5207400c0c00d581c1036000b0300107844050403110850002101840c00080c052407514245403454010020460f00150002450000303801c0038090700c0b4202c800142d0030f106000c0641c1d40d180c07904940040b00713000c015092013800401c9100343c0141121508507a41000800564040c244d2a0317805039481c0c03030200c0c4100000c0e41d003040403021008144016034004514030313856079441401035400940440d61501c01c809018903030740d40c00d0110300d01500e002001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945582347 1250 945581097 945581101
    0x409030e030d030207050a080318070e1605130b030402010c080301090c09090b1302031e0c0c070e011a070303020c190c150210020a0201060f1d060a0302030c01030e071a03 75
    0x101440c00b441c0524850806006204c02e0001410000700d0408565001d107880e83c0ba581c6001118202d01c0124000d100284110400040c0c1c0c5c0040690850240c40c0b20341503028030010307022041c0d0715403045203140448002c103a0b8003080042c0400d0701a5030000d105140c149520380e225262940706800070703006101115a103110030322403160454640c0b0002c0420301003d220b0070494030f0006401081c0e0703034100c0d2100741d000400202d60b4020190480045500d40300301c180305013884602900d003a00514110303000c41c401c0000114012440c00c0d2110304940d181080440d180d10a0ba03081512030b04800c4080341450303024400c1c218a0803041c44600002d014800e541e0901f08124205901780c842d0660000030351304901c400405840d580420801401d42d50108003590340c0c0c2c98100c2c12401880b01da4019001400000408940e201e07014103804140400d03400e10030540d8854004105602846101c000d600d03911070140680c0ca035000e900503810760b0118400341c0f004565a0503c11002c41c59a92014114110001c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945583597 1250 945582347 945582349
    0x602030a05070b0903161406070e0f010c1b0e010306110304020a030311030f0a020c01090f0b070305090f0301110309010b01030501050108040b0a0f020301090b03010f11040315020712030204050915032a0409030e 92
    0x10031540d214002b0714203069182c0f20030000c241910f0782020060304000404542c4818807044d0302441c2010700d4015155140182d64071545040c401c0203002c1101d416013070041f442e1183c1012000e40b802160000c040010291071030b0f4054521050b4003d07019441d00090081025214803800a010408110b401038080316060f40b0005214034002e4005400000605105124951840c42030b14105541801c0c400d81c0c0300b002800050300c03888074480341940742d0700740544006418241005980070740d103104002d000100802d801503003901c00901031140050104000680031070710701e540554004580301d5002400c052140135040680e4401d07003061901c90740700c0d402118207080911824282d05402c1e00308010941c00e006841d00c2c1840385110140c24060500640c1e0121000342e8100d0b14000d502c1b911000c042c9802c0c107005070103500280300d05417241090b6070000b01d81d90302c20080860101c0f40200904103191b0513000c1d590300c9110103050200b16042c0a1146045c4c0d03121445502c401c18026224a40540130100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945584847 1250 945583597 945583603
    0x38040c03140a0c060309030e04060f181a0108060d0210090f0b0f0f0913150906060237141b06180108060f0607120206010602030a05070b09031614 64
    0x510818070079031040c603600001c6200543c600050b65050700c0c01040001c9907007000c44c4c1b041105581c05920614120700041c9100c0492085001c651160441c007140020031204402115080011003000c00c511500403081584180140ca80c8100c00030400144030301c1c56004121340070901482c00c40440c0d540130b418442c550f2400c5035000200b0740541c5103481e150360003284205034010541840f00d0f044021032180f03516aa403c02031505003012100401c00c1070f00e41d9070a000040e00600c5001d4125182400102d8118030201d845204603284c2c01c1c17503802881c1c80c01d16001014013190000c96034000d18886040c0000e51a440310b102c40c2a022005251618074421465010083d00010510409081141c04810180451811000d65003420031469681c0c0d00d00c08658024107041100f6444034001414008020544d2444a51416146d0803126640e03210300d4266581c2c416800b6007004070b44107129850015036071708100d940c0102c80c0d409a03800c02c060a942040e04480640045541401004003207002080c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945586097 1250 945584847 945584873
    0x7050604031803020102120a0917065103011d0114070f080a11030c071a0c0d092901060e0108010e0c0a090308040f0609090938040c03 59
    0x107410000b01d4070f2641d80043d41e60720000740c044030400b00210701180050300403c03d200007009808561080c6014090030507859a60482c2c40c0c9075070307401e030244c100b00c142c20416012039960b00c0c45400c41032111490039a400d503020014800800c00060004107492501c0a0046040300c841807508070410081203e44907003500c15003126058440c2520081003441540003483d074030143c03000e04201e9516114000b40c43c0141c500c6081010525100000748410b040c88134008140940c068919411107100b1820910402001640d0341964204240b120252445460740100d0705944101c0c03c0e00340303941140c0c80310945d000514012800101d840d0f80104901c580144450407103050074079000c02158101711004003a0400604282070307000c0017003415803440e40070300005070155401100c8151070720f95801941c1040116801b4400010b40c40140000724000c26000d2048100c2d4041000c6446103c440c9501c81c24504004e540791412400d4a41f0011011025144d03d000c1d60185080342c618a0541c20601501214 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945587347 1250 945586097 945586127
    0x1302060a0320070f03180e0c040305011505030c0105301905040b04060504061805030a1101090507050108040516081e0a03021e0309061305011b0f060209060d020705060403 75
    0xf0405200041e84602030701c00703003030b03810700b403051000c0d003d245142d9020081d0b03088a000b60207080107019000490b035008e8821a841031000344405100001640c08102c403901c0790f2501540101070320107496000c4c80c054030248000314502203101300070201c0368400c221620454842201c2001c1070100e00000c002c0031807240e1003130750300612007400c060707590f5075009100400c00344c055075503078021408100068004400180c1c0c101e014007211034882c140151268451405040404c404052410161806004904440707800c6800344c00c1c01c51400e4019a03804000620440b01c501801e0001100180c1102c1110040e291450090072580c4070407814174008004a51803d0700390f441101d101e00003990003d05c002e14003e50321076a1440003059121395203140030340e40348540e0041c400320320804803800615292003100c800341e0361a41400c1070541007003200015100c014055082803018507000c6400c80e00104090400942100d02d0710035281c0004040b0303005410708441c660480c20620003030650100144c045500c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945588597 1250 945587347 945587411
    0xb1c0212090118050d120204031406191e150f090e1603080d2a0503061512070503062202090a0b0c190f080a02070806011a030601081302060a03 63
    0x81591581c9988100c01d441c0751040040d09070900285041a405423802150b04c6408202400b204428454544070704841d19142091145500006141d003401520702d40303401800003460701221006100041c0500d05e0f00e80d40200d8180d01c000400071000c0145c10018a01038200048151009100711b0500120b440b00480b5914030043c1400071814030310481d030310034100e01c50000c0c0105c1d6440f0b2000010340c1c0081003051103070060440a030000d40180045d8070400d030407a1211580301504c00e1811050003560000c0212000311000981114014801181c100700014600d600140a00210078003414240ba1020381132900444d200400e820220180c4014110102e501400c002c90a40c1803582c84554185c14a00381030b614500b40140b200d10a80500c00036040035000e5a52210807401a560711f606100f9003180d4417482c00001000c4903803403030400b0a0301a151801d4610344800c1c0c01100c078481c0c0940b0141410348902140c0c401a5aa9001000e0300071141d14045a400e008100d0143e40c80900d42014a0040f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945589847 1250 945588597 945588641
    0xb040305071e090c0210050703090b0a0921180b071505010810200c011e091a04140a06051503070302090a1112040c090b040903090b1c02120901 63
    0x44042c2c80000c081d1610b0802c00540c000001c40100d103014846083c0000703d030701d0a41880301b240d0345500140500e0b8003445c3d284215444412a201c03c907078030300d84040c00d006016240c1e03181144015044049414440c980108030a900c140c4d141c24103120703548142d62109002403201c00b081a40a0081840464803508002c20344c90705d0030341d035159662200c002e80c52a50342e03100c03420907401182024180c6e00c2054441510ba41e15000e07420700800901d02054140c840c0d90f4020300701598280118451030303901050b00582c28050352040e6001c008090302c01c5400242d0007400140200c0204801492103025040204030313401c24407101d81044001d5000c2a001e60030404007880580c80c2e02549079000345000000050b458500c91001c035160084901d60f00040d1410403e00091007101f1503c18150b0750008010088040d03a04108000c8032031110008001c104254000c000c4c400c0c010300640b58154407041840507208140d441c030300c102d901c0003010040c810f50350b90500c0f134402c009200d101601e00c020f2051964130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945591097 1250 945589847 945589889
    0x509070b0d0212100816060e0d0312020a02011a030d17090c03160e151e04020c0f0f0d02030301061d06041d0a050c030115050f070c0b04030507 63
    0x550aa009101000384005004400c00c249030381250140101440ea40d8650300f0940320403502ca02441c070038002c1d14400c0c800b0240708803c14001180894140762601d03c40b110800041c00315004c0c400e0710a0f030901019141400840303140340010400204542e0000070002d03124401045a8280c00aa042c0240c1c0451150107002e45c000020446441d600c40d2031591035138a03c9000d510f05940360b202c3c0c5805000d040c83e0103207400c82181d42c038400e483d0a40013482d035a40d0345031405002c01c1050100198810451008040e070946001a80701e00c038840a80054a41103008540d1413070505c0200c071100319a4002c9101c039100a0050003120151039a40c400795245514180005204045008101e02c0c031080a8141e1120f594039101160000c011201d00300316400080f0941c100c142c0022034043e02c9450030a800143c441b0740744400c4906131040440554007110709280d0840301900f01c5000d02d441018104501004540101c0c2c1d001c0080008140c0c01da07a0303608502d8000d0504e0f00561204240580b942d18050803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945592347 1250 945591097 945591103
    0xa0e0301063609020d0c06020c100f030507440c032e06030212070903021e0f09091e07030b01030f060f0f0b120601050d140f0f0c040f0509 61
    0x9400061100764100b405008441c402010b007a10000d40c080500072607101000710302e03501c510880d9003c4e0240e0352844070090034420442445140394000a120300514074401c2c1c000ea0055800c04428034207665000212081c4221886525010304812500c00144419024040c141145041102c22450345141032900740c00e000c0e4000542414210b046c100390f10003075420804000300c5541030844103110742171342c0ca90300035000358080720042c24810030b4840020440340c0103801a104490740941069045045040c01c800b00d820340b12905948407094a19640541d5106548540503882c00d4026201010300410071001d00c40c8101400f0440e504800f00405c0030860300307012141100c0d0454034100c40c02c40980b41920042c4462180d00c46110301e403902d107840c0e000d01a44510b450213400c2d200b0121821503800840d599000900c14964415000c0032a20001801c411001c4000bd5403403040f1150000300392103450400e41c1e840034018155000103140c03081071400c0d0288035000d201c50302082140d4140b412405407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945593597 1250 945592347 945592409
    0xc1c0302270a0b0c1c1e020d0903120306120803070906170109020315090a050f060109081905120c0d1e0516020a0504060608040b0106031419110a0e030106 68
    0x80100c0011544050304401800980032085840d034242d005c500704240041c1002954500740300a00c4110741100f6001030000440d010607400341d40315209114916038884c02146c2403050354904068803614002044400843e08903280c42c0b00d0b5440c0c0d501d07450240001011141c00e0780c003030801c212111002c04803019894800b0b5040d0b4108403c0940d995541155200300c115800c00501e8111050705e04010300b003205640001d018014410035000d0f25252240116444001c0c0d0040a0306908188844900c0503481030801d54501d128005850b6813204014002d0400d4122090008558102482c18400d00f6801812052140200101001040310100d0001c08500848248a1500d1150700440041d9074800015000a0030003e20500160742c4038240101f000750103840885d0000c00c1000003050103402801441071900e80d4004240e0256202a00c80e1f9820000c02c118202407541e481e0440b9079500f00340000e004005264846581952403030080c5030840d8900da0041d85004c28140c00b0201c1410301c02c0e4150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945594847 1250 945593597 945593609
    0x80f120703080901020403020d05010903030506041a01110708070f081612230607030b0312070f12050708040906080c030601061b050c0d06092a09020c1c0302270a 71
    0x106480c0e0303c1c12922402403096410180d071201105010301d0401c50150442021140b20340e5013030155440d40020300059806030140201030311218101030384154829019032f011400c103801110b081c1039444a00605010441d00700d00d924a42c540c0d010300c011041004400203550304c0c00e41010316545011a103807426440c032a00180101c1c11540c0d0400c00354400380303294111a040100340d6500d8100110064000c1615141c242d0013801010710f040e6030b494020068074a0541c0220361300740c0000340c1c1c0e44c6141807444c881301840144030381807000c140800c02d900c0180000d80750588000404a0901e00e5092030401440b130442c1c460350021b0014006107502800c100b14601616004a5021440c0e00d82a810110100f00703481c1c01031044041842030060307036006160514007608400500003000c10501c550000c0380b10849640c04030341b140402140d040380e8002d00318009003c0580e603281d8400400002e5844440c00964002500414120441400c0c4031840f81d0424406045400d1000a900481c400007110b03c610 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945596097 1250 945594847 945594857
    0x10f090b270312090f0d0b0a0c0216030302070f08061509100e1608090601030803040f062a0306090c0c060c110a0c031502040305061602070f080106080f120703 70
    0x40c11142494078000035903940003019a0b41111540e0760254003500700542e214030460320840c40351050b06050100101c115040081d038440d99540d20310740300c054001e01d4002d808500c01c00300d4110b40034040c46d905c01d02070751003907014104103894950070012400040d000701e41c035600244144041c4002d10048896200d20035500454565100d000f444071202c07980c2c0c0305c0252102c1e02d03006c012807819401c01407000d042c09500c1c1c4d07801d9a16840c2001c0c1c0c0e142401d001c001c254010800c081804101c069000c20700c05441404c0206405000c0380b000c2c160085070002c0002220813b4022240c40758141c0070310006001c800608010325841000028250b03080e00300b018184c1e0340e6031640380f10b07102e21900c119401842a4000c440140c03070186002030003816035120664502c0d444000c8802ca40703081d8021a412243c01c80020703c015254024101070400d819074910080d44221440000c0d55a40d008841000300f001400019089260070683c2e41041281c450001142d00034000305c1d036240741d0060039030f0f105030380520781 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945597347 1250 945596097 945596137
    0x9031507171f03062004030c060815061b0c03030c0a170d020c0f0c0301090b010b0919140301140f070c060f05040c080d2a020f120309010f090b 63
    0x104024194075414000c000b2084141c04024401641c203d540700c000764038680031990700034260703d80690145010050044c0348681017000301c80d2240070036503081101500420074841424001600d06c0d4003102d410000300b00e101c140034004401c1400090701c0c0d0740c800d0f4040d62602003000da005444a201140040c94401c44100300d902ea90038143c00c1c0c8044a85401c03003199100030400c2c40301e950b0303000d10010010074440c3e050024203500b03060050f2500d665120580c102184d00b400d9280b1902c3c0c100140043e0003441c41d02da80c003600f030710750800c6000910242509141c8a16490107041c00d4412403c81c01008284890a0101544200341010b511002610f80f0b14150f134080d1030700741c000e0700298900101c003e04000910060055103013980044403a01c20440d4440c02268006448101c520328911545c601d035503000c528079982e2060700c11000c1d4802010040500d0f285000603410a0507000ca4442c40d90011541c100d141d42c120105411941b001d0405003601d078074100d5881050b100302c0041803168144140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945598597 1250 945597347 945597361
    0x301050607150606032004080d081f0f1d0f0105060304020109080114070305070e100e0402040504090605060a08070806070c02010e09092503080d2f0903150717 70
    0x11850341c14081c4030014440702d41e41304401806000801c250f41c003140d2429035800d118034803078422a411178010001910754041c0c1300401792800c520041c561a010003200d030401c50110240c14100d00509406c0d001081068107101e12140c0302041c07004188418102c480500c004822184c08440c11150204c5445950b60345038401210740c00072950000d050b40d0300b072071700100404e03102c1036103684980c40c265020000d40d600c800b411200f2031000a080c40d001040004c0500c1060b100c0e640c41d0406650142003d03140c903603904042000c6800e002e60030b0791200d54800030b00c05540707860014140100490801406401d007050326250b11244040c2c00641409007009407941164000c0e0712042150400520300055072406900c8191140c0b601c0a504e0310180381d840d10010042e20404402d01503039001807007207051100c40c090700c0b03004080302e50242179803041000e103214502c0b0180d501d8500000503400d5080e00e9600f0300381031600e0120020307492045e1174940400c2091295202402d4041660304842400058450031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945599847 1250 945598597 945598613
    0xc051206180a050411040506180a0e030c0a02040f050105100c050a0209010305100c080c07031404050a180506011d0d0c050402030711070e0702370309050f150301050607 74
    0x1241c0501c441d251010418680403079440340b40716500440f0310750f5a2040f40c00410046030011a1115449003600001210314681795034006ea000c80e000c8000501d880588112500e950050350300061258030090344101142482c0c044c5c0020044050414081941410002039905540d91458404c0000d43d100310b006100c0c0412096200c0364018110140650f1281010358036141c0d40108039008508100075200404c0c0724180c4944503e4100310858141030b460360b4101c4000000e180124402141403002040765510142c0400003420301039103041100010b280c91b002901c2c0002c00b0075050010030140e5241c2001208c064000da11000c854112801340745150007502213000340c010a1b001807020081001312a004822030403078110307043c11190306668a0030070b00c0040c01c5c11142400103070442080410341c0e81000082103190781450071a1a4409031200d0014121a0b121206800049240508000d941048510040c03455019a40300ca645588007000d9611844103108190013940005102820721440c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945601097 1250 945599847 945599869
    0x302071203090b06100906050903071707052403040807062405130207020f04020310180c0801090917090105040b03040b06031c0807140c1c020d02010c051206 69
    0x3260200a00c42080d0010024480007030201c030501ca64001080d0903150110134506075a4956603500340c00d90030880211040d82041e030100c1d03014403070702202050817940110907001c0b8500c038070003d150307861411041091908030342829114a00038148005d442100401c21a0740c400d40140710300b80d440752545000c50040924280441e00301c15012460740b4185445800c0808445e0200c0e10341446410241d8124100e220b8060000d5200075090303100219420f05801960340b1913101c50300480b130550383d419000042e0300c2c0d80c010103613102c0e41c0725401240241c03c401e00d0760142030825010040c00758242d03900d00340a0300c42004d45902c14000700701105980c3c030400c00c80d4050207841c44825101c1c1064039080052480a90710a80f19001e207034038144a20050314502d130b0902c11940e682e840309456069064804401e000030b0881c640300c0412200d808800108004074a80d084035900c44561548400c0080c18890380301e0100c1d0440e4101114060310a41c0001500c14528081d1000849920b94500181001e610 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945602347 1250 945601097 945601103
    0x6071a100e07031e0e100509150a02071a01050607031101151403010e060f16030f02071104050f0603150603010e15090105010b09090c160501022a010c0f080403030207 73
    0x7494041054040c1d26412040280d00140110750190060860500543d031151407540500d60000d0341c1c4100800042c1c110302c3e040a0100c0641d26480c84070003c16002450032200d99a800390002502c208121a030f2000c0132120090f011407800c20750404000801c581b1455001604216240b2058006ca4500394021034864914528150f0400d41d140940264900c1c1c1c0d10910f0f2080d403902444016030750002c203000e40320300c548100034012555605c01e40a42540c102c007115080668501449810440e6840244185070203081d501c008005e00b68104806daa00040c0001d0050801c142800007907100050b8401e00541034084402403035070784d02c0c0401d0044c100746554030034a10924440018510141c00c0d01030140e0280f9000707211903070f20317006142424842c0b11102600180d4079800a8103401145d4064100642c100d01000c0c45c44029484032400d9801c99030f205400883e1004c600b080700300d5644c6e0301b00000b45868009001c1d070740014101501d0862001c400c10280b01600001404051003507040ba2201c0d41c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945603597 1250 945602347 945602369
    0x30f041113051006020f0c0d120e0411070b0a0608060c250309030c09090203120711150301050a060212070f0c090204030501050a050105013905240606071a10 69
    0x980b4003c1d03400007100b03900c600340141c0184440d070065020081490703850b16401420369021444682d40c2c40c480c001e400e180038810050701000c04045030341c590091814165024840ca501c0c0d03441c81c1048021068050441c0d940285070103420800400d000c03913400c4e4403911004c015620b4610034a03c40c0015001012500781d05541c0c0c03c2c004c0c5c20160024007800c1a20701070f2a40c5211a9120203041046506101010b981503104070441c40782c61003040020111b50b8032446442420541e15400308024598445120000e04030210041c805814200300740801040c142c4001c045504400a1709402446403203005403064100000c0315040c032030490b00700c80013464104821940c07299241801402000180c0c0c140d28900d081100001d040d6101e0304143e030a03042601c15091005000b02084094a03c1c0c40368100c0c26049984003100200c1e5003403140040a02c4040380d50311071200f00b40724240030898002c020794072400d814030031840030548074a0305441a004940e90048191100844114400340e103031b0150303003030301c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945604847 1250 945603597 945603601
    0x230f1302090a05180a0c0b0d0e010207050f0d02010c230405100207050306070f3207060207060c11100506030109230c011e05030606041d0f010b030f04111305 69
    0x124240d0025210300008816030480e00c40284d9850b0f11540300e910050541000c01c00140f010701928001018003211681001400c180d807a02d40f035007a41c20503a4282e9094000074410390500500344000011281c8500c000c0040c0c21001c94080c01c8182400c02c605600c1c1c800101100740048500c00325405083d0040540e4182d0a203184001d5882030703c0d004290090040901140f00e590180300c070002e110b03882d03480b0302d803200e100d01d030200400c09584090960f07008149454100002216001401240d02070200940c2c2c07041242003480c00d55074154120401c000340b01c044074001c01000324000e110550307440400315040d201d650010307024081080b0301030006007405000450707000074620402c02c0400d241c82524030303503443c42e001540c000d009504801a0300c003034030380c2814829100d072008690005000f0043c6040545031568443c00b1444e4080d001008080c4505012800254001c2140104070300006580b4601d00003103941280040038100078502030851075503071600d5503060b20160a815030340c80104198 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945606097 1250 945604847 945604861
    0xf0402030f1509010b12090106030b0901020c01060503030310060516060f022703071509030f1b080a031704060b18011703190e030f030a090603230f130209 68
    0x107210160380340c1401509240582003507082c40320206040b11070594a1901b0a610040e81100192006201e4203c1c0c2d503079500040000780e464031089002c3c14005000603102c40c0412a85400c4901d5500040d110358820310030480d10040f031f0146003040d11b405103481c0d03407200e29140300940c5580300c400c00203001e6030034028144c03554159507018051124490780c50406010221801803303007540c001d009a010f40081d60140032a003c54200041c40c40103901e0102407a0350b50362500301c502c41c00700b40304455101e480c00d401d04200095480040280034440f002d4201c840459401804240280c699031250200d82c0c03000030180000c83d840140c1c0c03903501800412044000e06c0604100c241d00340110300140ca083c5101640c5440c001054481d40c8003d9140540d040c000500d041c0c0d00e40c01c1c5a410103030f00d0b01c00d440d02140700d0303a410f2024040c20100c9850303804905040420150a44440c4010304d0070702e0001c10003654032081c0f4100d90343d0700311041412510301c0da05d9001c54141a40040400690060030450a20003d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945607347 1250 945606097 945606121
    0x110f120d06090902010c1205040e040b010614030907142101090302010501090b091902130608060312070308061306050a0b07020a15020a0b070302121302040e0d0504140f040203 77
    0x5108030040042140c662611003100444601c03040203400504440c82c0c03080080d00200c20185500220306005081c02d07039868150045171822134080747d1142c900c1d801007102903000303220745290028004606040d480c01185107540c4425074070541c01c400c140d40000c02e6298070342400c1c000c4036040c08983c205981c18449420740c080c00035290201d005600e040d00025201d0b807039100e0400e50400041260b4615105c682080d55480179064034a04034a42c02c02810f00341e002c00e111840700400b042c0d200c1c4100c903d8031504040c1840741c100c100c00a0f42d0410401c1c1c00c0042d40c00385c103085c0e0050040b16400351508245d44400300501054103c107030003136111080401c014004501800005108907001c4451686600145405141c0400c803c400f60388171400181c00500aa801c490b0f104120b4500103042040c52000c028241e1070030717a54a42c50800c0d4140100035420a030155000e0852041d0081003806030020000341315200e988126640c0c0c19403800b10f46078a80d54440009402c400c0140255100c0c2048000115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945608597 1250 945607347 945607357
    0x110301211e0501380d0206091809010e0c0a0302220e2104030803160e03070303082203090b0d0f0f29010212160c060509010906030b0a0501110f12 64
    0x80411419125480b011405402003081000c910750344028108602440705c036504030b0030200d034400d10510204909440c1c10240c1c071440b1000541102c51801e044080508584005110000300d41260107080041c0e115040b5000403a0740c1615003005040c000d2010090132031900e0b98445805082c441025090800022440c1e201e0701d02e11141c8165458403607020000f84941d203c001d140d200706000040440f600da183c0c41902401c01e0130821601130304a40081e0a1015a420407404201d00000340300d10b103840c00d113a10b15118400d101c440c04240301900e010700412120300c1240020302c0c0014584203001604d40114000200c440001c1c00700047d901414800b4242100e503130f1103410b1000f070081c1146032005c041c0404211040e0090b003010807480c0401d0701d65074001c22080e003861188440c4100090030f0301c4c0c0d03070200802155990940712080407000614010190340250105800c08111000a075a04550102110002d081002041d10b00f45583c504044d070313103140135403e0300400b04014898202140140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945609847 1250 945608597 945608621
    0x212d060109050604151803060c2c0a03020f0d050f06010618030c05090c041e05090a02130902090d0f0f03170f1f0801110d110301211e0501 61
    0x20398861003400864044c0c0e118059004501c0e000c080d010600036100d80007241016046a1811a1262260415144070100401c0002e45000341d103490900e0380300040e824500314103000048a0586d000040d56403440d0302002e449000750041c00f0b105541c40f40408481c1b2035208059a81400e40d83c0c0945448072030034440c180c003007215405400000c4001040036000c5d60342c01411450386505141c20300c03203444801031103403803d03810401000c150088000c41c200543e014140941c0c00550605080c840c68a202801c1c800c4280c2c0140225000300220400c40400d94102c040010307210700e411070024141c4030035400c020f4080c50480070000144101000441c40b0a4029180d015a06041d06420035060b43c04a4000109840341000300d807118282c00030401e03650002400c4046295111300da040d084507014035110185040004044001c0d035801d0003400700c00f500707002c6001e0440d80b41151a0058420888600041d804c20b011b8030390400110340c00041c05c82910800d9060403510070325155000b0304103100c6207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945611097 1250 945609847 945609857
    0x3110102060f011a0906030a0e07242a05030c0111030f011205010e01110d060f080a170c010501030f0302011409070603150510091505212d0601 63
    0x111115400011114040d6040d0320340580c00ba803030108419034040715288000285881080188420b5544c4006076000364800d00001a0a000c02c013042854070146502c0300a09020781d54440c0d807406031003110a6a003513528280721001054039a0301103000c0785007508108002407840401000e001c0000301030b0641c4000c610080014841c0440c064140c0c3c0412030f001189a000301006211100141c04441c0a851080002065441d500340f4440d085d9803650900e41c40c02c0d0400319504003410b0b01c901515005114101e0217013101c50030140c10540307407506030002820201241801d1000800e808040b81d02c0b41101ca00200150f5071a494a042072000b0b40c501a401036080c54119810141031100b201e006034000402005582c3c90040158080e10210b60364094840341e040c000907550312400242c403044880c0c0c1c3c1d5800090b40c24400824601640350511000300075003403024100c0d041c80040c03400004038006040721540d90312a1018402040052902201c07880070750007054411440325080c9000f42002d80f07070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945612347 1250 945611097 945611123
    0x4080106060f120501030c06030c0215012d031e02011106010b27131a0d050c010810060f031116030c210206040f1b06080708100311280803030103 64
    0x21070f2042d44e000b800058000d0540c800100540d5020780c1c484a440c10040c015503480010440030000c000009a004160510045400390008800c41100d10031516180d140c0c64003031410b603140d4281e08100203268038101984031050b4800e40e8000c40c20345517155002c0c1c085400f55a1113111044050700411000440005400c0d0700c2046507100403200d41d1b410b84094005e90038111101203510282c032104500000e41c85c44e01070b0068aa840f05281590700c00d0044009007510a40700000600301440202030000110b00100c041c00f0a03075000380014840b184914010954414880c0d070a52540300d5200d400c000a40301d0303410f000c101a00004092215401503000101c04601d2602d1402c1411310fa09800e00140c0050700010009007031481c14000240c0216005050086064894a1454260703002007003c603011008002d0f00c0399000c900e0360b82c0100c0780c125680c54603185684180d8a191110440d52141c1d20740b02224900000d5004000944066000e800c0c0c0e080c2d0703031025881d41b00c1d0300a000a540c51250058 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945613597 1250 945612347 945612377
    0x1a07090501082404050c0409110318010603021e0a091d011a0109061101061d041101020a0209010b071103060106110f07120f051f0c020f0a0b0c09010504080106060f 72
    0x200e203000300c41c201d0f04807218121640304100041100814044804100344000304181896110300002606181001c80e030b68101007014500c042180b035820600b0b41c0c140603007400140c0710700c002e10010606070800c80b00c4407e899000100004440e4001e900030301e1800700a03001d1600070b551850141e0840ea0300800c00c0040380103084000d44040342c03070b01e1b01041c1001c030200319045c0b140d180708d4202407031040005940768565008090041082c2e01034425002c068042c4020300a41c1014010759990900080c0040e407441d82c04502c41604c14480d4440d803240c041141014080aa8101c084012004040c1c45184d1307120ba2001d000c001c500460f51900c2c1c882e81944602202001548074140c0d5001032200004081c0c96880c8480095449021540c6014018500c0011018800c81031089504003001085035959034100030316059038000f00e180f1030f0b0f000001e41d00c00306540c00c600755000100541b4003660340d08541c0c0107840511a643c440c2280d90b2230a2000240140d1010407520b10604030381d074545804050034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945614847 1250 945613597 945613621
    0xc060d0902100f05030c09190608220309030212010906050106090f2321010203041a0906060108070f0c0506010b130503030c100b0406090213140613121a0709050108 72
    0x202c003c02203482000807404100b8060060070700b42c03000a018101a41c040509444008400d6220340c0129802340244408840310458000c1803141c195429000d07464581c85c0101404007611020307003e00d8600c050450307111400e4009040d002e80011043c05a9655154003d2280071107100340104a5080c2c0000f00310007a081da02481140828000a05160500c1040040c0c05502100900e65100e50781041c441c80d840038005544103a00619002d81031650441010161101c0184040007582040041102582e08050440d800048070f19080440c1425010192542c211a184c080d015100b030000020f000640d04000340304804500b0b1031402141d0f51541410f58a02403003e88402c182c00c4480f104800d4855548588148800103001242d15035540c0e0144040782c3c0504484042d80c0036080041c07028160880039190b0350710f82910141d01d064200800202d04000a0060207168070140800744107004032414680c101c0c00d807090411043e8100010003600d103250a100b8031740840c11110009400e0b030086 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945616097 1250 945614847 945614867
    0x2040b0d0b0c16050712021f1215090207230a0f06020c0c06030a1d06060120030c030f0a030e060103170a11190b060402030c16050c060d090210 63
    0x300c410300c0340c1034880b0000d4200c1a04000780c0c4034014000c400302c10010550421500700100b030207002c045001e810724014404400c4091768001c1048035000b00c01c401859202c0030707202e414140b83c4400541400c0c104010b0007981450380c00134110038008a1101e0601901000b1007010b4210503000841d401c840f8240d05403202c03001c41c00901496034030741d02800822680d40041401d511030f003065076200c1503010006009500b094036000540c40c3e446844001e01500d0001180c0c88843d203a0082503240b400b600002c107d048040b0884c002d010b00001c2001e14200c00300250b0300303900d8104003070700d8451080e10640c04040d08044503000001e030600071108505003012643d28103070781c2c03c080140702e004010088950a075000c8900c2400b00440c000240c85444030501c041c01227074a0811241c4c1c20000d080c141010914030281c00075120b9841001070203d805601400c464007044008540c8861881030700300395003000c444c0e03d02581c21071030000362400d0b0303643e00b41d00c03d0040034401c9400014200c0104400c41c1c0603004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945617347 1250 945616097 945616103
    0xb07120f09262106040509060108210f070b0417091e01020c130c030609060f03021002150c1e1201062111131502030f0a0c050303040f02040b0d 63
    0xb0500030111100190000c030a82080a580480d1400c0d42060354078600401c44411403500340183c600380402450180070b4180c100c07030080000c08103541804035443d182e6028905200104a07801c1442c3c0c545a00d41c0140c0302c036050018130564440702c442c10310a4505d076040b00e044600d1b013100740701034910140000c02da40c26690060503060050300b01c024031110800801c61b105055105040e8124030320307a12040c000814440d42e410108a40c4049500a030503201503411259005080240c140803144089000c0700449030102c0b403801c000050820244c1c20070020301c6401ca4034a440c40b00700180340880c0d030002c00b0080708122000340416184401035517103014460a08400151303001c0100310030342c810f1114041d811071000c1080c1e070f1045c40119850840f550701c642c6580c003a0707000c03815013110145104200002d25418624211070180e03e1002512846045205040e000c4041031001c1c00c00e101d0b103c480c195650040441c0e640b424681841c00c038509221404030b22642c00c280c0390944608104216550942c0c2c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945618597 1250 945617347 945617363
    0x10e030a05030304030521250f050f0a050f040f030b0a0b01050d090501111204061505010c0b151305161e050705010908070f0c05040c0801090b0d0b07120f09 69
    0xe0302d45e02100c05500081e0316601400f00403000c1f44080e04858000790041044000ca040c2d560884000707060280600e22160050100700a07000e101150803070201c5048458608203030340d4488891009966074080c0c403141c0d18885e28003007408a81c3d5581c0d54010001e807409031306685a690380d581c00c03400580e100b10001500007541406203c1008920350000407143c0d06c0703800041150750944024424a400c004420120109950207000512019103c0c011900d020070040440442c04e200c00600b03c1030000c08000c150000600000300d00200302c031210540040c0040c0354041208040040034080c1c401074a01e003588501d02030101d95041d00a084060b00910340070010713a6294030b4420140d82d03940010794144d5180d52103030107060008625030005d000852142212080008840c02d01c0040c030000341d004075004e90718101c140b50803140c00070021070454800920118040e85042c000c24008003209070002d00c101802018045e180760030801031135000d03104900400c00078400000c0d01c5c09860740c0f1341c00500b40c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945619847 1250 945618597 945618601
    0xf0f031218030c030309050610140607050c0616051903030b013011040305011512030e120c0907020c010210060e0c13080319110109121107030b15010e030a050303 71
    0xa00600402d10b90f5400303800c00164507101a00c0e000c0c01c005045410006000c180031052150403c1c1281034a043c9a09540c0c60341842c0311555095507a42003c10382510441000c50403280b0021500f54825010384d00c2019200d07000305071424840028803800d81207010a04001c000c0100307500c240c8072600400001070810000e19001e05904146070790f80d40b1144441d5031948400d440141c42e2a000380021840742c03000140f003d80c200c9010059070126044001902c0e19101c1030030119500010303a01050104980c400c604611003403186113062255900390f90422071000c00c004000d500441c0d0a91242003c0e026a101c5041102c803410485506001e603201c141881c0001c160148000d42c00b4200140700459014015500c0758000c51564001c19040c2030901c086124445a4650008a9000d20f50010703000b03000c0e007a0103a54045144030396400f16010081c1c0c018565040b4a82080a1001960403940c100203908020f00c1c1018006172400010307010034030000c6a036100b42400100c900c840d40e00200a54156 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945621097 1250 945619847 945619853
    0x303180c09041211070f09061a030c030c0405031b030712080711010e03070b040f0b03090d030c0e0613150c03080a0504080405090a09020901080705100305040f0f0f031218 75
    0x4100b41008a0802501d41418001c0500801011000c6c00c1c0d5040e100100c3c0d0700c0c09120030300359101908103080c20401004001000b2081a01b503d03001804583d07820384954910b0b251040500550780007551604c6141d07031090300304040507034490f403102d8250f0544e5a803030344549075456103480c40d450040041c0000c10114001c2410520124045201498010410044000040d10781002900314a5182000180412201100109202c010700c40c03072382041c0c210301c0c01c6038469498810f4444000c0505490b1200e044e02d0714410a101d448007003005140c00d840700c03044024202c100d60325008944294560040740c00e402405000f074160b240b40e0503602c045081d620548a14040c14003e481103e9280f810301002c502550349000c2103200e0020420000380d071a450f80108006440180d11510792604003070018044d98072404103684c005252410045816103517880c1020341503c1da400080c000018003040b00080110040c035060404d8045e944000024a82c01b403e00125641c59481c0c5038641d244011100c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945622347 1250 945621097 945621113
    0x10080d0215060d0b070207061106010b0a0309020d2a05030a0b011517010b030603210301120c090f0203061e09131415010510020106030b04110a15020303180c0904 71
    0x48a48080c1010021004544d03490b41096816194040581c10010091005c603034899007d01c54804210014103095143c42c051404074400e0b01010810151101c2d030200039034031a8444004029404030742c107034134020390b440c1014100d8908a144000d004800d640060340c2e240004140311680e800c90107130b121b6640b038001c90540090244040324144044005245c29143d600d0021a000303107800070110b035491405c00c00701410a2080103c40c4103d501488603200c480c40c2c19000d072410b45010f800803030140a9907041031045450f0550045004030700709000c005107109a80c01860043c1810386101009841c0c0c400c2028440c00702c1da980076000444030f0700150001c040e00c1d04da540c400340102c08400402030441641801c1440e21561500c0d0509110010400c40c00d0040e03920107180307030600c002c0017101c1c11603546510388400944058030301d0303d100001c606140d0702d42e00c0c0c1100070b2600d0100000501c150745d6020f0b40345d400484501d0b40200c1504000c07046080041020070318844000c2200f41c0075911030b45c400d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945623597 1250 945622347 945622351
    0x31d1b09060d0807030c030905010f0c15020c030403060f0b06031504020a110a030f27050d030302130609090515011b080d090302030301050306010902190c030e0d030810080d0215 78
    0x640300d840c01031101e01040d8803000038441d441c0280c0e1031030706e20521810042c02c000c070030358403d5041020490b50308090301d030301102034500c45078440061080c4040481d0703854081c1c0642c01c07501c0c21170300000400108100565208001540d0040814000070218104000d25400121084402080040d0040c0c3d82880c05e80d0042103c10980d00b402c0c003000c3c118041c014500740d44000c0880c04a94000314820165400c4100440c518034019400c0303940b046240e03150002842c103031080d83c5c0a82c1002c580c410415000340c0554a082122840c3d035408580d451000501e00ca0082c85010210703468000030550080c0010030050030b0341011703100d580410320403040c6148644007121096445c0c90003031101c1080240140900c5040501a0b4021a12035042004050901e88183c3c03100f03412a20400c51181056840141462003401504020422170b0b550700f020385000c0c0c04422407a40c8500408003010070035070020200c0e80550345840011280c0750725a0002d82d0b031031140452f4040513034002068441d03103480d03030310762a9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945624847 1250 945623597 945623599
    0x52211042d0b03011707090b032a04020c0d0e03010c050a050a0c020604170f07080c0603070c050313031101030e120d020903390a150519031d1b0906 65
    0x1c24036903540c12090304241c00a800c03c002c3c1c60b0b0a951001c048650800c01400075080c03410b010001c10b114817000907a5072451820308250518003031703d100c8860045800c0b414404030091f100b555990a252a16070322020492001d1300840c000740c0a00056040521800101c1c0c04292901803501c005988203960f00e42140420004102a4400307003c01601e6001c0500004d10701035038180f1120102200040c00d000710034454941c4d40d0b00100d000c216519000810701044038043e54103035941d480f42c41c002c403500c400d200d10281003441b00240c441342440c21020a403007241c2c0228070445184c00c0c664011011b6410a100000c82644078050781114051120002c00e0f9a40b000180140343c4184030000ca410300e81aa181c0009040000c24028000e0080101d19045510a6085a40c4a108d1000000d01c1400b280c002d030346922104041401806c1d01541c211090354003500c01040030082c60354001005041c0700d41e100358a8603140c3c0303054658813000080f80350103011904103030050300700c0d001c042c8441031030300078582c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945626097 1250 945624847 945624929
    0x151c08030c0d090c03060c021e0303130f0b010e07121a0603060307030b0907051507080d0b010c050105040506010302030706170c090a0b0f04080c0d1203050a0605221104 74
    0x44002032440503103400646c1300300808543da04080038040c1c104450007050842d02c5402c4110707500f03007001c00f1080342c0e03010054110f15070310701980d41000c95030060f000d0402448a03110b80c00110710202d1280c40184a080503558140d41e941404255400342c1ea285613000303c6480d050345010199282000103142d019a025003110701480e960344545c2c03d599000e40c0c14040705e800240b001e01c010b040840b000c51100e52000086440c0c200e59640b032800c80d2040d140ca002c000c03503039000c0c560603981c410002c210586400900034400380c1444d003890340d110042840101d110388944440010801d000c0d881c3e58100450140e02106203941d0311402c0320883c0e1050017450341c0030324403850106440505802415204e0709040416480e2401d1880c554a8001540c010700d01c11100d2200c01c00c00620316130288404031040d0702d40822687c88007412100900110340119910031841c1c400807800b01801e9913090141883e61000380b01b2003055096043c4c0920482c003a000c01803950041d045c1b644c3d0340750103580413400445440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945627347 1250 945626097 945626111
    0xa08070e04141503011b05070f0804080f010b0901080d0c05030c15040507060c0b0a0207240b040b090907060f050c07170f0c0a1a0d05151c08030c0d 65
    0x703084900304082c020004800005001c09015001d0004030a400140c2c020865800499032616050102c207241070b040102c001003800c20855074410b00e4600c1c1c0c1e4450f0302962a5a1a85d203070035102c070405604440151300e080a10100d501e40704a01c98100c443d140d010304000c0c200c1c480c0c11202005030b2042070750b9501c02004050349100303042214943d854008003000c3d20310704007454528100f408680c0700d1304c200b00c0c4003450440460105541d07250080103101005946c1c14661910031503a40c801107100039001c1064600e07160160494022900900003210100420400f01c02000080300f8182d51010460344101c00030701c405130180102a05110807400c06904044400d40743e985012003a8200c2008560900721040225804002c51010106c510020b001061048130118050007161310501400cad0b6807a01c0c1c1d00420305051000c503a1307940e00d130640600862400301c180c3d4000c40c2c903056940c0c0c000c200101d220390b800103050b5035120744542d01c40076451035512940d51141325a0840400c0134102552012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945628597 1250 945627347 945627349
    0x1a10030b04021c0c02060a0507020d08060f0d120314131101200709110c06190b03011a2d061806070f0314040b0f07050c0603010f0f060309080a08070e 66
    0x114070300203c0300e00101003035a40d240ea200908120002c0c02ca00c484030305100a00c94042d4010a0074103422115113403400c2160780d4a40091120041c500405810030580503003801840408102c82e0f0000714980c405000a0b10350000013001c47d83c2c00c07120031469101950806c40054050031491101080c149800d00344107a1140315603500c52400c2e00e10908a0303000d15020000005ca030302607001b018229003c0541840700031104181c46a80040c2699204990384180a109915581c086081c4040c0a002000b900144803010410070012000c06c81c031900300320342c900302c880c4510407141e00d0103d21440f402d5040c69020050004030b4006540540c01c42c00c0c0782d100b503443c644030071004d071920a0080e130080b4000100d904001e05800d903039901008044000304405d01c50f5140082c1164500850611100da030341401d07060032070804030701000d82d42d4482c800200009000d12420420700a69001051500240b99207183c143d08403181042c1c014480c0b40244190307130905002c2c000c200d0703020b0454100200e40c80c40c020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945629847 1250 945628597 945628627
    0x403211404060206010617130f0c0b180a09020a02031b1e0303060f0f03071206020d060807090605010c0b0114011e05040e060f21070308070c08011a10030b0402 70
    0x74000b40010b030b02c900010081c4607444400c0700d01241612096485600f85045d00600d01c002d40303003000d080510502c100004010314600030b20001d04903c2d00a43d01e8081d403801c14a0b88030a00c4407094401c050356880814000c1a40c400ca410700640c9070002c62134103142410480404050000d0101036004103043c850074038100b0018444040d52100203150f4a01c2c10604003c4524108005c0714050390301c10f00d0000254a00040da042030305c0308001034000305015440c158010f81706405815040a00346500080e140000141c0780c0d003230350171600d4140b000540f620700440705016808806400f5900640041245000200540c04640810314100140c4005101c94841c5205070b03010305000500c0c0080c0c00c220094140120603004402280c410145201003130000b1000071031580b48020403e1003000304840010100a0b0038001d503800440f0070703140d07100c9040c130200503510b504c1495215400d061240088034500c1d00c15081c1c01c072004020b09520048050100d0040c000c0b8002280c01035420821240100444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945631097 1250 945629847 945629849
    0x20f04052703070c0905041506030b0135060403020d0e0f280b091009150f0c050d030f05010902070203070314160e0403020c030f15100e0703200403211404 68
    0x48036011585060501d0142088203100c40803408e503a10300002800001d0344c0c80c400b6411503031304485000341103040c6120f00c2154900c03612010004074034040c000d102c100001c1211071003603001e43c00ba600100d003030b600151070035107001910903400516062210660315000645d4800040c0c20b0700300d18442d418040c07218860000e5904032038144040805c1c2040a440c1c64100714000c003515140a804c020310f000c253f11910341f040f01034442803000401e011003550380701d070b00c4080001c1d4000040f5003c04000f5000900104401d003201d020850a200000c280760380035000301d80c441075001c1d00801215103103458040c0500340c60520701e15680150400040049404030350305001d0300703a503e58098141800d01d0701170300c0c000b012910540613802c030440e41911640003088000c1d01052402100e02d181d03031001070036952101e007a009412480a56010301100790340c140e1218003200c02200031a230004d1400001c01030a805144401407044201c007000019418840c190340780141498100111243c524400202040d001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945632347 1250 945631097 945631109
    0x3050409140402041a03121e0f130f05030303070f0e1201290607080304210f021e250504061503060603050402100c1716020f04052703070c 61
    0xc103005001c10340c942031040401c40140f01125107060340c05817004c2904e800c03503082601120280414651544070700501074032400c0004d0407130903a503000446131100759030f00040c0350520b000045071742c0482c0c03081c9011500030a4590040c01141140d840310710490300c00d041e80441c0b500300a000c14991043d620b8072030428a8040d00c403400440e41005d51240040316603580d6100400103039400b64901c6881c2c80b00800c0703408c041d403c01f6215540f40e03130780c1c00c0a81692508000708020750210f100700781038242d030201ca00a882d901550a5640d00720001088660010b07086408030001c0d0000304c076820b0154000320400c02c80107800100b102600c1c0c0d40e04009812202545d0020b019456090701c894080c9505108076400b91059003001c200a05082c1c0100e4200780358044100180b0906070354040c24080c04011422080041c5002035642d10a17125524a20b50300d000000c0b80a41e010001c031113103528250040a106000c118412082450200c1000040c03201d0385010000c1ca000400500021a61040904000d044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945633597 1250 945632347 945632381
    0x2090a05040c021e0708011b090501200a150b0409020f040b01140a051b031801030908070b0406060911030903030f1321110f0601050f011101061508070810030f03050409 74
    0x4036102c0084d094440c00303248e44114000180c0c0300782d02c00e50410044003c3e15400e00e40740503d80007004030f40123018603803450001944900c0d9031000420032442c0a40c01c0e401c0500c4401e00054240b0030600003961000a03000703510041e030521000c0c0c4e50519902c290321250b0145441026030b007030385020001c940d01491110000581c0000c00c16001228580e5501c0f4400900005610b862804002290001590110795041548504924081c072100c4802d0310310b601d0f000b03140c0c903a050409107450001440d1602c191404a82404041d803500700c840720903203100d00000d001840ca10350750001c0a1200c8000140049075251100c031160010a0000601a05d4003950b096010008081c1078005080d0301480104500164412881400010b90225416045503c259451020b1580b41401030340e4002c510510925190b02c0c2420019544103040042101c00d03403651a214031540358100101e400840444444205c243c400004000003030300c100041072100d0191500c1402d080c1c492100c541038520081049032000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945634847 1250 945633597 945633599
    0x4060803090a1d040206070c2103110304060e12071205070806010b0c0319031d0a06110306031e0a1202060f24040207050a06110403031202090a05040c021e07 69
    0x8105040b072000a4007104084140e4044241c0b840d00318032000a1000b0f01411000c170f03200003000000c071080c0e40500384070984c041d1155a04003a28800d00c0800c3d038240d0000e10a107680e8102c0c02c0f40401110240d0300586d0320701200f00143e40034045107000c0707190090628854000f000070144040e2090364803091148000d00049403a00c0c880c149030203410b8203e078441040811108007a040000100d03045045010882d00442c21010390680003421001110b80c1c401a001e0561000064042401c0c1a42840703041c1c10001c103802c1c83c0c5211440e0200b01c0340b00c2d4055001501584001d180b00c884080030300f001d4003c4a1806246680340e10a98080582e80740c00741e40154103019042881000065110520320346503200141441c5045e002c52400300e1955000d10380c006818400d0007004d1201e02c0d18150880c0003401480301c494041a0307640e11510060300050190351981d1459640c2e40200c17080f640c2c00400c2030140b28200420040180b84501c0400c00358442d0041804004003e620142550040d01c1c1c040c240b82c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945636097 1250 945634847 945634849
    0xd180b070c03151109090403020c03070603022805120a060f09020306090a0c020c21030429040302090105091305372105070c08060a0c26150406080309 66
    0x412103c0e001200050400f50384041a829040968054a00445074140b0584960400ba42004811010310b90035025200c1c000c00c04e82d40540080000c0d80a070703402c0e10304030051140003d50410300a01c4000004100700029020030200319000e0360007051513000000c0041d42c40d84c130000c0e001001c0d4001082950040100080d40c0780c040352043e800401c9404c148501c02c50074500035201c01b10004c209214030309880c030702c07850f40c40322000003200005460b00f05d9039519200d404034020310842c0c12004000400d00b524920030015040240c60440754080c04900190742080f003003040042000700445882c2240d21500f0020490811401e90204000e4031030381c8084100340c80703804080003802c4848941000e0b02d810030002854000441e600308004c0601e0010079840e0322405c4a8a10940c0c00c0601100440e42001c2182840031035464040c0c0200c41040009103003000e02600c0d109071030300e03070a00a0701040e042c4070503042d0084039407944480e1030b00110404848103c001422207100e500104003581c0046140c2d142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945637347 1250 945636097 945636113
    0x803041716020f0103020711040507030e010f0b09010b120a11160f02010305060604030b01140f102703082704090620310906030f03020106090e0d180b070c03 69
    0x90f0600c2031906510b424041c0c0c8504c07400711158200c06000c1c643d10300006203414400d5000b9140e582803100248194a91450200080e04030b042c4168401c0c010301000103488506401140c140c3c004140148125542d502c0040300206000070b000c031881c01080048040d011701c131661002da000e12420003ca0f10490500004080746d000400050048d90100070520101d402d035100f842c11070304032003120300500311800c01244500b40d001d040304d030f0000d1583c0b1404584903013206000550ba41c580a84120b8180c0c0901c00700400c182520000e000100200113075252090204a07607124074419102c9400c0a003658000300f411110082400c1da0b18560710390034181c481d00c01c401088083c02d0001403890410141e180100f40c0c1481c880e03011165400c2d0b020b0118001651803240400414842004111051b66400c015880e41120b060441c0107518010000c200360800d0b2041d40d80480c041c600401024084d0752050704c81e440d1100e500080c015050200003070b411598070003012481d01c1403404044051030741c43c1c1210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945638597 1250 945637347 945637369
    0xc100f090503012c0c040e030409050a0207150c0c0210090e13020a060804030e04090b01080f07032003012901020d0305060d0821040b060a1403030403080304171602 72
    0x4801c0c0d04040b2182054100b00109210502031031003080d80d0b07040c03400444c42c50400d41400240d0000d00f015500c0c506800044050421150a400c003441540d440c1e40d0030004030700c55071000906020b480c802560540300242c1c48690f81c0501030420b141401e009800241000c0c08101380403000074422003082c02a80c40010800b90458420744450203240c07016400a101d9126038020f490421449130006028544101001581110040c01c1082101001c0c1040c032030a020034080c0540700e1050305154545020005002c1c01145d410107586400d1040405032940b4000c0c1481c0225410341d01c92411025036000e000c2174100c00000d816020103c16085000a410100d04031f00000602d0300d00b008000c0c1035115440744420060380095042d55841d02d000b5200c04010129420102900086040000b000700000582d4018042101c0b0058540e603034002d035403400c43c1c43c00400703074064100703000402c0016003082c040c41e04984a2145120080c01e00d000185e0642c000c0000e0700e03820380702c0f04804c02c05d500b05091411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945639847 1250 945638597 945638599
    0x170706021002090a091e1e0606090b0307080601020316080702010806013222031101050304081204171201090e03040503070b160f0308060a0e0c0306150c010c050927070c050c100f0905 80
    0x182b40e880d100b4401d00c2030000802c01424030841e10300144507a031080c0100d0740524045110001d84004034204800d003078000e000228003180201c0081580c560140042e1401d6201d8915000d000081c560040480413100002c0081500700500c16949166014031034a82c0509120f03290418072031450030300b02ea07480088003000d030500c0303810410321010a0255044072070442c081d6400c142c0d1922645828009221103d200c0c0c848104089a0b0684102c883c080140c100e480440091044074680034685e0384a20907032213016070552100c070081240500004c0a45070b07890320320810701604141c5480d040c88007001d001046000660460810100c1c0c5801000d08010780315a0047c9401d40c07902c1032140c0801d2001811680c0700300c5d15816006991498602150500507008000740550700c52010080c0c680e4118015541c80f0b04804020740003003075000700b8a40d4500035030032100c84107a100c501c2c040d62000707960541664540140c03061507074140c846071114a5903810551355801c101c1c480c10f000a080c1011a0001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 945641097 1250 945639847 945639857
    0x3150c050a0c030804020105130e07120e070303080c09040207151b0806061b010c02030c0c15121b070807020103140903031609170706021002090a091e1e0606 69
    0x2140c005501c19980b03004654581400080d940751800180d034203001d4440701501e9241d0300c46000c124156581d12150141c1400e80302d1700000690b0031070311402c3d01e541c40341d00c2e01e42d07510442040020034490500c442d04412410702185c5002100c4000c20300340d0f800010240c074801884920200543c00c58820030305600c024002e101c40703840c0400b8000707207903210142c500e500c907800118541008032a8001c0000d0401c0841000300321800d500742c40692243c200c2000d0030b0044c01031444011486c103018008030182d4184440c91450403100f07128a88002c403014221000300c40a41e8295008843c564000b03242d110b016501e035030f0f12011a480014140c48050b041100300503401820310a1a44000044c1ca4015110100c401d02031000002e003101c4102e215408054242e4140709503494041c40803c1960030b8403500d900360b03080e1074004160b002c140d100f403c4a640c0c0019040074100401c1d4100e038490b44040c03a000c000658000100c1e25600252100c40300212071068074100062400c00c06445014020213541c142 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 945642347 1250 945641097 945641107
    0x15020301050a0612020d05012705011d0408480a03122004030c0e10210204020d0605030106061d0402030a0608070b0a0306210f020102070f03150c05 65
    0x1007207442407030f03110b05018403100d424425041065501902c2c40c0c07001000d8204903940c0c3da0f500d80888900004601000c5020b0904021036181560003a58107840300014201c90399404243c0c40440c0e0000184192480d64052003c1d8041e142c1e0003100c0744800007003240040501c18203040c1800f056000400c0c0312584004291444c4d203030040803a0300c02c43d040d0142015840000900303a5074014100c82d0000d111407208400c1d80040c851020070290043d20b005a9120312410b8650b858a507c0e02c0e01502c1c58004025032031030400500303c0385010a82022004001d02c0c4240165901040590304601544400035071544018491802d092050b040103003001c2c60a00f00c03103003005840070243e20600100501850700040019400542a04084002d10061080710815640d44000c8101a0008000e250000b030900c1c40000e0520494407001e01d500000c40a0b4030700c86c2a280e41c800074400302c501001c0741540144440010140c41c0d140608005601800b00703115180d000e000b140c2c04a401512180051140500c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 945643597 1250 945642347 945642349
    0x110d11100c27120f1502070c17120c030315030105070c03080414061e0a0b1f0908010c09060809010612080313060207060c081305030f0919080a1502030105 68
    0x544220a04070700c190790226600c1a4900b804408026000100da4001441c004401c110610713000d48032190185109401c40c80c034a440c01000d80c86880d6010300111940c0005201081000103510000f0b0b40c40300441d2140d2040072000c45240c0c01840344240c03950004420441d0b0000c44e4084400b03001070440080000d480d00d2007020342600c03806e84010382000400c1c00010100070003a240c111580480c503046840525015110010b11100e292104e0403036031a020201e1001074550190410b00c0303000802000c00707402c641c0b40480c4000c403c2c5034042c041140301c140000c2c3c04a020702ca90003045156903900030320780d41055009420b090028226055507850315804110007042c0c5010395404a600140303c0b07980351584200c3c00d0324401e41800152940d03100180c7c1004000160b8403900f941d54080d01c0707130959a175800000c150b643c04144006003135a041000b492401d00307000f40007000c00100040c80c0480e0040f100308844101100c3e500150015803080150f4814448010404070003036070081015072075981000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 945644847 1250 945643597 945643607
    0xa0501060503010b09010203220f0e06130e030909190c08190915050a050103230607050a03240602010506060a05040b030402210c0109051e0f01110d11100c 68
    0x102c1001301e0300b00080341d002c98030b03032003413086a84415030078810001081c2d070340c5611a19100710f4441d524428101010008032400410a1a40b02e060018602040300703480b40041c0015050b10442040540801c0194205581e10494840e0081c001c102200d24201c8040030004104c540d448007410500600c0800c01c6a10040c1c0d07402c1080340c188168010800c15014503029500c1320302c1083c4440e00c0c508242c100004401c281e81704074101c900a00d00c0002d030103801040340c504000304100050071900036000046980c1d0080c0300400c401000343c0740c0082d403600781e40201d04003106a202111144200408100403195090240740c0e0800d50444260380760110040c0007920703d106034421020384e0800400010b042d5542d0709914541034200650400992022100c1c043e117942034907241c00d000c102c00b040d01180e18200010104070015829203030302015442c0b50100f1440e45c0c001141c1a04010400401400641003440b0b8044410741c2a03c4203618200140501d508100500e64180c030b000d031401d01d440482d543d02c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 945646097 1250 945644847 945644849
    0x1206210f061f140d050601080102371d030d12060f0608070815040f2a0903020f12030c03070303060503060f0a0b01030608032b090f0b090f0106120b0a050106050301 72
    0x7500c3c03079541e03121054000c42c42003800b01d100509179001313981c000503407108190000e200005002e2900505010703a03680404002c140051528145422000d2000d00a0b00404400050802d08010000a2000280002c0c9841e0000e002c1d500041d480e403059040712002030080101a06400c4144802241000300090030124002c080404105080303002c9050440d00d01d1509810806c0540280894080900b48101034400454080c95046403400000300d8540b038840c2c0220003070a1651034410080c81d503020003591211602c4240d5100c91b5100768501401000c000403c5140805809152545114100a800c50740315a000c0c2c0d001c1d8121300c0400603010207400c5080d0740030307d000c0d40000f1027a04180c0100c0c0100301d141c0000809200c0002c6500c00f41d01c0408030a0b00210100080c01d03014440c50041d40c05440d11540002e104102c06c2c00c5903000102e080281e14be01654400858041c00395008243d42554a0340d488226510602c400480500017041c2440d41c0c0051409428005d41d403412100034868441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 945647347 1250 945646097 945646109
    0x70206041212060b04030212011a040e0c060703090503060106090302030303040201030e0f0601080f0d09030f141501140f1c02010f02030405120f0118081206210f061f 73
    0x5001a40d03910703401140c0031202c0300c105040800c40f464484c0c0b01621079501500050384145a0b0074030951010405000350780c07a84584021144011129000344005828811402d220b20300070303012040f01f035440700005002c2042c0070741c6e03546c80f400d031600c014117042c0b00c13068100f403040000d1403005101688000003225040b030390a00e000240c070b40c0705012a6081c0031880f580641c0d140104400000e0010000564615203441603041da41003002d03078801030703518640602c0001c20301054500280e01103003001141c0618080c0b61000d4612000c8040c01c0f8070800c0900b40c0054407200f01c050350112941c01c04449040c00c1000655103580c1c2d060030810710b021250000303a0000d0400a0032400c00684a10038420f82c0d000b40700c06018001060b01caa0810340d02d07110020300c00340c03a5602e0b145203040d100c42401c008541c05071b0001001c502c0c081c1420824101000010b1416800c20b907106071141100414a28060721921070001608561102c9440d050800300040c3c4805c800760502c00d512560800c5154602c1c0407290 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 945648597 1250 945647347 945647363
    0x702121b130212180607030b1c030908100c0305130f06050702121b06131703090313090507080709050a2d0f170610090b0301290f03030307020604 64
    0xd948100c00c0c0207403080d0701c410440180e902c403c1c000c583c3c0395014441000f501c0031054680e071b540c030410110100c3c0c0311701d11001d42c01114440c01341460f500888042d05500d000b032074075164448d260360310a89819000e05080d08940e64480c18402665807505c10a40c004e8175180c90071000d0401030b04c80342599854244050241035892010a000134000c000302400c061907101102c3c2ca421034001e0f11103480f450000341c041c075030252400145540c160b0000f07240c0c03120792098848a000700045051600c3c0e0b08004d0a010f602e1104100044070030055541400c028050b500f8041902c5c600a90000d010190260038001406001213043c0074907903410006106680301411a03509a0082d08a038101842801c686508400e0b241c002c007207000c1542c018554141c0c0c0821041341c0b20700230440f515523515101111044010130030380b20288518042c54018110070f5100070004100245a88111000e50313104007104106002200d0000006081001c0e03483e01004049000e0350452401d984081d4482c0340003040180081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 945649847 1250 945648597 945648619
    0x807080601051f0e030d0e03010e0303070203030c13050d0605070f080903160507030b09151806040b04080c2a01020a0203070303030902010c050d0f140a0f23030c0702121b 75
    0xa0301c602859003040800030102c86c2030308844103010b0a01021901310038000d5003064040d0f000c6180010440c0e00805559004525503640c00c81d00e19031a402600400c0d0110039902c0c00092141d8940018040b11070182c0320016140c1004000900840707060600101400f09420400514010100681d071024400b026004c0c20200d00d4a050740c00c1c00202c1d00000c10342c1d50401d050101d2841c0004500101ca9100a47c80c0b605803520610f9040c2c0703481d400303000d0051740e110100040008401295442e0072500c1602100d080480c181c032981d08001a07802e4540d40c41d142001c51074424101035100c9c0704c40304020700145c8480ca0554011075110303515408040c2c24181c03502c0150003164464244c4c0590541c0080550b001001205c1c401031108034003404900c0003403107900c2d00d000c5607007041088900148450716403508110209509880c2c0c040307013050303003000c0300c1030814030b02e28181440e00258440c04041c1a82c56940c0030f288100300808409420600041e44a640c542c1e65046e0050000804180e00301c0703000c0024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 945651097 1250 945649847 945649909
    0x10e0432030f04080c012d050702100e03061821090a0e060102060105041415150a02010b0a0e0c0f180604080c18090c010507020604050d0b01080708060105 68
    0x440301094203440c1034403001800582102c0100d000d4400d0f200c907003050b10b10b0240310100440c0c1100c0303104580030265187c400c1d499100c11030071a00341100121828081c1c280340c56500059070070f8607204d40080110b1210024103d01d860144895a8842010f0304036800100c01c8285d1750742e549010709000303104d1000a00a04008000500541c0c1031040010040400917481d0980001000425144103000d4440d07803002050700d203014060825140340517880800c690b69600c0350919823042d0f0f051500c0d040380071041000314001c9100000d090f940717040c3e0000314211440c9014011361096503070055155040d04414064a45400c80444a0003401e02d0b4099480340d81070949101744c0c0700c10058469000e01d001500264012010520009c41281140d20303403050624550201c500713610449248a440e0441c407060003581d0700600203030200381d00140c06c640c10282c40d400072400201600c0d4050700d22600d002d004120064003003129a002c0d1245801a00c40c03940340c680422480b00a28400101c414141c028513507030303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 945652347 1250 945651097 945651173
    0x30d030e01061809060605011409011805032407020604120c0204090b01141e06041a040e0115030c1e14040f060504080f0f190510050c04060314060d0b0c070804080312010e04 76
    0x107414001c04fe00e18a99805084c110140c108814802e8000d0300300c0e00103040d0b50300224031940320340d8204c40215020044d12034210350001d40e0000c01c0343c3c06551514400c01040040c150789000e000700d4181817501e018180108030040d1842d04131204a1100100d98a5171501c88801303480031034000020030040200c0c1404010020301030754100c001d030350941100004246400740c0710a40c5882a40d1000c21000c075411808480301341a810117001e100c11045120070f10148940c000907103203403a41d018a400c0644401da28242e0f548140d221800044012600307100c0580700b8070090100d070340b02900070b00500c00000100340e1100d040440119030000302e14891010700900f03100700880120004000c220a180c01d01006007590414052000000c0c40c0c1132080c0c19901c6180415401403100404c0740d65180299075900c840108000c0010030f07800014007840d400520208082d10141c1800c5003d903446402d1040d0490500c00164403000b40a140c020500010684800a00b034003034a030a16416041c0e6002141612 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 945653597 1250 945652347 945652349
    0x4051e180910090b0f0c0313030f020115080a0201030507081315090503190f0302071a18190611042603040f0e0402041109030d030e010618090606050114090118 70
    0x16006050184410401c40304d18200c0b4070892400c1e41303d1070151110202420315020803140310051106045108000c030b40250070711072042e1154800440c981042031498000007225030302441035580980c480303030215a050b02406034000d50303a161209a9280c204403090910442000103085c0780da181e2600b200a07286034002c075040d80e4010007202e9580800d54400c000141138040c8010004640031924240315102e4001c50f84920340141c04c0440c0b42035074904c5a000760304013400b03098426a0b101225100f0f00010f0003c40200c040f0304920720103085003424400245e17101a038103803800841c01c010502061710f052513040f41c200504c9444038000d52120b4403680c9507108035003001180902d40d01c40051000080c0d032242c0c1c8954400c0d82c0c14840f00c0c0c123081e01e07416180240340c032040e03040d00f12181c6451031511980c403619680340c50100200e1020b640755204550f00030045500d864051b00d075a40319013070154078081e100081200f07103403e203140180700392203a0441c0112111181007041b02000c240a040b00e281c4000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 945654847 1250 945653597 945653623
    0x81614031516020f01181e0f0b010e060a06050a05031509090718050112241e0b220e120c0a0b07021b0d05030c070b04051e1809 56
    0x4007032800c00b190078000045810070440c0051150790703c01000640180140d030b080948070301c06000d80080c00d5803407084420741142100540d0003c182d0000c08039109202081c005030091008460300d504041e03040000403c0280340c1c9020320300a20041004540c42000c6401300691303460300c1f9840e074482629208000c0c85540c1c6042d44074400405001001c00082000c0080320f070400c028441040c150381143c0141c4100344500903042507044854000b01d00c990b4420001c9a14107210517179080d02c2654a801140c0b0019409440f5401042c0580c5504d0f1052103094107440301112840140b80050b0080c0d09001d58007605030503c6500d9944d1007107024410406c3c0c0035091101031041d9251000b101c00da03a6074482c480c20580b00150b01602084010740081106038030a0b030803881f0082100e074844c05000380e640325003600b120f00d8030081162040741203040c0442809400648002d0303603583d00c0c1c1000c011304c102d0407013040210f0032840a0700aa00707599404e80d4402d01102110054166074035a03403a1424812217407815 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 945656097 1250 945654847 945654883
    0xc0109061506021605030c01080711060f15011d01121e0b010e06030f22050d0906020d02031602040c05120403120606090b070209100f12050708161403 66
    0x449480100800d0203001d0b52440d5003100c0d0208903070039a54034800c03418410a9016002503010010700c0d48101c003025404292400d01a2840c001c0c600c4a5280c580700321030000a100030b40d010300081081c1d002c0403012400c1e003464030b41c2030041218260038800311410b5605060000c400d02c40f4241d5031040d000b4550b44040c0c1021411051030032240791014090b10180c0704d0006454002962076460310070140d034040d001e1410164aa40d0300c0e0407141086c2c1d50b0909900080590450380c03103000801c00c01c507440321041e9568038844294a0040060f15080240c200c0e00159041405108006040c01d801250074030f804503000300d90206200c10940b054802e0030304001c0701040b040100300070f240e00029041005110f90074100b00d480e0383c030310084503509418010203c5641c0304010301c40161410035042034002a02d0725100c0e22840da607440c05455402c0590014105044e440d0304002840000d0010000501c00d00c0007400b0b00c10f680e2940c1d1041d110711400b0300c0c0940720309036203122030644040101c100c3d0310b0307205110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 945657347 1250 945656097 945656111
    0x50601121401080706110604060b041509020d0e0309030c060706140c180405040317190c020c040f0c0504120c0e13020f0301110f090114130510050c0604080c010906 72
    0x846100c001c402d02600b00180f08540001812500c2094030b107965014820107044070342c80d5940c84002402c0034001182d4495121040208114a041078100007048400b400580e19194502910183c3e6000c1d002447c440c0c0043c810380c0c00b20b850200310075a03c45001c0b503010b556180b040c54044014488260b580c1d128803402e1041001882c0c40308020b055000007800b074810f903003604804100559004071401030024020801410f0604424240c0682181048100728492103000c14210211881b070302905006038400c0d000b1201da41480d2042070040c0e00d08a0b014081c0c140c0d0b009001c2c080e0b200d54402d4000c848010740404c0107005007500c141b4040c1c1402030101281e0704184440d150840303004031041e8850b403001c803079200c20362170140700751140f40c40c0bc0002e15040043e60703480c4240c243c00c001044c5042c840240510005107200c0d0008150311100710005a10b418140000e00c07002241c2c40f542e80052050030448000007690002c0c040c0e500c20b40c80715000d0741da0200503008602400324010020312450030619 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 945658597 1250 945657347 945657371
    0x41a060f0105091305040c03020a0e101203020a0b0705180a0b040b0306061b0d0f0807080103080f120c030a0e1b06130506072f0f060904091a01030c05100e0405060112 73
    0x112101140e008850302d22b00300380c4850b420001d811054031440468283c055003080020f01c449604000301f4002d006403413088800340c0782c000142001f00c0e4110001240080d048030903040f0040c614810140549106100508104560300f40348128040c004c50031601000090f403982d20700013243c034001c1d441148080c00a01c42c40e040380d40c0b4603580c030564000c5044170801c061a20700c80c455052162456580d4801141d20350b450308422640310001d640d1a4070000c0044692a80449848501032080040d00d9a901d180c082544404c4520030000084150452600100204980741c044044607000b2907004d6621600035940060804296100c550421004580e07481882007000f807400d042000d80c041c25032280700001c000c0e00c04451034140517501ca08000000030450804101030300340580090400900290743d40c640005022014100c40209642d0340b0061042045070074141c80180000d550b13081c241c0c2d40c540030140500a04900c0140907a9844001465a0303116100051a00c0e0150358104039540c0070342c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 945659847 1250 945658597 945658613
    0x80a1113021e090f0603070e01110304080d0504081c1d03100513020108150a120501021303080a030615080f0a0b060c240402101101090218041a060f010509130504 71
    0xc03e52520404015686285904000c3c0480748151202c1d0345500084040b9001940c8900034500078214501c414000441c6916041000b0090443c064540e0364446140c030f12428a401d0301106101c112609a040c049050354001c4010310002007181101104007101402007803402c00c0d01c08040070440c0c100703428000010199a40720700024002c0e83e490350280c0d40c042c0e1910404078400d0120350000b0750500304203c0c03d00340b011154800c074856800540b40c0800e066040700300d03011940066070045d5000421500b803a416114140c001d150603120011340fa140610054007240b8008d011950030440b100002c1d40c030b032075103521103400000e0080529031580300c04130310b0781d0769400551710500004103032080500301c9000f1a040a40306a900601d10000142c3c02c00040320309484c42c0b4421b1a8642d210003035900181e4541b02d03000c1c1c2c0c6000781141306100e0b242c1410001d241c091808591024140400c090180c944c0351442d56100d420400e081a55441c0400c070702180400c55a00c3c80e00d45c4451a010074041006144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 945661097 1250 945659847 945659857
    0x90109050d081f0509010b0c161d0a060501142b15080c3d020a0b0606070224160506160807050306090c040302030f16080a1113021e 58
    0x348403841502540f6039070392201c08072401340755484080040100103d8007a00000c064441d0b691701030707aa00064040e4440c1c4201020b80114440000080c48107540400c2c3c0c1c14081d500114042050107454a0800040e001401040c04da440b140307030000e41001c05112003415945918106003040d203101d4020341441d801000e03682807294298513500c500185000b0001080c44c206c060081501611403440c2e00b1038148022034148041080b481d80148520142409052050381d4129802a160402661815064001000300300a204082c10300a003800b580701d8005072003d9104004d00707101441c03d016015946030045000402c01e03600c0700c4c0000010014049021401144040d08c1c13030303501c10780d02c1c4015140560216003401c00160b0900003c0c48038a40740c103059801100c0d070400c040c506601e03078001c07900b0109506c1051003a43c3c8103003198810259201151401403854501400f1810400e0b90307401c04044180c00709903c1400c0418041c4075401b01035041721040c40806104d002000721300c0001030096000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 945662347 1250 945661097 945661111
    0x120608060a050a0c0c020114090307080a03020d020c1e1002190302100b100516080d020d1b112e091a0a090209070809010f18051603050312090109050d08 67
    0x10300243d0380c2441c0c042e0b541c29117080c1e416160300303001e5207000303200c00c09581001c0318a99140c0700c1c07030000103120342d000d0000f603207035601903409491400358040e806842c00c84422030260042541d1181c07504001c04038a03680102c100d0403140340d148081c00040407468601c0244102202c046c85120f441c0130540c00084031300303001550038005e100b03203002e8400300315180c070100502c00003040381004680d10045c02580007038507061107004610f00b8507500030010000c9130026201e12584135500e503940a81604051911120300d20b01c0c4c9032009030650300f00702c01501c43d82c100104140040405140000500c052040e104104a541100300101d040f182807101501220562142c207a507071440105124107868041c150380250054000d408a440b055011120b80000802c22401950b0f180c0302e0303031100a910301840740400a41c2a0500f50b091490501a0918039542c450f000c81d40108101000020380c0030043d80da0409045c1441d9402d51b032145617590244c425180c00030300c180610300c074503002d6903004004c007401400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 945663597 1250 945662347 945662351
    0x7050a080706140705161d180d0c020d150504030906021c0c060b19050a0501020a021c02181906080f0a06020d0908030109230f010303120608060a050a 66
    0x955125616122211405160002030f5611035003140b07034a03000000e12401d4803445c11100c0200c03034400d01c00400c1d010350704007030102d00c20030044c2c0003100402c40c0401d030824035012820132551a40e40055036901c2c01d24208606004147c0420b506566442a542d0700041c0c0140701520312115040c0ca01d40100401c84049000c204070b10808143c0314800145140c019650304207030010941400015503c41359041d8080396115207481d2420a507803100e0030f15081300e0705174400c00101c050818040041e80c46c92a000a41150b0041c0404e9000d030b5515000b0016104040760021946144ca00104000e9090110300030030f000026000d000051401c000700352081a03004000b04626900c03151003c1e02e070099000c1311031440d8021070307048000c129141e00030031100c40340c8240005c410045680303107000f5800036440050095590441e00c00000305007090b00964924009400c90a0b00d00b41e16184620b03501800041e04100007014280e650780429403001f005030509200710362561404030792800c003620003140d078600d00038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 945664847 1250 945663597 945663599
    0x110d170d050106090605070303152301080115050d090303240e060607030c170d1103090d030509060106051806040e07320913090503030a0e030906030a02070c050301060807050a 77
    0x601c28244c4609484055a0321450915261400c9015200d20f101e05030701840000d900081c20012440710140c1d2914100f01d12600c8102c440014112450591140b0035400c0c6000c50321151170362081c03c84001403a1b02d8000202002d05040480007060041c00307861145840015410011010310344034412140200c03008101c960701c0e5003d01800e40134448000780801c05482c1e020f40065035075854a81002105c01085044c00310400c498019030355071124907181d4080001c180038a0b0744050020f1680308540b81001e0080342000d1406a41d11417051007417004020f8040b6071485002e40e0301e4140201c1030f000030303c1c40380c55a880b490600f215040540b2440041103224944d0031300a00404451504d62010078544035603541c2d518044882c65020151856115801c16040d203441c0788a4420b2100040c01040115168a03111442404071180c600300707010154018000d1544955030700d4100c0c0c0d840b00c802c86002da02c0e2542460441c00340b01c402d4206603415428100d0210b03070301e58000303030440c101e80e0120341e095055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 945666097 1250 945664847 945664859
    0x207050343060203090a0b0703270302030a2a0b06030c1012090302100f06061812150e0706080604180b0609070c14030d0b01050c060103110d170d0501 66
    0x6000c020041c24220188500a1011031290380c0950f90020412084e0748440d1030300c0c1e65086146000300e0304c81020954452400026200e010850342014401c1004108105100e4501075900e001d40b00c084401c12004d800700032070705001024442c03c0000402070541e500480c51070b0031004010220b80150091042d00044070b41482c02122509204815468480032074002d503403280d01420001d031301601940b00300740030144195818800d10000318411400000c0d040c4c01c00000401030503040c42c0012240c0c1e405001441a580440081c000f542d500c002196405911030900e08007508043d0b2000643c0d01401c40c00203a000d401c103200510405044904001e1446040320000f50035410003009040380c00c0d00707c001007050030491020740d001695410850311845140d5240b540303201d1040581009030b0004100810071608a0240140311718090929500b000910381e516561303143c0511000d86200c10b0f003190895103446400100004070740200e143e403e010030140d00151180c0c000c410034402545004000510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 945667347 1250 945666097 945666187
    0x303030c300507030207051204031403040308250510060306050709180e0a08130e06040e031204030504120b0118060807030f03020102090409050c1801060909020c0102070503 76
    0x50112110480e5141900480700780c4010a0300030540c9090680c204404004074108104248220700d2503001c0580d0b890544c5491308141c880007880e6100d5a1042c4802d0000803110f030251121100e0b224032010581040136050b42c844401d0203c09009402004014030a040d0284c0044058a0041d20140400e481d41207080307400c11030074420034211a01c540c21700c0c040300120350000b2510103100021034403c400315469034100c640c8504014111041d91503010450000242161544190b0894007004650206100704e5260f110700d0300005100d103040c800182c1010300902c00c0c0d8010749000c0003994071545051412072141c61082c0100c644036945c100d41c91002548a01560040d40c2542000e003a05c1855075a4210306803020510480955400303000810762500c40f4070808a000e0b0140e0010003103040d070b030014001d0340359107414044c1d00c1d113000350300601130719401050210807a90b851400580d0f1320ba60ba60801e0090003901e800901900000031040c11070440c2801c030b042c80d0301d120510741064940407d01d10ac0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 945668597 1250 945667347 945667397
    0x5060907020a06020906040e0c0a08010b09010c1b0b030a270503040b1e03040b0a18030e010f020304030c17070806041e060e010908180d0c2903010303030c 68
    0x5034050034040e00041c440b038000d1704041201038030040c24a5222101280001c00855116a40f44808038545850a034091055070051000e40c194a00d4000382d0702c0000d091100351312000c0e094a00510b50081e0b020030380511840100549010940c8030304040c05070201424912103403002c001d0004c44480301081d0701701000d845c603d902030011444d0a00e400108821a0841c051044003c21501c81110700a1744e41d000440c4610f00c0b13805100700500d40f99000720100c501e2444402c03101080ca0001200203500001e0403030342138100b400c201000d1008408103e1541c49107030401030490645840c00541050700344500070381d0840f8042a104250b0300e4030745003940c416044402604500c0e110021040801204c59500400f5008082c0801d003210915030442c295001d85a00301c40011001407600030011100d06000041d5a044411900381005611070130001107250240340c0724152041c1606800510031808414068103200c115602e941e580d00700079006210310703100031010500c3e411003c00010f8941482d11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 945669847 1250 945668597 945668611
    0x100e010606090611031206150c0706030614101224051005030408040905040215031e06030d12180215091314180718050a0b060307020a20090c0a0201050609 68
    0x14281060b40840100600b8050015074000021448c1072103642521401030104460980040c40e0701b03868200018110360041c0c2c49080b11101d50351300342d90380d0361390307900300c0c5101c0700c040e2a00d084102218281d60300284540d1140c03031031011140c2c52a584e040b0f001c2e07480c0400c44004445280d2101582c000079a01d612040390f0041c0341810400c0144503013161070380110f41041c00501584c034550a81a103894281c1c2c0141c1e80301040c91001c40c2140b42c24041d01c003429610400c1600a013540c03010000020f8012103c2e80d944000750341c4c5903074107600c0100c0b074041a8803420740c00410300441035443d00064401603200801071030080500c8103031100480c0d6140980100c0e0300f06042000701554071000d0a4103408800c480e20a518064507000203404150201c184003d0260044002040d00f0040300c600211032a403a04c0c00c0c080d6000f88200041c040d004182460280d40040400c52804400902d0840d54402c2c0d00d50103a01007820700c04e014900240c48044c21011085800807c165142c140c20010500c2c002c81e004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 945671097 1250 945669847 945669853
    0xf0b030f031e0f040810060b1e07080708030123010305130f030c0c090b0112090f02061605010617011410051009170a20060306040b03100e010606090611 67
    0x9022202925041100d810611031114204508812800a644d016512031001640100c071801d0542000c0d20a4500505c15460014500071115900000c020030203481448030070004184070381800008421034440c0c592101d1221b81d070390b031640400c4200003020303180740326558599004600300d94064800e89004209040300d1400d41d0056681c1c10010109189080b0100501e8102c180002a0401149006450006408541602d07010b0005040183d65001d46600908024029000c40d1919000320951a0162021540c0c1c03900d111980c110f0204103c001840e40d840e000f00019440c41c280c054140e00700000c3c00030f000380140758201c041000c201340d5840c4081c0055440400c883d1410038600601358400d801c01e1441180d8400b0f20f1003503184002c440c1142900200440003c00030710000040104c5010486144420514000300344240001032030a0300071541c030840030409507800c020303c002200c943c040921609201c02102400380a2510178640481d02c1d090002c14124003605e80346180c2c0c0d00300300c02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 945672347 1250 945671097 945671107
    0x72c06090402122d03040e060402071e05011d01090b0708060406032018070903030c2d0c05060403050c09130b011508100501211d010f0b030f03 63
    0x401030100006041242d0110301080c8031241c90600b44521149052888048102224040f1080c3c00c2012020100300143d002000148078020b91840c1c00c41d00507a0640e001600c1e11150f01d8038103070b442c030f00001d121055a099008c1c002000415000345d440580b480c0c070a821228081d880d81800d850510200400660415001540e041c0c419070342e0300c7e032150700100080b41d000c0e940d44646004100c0b104401a510442a10684090600d941d00d840d40d840c20480000c0289443c07040207000c5117250000400f0042c840042d41c0c1400f0050304000e614040f60100020440c0075018809a041c192640460720540d210a0003c0c00c1d10b405010b4a0807250001c028085101a00042000f4501c2c01000015041561003d00010030081c0c00d0550191000d80902092084110400351140400408554210043c1e00d03042c006668005010f5202241511958202918074000341c40540b0709644030709071001e520b000380d4500400540010702c429460704000c124515003070003815101c1c50002c1c8110025841040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 945673597 1250 945672347 945672349
    0xb060c0604030c020f0616050606010504150807051306120c08070e1216060f031506090506030910050a090201090b040e011214031204140a12030e070b0c072c06 70
    0x2100d0f810740c4024181c2044050340ca000414981040c0700900740100507800d003608200c02080100d030004401d0901d1400c107403411141c4607100868661100c104000c9101240e040c0d03000d602650407210401c210100400c0c0c50b0030006151a0089a4500c01030303051400000d2050b000c0e030b861a01525a50ba01c2d60340c0d00e05003a00f4018260300000403441244900e0001d0500200b40030340001c040e0100d6594808031f8105100010280c0f1003400103400300403040242008030303030307044640c000c2101c20580304a900c0303558070401c0b241040c070302d1100c50502504200c200b0203004003d0b0300c65000e9500c04d80340c900300346884802961250207140600f05503010040018002c0c121410804810144524002ea0154800f50b40740c60841e0802d192010004040324140300410281da041045c156141c06c004281c0d40c0042e0300c90040181501220500341039a400c01055846410b1024001420401031000c0da034034404d018842d51006a44229075004144542d41424960902912414a50b0300250070311a511544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 945674847 1250 945673597 945673607
    0x6041109131106220b070b0901050601021507051902101103090627150a0e0604030f0503180715030b10020d0f030902040e0706140f03040b101707090b060c060403 71
    0x2a004c1c0c0c00c0a10100741100c040c007841d0104010b009036158440d11800245405008a98041c0504c035059049c8403c101c001c0c1d0380055091501c2c05121039501c05611000c9094400348205d924180741505501100d40c00c20390001003a0300c1203003005030200600200102c0d03003240380c00240d480050b03641005000c6044560908610011100101c20750503502301ca600000e850200128003503c6104c0f40c8904100d154480d52251a500c0b1072828060007040c50142d40c0202400714203c090340074024040b021a0300080001d140c61030b44000d0008658040d43c44031911000b00d4901403061000908050b4800c916042410a92210820a400030060300d403401d0300a843c10400e40260f802007594440c0640c016030f80703d018404481c04244003400090b820408024294840308041d4200e115003040038205603241c0b01704607640035401048608507500c035211504036009490740b0814500b002041c28464074800424044110f07200c1040403c20242e5840a0000c580121610458a0342000e07001601180c018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 945676097 1250 945674847 945674857
    0x20a0c02060901410c10091b030b04050f1606050d02270a0506130302060327030a170f010905130206161115040605070305070506041109131106 63
    0x1410904c20308a00980b495075072810034040601814460383d15000e10502c4541209400503a4082e15454005000345907a92030030703c101040d0419681e11600340504c000c24500094600e42d44544004003683d901300701c0b1900c001560305807894094050740001503040000d105001d5148115041e104500d0b2003000d88040d00480340320020304c1c0d000c029040d40800c6000303007a011110f038804c40792820a1003605101155800c1c3c2c0016000348401c01c842c0d0003000c001c0c40f4803012294104c0c0d0322036407075891141010070314004445810031049403c0700c1190104001c800f8026100c4103944911036669464401e8080b41c50948580c0c01c5107040030014408070103207421043e0b000450a21000e040c1c545640460b046030b02030341c24980c01c0852038104030108400c84030740c1c0c1c8482e0340032145e00e0404819648003280c0ca00c00d601c604c40c03d0000000b40b81d0100b40c016403e40d81500c0c3c004069407050b2605040180c0d803141c44a81d850b02c03401020300007031811300604002040c1240c21a244905250303400050001640c40307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 945677347 1250 945676097 945676099
    0x60a0f1413060c140d0503071205010f090b0102010f0f0b19061b2103050a06080c060a030b0d080d0603021309030c200405090c03070611120721030c0210020a0c020609 73
    0xc418141c0300c0b030b59401c2120454031006551001e98908d01000028000d540c0d02c4017102d10b4506140c0104019801c90020400342c0d005107500196803260900141c1c010b14000941b41ca4103401d1081c0b210b807190b41680300e94503086043d0f80350102203c84018404c421051380c040e40c004146c00c2884550110100b10000d540d4030301c1403403d2000c001641e044518644680b0480000181e100c0d01000300054407400b440d40101412030086c42c00302c225000180c100c0c05042c00c0c2100309941e40301c0114a90791100f60905030a074010109556440b00d61071003901415030390005030b0203180d0040c0b4841204000380300746000583c041d0341b10800001c50b40d503034104900780442840381c001417140e1842002da0700c5110740e5004100b088000d0102c004001c00385410b000c5964494070503c1406d4840c10000ca0010a0107541d071400c2007136a44d500c80303943c0b820a202d5540705102c46010309051f4260f1815039010b1b030241040320b00c16001c40ba00301300782c013800b04168130175108100c00082c0050340000060030940d010303007a0520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 945678597 1250 945677347 945677363
    0x30203040609020d06051617131106270108060607060b0f0319020312070305040e0703060b070b100e0c0f1e12011401020d1e020705060a0f1413060c 65
    0x302d1034000403a050b41420007a1031055442c0188050f0000c0d1442c03000c0c8a20071414002400700025001c510320100003000301c03803040201d4503a82c08018061802401c1c0d03081c002d007400c0d19031001700c401d0020015600cad100700d02c601446621008941c0100b044e144a0301c00100380e00d15205503552800c000d0b145803041d064000c0582400400c4aa406000181b6401c883c40d142410b05e02d030500405142c151030070800581c0311810484240400c0d405021034050b103071320400105080d01e4a60b0118001e1110398449404010082060000c0289001c040e902a10041c0b4002e503001c0c1e21481e00e448800c005544e80008140204401d203001c0c805080a0030a42c3d05d8840f41480385241c1021a491950000000e1644044e800c030040c041041c20b5050700c0e0150b00e0a100034860400da8520242520200c000c014082c0103e2131071843d000d0307108100d6040a404080c150a032501c01d02c4102810801d4441c918001081c0e6000d0050700824041c0c05881d920003c4004009109190802c140c444ca805142d00307640c489 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 945679847 1250 945678597 945678611
    0x1509070f0b0a110706030207051b01140a09050a0b03160201060609230d11180705030103030309081c061401030207020d0b0c070c030308060907030e0a020609030f100b0f1f0302030406 80
    0x2200c18044c0303000070041a107015948400c203251190a103a04008a080d4004181200103126640249202d00710301100482507510341012078203032907000182d402281d03c240e40d5079000c120240310b900558000c00012008041022400b1416400e0751480e009020015869840130481405202d900d54000404241c0e072005440e144000b003030004200e4401a90701c001710b03000301c032854101043d400342000c80d1a01d90039402e041c10740000b40540700600c006001c0513290340d081814030442504880801680405600d51040740310600e0018000f84c0c4a42c80103102140070302003a55000f40203d410280d8024003040101d501030f6114400106c0c0600700c804844018010000040c0d15046000044c1d40280c03140107032450007104014550720020250020103042085081074a40c0010394141070550403101030340c44010940c04645070a00d8041d4000740e40c4120211010f82a8250340711000024040d5145403500401c107080c4041420300540d085580c9110180543c045440303030740038507081881170601080b2a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 945681097 1250 945679847 945679877
    0x6040f0e16082e05060f2701050a0503030415020a08070516090b03030711280807061107090c031401031203060e0105010e090402041d1509070f0b0a 65
    0x1001c8109003a035540c1200810038040910100048018079004461040c40d981c2c80703464a07024030a07050b1200240540b910040752241c0d903550f04203092254003800c03024600304c10b01b0010160409015900c0b003035000a20021400b420708541c10b0058500140055103010f00d05807180c0000b10151445004500828040c040014082030041c0109401580186000c0240c0250380440e004c5503804801702600e8080c502c1a2514080261044590011500c0308003031040c034042107540400d1540052101e40c904100240c0b441d141000100340e500b982e04541c03019440d039405884088113000402c83c0380d800302404000d41402c642004110b4801460007240c0000b02550844410340e084e0401c84507040170800c0c036000d1a60510454004107160b0321403200552400c0c2c0080c0c8030628008030305009898041c005419529241c2207008000c420b11154403004000a02607510340c00a404582500400c403070105448000004603d000d40c2c4100e042080000d06d0407002c0025a80031603074000500018031503c0160f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 945682347 1250 945681097 945681103
    0x20607050f060708160315060305060a17101a03030702100c020d030305090d090b0f0d0b090a0b03120c12030a140f0106090515030a2004180614010806040f0e 69
    0x143c0035907102d110300ca0038030300032241c4041034250300320041516204130003001c040c6000d081c40440300c00e4200050280c41d9900458000c0d0902d410049a840c01d4110320804518000380c017443c41011000200720000f0b0014a41707100c0c5a0306403509516030b00920082c030251030300400c2440e58a03041d041c8613524840300d03070100e8440382546400b40c01090ba00c2040100800081c400350044280c82d1910048150900d041030105010302c100100c1100c2001c07400ca00800003a60264a008a004292254501d030034409140601060b540480c024080c1c17444202c0c2010340c1405803001c034220036001c0c202003000c480d504d08160700010f2180c0003207516021030143c6141c1684005000ba000c02040488541c10110040d1110005900c40c1d405042d690003186200d05100080d0383d0082c104a50204078034403540f014010700100d0024805034903074005000101440041401c1c440d2505940c014400b560f0350700b10000700241041c12003030100d0b242400291840c5010350140c0a9500031610000d004107114998501d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 945683453 1106 945682347 945682351
    0x22020306030a060905070f0e0f070e040906020d05040309170303060405070203070c0609030b0a0b0d0204050901271b15050c1011070b160c020607050f06 67
    0x14603070307410300000b5103a03900820309001140f01030800c10388800702c038411103c103c28000b40000d200d040901010303104481076511f40d9003d585022054a100241999182c0d0003651150780100003040392014184e2809025130014807440c1a240281c031394191500110440e01e02e1580303820317141d000001141c2d0711580a440104450f201d6070016881c0d8003403401c000f000c26286031000b2030403d5102403d08c4c01c690090038240000c2d158100400c084440804400380c110216a0101000d401e2903040036030891b1040c0000a4094040340c0b61401003850b0441c0307501c2900001480030309000c8250000d80300d4900d500c0c02070600a1424210700c0d00b03034001403072880c00d000d000300380c100320b8007004d000b540100300c10460b0600541803807400c15403082d03000f00003c65248500c6404105103118640b03415041e100291110f6054803419004c01010380c01100342251355210b0042c201501c0901030110034 = true := by decide +kernel

theorem cover : BRFrame.Cov 945503597 945683453 := by
  have h0 := BRFrame.cov_init 945503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 945503597 ≤ n) (h2 : n < 945683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
