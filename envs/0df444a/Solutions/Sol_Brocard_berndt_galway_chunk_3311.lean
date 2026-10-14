-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:17:41.117995+00:00
-- url     : https://prove2.me/submissions/b7088d08-2ced-4742-890b-47d9a10bb553

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 595323741 ≤ n < 595503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 595324991 1250 595323741 595323763
    0xe0105011416020301020f0d0c02011409190507050d08192c040905010e07080c0303190810030819020c100f0e0a18050f01121a250201060503 62
    0x1c1c0920100129120341c50031184880c40e40d10060314540c116100003400ba10403810300669410003c00c101d2404040e40d0702c000180b4015070020040075448900703903010808115020a010780000c5484200c60501a00070304141d0310613025690105d440708005a0300307100b940713025154071401007120141425007642049003a40c0508020301c01d41051071900c00c00b042c43e400c5455118142551488680e01c0315003050741c03050f034030400074002e000a900708503a64085510034000c40340301b080c8204050b400c001c0110744048900108802e4580c0d10007005a80740000600340784400302c2e44240000100b41c00402911403101c0000412805084501c1d0080ca002044043c0500c034a50404403981c3d00d0390480d9154002607983c0c1001001440e00c000050ba8160320b07a4000e1407080b4968018004551280d030116200d02820040300c501030342c07200031200b8043c400940c0204444a01003515245480340c24405c0c2d406048201206207070301803c01c807800e42005501218002d030303440d0b620a20103843d081c0700080d104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 595326241 1250 595324991 595324997
    0x608040203070312020a0c2405120a02160f0b0601120203070914030a05190c0e010b0403061a040e070f15051b0c0a0e0103061112061201060518010e010501 68
    0x58201a0006034840d0300038400100400103818010319224005c1c400c00c1080c03034000710140d82c02942c807080b0401ca405401c0c15181510a00c4076200f008602983c00da50b04a200201000e00d44d50b03420070b00700029406101c9000591498182c8000040c0d0b613010300380c0c1614440c0c00c00c48103500f000b10015225a600744001e910090040c401c0181c000c0d4044400d10880d0910108140c1d20290350740401d0030b111140401408e81d0240a040003070305028080460b5055100390481003885656001c43e0494400078003404090303007010402000462611b401c880001c0070300d5400b0910706000a00000c007200c42c0c4101198a070782013a041040021380c00d207810401066110403061200040f440300034464411440a440f44107100c010304000404100400b101c1030b90042c200c04002c50f10352601c00f04015091004540c1c4a0034000f0b1917450300c180500b0398440d0800c5058241d5a9203444007081104011000300514540d070351140011030b03540d1181680001d0b140f01151031803c4d4107000e0103481144050b0015414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 595327491 1250 595326241 595326257
    0x406060302071509080f0a021506010516060504151a01020c040c0e090c0723010b0a0e040803040212060c0913050106050301050d08160804061d0604090b01170a020703020706 76
    0x1080b00340d4001410054060f400084a20f0145440c10309801680c1180e8443e20002c58200381e00c0f5000282450340b038001001e0300700580d42d414011180e911400700c14883c0c8c05010400c41300003031820342045800c9485800c4000c590480c04009000301d0b0f01030381112422280701c90075549196010320031070820300010359041c048061210340142c005288003444c02c0c01000c0c00070006d1802c1c040e00d01500d10301c0e50f00c400750030195023000c146011400c06449060031701e9481e00849011600e01180300000702c07685a911000203a80b00e80b25001d894200610aa07040b6645080034114001e05224052150030300c1e003843c90311054081c092010b5003480200d0403d01d20f103404c0040c049150058203881c11100202d071809160070ba5403501c41118081da0039184c020000440e42503081140c03003000b030b00c03c2d07860030740c0c42d00c140b4420940da01104135070800041c0e4000600b008184220490b98020f21030312041070500b01c01e407007440d0618048461701100e00f00f92a55021954108056051080b980140420b1401d501d07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 595328741 1250 595327491 595327493
    0xf0f0f13031209320613030b010905010303021c030b0a06080a0e03070f060e2b1418010f0203070b0103080711030f100f1b02010c0908030a09030602210a0209040606030207 75
    0x100c91500f090b210f03461030b200354492040303601c4d4040019082100240c00f4649540d031580340c491140e56240000c485144044001044c811400e1181a04982d0158010400100740503200000c40c80c03840d200700201502ea071a59003c5440f80322031000107094640d101c910b00e140001c00f1004850542e0840300040d01f040220101188049580341d0030103030403240008812201c0079410307140c02d81d040c2c802d0308640c0655595183d541c0b01d0f884840221110342c1c45418801c60702981c044101d1007111144141c0703040241419400b94842d0b40300034129040f0f0300440340b9000072a1911140c1c01001d07441103812a100040c1c020800c11100c04d6070280a005400900003282120f6040e81c030b5071800c25021101a54500d0020389030f03012508945204114030303003a00c440040d1014024060503052010f480490100400080c40480c0007044441060303080e951042807078250750b40c61010358032408005a41007412141004010400410180100021000165034010081c24001601c030395501c4407040c9031051100750 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 595329991 1250 595328741 595328759
    0x1513050309041104080607050a0e01031b11160f0f0605030106050703050309010216080c010e0c0a030f060b03070612060801020405130504171b0f0f030f0f0f13031209 73
    0x9844a07500b01d5002c2640700011400c08868042d99000740110304c00d04040c4040150018014a20002650388086840380c1000054080d625046512030240c2010301c400840350348504c02407222080c203441a22a0b00d00200003c44100c50a84c03c54289480740752400c00048880110800c01003500741400e030b04541c50318074081c00c00c2c005c0180103000c1c003000000080c0040000c1d4100e0308400d0b24010b5402c00398009090400b000c0d00128405c98480d860700d0781d1a01034444c0080c800c024001d009010341c0106066658002c0034902198040324103a880340444007030b5a40038007041c00644001d6640250a10844015805480c2c266011030b9003648108404e03c5552901480700f041c845021101003a10744035840c0401c4d00586100019480340c8001ca0b01020003458008540030701d1008030116424001541c03052030700da085141c0c0108250340100806420a0450310140a07901050080c460031304000c1c28124030154004062a44080006901481003100900300280c0152003480c11550240c2044041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 595331241 1250 595329991 595329997
    0x90608010e0a1821110a1e030e0604030605010e151003020703110105011d0708070c1212050103060b03011a09070c210305100e3d0b04081905030d0b061b15130503 71
    0x107036048061f0440f061007410b008514100740f5580c007030a0903036604e5581c02d08a00800003801741c05d03103004000010806841080d900c540c40108014065000048680743c10381c02540000301c118107000000d655405000c6081c810744d1700800038581c2d0544110900035400e9141e0200628032000e0041c21000e0000d0713254003100c00030351140d01c603d007103074808074680050381c0c44480104000c01306800c0200100810040740c001d00030b6200e00750001e01c0301020004000c030f10914405422604090420005200e081c490310027290f050f4082c0f0515641c14085070b07403001e079103103440740442c0200e6110401d0100000700c0d9850b41c40201558104003100b030420f0000801c94030110f003d030401180c06000c0724403400b40318908202200c0e00201c1d644185569900c4505101c0d0018800d441403800b078a10300c01c2c0ea410400300e401d584286d00101862074800c0401c0c581c0b0043c2824000b0710741017074041c000055012800c2c0039030003031300c3e00c0307600101103d40d819001044c542da0300411620b44803d200400000141e000429 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 595332491 1250 595331241 595331273
    0xf010512060d060207050102030702070306110c03090411070506040515070c030c1527050c0f010c12030f141b1c0e01110a0906090608010e0a1821110a 66
    0x7402c210550760400d030004c3c0c002c1c050081c0c403c0d4400424000d00a4002800c00c003140d105034030034417001100c82400c9055010320749052540d60400c0018020b1464a60300c0003003000d42011403e404c0242c0b945800d85068021101142c4c25072000c021039191904e850b0740154015204c3c0340540b8041025074000745101d20700e0600074040b010051069803100055000840e402181000403040d080704058203203d001032000341138460b80100c03c240303161801c2c0034880c2100040103031607900c5403445580d100003441e00040010000c16079030301c0078030403500400e01468492580e4080e4803045418506c000521042481c400c5001c000e2040040383c0240b001e10814184031044458002925440c10039100e014148910400c80003003c00211b891009400010001c142c0b0025900e0111440c0c135400d0603540e1030000c2c05404612801c41001450081045d003002000d0781c912a0b500644080c50b40e201c000303241c41d000c0c40e401d640b2040c4040d012159030040348100e0090a000080003407000e10346a094020384071004e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 595333741 1250 595332491 595332499
    0xc020904020f0405130c080f03041e0b161b050f0d0501090203030304060915060506040302040203040303140c1c05040809190b0301060f030501050102010920040908030907050f01051206 81
    0x40020155034a00030300d8400700c80c02030401d00580c5403440b00500c80209001c03007101c41b81c1d0078120100701803000042c0c682a940d01000114174042c2000594007200b00110180042900c0c0b40f000030074168590006000c03d2070f1002c00c03408440d60103107410a0341260903500c0300106400e1000803c800d6a031054030584c1401c06481d0749102602a0600c1405003181240194042c07000105001c1045001e510440200d80591a80f00b8030b041968110400d45800323101c1c035644404244814000761030560b005540146c032034100000e1a1040903418003000c202200c400c4161707040802c0c0c003451621181c65600b49c0e107070340c59409c000c82d150513038a0b180c00d03002c0d07076100034010448a0f00b03000b241c3c03055104d46d03c00380c00941000c1340c0741d681d1114014411906003aa10b40020b0800c000000c1da540140a08084158030004107540c000500143c20250081000741507841a1502e028001046405000b18000d0a01802030010142864140410a60341350341c81e5041110420a03010400c161000c0c02c2e03080310b0112 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 595334991 1250 595333741 595333759
    0xb1302060d0204061d0f09191812110f0616050d0f0b090603010605011407080915090f0603061003051b0706020301082b08040203101b0e0102010606120e07080616030e0d0c02 76
    0x8035090014081c41824100460f080b101440074404103034403c0180c81803940d14854039941c00312a460311284000e440945603030085001c50355482143b21014607000c0c4903d013070f0b41403416074a000001d403107206c0342090303106517106900b1314181000e0f66007a60101e010340c000d00c8007628203000204462a0f881d00c0c030b2007894010903400100008802200d0300d03c200100610607880f00420b8280c01a0b2210807440e224107200c1950007010300b05035058a1041030018801c00c01c044210006030060310004011602591006254030300d0f144401018040c450b000310001030701d960411480340e240200c0046d0b4002c0542c03a100c20030340f1900800f104001c41090354038190380745032583c0c40802e18108003c206000d86604003410302400c246402807a250400003565142c1422041e080164200e800ca8000c1c24000f40306281611a240020380200d030043d100b07007080b62041c1d56111007060510034240ca41031421004850900c42442c0d06024100d60b40c000d03200500480310300840050010810600d00030b000319105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 595336241 1250 595334991 595335031
    0xb0c01140c3004150c14030601050c0a120203070302010501080703020616110406121109090c010c0f02040c020609073002060705010c02030901110a0b1302060d0204061d0f09 76
    0x2c000800380d00c41d0541a1103001d42001d1030b01c00c084508150f202d4040720b26018000c01924400c42c961001c40f1640700016286464072401142d007644015032103007042c4646020000000d4202d0840107811a0710703409107403036030b0b440c0c6070003401e407841a44030901603848008240f004d699800115914400c03890041c1000080768503080121501145036070340d20520301400051502412261002014480c0c0740d51514000c02c83c0400911481c140c404021990000d031070700e0120350140c200421410f000d0351203154000350550005003a140c00181130381c0144c105d2014080f28400801000d00540030f002c0a5042103038030b46444820080400f014400c07040c0c0038032660b01c159100c1c2d40449009981141c028880c20031041d2000c0d54039030244410b5800181903101002e050540403c0d1240921390200082a4648407400e000413084140c1034140d0340180300b040b80e030318051214801000184030741c0d100c0c02307007030034112026071101d584180381c060040781c61580c0080f1030ba4401d0f40ac640d004411a40c800b264fc984 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 595337491 1250 595336241 595336297
    0x609040c090906060e060405070909051e0c070309080a0305121003050318090a200304080c0607021f11091203130803040504111201230a0b0c01140c 65
    0xd603000d411994981600d8500f4040e0940009082d1003400700c4181307040e21400207005c2292011110200015501102440740714030a400c43c68205000350800340c4c20b03a82c8442120b0720800265507403a0b10110000f4107504042e04800342d60020304004020300700400041d100904a8821407284000a4002c01b0000300071010307419482000c0d41c0c100003105c0c2c07907440030322000c03410424071081d0510903040900000c2041c51107000b44292130104810f100c1c00003403200c00a00103500040c00c112000c1c00140404510003904105192081c032083d1b000b0036000c00b00c07041e21030202c03199201d1030000500301419180c500394603204482c0d04190a80d05410981034101b551411030007000c0310b41c0602951400001113041002002d042074070070455080043e8200c611401c0e4140c441c40d44059515001e0500401210012201241c030034202a16198101030580000442c02c527002e0700545c544403008201c0d0340500c1002d00c207084584031002c0c11030708103040c401840001170040341c08552480d0718280ba011102c0030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 595338741 1250 595337491 595337513
    0x80d08040c0e09030c07080102030105060a05070512030f0a0609090c1e03020603010f05010210020406020a2910060305070e010e0f010c0c081e011a0603090a02030a05011a0414060904 80
    0x303140c0e16042280d0520f140f03200d4503980030595119240c85902c10100d642841842103d048500c0104441d14007200f04100341d80310781002c8000e442a010b500700d800000048100250301c01c010f0060300e000c1a16022074581c044405541085048038a40441c60b4000b4aa0422040c155022000900500c4644d030100c60200c00490f08000d40286021000003081e60408000302c050b50b009800303403081420214900822402a489039034010382c04040ca810211f8099050030405404258103e100c000e01008080494801605c0b9110f041408220400c800360340b52280c0780e0080701034a88943c48444460000f09070005c01060b0b184581c0b240681c500b026070181e1030f0908072a511010b80c1e41659503900095440e11200f112220440c8100351951401f444103114a0b50b031006142c1c100b0799007041c0502800700c0c0d9080140500d404d40310b800d00481c05a41c0402c00103042e60301c07a400109a030101070450302c00100b85840311500681c01c20301d0201c0d0b00340b42d16082e00e40c000320644426015654904220351011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 595339991 1250 595338741 595338749
    0x7270b040308164103191107030c14090f0c0c1005090a0c050108091908040e13031404030809121e06010f0e01050d021522090605030304080d08040c 65
    0xc1c40ea4066000b0301e100c4030075a400c0026080c00744030790344c58070301e200d85800390f0000d00b00034419003040102c1e50500c00704010503100c82002e40b401d50324190f10007200c9440c150b490b40090340d0600c05d0324402c00030700ca091300e90340d80354134400d03502540c0c1401c0c911080d00020a014242c0c1c00d050901103001040510208078001c10a100c0790024032030340c10a41341264848118080030350300e258100c034010400394015515240101c50040003010070b03d803201010542901031190845078903a08010000700004400070890250303250804665000c50507250281c0154010620300b81d2100e0b0600082010070480c90565140c95000d44501c42d90011003410641002950140c9500c1c0c8004406003030840000099054140c8149801516503503840e040001c50344102449240d91146001c0d42076401030401d0b514508000b032200d5100c40c28031080d14291080e80f050400c0f0801d841c0c10f03e5004011540d400d00032075000308002d901451815080c01c03c1c1a0f202d165400b822806c1c0200e4a0228080000464500d8010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 595341241 1250 595339991 595340003
    0x7090209100f031e020d05061807080405070513020307020c03070f0e0406090804060804050d0306031211070e090c0a0e0103080702120304030602070b090c040e07051504050907270b04030816 83
    0x300c13581004000094105040d0300c0c11131481d010004000381882140c00040240d0424440314917034445900301c514180050040382d03240030b8243c0c0007603180c880d0420410342c400b0581d00980c50b440d020394024905100d410740c0b5442540100c00070011a41041c08800c15a40035034a401e0041d907460808201416405500801c40b500c0010001001540a800a80100d201c0d20035148000701c1030b08201c050b5019800050480000103581d4180309010700c0e448042c030000c20f00ac0d10500355994121000b40c0c60b00700c0700c060682d080f0b003010031098a003111400c40984407040c120452941162100340290085000090182c054000007111001040050740c2c001c0d0780c4180309640d50b0805142035020160165444061407050348000c0d00c0c079141c01c1c040d040c4055212401099085d14000410001c10034880b449034003010200408201900e414040c10303c50707081d0351034080440b01c44046001402c809090304020100005034203214850128048a0403a5000824240c032a030f1805400b00d80c1c080010001005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 595342491 1250 595341241 595341281
    0x2130b0f101112090312090f030d110d0801150c0215030109090c140907081e0114030f03030106090b0f1213020a120302150a0e03030c0c07090209100f03 67
    0x7141c1c084200b8082425020650342485503001c40e90f0454000c0d1040c590303054100000101c1e180c2076a001600700903000801d400b1013900c1c07031000302c1d007090040d43c007000004000d10301c01d00140c08204250320002e0240e14041c6015803500d4030700d1001c500050230040400400d11790040a642c0d0300790302414001040ca0070143d030303540e40f104a100108001c0c03204a41c141000000001c0349095240002c14030140548101d0260341c0702203045842c8c0c00018291200c0c404c0d0151240c0780c1c200a498007602910000c0d03d0b900244030682e082518008201540c0001a0320800040c0841c41d44030110300203c841109400382c440301001e0109400340100c034164014101c52008014250305401c5481100500980d460b6402944a001c0461540c4501c02c000d40035900603840711600c030b429500b206520074542e42c0300007007045580306030304c1c150741c07054076610051032012840b07511010381803081100500000c5400c501d40003200c40850882003142c0134840511210355000701d4120300a4210ba40c0415a902903012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 595343741 1250 595342491 595342519
    0xe12160b030601090603060e06010c02011112030402150301120b04030314250306051804060204030204090b070912031e02010605040513150501031e052d150402130b0f 73
    0x1109070401c8400c9400928a014002910703400791142ca000e44041490325811543c2d404010348011501c0d40e0100d0401840c1c1120810101051040812004083c00001c3d501d003080e00401c0003104038803060070b00000040004200326802e40c852110050750003014a60183d4850500340c0003032842002c900b00c2e880b107510170080f590010001c03568480781c502d510010501c02c0d00d0710481c12240e00b8007495800002e40441200803e542d40da038103500030301c1a4005880e0a0701c1360b002c03909480c0340b0715003140c860f1010340c05c1c0420035402c0512407000e0174401103c0d00c0c07980e070151002480c1000d8024006402e001007440c51580501c01e401103c06000058814402401c0441c0400c112028a12042c2e602d2103001038807000c1150b4034050141200c0e004180c1c0c08400a450723242c0f608007040854100d4042c8a186103441e98141c009444100320319100080c4541b9079070040c580c50030141d01200300d440d0303152003004100050f0b07030b06801d8050381480040000340000c450b80100b00511442c15005502502c8200c0c0a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 595344991 1250 595343741 595343759
    0x2030d030617060f06040b040603060606051b0105040816150c091502010509030f0c030d0f0605040612030c2d050607020c09070903110d1505090c010f0e1216 69
    0x8084910001002c400000c4030030019407070741c800f40c818941d080c0e0340502207049882c3c16001240f1180e0018070014405035603640b420b0440340681e1040003c601c001c02d110140240e9280d40410318200a002803013240350964480a0603c0fa03205448500310000c801c8034140302580c8a500342d903c1001c2802c00c40c5e4a01403001074030340b5030301d4420b402c8482d0004802c01e005600c113020310750003407030301800442c10150b0500f0f140606e50040c09120340ca5200034003c03042e80b211a4003c4075000c012240000501a00740001d1000355802d98001c0b0a00b403454602c104002035100511007800e030307007007010542c0d4098440142d1415450b0403000030681066540c4182c2449000700b940c80c080c20681e000c540b441e00d200001c0c4003c10100300c80340303030106015201c00c0020908030006c0c0c0b11859001041412481038980c2c440743e0940c070544003c085d01c0e135110100301c44291700b004120303003003039090a000350318a6a1100050624104101c40c130b01442c4c6c0080316805426040060014a1105000c02c1e440320351a030240e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 595346241 1250 595344991 595345001
    0x714030a030e01050a020705070e04050307051903120e030a08040c0f09021c060f0e040c0b0d140a150b07080403051218010905060406030b030f010c090f0e060a060f020a02030d03 78
    0x4403076154a07001c0407585c42079070b034421034214591050140079414505414558181c81c02401914131b400200a110001442840030424102c4a40340c0c501e07408400707040040c0031810b807030040e6400782c0c980b02400410f95800410340740340f840985802c49180c1da80e440c080c0011405640181000401d4250216034003c05801912503820460b001d0500030000b4201201540d141c1e101d40d40900745032850074000140200d03a6540d000b8080c180645155507140c0c0b0345d00c40c5521904004071910740c0d40101600b6840380c50039a64215081d10b6042c4588458001032280b8911944525200501d00241c4c0c0404c2000c828252802141c100041d0b40e0780440d0304007822041c2e440005820030b800c0d0004005035071507000b04035002c00e0302c0c03000d04480d04041c02c000040e0010101038043e680d15108400e03a41c00100400d0040d0380600308599906150b041c508030b00f404180d00ca6402c6031a20340d0000d8200082501d80600c4401280c00c0c91410119000750004142c2c00d041007510040d41600640d0541c0d214a5099040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 595347491 1250 595346241 595346261
    0x50703021809040f0314040e07080f1e220203030f091201060602060a020d0b0d120f020703080f0f0d0e030306123c030c010501091b020c060714030a03 66
    0x14920041e804030381080119002150000c10f6002140494800300c0d100b0b40710190040003110800d40b0300340d103d084a4420715812156080013035080810000040e0000345130301c8d0070144000d900b07030003100101741d0322640240007010001030710044000c68482200040341d2030708032a00902035941d695003106030942152b1002d100503001d00024844c0e0102e5807014400c0000702c071001c0e4040c201640f22021000080d521415550038115140c5805038860384d980c030f0701d00c00c2e4503108620000c000d070f404090140482c1c0c2407003104425500005030400c0410859002c64134281211245145d88070301c0004004141d01504060708100c600e00140100c25041c00001903000d004200c030010096507000140c00d41d50603000c003000110340120401e01840e04d20f03d001c4000507101c4034070106411405604903038a1a000100c84030940e80d102e100401c2a1078061141d01044080200c00c090851440d07030000c1c1d55081340500d40c41c0500e0f400500101400150ba00d5428400c4400301540c0c1c2e2042021401000341c450401c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 595348741 1250 595347491 595347517
    0x9030d3005090c09070e091302060c0d0e03121911120903280b0601020304080d0305010504051008030a05030a15061d0f0f0609040213081e06010614090103090605070302 74
    0x20f26103180f03404141c00e4815603440e900c0b010030708810824000c0780340c2c1c043d02d406c40c40010801c2004c010303070350706014000300b403c01d00080910080c1250000d00c00e4644610460117908464110000762000f00300b260791090201e0043d40a0700240c7c401103400ca040c1140b490524068000f14217241340004000f44101e070300840845804120b400c00a0041c0004800c0384210b4041c00036030a0002500610450780c081d00500581e41481d42d40c000795410002e440d00c1180c002562079006001c036161504c10b064000c60a556101201400c1003c8aa03680c481d4000c3c6005200c804400581c0100c160b810494103000720100c1c1044456075400c014001200030040103220b14001d255815590030040c0c5a038a80b104018840000c0e00c83d003a084c0001a40704000058006400700420501400d003480132a0041c1500c10041003141b208200c07004144032170b022a1500c941200d001000180e91000000f0541609000d6050313460080c80010382c01842941801481581004100100507802d07a01400c141d00344d1007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 595349991 1250 595348741 595348753
    0x15030606040518040b090c09280c050d05010f120209090705150703080f06060d0e03040902040b0403120512070e010203130e010512030906040605070c0f03060b10030209030d300509 79
    0x46c002d403904c03003540000c1d0704000c2c030720005040c10310006206058800e184483e128a21030140039107095801040c480d50104800003010046805030384210740c01000d8100042480c6810311842c0c0f00340070408000031f44a1100c00700400e444020a125103c000e100040090b00303192403c0940c041a41c0002e00181c012841c158000303500f420807001000e10401000f00400c0c1b42000501e0580004e04085011100c03c0c4003c4c4004118090544020400740100c25030707450300d80c2d01d5880c140e0412140601c0407402c12030184940102043c1c10b980890b040f02d01801d00300d4000c1c00000040340b6500440030700340c072410003410300041c042e1154100303141030380c905072181e0040d03400c16130138a5528810411440d8100108010030007805e88180e000d040c51a21030041c1c0228641e69041c1b540600c0000d130400d884032035032506248490700d840c000c9242d0450b5281020341c20320004c034002a481c1c0a90791429070501c03c0c0b90410401e04040e0100f050401d12440c00341040b41e50f9600403243c001e2004480402c036074420b070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 595351241 1250 595349991 595350001
    0x20406080f07081003200a08160b0a081902070203030711040501080a08220f15080a0504050a0210030b030d0e18040506011811031501030609050615030606040518040b 73
    0x24402ca074413130603801407032001e15071035030740c40074002c00c662500550408a0000802c40703d69071501c40b980207040380c100503c001c800c000007003907212015a004c0d00780032000700700d9052203c2d0007039000ca51040c055801d034511614000c82d600c010340b045e200004d5040c003000940008200448185c4400a40180c0d8108147d03a01c4036141d690300c1a03a000c020f084440240302800b14a4859104d000712161400c0304580140d5442541d0054003156800508000c140707910000c4446500c42c840701c0e0300c40100b0604b48114201603c5584d200c14483e0800783c0500c040101c00741d4440d0098211100d40d20003d81114000000c404004014010004250b48140042c1c0000000c1120807600607000310380110190403603910b0410310240700002032590f1442c0b15124850320070a29803840146108010446824000b4220b1400050848455400c610a20382c9040144200d50f1215410f01810403800500a07503203480b81c80000340c00f0b008950003d40d02024001080d0260000c4034207150040d44a10f946009c0c580368 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 595352491 1250 595351241 595351247
    0x702090c0d0506121e12030403020f0c03161404150909020306090a030e011b0807121b030905041d01090c060f050a1b020d060c050a120b060f0309030d020406080f07 72
    0xb80c4c0600c046580c030458481c920b8400e4400d00e01e55051400084440c048100c150303006282d001107500b82c003d42c102c80358003201e03124107120107140c2d070108801a01d82d254141c0843c0e4284851800b9500300804d02280344a6152110b9012030443c1083c1d00c1c25558a5a0b100081c1c0041d28103e40700301d01a00454010601d0200001910f00240b0744c0750702e42c404000c4d200da0044600726a80e1845c40b0f039807881c002d40e00d0007090441c40203160143c02042501c6031000140c0300034009a0000f030156100281034030000c00880e034400140d0b401e661b000c480c0451650154000c00014140c00042410a0f502c1c12081c07004000800c00345d4402c598150315080d980400f641e0b07045d2064011001c0d0072000c01e0103007581010055a20800c607240900c020203102c188040754072940304541403d40213401045000039028010f641248910307006144040c824800981c0440210300d01c0d0080002c40d0752000c0300400410350b040002e0065402c245000841151555611140103200d9402907401e05010019000490744c0348cc4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 595353741 1250 595352491 595352509
    0xf150409081c11070602070c0b03090a030809030903061f0305010e0f190b0609071b03020a150603081c0b0d03090501090e0f070c0206090a060c1a0f0a0e030702090c0d0506 75
    0x800c0f203041410802c0b2515540e002c5d61281070b0455401041c0c000102e140e074600c402560045005500034000004a40b5000d00031a202400e400303215070007403040105a690000c2c61641c4100c407032070713044141e01c00b800c200401180c45800042c01035003020903c901500000504011680058048450002c041040210040c248900241c20400524005051350030141c0fa001c3d0003220914003906038482c250242c440c05110000120010b030800b02e4518240700140c554501048500e02c81005503c1c0b56940e0620180724140143c0001e800304d200e4802120460b902424403450050601100c2c41280d2a004007180c1d80b80c00f545011802800000ca103082d000d840325442855030141d00002501d541105a46202d081d07001240e110504000d911055228050004020903a40d00d684440415529189081c1ca805c40d0740a448134009504002c080141051180e410586113040040c440d2000070a0905602c0b40704e1004e50800c5281040c041c2c00e14006000344052140e40720101f01d191691010402844 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 595354991 1250 595353741 595353761
    0xb040b030d03020f07150902100806010c03180909080d15050a0501032f0c011d0628110304061406010e061c050a0b0102190203060f150409081c 63
    0xa803005500c444024040d900810f2940407031584d090400d58903035155816010628081c0480304d495112880c00c42c180785d503c0444250300d5050078660b5151480000b8488402c004001c0c04004001c019490a01c8201e9141c1000d4081038100388040344003800c00d880d90b070344210600f02c0d8151070704200002220401924006a800080003662420b1400c001100540840d040081c10b480000820a800004204601c3d40799803004807015101c0d00c0d0a0405400c45800462046218002c2c200c000002c507000320300389034041001c0911401405855840c021007035481c8000458a81c581201e28000e01c0078080690f12070341c882d0805103c030001101c02c44c14507402c207551941c0800ca0b850042226031070600c010301842001c401100c0781c0840c582c41040d00b542c0c4180c030415109070342c0390004810395074144042220640d01a20401c640d07030843c1c4c08a659000000c006038440070b4a613001c0340c40080702d000e40c0d07070b20110001c0050050038401c0c1010002e5622030210440a0304503001c1502c10010540a605100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 595356241 1250 595354991 595354993
    0x1060519050309160603060614040f15021006081b220b031002070c1712070209040c090c020c102a02010c050613050d050c0c04092909010b040b03 64
    0x10040e080000e507115000604541400d0251010329601442003065100051001e585d02250300d920700300703014120ba0400782030b20410200c1008140810308452031140f0450b1540c450986078012007504c120b0070f0003007111040380700500f08840003a8a42c0c0001d0f49000500c1e140003c0f10903065074904000c03540d00a000b901c800e10020074404030000340306503c070005006000d0180e0700d1030304a0140c0001282c0c0034650845140440c2d0400707120342101d012502021440c4200103020721402c84402c00e030240100040244581c08000020b01008080d680400041c1000740041c030914940c0d4070080c0d01c401c90642c030301e4040c4404800c02451184142c0e03012542c482e11060030050080f10301c1c03466016015550040e4140301c00300c40100b00050b0b04121082c413962424150f41ca03002050300c2c0c002d0410368070320a4042080404e001c81c0702c2142003c603583c04500400c9a00052601044c03824030b19a499180328800300c9a000460780840000d8130995600c1035103644020070070708180c4010481251220707502c0b03c0e05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 595357491 1250 595356241 595356277
    0xc061b03070f08150a0602100e0d02060f060f0a14040b060a09030215120106090f0803030f0112060b0310090302010b040e120d020906070807060b01020601061e0504080a030207030b010605 82
    0x190307008120380c0380c10004d080c0b0000c1055101130003080f01e031110341d880100144d00c10140c0320312101c071511035014007015503406001c00d8410b0100095803502c028107040c1c1c082e850300d0089a030b56030b03403210040030004021304020949030740e40310001e0070502c07aa2001805181072441d60100340c509001150802034081d120405503e0854090080802c008071209458403020890a03900781c2502a0203070082c032095498203c154280410f4010b9141c007540203d06551007441440004040d1880c0c480c191410b62484070b0340f1b124a424550068060502440c1e0980529481222003201c6900b10743c41040c000d800a1008042d440140b0040714030f919100703070654000f464210040c03240000100f00490688a000d03081003200c4000813019444480100d40503540000d4541c20001c40d03018610307103c1c13424000340c8565827502d50058816604a1120202c01401507000180c3e24020340c2554082e003040c0084610004c86494069030700d04403400190749032500c8500020b94284602e0032138041244107035141d48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 595358741 1250 595357491 595357517
    0xa0501030c0b1c0203100315060312031112010e1005272a28090b2515060f060e0f0a031a04060501090605060403080306150c061b0307 59
    0x365040b070348141810740403810720f00d900ca48842c0091030103000c1012149540c9461890454111507031019980e801606108081012800300c411f04008203119040201d9010341042c0c0c0d80555108081c500c0c510325034108000b00e142c1c0b03207160060b8400c1d050303201c050604035115410014070303d28140702e40040d410404041a41110b0480c0d06070b40020103103125280d1203504121807030994002a01d4000c1c0d4803401f242d50b0155050030840200310040c8000c039200382168940f4003d1600505018994940400003050800c0404c2c440e0030301502d4503004103c142000480c90051141702c9540f428081c803600704000440c9a62416040c441207980c2d586403520340500410034441c2036500e0040b400ea22280e54000040460400c03001d030301d2110083d48083e040c0e1324140c0380c05d43c1101c40c103070400c5d2002c0345000c1040c8219100c42c0c0490b401d880c0c00008280d00d0382d0300d420000d12110310b580e6030003421403808105208030b140001200303400350484555500da411013079030f00300b4201e000444100c0c0020b000700319018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595359991 1250 595358741 595358759
    0xc032404081b0d08071706010c020d0201050c0706320403201e040c0905030d0503180f0a03030e030a05040504020717190201110304030207210c06030906050a0501030c 73
    0x800c1c2080301c0d2203154140300300301c003a0b81005003040912011900607820000e01720b0703100b048000303001d254131030071411820030b500002c014000503400280030700200f400c144113580c021401c0c2c03421044036078100c0713981584442004284110207400804028140d485024505140c1d10342c0c0aa00c0140d502980c0c2018610345030401c40401c04942c06075483c51008081c1007640310300d9207500d03230095512407054241d6040310900c4212418004c100c02042400c11051015507400310302d0658400380d5180c250b4030303610740705880e800d0041d450300601c80c07511401c0c100715060b00020440401d424000d0b04c1c00c019121485132100e8591160584420020300200028042490300303038041c09280e0f000e00001c0c085000e1035010030302c450307200020840e01038280c5003985080d150709000304502c0c16402d188507400c40c04c069070060354441c114050700b00c1180f8894803074034508515442c8065810742240d0410011555040301400400ea00502984c049091100046860b1945e00950341280d074844004241c0520300300c541 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595361241 1250 595359991 595359997
    0xc021c0e091b0d0218040b0109050d0519120908030405030a02010c060f0f050a06170303070516080d020301031401020703020a170702090a0614091501031805010e0c03240408 76
    0x103542e1510001c030150a07242c01c034001401e1602540d0310b005944030000c041d441600a040c00540d8456805c00c240c1c03110a9034000344150417600c0503605001c00710503078074180e03081c5069880107541518041d00030100340314485034030454500c055210b020a440c1c42e207001d40e0300c0744194000d25030598002c20060300154442d03284182240c0c043c0070000340762001050440107540500c44500e80090b19041445010700440c070a403070041c07403100b071680006248400815203a01004254100340040891b500c091b2409180c00c0f4120182c2c0080160745e6800d040d041c0350003c0d0000c0c0819500691700c0c046d84d038401c1d4014400c6440369905500200201d02030742e510001c01c03602c200e503144017514041c041e41c0016110074591900072542100b0106080b400d12409140c00044000c031039225141c18802e024803141c1e808002101001d0a213404507955010044020714580d510000610a610b844010401c0d45004203045405c080d084003500d06001c00750405c9040011b001c2c4e180d4400c1582c00d004140040e04090007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595362491 1250 595361241 595361251
    0x1118100504080f0601091a0901030609020607020d081312020108062b0c030b0921090307050d06050f01050108060a06181a04060221030c0304020310050a0c021c0e09 72
    0x4900d01c1d00ba12092642d04004265002800da40d10000051003048500d01406501400349948904107001c0e44c00064517162042c07002900e036a0385c40940c0d0056403a5003007291002038010300f040718003c900d0f141800841c0d109280904580c401c40341d002c01c4000d0036020184000d5016946c01010b6181d010420a03800081c0149200b0030200d403012003080c0d0305184500c40c01a0007041007000440c9181040f641d54080103000000c190401d20020000c1c40a00e400301d4603044030f4920300d80d202d10301d10000c40d1030f00042c0c0d00320550008444c541541008400d400884c400c1c84015039404051340d0f11001910386103401d48a00d9030000d40a4024030089115480c0003500c03d0404110400440d52524840c9400b600d4030000f03049a0800a03003030160640401c901088012522021211402007402c010300900002c2c0010f4100c6200002040540d40c08003d1514151800320013006917003040d1465000802c0d070000d9041c058051400c04100c5890812809070b45052691603003d40e580301142000900352000304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595363741 1250 595362491 595362497
    0x6091d1f030c0f0503120405150c0c062b09030f0c06060e010e011508040804030f081e0307020d1d210a0c050f030a0201120c090b0d0f111810 62
    0x10300001103000c0b4101800104100300c903082d0814180400d0506091b12401c000705100d408000c10029512102011038135006e1140d40d06840d04440265142005072480e00c0580c490008500c8424501c82c4910450010b03a1400320541000a00e400480550b050b2050190100710301c020a00c2e06103000d49001451544203420002c0c0c1140c5030f001c00034803110300703800c00321949030480c00500c00103200c00605030244020b8100384110b031405a580040c103104a01004020300c000601c201d0402450500380c612110035142040a03042250b05c5a075095002150f041c030052042d0485034807203d000c0c0042c1405a8100380b001c91400541d01c007440401d00300c0d10740e2044403c0304ac880640d10b0201c10700c10b86100318410400010981e150a0030403044c4468089010311903041000100e00603a0042805585000c001d0400300c2d00020b1201c00792485082c0d980314280e80c0b02d0004665a8240503680301d91b000d241d4501040006d03e0540c203a490300e600414a03001401001c58214038118a800c0e00c0040b26226286 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595364991 1250 595363741 595363801
    0x702120d060302150a020d090f03120504050301290f06120717040807050105100b1e0f070b0f010605030103080d11090612040b06151803030c01050403020706091d 71
    0x5400f04e01a44280420080c107801d0119006400c0d41d8140100d0f6000252880d15407215414202c4403c001c04d11840010b190400c50300710302420302e0240c400d80c1c0080c20010b00030008103905015030b010f01d1002c10749032a403020070344a101069240c0f280c240c400e82d40000c1d0a85041040004e5020840100900075500340580300d90700c045502516a801c600c110310072411592286402e190050039108040d0030303030003030024900050001803203050603900c1200c0026880000c00507180102c0d03a071031180d4480c040070f240000442c0424000700c20b180a0045079110300041c49683d8920040340d15020a000c02000300c0307c1004403000f86c1116812030b1800c0010170490b5890300c9071040006017260301603400080745d07075244001c102c21f00201d074640da58000400da03044800c081c80384800519a129622544480322038000491019840c01c0058031600e9011100801140c10603080196407150a0300c944c0e00010441e81011a82081c0071000303000651031618130707901680720010903008031214a000c520640d6100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595366241 1250 595364991 595364993
    0x170f0406110d02030315010818070b07110d170f13090b040e0c060d15090c020106080f0f0607080606071b08010b090402101b060e0c04060e0702120d0603 67
    0x8100400094035195110a105a80e803402d209881c686402550010f01c2040481034001d0020f40c1820703824030b0300c40c042c0d982d912012500701034812422342c5644140c403404201c44500350020b00402d401400c02413514541c280c1046100369005900502103a403410b4210a02c03484038024181802ca41d20031a03090000c3d40d03c1c1040001d403d544034901e41a1030303060111309420144221000c1c06644000f500154030745001080da94840d803143c02c0616555554046002d00d510543d1002600b2035050030b20110b41c0da058001d0192001e0300801c07080380a060b011003200000020b01504180c6a0360150007144d48850040c0c070f61040042820703401c01c0007002903d00064000000b002c91003240041e01c100b00e810300c078000342110b00c01300c520750045420b0814840580e884200c01c003c100c01918085545010381c034402100c1040f11100108250304003007924803800c0c0042001e080c8001c040d1400c00c016030382c848007001c142d4000ea0701c007405604400c40300b060705800c12005000d1a940c0403004503540e07540e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595367491 1250 595366241 595366267
    0x507110c060405010f36060806090c0c070b0f0702032e0b060403050a030810050f0d08031f03030e091003120810170105040215040f0b1809070c020a0801110717 70
    0x30466540d0f40c0301b101c60414007402030034564154090003840c07801e0074640c602400420144240508045240d80e404500002080001c000a030042e010000c3c0894951803400c46402c441d401941007280309000b10840803024034041c0c0200c030013160b600780303499440341c072580400380c01007942180040c2c110000700004000304008001e8044141d100341d80d202640c0c03034403000ca4104103250b03400491182160740c407a60b029135038070340f100d0320740c190001c00c4243e99448141440d0310380c011188841ca01c02460580c000b003490740140704441c0c000300507070b8041260303035684c40d60108224040c04020200b64140302d850b100a032040c03010350303071080d12200400c80070b0b91104c0070042505481240980182c0d183d208000031030803c02c00c1440010000d007110350801b414408005c5a1810b203000782d403245180030806c80701d41c114050351224400000f400c000440e0501c080010700890019005a01800000030001500c800510800f080514101003a504098682d92004181100110a03690084090142c5014015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595368741 1250 595367491 595367537
    0x307031b08030f0f0f13020609040f0501031a070302250f02030303011707090c090618051c020f0d0210050a020111190f0f050409110c07090507110c060405010f 70
    0x105000b2242a41d2510084d159104000184050b0740300c5514800c2c00805580c401030340c1d03000c0e6411909540c8846940010800500704a08054445818000004240141e5444414104940410300b00c0c2c20381c1c3e62801035003079100317040f115210702c0c1d4a528411102641d104180c0035252140c0d105502c1080700340c00003441c64200703030401002c05002e960341012019041101c0710040250300741c184a224000880544207680c5071250341300344016101d202c00c06e070820303020604c05000d0003040c4080c02613441c0420b400e50ba61510049001e07100d8400c08050610f0401040c00c24190b0040c8500700e1800c4030385040303456030000c182a03829507403207201c41050381d80c010020f021b610307030036003054222810314420041103440010104000d125421000001c0f0b1944841204c0a41d8494400820260360440c0000e0161041c407090404074012545c010600131a243c11241c0030f0f03002c0f56552860034083c406040c5c1c40e034416168003a4400c4c1f08000400195000d001c1c0c2c0d8070368030075506100b1174507520781c00c0c2442154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595369991 1250 595368741 595368751
    0xc0405090412230d0b031507140c010e0109032d1b020307031217010305070911040312020a020901091802151209060105010f0809030a1101020408070f031a090307031b0803 75
    0x4200402c1c13080c565a184d214152003900100d0040c051003505500d5900d8100020f41035004020340600c2001601d0712001c12601c03034144500081140081280c0038500804181c4000c034005001c0c4404410036158000c11968080b1048840100c1d8400031002903452001d0780c401050004000b400043c0541d40901900004501442d0b484c500700403485802001c20000301c90f1032250b03441500040c000304400040180960b80f07580000103402505520764192401560f04c018003a0050070309040c203081d4081183e880c1584207540820707170f90741c844000750709441e0008040020925401c40031005850310460005501040460491422298040305d05080c0d07412610700e135840c3d000400404c80742d47d0110350701c1e00400d0249000a9142800d00c0c250b5101d118600e126010404509601c2c17115800030f40c1181c3c014100c078802c50b0205c80c0c1c1c070000400002d10a11040d1118400411291080b02412035400e1181c2c4940300503501d05600c5660a031000364680a0034450541d0a84800340020341c8840194054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595371241 1250 595369991 595370057
    0x1d01032309060702194106010602030c100f0207050d230a080408091912032304031403090d06050a0f0c0e010c1401180b0c0405090412 59
    0x40e15000301954503015010f4822011035014048a0301c866200540180f402588609420303103061000d4044040400c140500e02540ca01e008208035403807000121030100e690042c0c00b61011603070f94000c00d9880340116044484a078208008511403580b07182e007c01608281ca040050504000f920b5451a00f08400b21003c00702d1080b514154608145221b807488001000d00c8251800e00d409200070b00c85040a0001000402c02240d92100380c0e0b00c0034840c4007902c0d00d40350045c002e41d45d030300c81505080a0420040e40400d040f025030055108201d006008881103981d0183c1c9480d145070344000208140c0e2080b804180014405400990b84680903880814019035011845041c403402000c201d40304020a003524074504480c480880c1c0c0c014040c03d0f4608024240b01d02e40106604090100010b4404002c07025440c0a10801c02440c1090184110f107004910b409203550703442031140b000388224014580c4c0280f203140010000703038000b5401c0c0c0c0c0d007805500d80f1207108a10000c4582502210030682411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595372491 1250 595371241 595371311
    0xf020301030203060f0411011d040e1608010e0717100e2d0c0402031008010e0307050f030a0203030118060e070923280803030c03070e040207031d0103 66
    0x541c41d0030080c45412000200210046050030354074003108050b147c00180c14440da102c1455060110101c81c41c00d10030003e0014440034012050180e1990b4204c4a02d1039070102c40080840c600c5414490003155192540042465505061a840d09124026162400e6118100c50001c44240030301032402c040006100405440d0100d0441c458200c218901c50b403003802e0602801d01c0b64040004502c030400d403003920300603a07903103a404401d215042260400505c66003001c8102c5d11a00002000b04421401030040e84d00500300c40c00c940361240300c5c00c030b80940164020300c01030290212a104030345a1900440000501d03c0c4e4448002c0c12a91046070340e0408540590401c1042250402c2420030b20032500501c10f00c0f40d8a0340c1c2c0020a40702600041140d10340306280300c1c00c0341d01d8103c103a07071014007005821070b522440c00000c5104258022140314001607070000c19082641847c0c02990071003641070303c0c0c020010703100040722007003120f84802d040d040585506407800440c2841d00703044152814940740384a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595373741 1250 595372491 595372493
    0x515040206280f300e07081e0102040608010b03091e1c030507050412020d0501060b1c06060905330405040b1c0803091002160209130506070e0d060f02030103 69
    0x3c0348400c0c0c1056601401000c0a00740c002d00c4c12034030620134101001c1216070f2080c1d00815520002c04032040c0715040f5209021010030b510400150110850800d2030400030740c0000100414280e00540c4a100003107440440140710080491002d15030200051041390b00072030455400500500d010301200030340303030040100701143c20301c040c0318000e0542d0f0070b040c140300c64140000000c000307205038820000200700e076543e44c000f1950707074030f03010a581904003000b0300c4001e072603d500e203820f684101c55401690314420114007850f44180502000c880094032181c1c022032801c02402001081990f45203200010050716000300381540e810580c080303900c031110f161240d0908080c0801c80e80241030440c03103052107a151100e403510103041d01400d103502560700b0351a51103c105840ca01030411a9103569a800802c8000308001c40400740c1108034000c880030b0445031203015031350100b05030b01040544035801c243d000484a03809448030800d4050040c200001e660075a40326502164480c2c20101086900080104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595374991 1250 595373741 595373747
    0x201020d0614181b0703020a02040204063612022d012007030f03180b211e1305150907170d0309060b130e011107051504020628 56
    0x81498208030022040c0713043c9200300d8003240a4041d0907061842d4000b541c0c0003014400e0081481c080c3e80503009644950304c4000162030b42421400701451005903200301d101c401000c5240401031040691801e04e460704004805542c0c0d8200201640c2009214000440440c0504440103004100081c0c20710b00701c6081000518080120340e6a142905a800d21406030f01c202045540072240d001c11903294420480c0b400340c0b00c92608009041d0000c9003000001b8281e003c1c64000e141c2031092000300da00003080c1604070710383c0340816910131103200048000e0148101e0004409a007018020a20041c0400305039103980c41d018402c0c13840082850100140002c040c001c100d244054941001c1900b01c000000d0052503503920005481e10405407500312141c10700415503c05500c4503400b414400e002141c285561000e0b018850b040c2e002503280009010154000a05503103019901201810403803603078002da00c4200101030000d0744d000e4000c1040a40c2811160381c1c0c841701203121040603d602c04d042c2009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595376241 1250 595374991 595375009
    0x80d09050f010c0e060a020a0c09050103060b1e0904024c020d050a0e04020711120606150d0b10020709140c040e090709151e0803190201020d0614 64
    0x910180e030428101d511080e410081d13003265014203454654440426140880c071f0100d0f541c030060030b5101010f2000c1840d091710f0f040103043c2d85c01504240080840182400001d4400d1440d09201c020145101055032801c04119a00b15000030680d41d03d603184a1509090940c00b00c207259010510400e400700d00005038a0703220100c50396034075034085410810b40e0107501c0c1c00c50b02c0b01c0e440c00c000e00026a49203950140b21034641002020b88119140c0c0002e2a03c035420f080d04d82d940b10701c1540780701000303440c1d10000210a4402c080240c20484000c50010301116250020310b210043d01c2e03280c0c20001495210314002e016401c14a5005140c828503202c0303500c0440e1000c12581c400101e940c0e0030031520400e40300c100c03004c540106180303090036690b00032501d0603e4869088510180c0c280982800b05040400aa070305854201101d0080300441540800e11480a445003070780903001480820480c0c0d100001c021a808118000580751811595510b03086411980048802d0300e20340c0c180c095a4107080b002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595377491 1250 595376241 595376263
    0xa02041e03050a0803090f011e05090f070510050904051513051e090c0a0602060a0b0405011a09060d0e030a0305130f0212070b0d02030702010506060703050405060a0903080d0905 78
    0x180319542140c5910f6180ca040b40d001070a4a04008045551800d04004e040c00310040c81d4001c011003120541c1004000c880352007041285400c02002c61208030010030200302e41b9034200000c000c40f5144c14180b24245100f8241c5c0800d1100038401c60042e0b80300ca01580b4403d01c0301040c1003049038404002c21410041022849103820f20b4081000303643c2c1030141300081ca41328402c10300c40450342c40e01102842d0072040c4010b035410044140000907865000240031303000302c2071204e007440180148000d0104950013441021060f1840e070911a0032850001c00a045e4031201030f02c40792a000002d00e100060b50317068001c04c1c0c1d20781d00005101070415070512801d500102d41c1050780076650842e45640e5100e0a150f4001380c8102d109080c907003e4050100072250007018414019503d680d0f643d005903000303401c110b4401001d542401d000400710f2501100b00c80740b141d41a202d0318142800c003024020503401038021181800702031003001c00803501000150600c0780381191f004c2031a8805140c41401c0842a000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595378741 1250 595377491 595377539
    0x1509030c01060f090c11032205031b0111210703020f030301080a03080a09031d0418080301080f0a08071101090504020c100f0209030304140301020702091608060607080901050a170a0204 81
    0x107140c10b00c5146c00300454503c508242002d0050142076555207004510903481a0f030700d44201c04a640d841324071082d40b400c824000741c885110301c16100b00e1180d22441c001113890320704118034000f14242c840c840007805a0502910403105518046180d40707185034020b8014203525402007000004150748080b400342e11540e140c809000741e4055940c0900340114010041001c640c54051500b0725840700d504c07907030b680044d1008100680c4134501f000348541e03100780100c0c000d900840d00800e103c3c00c0009014008603a10101440c6045040c1d29201b0100203054030940c10081038840000344c0ea51240081c14680000e1805040700505100c48401120711100740100c07414018070050041c0d903400310644048071070000414814411800000f40248280c0c0340080d072081602040c454014503005480c5000da100746ca900840d074861004205190041d06402054180104451403865110390064600d466a0f820006800314542810038500034040f01c0d00f0407440d90203e400c010305400c4000302c55015641e10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595379991 1250 595378741 595378757
    0x5011d0912040302010e010210020f071a0f04030c0c1a032512090c05060d0c080106030504020a15021c050c160e040602031003052b111509030c01060f090c 68
    0x40408070680c0035521000c1d040c4481c000341c2c0800f6034000d000c80c01c4140380340307032045683d40c0500c074240c060b0781c021450550f20320500c0618400c075244031010f603a01601c03807404c803d40c3e240c0d00c9950443e001000301000700c0b02d50848400004050900c1100ca1131140c00b842c41460712464101003010b10130021a12002c0700034004c06480d034035640c00c03441403102144101e4000c038000005003021441500c996209640010002440d564469119802007401c0034050f55142c1d0a642e0703c0004606580c010782d00030f540403410b0001006410210b8141c10232804050040e18001c100c02070194020911403c82c8102145000031700e0300b80030030144046960b01440c8259070300035500340702810b0f80003031006000404665001011440c201c144a18440c01503a0000881d00d40c0d0002da1140c241d0100c0c0150040d044c882324400346800c40740900016910300c1b0000d8024181c079000a0f90040040c5800340458100d40420000081056002e000342800303001804c2d401d000306480c2582d00e600f1105819038220402ca01e40d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595381241 1250 595379991 595380013
    0x10f03110a15211418030903100b040506152a060a050702060c04260f0d020a030228021e041d0c030a03050a08070516061d01110a12090605011d09 64
    0x70329084d50080320788003000340c00c4100000c000d40346110306040964948140342e030302c088840d0944c0028032001000d071f0303040c4401c1d2505000d00c003044941e40072100840340184440d140070710354401c0c46040440304018200007100714800440c1040010386000401c0c03a2a6001c02c503140f034040054941002ea105d84250cd064500184089168401d0348a001c0c7d05904c04642900c01c0c00c100b01200c109042071007134a03010040f1800c041d40c1c8506c50300007100540120b00078520380d00c940028900c3c00041c10340c40f13540300b017120740e0801c8a804052500e4511000b0910140101900c841c4903c15489184998008061002e80c0825281c00c0741c0643c01f174865400300d1079490009a11406461940f8994188020b40b5201c0710416075503405059040c0303110501e10404002400120382103030601c1051080c4000c05c10040c198154284e80031440b02802a102c10030203408010701c03d440e003025900181100103014004c80e903601054841c280d000c05038140c0e18a80c451440902125000d80140e400c1c2c0003489000c0740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595382491 1250 595381241 595381271
    0x307051b0d122003010b03010801050705091309150501150305013c08031911010605030309100c0501050a02070b0708040209040312021207090f0608010f03110a1521 72
    0x48182da4000981c9071200748014442980350340c00700c14880d548640d100e42c0c548100b150160400d2241000ea5801c290204440a0040d42260306000d80030b424030320440303071021185019042d0918111003e42c01040f2216800100d4031502c0e0190000c2c1091401400700d14400800b0f455040c1c100c41940319206040c9003000c04034101001e024084d05112129031201c610010891291560161220b8000001c20205840c500381c51006a5042611410b0882c41001c4056080381c10f58010b40b03825510030400300300c051805c94140d40e2000d0032071400e1840c034007969031150b00351402070320a6040310f50081002810007a503164181d40c01243e505d40341340145491f80028401c50b002402c050309002101401d91925040c0f40c04590122850718004511400c0400004100d60024455603001041150003c0b810341c3c2304624a5049076001c10840191038110384580300c0c81c02000f18031030342c01040c40310005000e80200d02ca080c2000c50540f40c24902061181501e540b43c0e401c0da00292840e80342550040780030348 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595383741 1250 595382491 595382507
    0x2031e030f01090e0a080f0a030614090a0b0d20030c0d0c0e0c0d0207111009030b18010e0f012301060215090f12130b09030303130807080307051b0d 65
    0x41d2006004c070b03650080040250410441d9040070703040b40d0002a01d40381084c440001044070750b502c0d07079040100969880c40600f0300810302c00c94030361154900d03010448484440d04041c00c40b0700010001e03801c69600340d030b880d000d003400300212442c0c0e00030030100c0481034035080c402200048003e03900c141d080c2d061540e40c04141489405030070071b9612103d003c5021180c01400360340d000c0f40c40610441d61440380d800d0002201d1075070729841d4070a048400300c41e903040e48600741c40e00c200d81d13004030204800d89070701c3d4110780c6c007601000e6074501e10740d6076142038036480c0010000e5111000c49080001481d46101880300d11030002c01c80140020943c85004020240d400240403020000c422810000c07505c820301803034106091070541d1211449041a03061882e030030030000345501d604c80c0c0e84250110341d60703030080040790255003012a41600b0030710009214000c1c041a91103054480d5408515140c59590b0300c18580d081918a40000349001c86c100c0585010142c0310481000c034a00106401d903054000145600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595384991 1250 595383741 595383749
    0xf06050306070c1e02090a0504020307051507030e062215091809020f0604180b190611100501090902032e18020604150810120602030c0c070602031e030f01 68
    0x10300b8154004c44c100c0081500030f4103a560080400f0031a0038501042c90281400365800c0c0d10a02402c080010140385c107804040b2140e0084040c1400e003031003900c0c241ea40d01000854950804400c00c843c2c4001080401e420311241c20142402c03280c1030070008402210b00c03140400e402400301e000e00600c43d0030026142590030740082200810058214404505031940b00c2d124203801803008600411a4003243d809100140b61120041200c110881b080200c00c070322110030100444100b007414400f99200702542030082c040e01044500d14a00304189204448090b8800542c0707030b03943c00c4000c00b180707070600081d401600c03500100305204a071a56400b0201c102c0c1240c0090095070b4220140c01c1007808103891010b15001012591140e03a1590b60142041041440c80005400480044e0312820b41441d25021b44a83c000c81d030246400344e81e1248025400034007040c03264007040c05100c41142c000c02289000c0c00050b406542c072000c0c2501c041456510265808108007400e0041008041400001c58115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595386241 1250 595384991 595385003
    0x21912030e0706050301061731200a06170a05071704050606150f0f072315010b04140d0602041511100b0d0b040204110d0f06050306070c 60
    0xa020014264018500310710a1030480c060200005581504000610704a03015500e80f00c041181210585000800c2112021680a00c080400c10820103c1600345101c110002c100407000d02181c80e41000a4980d506112200e0300b01c4040004900341012440020441d03801d05011031501440901c03000e61009103d4002c4d1a40c80000039101071003101e02e400b40a9001070304150500b81800c1164488070204c62460144400b00d480480548041089030f25001d8400c8039103081c401d1000da000040d40c05500140c0e00802c1c04039410a100c40e41c03190042d440c01c403800090100c00c1000c5880300c9450710580c0b1883d0f214209101c20025241d40c0307a00541c09440458225144103002d1070204028055508601c0d2540c0720040790361aa5030704400b102c1003a82661080b20039481c5444a610141c03102c480045400c03120703400081d00011088109260450310092000c41e40000c110170350b2402e030300800d080d003400c1912080307403000320f42c1c091044c5405080e0a501030061407608003030251528240100081407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595387491 1250 595386241 595386263
    0xb04050c0a0815180109050c0a141c020412050f010b03120d150f0609150c03030f0905190615050a1208040506030709180507080c09040f020c010e0d0219 67
    0x850445400380104070310008080c0d50313003003d0f40795030743e80c203c08240240d0520300d1414012603c110309080aa80000e0b00702c1d5036080354030f0b07440344054505030041210224030b00c44031007601941e00302500140c00503001500c140c0490300c04600304640b41a1000700c0b00e61b90380c0d01d0024084819200070803906180c200131007000d540d9540c110705840c000c000e800790700400c0702c0c01c21030007040350344500c405081100c40325500e110038a0344589005200030001c0d902c40002c18607080e0360b200001e0194000d0031080d07040560001e81c013000c80d120039041060340c542c0e0380b120300080401081049000d2140c40c07a0b0111141e0007400240c2000003181030b460a5019130802441000307829410018098103e1b170140501910081e128103003400e01030320041070390056030301882c030084412000d1801c2e80300d00c034410503242d070b6100303881d8071030307031290303d401e6215540841c2c000b501c83d21541c1d01c10141e80010403c1140003c0006000e0101035440303400d00b0903aa684108541005c00a48101c0070301c1e00303105250503003088100382 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595388741 1250 595387491 595387501
    0x60d02030f07090e1803070c06031401060807050d0c02150415140405190206040f0b0415020f0a020f03070503010510090c0203070f0605060f030a060c09080a17090a0b1306030b04050c0a08 82
    0x21450189000c01004244580d1010440a6142c2c002f800010036150710f1021990301e43c80141c031850303802c455480005400340192584407001d034005141507600c600644440c03040d0454114454142240c0960b1403410003240ca541c4000c41b84150810840c061001b44641c0c10541d85880e110305900341220128010b09400300299030b00c9074100d50042c51100ca5082c1420b964110b40819500244501c003c43c822000812407040e00114841140014040180204020b40d60802903200c1103a00c809406104072200481c160b2800d2080a00410803000000005032070010804141c5117513034440001c5400510003c1c000602c4404280f01c0682d1280011500d17541d040040340080030380320b240c03540c54851410348000380140b81d800040301c0c26866460b01c1d02c5135164540b031070b0ba50303064010040c80005c18503005140e82410a014050a001c01080303c82c030f2035a5452981e41d181c0041e03042606a21001100b0010306404d4812015024010344042c002450400b055000500400300078400f0300c042c41c00024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595389991 1250 595388741 595388743
    0x4120f0201090e0a0b011409010813141009050d170f0a090614100509010602030a18050a080706030507020a11041802030f010c081302030d0f0905060d02030f07090e18 73
    0x2c0e02070030b0001540b040d18030345491900302411420000d1800700b03505035000b040703000180d42140c05021068568074142c1c1ca600c2034004110040060030f035110760a03022030154844080c4200c000a165882001c21030032603600b8944d042c1202c2078505400e101c00c20300e00341010040004d009a00494140e803000481c0d6815811401601d40c03100010401c524003110f9500e030415105065002e15889032000780d036682c4800074030803030345820302540c0c002d0f91060228246003841a005449220402e035814a0035681d1070011451803129500a1030094000314030034003400340d00d8850103520410600c020200f1072a02e403104008000c4898a15024684908014114034102122195a00ea02030106c4801042e04400a80284510170303000c400921441c2c080ba401000801171000311a800a0207483c500c0103070368040d90540b00200000303080c002181c030b0018041c0d0b03940018003071041100002507074902d454121a854180010520f0b01400305681c4140244044400c1d586c0d4401b010501080325420310350401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595391241 1250 595389991 595390007
    0x280c05180f0406060902040b1b060705030109020702010c0c06050405030d031a0f030312010f14030a0213051b072d030905060c160801151208030a0504030c020607030818010204120f0201 81
    0x1c3c0c00c403800010b000405030000d1005009d6455041905808503030382947e41030f20341105139840000a1014030052004045580c000d103400c501c141401c41d4042442d41d252110b009940d400880402c03008a42005641000c6c4080f004000280c80d00304148440c0364a0304541c41d2030003440314000e01c0241c2c4242030b503071410811501d0001030302e01c1066003503a4411400c0c4a2440d24029000c4810880c3d966a0860a0000d45880420b5000780301703c4484103040121130042c00000c0024040101c10804060109100350051140d036000303400415084d08852508038070346c0781c100340e155145030b00f01c0030000100e03500c0303030300e1509840040364440d07a50784072448103502c0c0048040260032070011461000409000540c0b003440e484480a094281c15662200c90801500c101c01c80a011000e0402c00102d04400685c850742e4418420b0400000c1012035401051072a00f0441d011400b0a100c9010301031320300c02012007403100015610013580303070a040c600020280710302c82200400c0743c0c1200b01000110f83c0180c444c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595392491 1250 595391241 595391249
    0x12021504031b082b02120402060705070b0a1716020d030f11040f1404050408191202030a0f110903031219020c160e060f060a02280c05180f040606 64
    0x4903603251384501d07101d00488140b03013080080c11003209450424028103402074034103124400000c03a07440e40d19030f001c0c482036030f02c4005c0840d2540503080b0301081f640154805010460b005940701c2841400b001121603a04402511401440014681030200079600103044012601c0c00e140c0800c0e2410759003001c00180140300811b14409401140104484140d00210002c0311070440c1d008292225880522040315030645001d015020100712101e0320910149000d040c400b042d00d07141100c800c4044561049030025240130f910503454503040c000392107050240ca20300c13184010301c252034182d0b004000fa40d01c2c41119025a20083c440c800500001e8401455900000c0a07100643d03441f400010200d8454005a80b1140c500030f8114001c5024640300543da0b111b04009000c0c2075040100004011041d003240c6001c50840c800e11010304490b2171078108000c1c1e00100103003405254511403800035102074441e0405401240c0018031800384190a82d130042e04000c03d0307402e071052503c0d2800c0442c042c10b80340e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595393741 1250 595392491 595392503
    0xb0d0b010504020a021c21110a0c110603070507051b010822050717120306030d0c050c041e060b09030606010320040308041a130501030f1d030712021504031b 69
    0x1721a403c250b4000030007a42c1f08860303440e5550100600d4070700c14121341e101801c48020000501c11100d00900a22499019502401c4c5c0d03000c1401c94440051040d9004860010018801282c80300401200300100341d503000d01c2c0313800720b030030384001000003407800034010041614600352401101e100c0140d240068440784c3c02000340c0d803103981c83d01d4000d080c0c45550182403501d131145030041d90303519011100f502d0040390010090140c80c656403104a950308101401a5001d014140c0c1c40a80303550303180318040385180a2140e0280b0180501c84c240212900c0368460010754504100a9580e41e601048a6900c440d00b400c00140c03c5414428404440d079210342c1c2103500b64000140403041c441c01101800440d5814481c081015100c1039011406003e420f83c1400b41c0103020001f880745600a400040400c202e000001078200710300e00100426090b50504019690000100c4500307000f400d1301d56084000d40f6000420340c224a180c51414419001080079041115402c42d00003d5151915001c01441d007004c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595394991 1250 595393741 595393783
    0xf150d0f05010c0e1813030e1c060b01050f0714030909040809030105060a0630020f03060a170307030f03021309050603060a1e0e01140c04090b0d0b010504020a02 71
    0x458082c1c000c2c00304105080c0803078030a154007441c80c0303040801401c0c0101d00280d03407400c94880c80180521038048807401c6061000000780300c03c50392a050344d005c90790246110840346800c86401c24104840300555450304101d0200085504140c00d4411105d40c0f5600622401807145a4140c55081d030040146241d80303d00008103108c20b000104000d04000c42d0200d000700556105c40303081084569907441200003044000703031200c64082c0320050440741201c40b112815000b0405041040880c0e001480301e03010000d010041c4040c0741040f02c131600181194540e0140e80d400326014450303480c05a514010200000d0099581078a84039405450404000103071043c003145e11540d404000c0c02c801c5924501920526000030700f0407001d4001d125460f42d0004106180146150014015049228000d1115074942640d0301501d240340c1c041d14403c020070f904094585042c0300588041d24000c80c02188203e0400d8400c03004990340582c0641100c40403500142e46989290080c0c2c1801d90b502c1d64004640114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595396241 1250 595394991 595394993
    0x509060d0c0818010b011d0d0210020106140a05060702090703021c290a1202060f040305011d0c031207021c0b070f1d060a140c0706170f150d0f 63
    0x110124a0090045a0f00084151a20f00703806003219958003500d03000030b011014010390004450040740c42d0107000307006448181000d4000c50b521380a211400c4006030b540760010003052100c602d40d0035044008603507201c05145410f00040b03140c0039401c40a84955010740100310114002c0d81115100d214100c0c418401c0c0300415440700003442d002c900e0750413030840740d402000707401000c0030740801000005010100709030410070305254002165504a07045801004080d03004031201e409400114490701c00818444030150040b50808039241840030554082d4038100099940070a00d40182d802880d4000e4032a6250f0000800c50252100f5528404100009603818859403504491240405071203406008240c00d0007160410b5001014116080c9903e006006510b0041d00415403001103151865180d6032200d031038015503009089030a0f00d03070300030315003080107907000150f042200c0c501d1590b21400d0b24141203000c5404000900318034000203c1242056655600a00c203541660080c1801003030000d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595397491 1250 595396241 595396247
    0x20f040f030317010e0f0a0b0d020603090102220308070b130602070f0215071110140301090903091a0d05041b0609030b06030c01140304021309110103060801020a050405010509060d0c 80
    0x4040f00c190032680d2404008110b801c042d28819000b18182078100545507103040d01c0c04c00400b420705500303520401101e000c42c0580d4400000e580980e0140c1c0005079078001c1c1c0f04c024001c821525914284e4040d15140c20408517031400242d64203590400040d45243e0b5810041c000f13065400ca1000382520300c08a0680f0074800c0d03180201c91a68425039040000b546401103458941c00f40d070800600318000f86503001140c0c14801d000944000707035420000d00c43c02216010400c5074000360005c0341d82c83d998400903406d15900c400d0140040243d20505c503040021801516242c1c4a04c6001503421619003022800b080380651410a01801380e4440715601d603250000180491540e2001360340580f0b10704045240f6182c0400c5000b04007070305846080a10f030f1900022081c03500000c0041e6445920800f8194020840f405400060b521406d041c0c0442c1801c2c0001400311040e5400c00421a803050005246072500001200c00341c0b442403d2690303c0d4042d1500090300e40c4030301c543345034100b41000030361014a50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595398741 1250 595397491 595397507
    0x3060f120c0f0f0902220b0309010b1008042307170c03030a080105010c030c120509011d0f060d09060e030702010906050a0509040f14090c0f180109020f040f0303 71
    0x22041e180c0c10403031540e900c0540d1400c41140a19040c2584100c03082119400360740c0100070700070b00306001881c0034009003031140500c001036000010366240001005030002e4280314450740034404482001e0000c00c1c11100070002e10005100500400309440070307090382e03040e001001403044114001c0314070325521445017a01da1500c0c004e008406100d020a502d560345004800da4514000b00d603035070700c1540c0c078000c01120f1101503408250240030088442d80c000c20800380841c0e180c124252101f0b951990f03102d000500c03916600003503010b61000000c4c10006950740c0c0a140c1c480590407100c15442e80001011100100b02c10040200101c1c0741584071000d4000c080084c052440c000d80700d0500381035481a00352554030840e04c1540015101300080324807071800e40d228904035a045c8600159540b01503682003440a0b00340c64010455120490080319071a005212003061242a607102c41c81308600d20000c8240c040c1030107415041e03a00410840000f203080c100380c40c024202100701c0c41050b40d481c10003520b461 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595399991 1250 595398741 595398743
    0x510050717092506171b090118060309030e120a03030b040e03070f230607030510032a050f01020a060c2a03030c08150d030e0303070309080c040603050a0b0703060f12 73
    0x102e14650720810320001d202007911891420105162490f1603a0940c01b00741c1c0000c0c4100c1c140310800400c120080c0c40d2034010800350455890000300880325040c06050350103403150045c85102402e048900120b0080395001c010360b458200030130402c1309400068058010747e40c0c4408584130105401c000c1c01462400c1031003082c000d00c000c480340c414240120703040c3c20662140a843c1d500000102d01083c0c46a4000c9034003039401c002100b403079134999072030b040c404404583c04902051280c03421008290341c40d1070301005107400c840d403076081c480e1000040d480b09d000c0354000d811180d5801c007a1135030900840300008000248008240302d180d40c10100886d4a02e41042980000d15211440d00642d026810030b80c01a610302c0c18100f03d251104040102421075120210200700800c40c2c03000c200d8404001030100f15119441c2d04420030b0900200c1d51405040510081c070031400e040c002c0020900100e1950303103041d0000b8149807155150b150680141c65a5400000c0c426002c0d90001900c1c2049580d400700e003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595401241 1250 595399991 595399997
    0xd032d061d06010203071707020a0326040f030b040804050a06080a0e06100e07090f06030c0e0306010e0f0c1c020c2103131104090503070510050717092506 68
    0x5015a8901c1804498044401c40e0169004206000204018089035004080b1a1490529215a941c00b06090702c102303620441d0000350002c21910482844134000d07500c4501c3e01242070510b440e011030300c40b008149100c01b80503050080c0104046c800d400c4100d4001d072001034030b040d00e21559040003d140107001c4420300320301460450500400385002c43e400d4001c3c00c1d40c0303440302d00d864100700e01440700d41400381c80301c41800240400003403450406a410002403c00e6140080c0c101b00460024043e9030014134003510a030058401400040c1101203050f4100d5408850044150b50b9961035024034401c07510580214500680c8410010500360003d003c4050310100752121031050028810340340c4403010704040d01d03076070520000c0c40a00031110f019100e94000e10034021441000c201003802c46d5139040040d22941c1000803a4418000e04100c0411401c9a070507040010745007a40c001441c540d055806054030310644000310b102890300700002d80742c24400503440c52851016199100c00241340d84141d4000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595402491 1250 595401241 595401269
    0x50a0608011d060d080d0213080601082413080c0303011514070c0303030203070302091908010c052706090907030902040b0102152d04030203040e01170d032d06 70
    0x1101c1ea03060b01c00350044030068072902502402da42c0d0740c04c0d01d4204031028a05030b542804800c20b03200d0214001801010302d06d01810705035042462043c103106048100151401140c3c42100c00e00030b00d10000380c0d02080c180445580300a80b0b2408600a00c1031489e4061a848080004600c0074a0682d01c9084a019511002000c1c8803000e0714071403070f001e52031000d40641003800081000c03d009400540d401b140c1d42c500185408006070011358032800c800f0104015804200090214400034070400c18a4510360034a90b0a049601200004614202c8041d40c2d04180a0388003000740e4030b40074140c401360b030b0300107020a41c18980300c80000c00400c4c610300300364892400e0041c1010340e940042624030701161195410328070341c0e68143d6240d0122800c103075a405050100c520a8282291010b510340c003461007540590341c0c43d482c0592180d00900180c001d488014070a0500d405003140010384000c001900b03041c007103007080c094080f190000c040300801d200071b070245020914403444203902c010250b070b036900c1c013441c2c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595403741 1250 595402491 595402529
    0x70605030a05130201020d0e040f090c05040b0f09070f021002030a0c03150503030d0513050a03021020120403020705060d14010807050a0b0315031e060610091e050a060801 75
    0x44003c012000a40907812000f04200d030305108e10009040000058400310301e1284511a0400300c4041840560b09a602d60b00184143c6c40c0900a810201e80e04a540c12220001c600004483c90343c0902000e09000f44580c03881e810a0007404000002d10341c1c41c4046407607180a20000300a03007640460040080e10f0311121840200b9407a8012050f564041c004500301f40e030341035000c0000d010103020006010100501075000030420000082c1442c442c1d800740c8032726546502101d040d141e040400c80c83d010000d1001d2900500c1c61002d41e00031414003c003184c0c05171180c0c14241c1c04e22030550030460308030400103090b101c803611a03040030084801c50014a1800c0ea601c0c0354150f1585064003445500c0300e00410300b0001c41c0b420601454118500c481060603000c01d0317100091602c402111920701c010707040c0503502c5e2000e00034070000742d0040003554801c18120000c00001c1125a180c0a6640440c2e01d40350451282c00115541e000501006002c0280c52912b450021709031500034070940785583e8084007258 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595404991 1250 595403741 595403761
    0x2041a0112060305030f0a0228031704050a11040e12270904060209060f030103060b10020604230a0503030406020c07082b03091a01150c0506060d03050903070605030a05 74
    0x443e80c104014605100c8101c00c010596440b00440d01e045200340180007070107500824804260303003d08a500c2c2e424031598500039010208446803021a0f122010410011442c0440c0711280a07a22200458480707040c000041c0040070031000b60042d900c2840100e0f10b806091030010001c041c44580310f0382c007520b10400d0a03445003816022640c2c100c806440402c00013170702038014101410005007000d00b410100754580e611901700b680300b9030f00b060304c5031092580c600300b10006c000d405440744040c02003498036444150810341800f0400082e62040b41d5014107a01e024022880607940c400c05a075900d00301b1782010001b0f0b40001207c0185d50054940004042500184412016803035140200c02d01c0500c5c2171104450b06107440050506456200040000e450124901c401903808a264034265040c01c00080e0400c28000c2201c040c8507100303032000c01244000421682c40082140c4104200e5040d160071a40d40c0109010700380c161041c2c5d403000c41e0064011010b940b0501c1c9041c800c01180c5d980b03031202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595406241 1250 595404991 595405001
    0x216030903060f0e150a0e0d051c060302010e011404170102120108070f2d0303050c010f05010501051803030403050a0309030b0601020313360c03110c0c120a02041a0112 74
    0x4042c0d0344001c0103103444e5605c9a02850303114540b2a00080d1144090b560300b030170408031300589000120006050f03100e0442c2c107504c4081c8506030340000c00c04c80e810742e40060010081803a9148c1841064154440070700810380442e009021214164110103408014a9001c6d42100020340d0580d00038100104559600003590811a04036100c850305075031400b403a03001c2e074000a0380546482c800c00c40005540d4420030601500440c13082d81c6c4d9a503292074120005085031580c2c110380656608200040150341e1740441500c3c035110b40c544a84800d0041c0c0c0c0700191844c031555100078907074002c1200c0e90041c1038214001c182200e000c3d82c0381c0002d80d6926401240c40f80300d15142619400b10902062201c00c0c0b41c001d418200c0e807100501700c0350000d0034050200c02c8401920303a1580c0c40d070300c945400d400180c1c14007590300c081a5980da00350500e02d04070b200588500300440418010ac4405250b018640b030208050030f42c1d03580180040001d040c00c20340070300f100b65880080301d01042c2051001108c0607614492 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595407491 1250 595406241 595406261
    0x603110303190503091009120f030507050d0c050403050105010b071209030203060a18020a08030a0f020604020f190909151409100c05040306020d020c010e1218040216030903060f 78
    0x1441c0c0341104800c07010344242d0000b411740303010361240c09a060786445030b5100c0c100c009402070300c407101a03901171400100341100400085080500b02002e00c01400d4000094504c6d030134440d240403440340b90400e02140c0f58021070307101a12960030200001001d00d9600c0040c1100c50250720316115241d5a8501a99405032a10001350507500c00000207a080c840e80d070000345041c1646e41d030400768002540004030507518035002032915400004007400c000c3c0d080700302a010b040007800501650b2509800103482010002c845e24000c500c00c86080c1c810841c4621a072020340500801045102d0150409542000089028500091901230850f481070300004040d44590b05000040040c6040c07055240003402c042c7e011641404014040030001035064005001155040d030350040e12044c80c80e10160940d1200c216041d5980c00030311401605441020496203040300e0307030214402480c0c008000c80e00a20030b10b20809000780004105804145d4802851804c5a000715014001c2d10354101a140c01c444110b55 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595408741 1250 595407491 595407517
    0xc03040204050a090b150907090621060b030901020a08011a160204181a060108010602120c0703150507122c010e0109260f0301120c05130603110303 65
    0x2401071070719401c02c81e84001c2c24800466461040e0b43d5000c4500c4040d180d60b03800c100a00400e8400b4100100400e44c000c54504e041102d40d407610700098801c12680b0f1300c3d0358201214100f00f000413200ca4016400400c00007070300079601d140c42c40d10386000350003401811b800100c5440001807026000c144503444584101040d03468051038984442d40c084110304200d8000ba19012401d603104850310800c0350242c0a400c1c000c941c201c00900e2910b03000001005a414020540d006200896000801a034a00c84448625071303a0002e0b210803501e00b050b9544018100c0101e0700303a503030624000d50400c030b009480c2511000055800d500460b0207458850b005000d181c0034003d1815141d80c10381091b9080c2c02002c100014100905428190964410706001c0c0c900d0342c004d1b04402070f80380041a914102c01010a482d500785460407106016503c418410902000f50584d81e070300a200ca0501d0302d000400c0c0c02020b0103402c035950450702018041c0d42c071090700c90014160540216040210480d9005c0250003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595409991 1250 595408741 595408747
    0x121f06080c090106120608031c060812090d03020a020a060c030f020a02010f0f030f090b060909030a020a0308150d050705131103060d03050d0f0b0f0409050c010539010c02060c 77
    0x5070171166807942d102c50220795901ea0305d0000d141c00d82800280001620200103403034581c02c00f02c0007000e0303075015070201e10148c1c015920355460720003c00a41707500782c004603000c00c21003529090072458270049480c040d600c050403c40010700941c00c04901510b051094403650040700350050141d80701c06024001901003004804a0300c607403840340303010b1903440d20300c0e040000d0805000400c0c2d0084840404003202e00305160b00c02c2c050240f404029080c0c2c0148034500852820020500084d141d10003040c00405110840000c20200c99102d42e45c228440400f0305001e41500072424850b9483c4154030130300703029084800e1540814400c0b8000d00301518820f41ca22840c0d5214070341403119038140b068040d01040820320020030240c21078040c0c851601c0795880042840702d03019003040f2001d0008005144614604101e082c00184045844418144242045030300c412908101c0d0103008180d111003041605103c540581d00862042000e80f0f00302c5007002084010b5004205a80d00d000981e103030b010400b024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595411241 1250 595409991 595409999
    0x7020a050d0c0306230c04050f0d1a070908010c0206070e01020304030203060408030601090315051005012a17040f0e0108010501030b0112051f0506010e150d020306121f06080c0901 79
    0x16045100c0010f40d00503074075031746082c401c1204003d4a0586500714403850004040000e8603180c0b42c071181c0c3d0f65040301c006260f04403954800c10a0460291216040001c80d800a03407054000d041400046c50510000c3c0284200008000e4440740200c0314800401c1580240c03814652001090301c045d44d034050010170f116204c0b502d61494a81005111504100a044012001845820640728190804400410641401c100c404134071a140d8011034104a04291440c081e5002e81c2d4407200c000179003e660046886050400c141001d402d40303039004090100080004182500041000440b880f14000140a0f42c854ac0700c2400d03a0301c00c0c480036001d0308010780180066160a4001d958507846142100e0140c081c038480b554804620003004d1140d199620100422960021440001c0c2c1e5000c65095910031001180400342d4012283c26208195012001403015141c103c0020062101642224400d220300b0200420481d80045005469403d11400103100d520015486000d0b010081481c4050780c24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595412491 1250 595411241 595411253
    0xc10051504051f08030c060f071d0f0a0f090b030d020d0f0219060b09060a0f260105094c150902040501020d0509060f090a1a07020a050d0c03 62
    0x41e0503800c1483c141c0b034011100741c00c0c0803040070080c035660000c0c5444031269541d042c1050781c000c102440360400700302000000c9a104600203500340d520311143e803e918204020a1144601c030702a25084014002c0200c0c5a4114102690480320701000501051812005041e155044d000e03017900580d104403c8482031600507c1001011100d9204840c440903000d001030341c9401c012a0140c62440e40c5011315003c5040ca203403643e80c4824151004c07107940c2c0c9400000e4400c03803143d21690503400700c255043c071482ca010b5038015810700c003200024001410052013107501c03100070204540240040343c4016400c68642c049107030500307a24080001650707500031a00c18502055012070340b1041d54810180450011250840010307001d0322000584941c24480060319180171180c50308180070060209406941d1100c0c1282c94000780c030100d460b21289103a01141d078034411900141501e1079100350031064422040040d01105000702c64041c580340c0d40d8014008504812540501101390006007130020400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595413741 1250 595412491 595412501
    0x52703071e03210f05090613080307050708040305011401060c08040b071a0a0c020d0c08181908030702010e0d050c0907180f2903010306090302031e0c10051504 70
    0x406820008119000001d1842e9050f142c05802e0719041e9641c1e01c1502100320910030541c0c044422170080030242401040048202c0201c4001056050004000380d0500d02c0391080d224059480400706480e03a84928205000e890060300c891403400038a0000559035201e02c100f1007403180c0010040d40303414105119400c0a902585058070141c80380d90403141c1d4140d148100d00d00c1081c030071000007104004914002d08000c0141d6099042189420044007c50400421686510703020000d40a205401d000460818100022074110700c100b001800125280044020b1040c02e201342d8030024039541c40d4081002258500034041d04a40c8598281200c078140109072603080082d038142000b800c00c014155442189284d00703c0384003081c0c40300e000c120500c1440c0040c410081c600d100408141241c043c0e00c0c140340014400940a540c883c0310b0720701031600078411110042c00301c0e05802010055254208034a521104c4c807581c1e0792003116041d500d10f00c0c1910400d4081c06001ea9414005000e002c00c00c40605 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595414991 1250 595413741 595413743
    0x5010c11030a0f05010b0a0803180d0c030c060801061404030312020703090807081b030106030b3909011b03020601180608010c030c0f08151012052703071e 68
    0x40b144040d9800412107040486003420b20501c004075031240040c1c1481008480c03680005003a52081c44000d0010002c0008904500d40c16515002001b06604001c80f1082041d4400307032581905610104030707568800400340c16036081e40c49840e610f0303903290310544aa12171840090006500b01e4900b8000403007907002040c505020b8644182c03c25250810386043c640c41d5030041c80c1c103502140c580b01e59084102e650f80c0034110200d00030072680c2e2864685103103610000f4400e20002c0c5020103082c045460b1b02041a2800e424030303007034114828051208031155801482c3c00c074007046180502c000c8403541c0e92010f100965169015240c20391074603a2101040451104003100c0c240c460f080451000024440d10f200c610503a54082112014040041c2240700c0c2030034520204500841004102600d15a140721503503820380b058002000c40c808210f03101c0f28455110300c500d074201024000c5800b451880002d00707180102449450640d00900c65a0303912484000070100f001c1030202c48080460001e40d00407003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595416241 1250 595414991 595414993
    0x518010b030c03091e24010f06050306061308210a0f03020f090d050304090b060408060622091b27020c0f0303130606051e09070306080f0f1605010c1103 67
    0x1a201280c1117880751104014071511680a007854000400003410003098012001151400c13550500b071024507241110301811060140c0000400d1041d22440c0488404541e8a40800c0342c10303450705206030b00c505d450f640004004224061201624040004907501c40c52552510003220155200540280d008a0446d4001000034090320625403518400d18101900c81d0303000d0340d555428821203200301c41100881e0340c02040240414001e0304400038803650801c1d402c64005c64004560030121100404c010200c00340c0381c1c100b405001c10022094021013084101c440d01c400c503561a011600301c1700342d00740e45002c0c1d2800c2620080c01c5840f819401424541c88440540765417040c0024841d10b1544151845a09494042c00440500030903200304806468120f48849600d00140d6505c6d4030088084031451007042d0a5020a0445010354002e10040c40e41000f40c8460031050000c0c683c0319094000d007400140202c40500204c01e000428240c280d81050311100241180398458400030f100204245800d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595417491 1250 595416241 595416253
    0x1360506070602030609100510050f0f07080c0c090915060d0b010f030c090b010e040f060e071106180a080a02031e040302030c220e011b0201060518010b030c0309 71
    0x2500c550300240403650082c2c8001d6940e040440910180c410010b0500021800c0c01ca0b003440166262024051491014030f46030752190700e03400c000807492040386190721801b440024040200448607000d46412008181552448083c240038050130503011900c47d04c007038016100d0b03803880c1c021480106812401c0038002200c2c0d03071240d50340c0b070703400e040c003038004056040c01c1040c100104a8030f00d41201c09820044014800880c0100c0081e25410940020303500ca1519219801207030001c1d5480b19000b80020505803505040045001d00000d1001d1a0034184d4041d880000b00c80c0d01a442a105400140d440201403550b069100c00c40f1a401c0060300c0c0f400c5020400040c2c6907072941d40e1410705501c0e002e15804c0e80d40c51651040500d0590b8610300710b405002c01c00b45c22030440203205808030b0300d03240d952000701d0321515503c031150042c02d050003107500d4480c09220421001e5415800001601c04c284c514000749a400005080340d40424442c110701000d040000982c17044085029640000d929030032100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595418741 1250 595417491 595417499
    0x60e13060515160605011d0109060803160f0b070e01030e030301030503090d14010c0807110d02063d030605070504080316020f0904050a0c0501090605040b0903280606050136 76
    0x1080d42d1302039010b200960118587c07001015807040e0602d00510f500401044482c3c5401c1720f2689030302949a0800360400c0075200d0b4001d006141b030f4102201e030344c2b19403001d01c249030144000c5d003010403501c00e003030001c0e182400308140381500104a90590740c014000b07504210980b02005000045040b08070313080d000b00f0000d401c0c40c036001d000b803071407141d1952548000c51611714001000c140e0b01c0040340119500a82d5100c0f84d0301d40202c1c405030081100c0c00b0420240d05403004031500d044007644500310280214a03403103c000b4803040860152881080c0900403601c0d80e0000b100d4034080c5018001c115001000b02c80500d080d911512042c0d0b501c05000c0c810a120030342c0010751410030803601a02c05401900e0752008201840440a000d0002403c240c2d204a052100084c03460060b8050111300c080b0010b604081d6960405c02c40c0001c8580244003001c1030000e2115071072104800d1011200340d8200000070a0760342c010101c01290507a02c1e038004080320940003041002d030100c960360305020007803080045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595419991 1250 595418741 595418753
    0xc020307060305010e0a0b010806010f0522080c0108041a1f091a0301060b07060509101d01150501050d0203061201020a051b060906240604060e1306051516 68
    0x5001005942c800084941c0341407008014104014500b0007020329002e80320096a0f085000c041c4c1110003880e00d1047e40c840ca08081e142d0b40311781d113400c105401284c0c91025074503d41c01c50341c07400d58400c0c506031050107106900540d4030748029038008281c0c00000f4011074045d400052207d030320000404c20038103041540040249268242d40041146a40703510802c0b140d59000e1216211101045e0009c03c400783c44c1141940150203880d100a288984078800300d24102c008010724051095050800c00503283c5140014400c1c0c0c500e526003200702d50801e010b104048a444c1d150b807045a4040e1601c030300d0701161081c6040291720080c84640d005c441000c03580081c000074400ba00342c600c12926200e40d07070f804401c0100e01254210007128250750007001040001240070861580004c07003d110301c41c814911026400c608205c0012240c0c211101090000d08a03900090f1051151819a4007598030a640d8040c0b6041c1d45060040c2a08500c8034251405481820b400401c90080c0d810924403594200d42d03202 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595421241 1250 595419991 595420003
    0x30f11030909130605060d1e0206070b090a120305090a0f0f1506051203341b0e010801050601140f0d09080a03060e040302190c090c030f0e0a051b010c0203 68
    0x140078240c1d6100f40c541082554032829800007012030f05079005400710780d0381414601c001c0002450b0900d140700c0040864682e501500c19050340489a4070407031500c1101160317500031007017081d9481c030280300300750040740d0092003124011b40c5420050281e400103516842c100e0111200221542801410304c6000f090380700d50000700c0003105c050041044d602c0c24007008000510640b495480760403c202000300f400b0301c0700c01c28400c1d203242003003140031908ad05918010303081d05240103070060902581d0000402c1c2000b5160f42603c14540c0c62000a980316050b0600301c0e0000c13aa030502060780000c0c1e440c4507030401806000e002414400d601c0c0ba2811064107482900c80501049881c41804211142034503018092100580419000c1107003614003524025640c80d07801e0040b4420301c0d0508144004c4c0002c0c02c4144000d0140244140311100764902d000b0020804c078003000203400c0c60000e035030950700c1d008556a554960003c0080118455042e20315040c4241c10541c5e038144242401c404005031028014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595422491 1250 595421241 595421251
    0x501020c07030c05040209220b060c1f112a03070302031b0307080d0c0306050d0803060f0f061c06031a0702070608010e04080c0c0a080115080703030f11030909 70
    0xd04006071841c540f04042d40426008244500d0043c00b140780c03d074403054200072840f6080b000381c030820b0901c2107100004081c804481500480005200160008002101a0b841d00b050304414200918064250111840071340300803403090041140c941c4100046100107039200505110002c1655507440e00c5145500a501c11405078202140d031211a1214111480300c050305a8040d510700080c0743e0b18866144500d00042409036680c2030f407015540d02c698082c601800e005045002400f4140c28400220781046900601c1b0340401c40301c1d02502d007480d0120303032034140b006405641021882c13220000f0100c2280e01541e440c960710a4000040740e004480481d240030440041901c5040a0100034104000c5400c1401400350290041220103508503101b98455004000c490702c41001035411400c01c5410580c01c1d9018040c00e1011a9665041d4000381c0ca151000180000c42583c0709032194540d01248000340220703250480141c0714038000c0010685840b5180252882c085141002030340c03c2e0002ea131 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595423741 1250 595422491 595422493
    0xb03101523030601020c1e090106110c0a0e0a0e1c210e070515370305150420040603050105010822170c0106030f022107030b0c04030501020c 62
    0x44a000c41000000c00e008449040300c1d903061035442c00b070001079992803c0e41c2006000310382024281b00350a038610012507003420700a003000c41c1075070358400007805092410182d10503801041e01d803030424900003940724116141443c1081c5c0ca941d5101400303005080c0c803400000580101803030982002c40d650101140a40f10b0340b2490b00d40000120165071031248010b041c00c6c451310307080c42d03400c01d444e00046034400c88804071240542d080d24100b1311025402105e1041004500404202852a01c00d900c400c20006000281d90042c0964540884c16180e042d104000029410217102d20130f410b00385c01049401504848078081c0c02100500c000055020741d00810000f03507144014085981e01c50302c45038006050b0b5021103120145040d0607a40c941025030024410881404c1c02c082d006030490039101d410070804020015140c1d281828909030b245032904912583c010981c0d10b0032a003400d900800c3c1807a0500051405c5421580c0d20001e03040c0240041c01c0e166010320000002a000340000c00070101c0441c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595424991 1250 595423741 595423757
    0x60304080d150602030f0f04080d0207030506070918090602070206031603050f0c1902010609090c08160f03290403030b09090d120f060e16140307090b031015 69
    0x70703019104403960700898681c00100e2400410030180e000040e01d04900f005e01b04240c0e2210f0888a0300c91a101e42d52054615020b02301308160015000b00e00d2804490140b016a012656403843c2221a10040e000e00141803041079904441d60340c9940c004181a031241500614050355900001d96036001144e880c1c1c10b02d403064000c0c1c081070341c1c07502800d81c120098241d03030b42171420b14400e111810f00410891003510007102190580d0a8400d4004500600c9402e404000c0d2842c6401c0042900c1160300030080d2034410b070300407901d00340700c5040340720115240000711690041c00c1d99155201003240c20b5000c0e5800c1848411541c5491078910f05038040c0d8865100043c5406a04052028802c0010f00c8030040390000c00000a94640207103100e0866059040c0024500500441c00d1000381a076410001c0c61201503030421070b00145d8002461207190b25512103d83c680d4802460f00c1003440704403140d0b8005544078008020800d040d60281d0b400a0318000401120b5403281109a8010301e4002201c000440380 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595426241 1250 595424991 595425007
    0x330a080303040c0f1a0901030b15040f1a0a020309010f020a1a0601120e0d0c031e050901021b06040e060d060c0f0e0105180d0c330c020904060b060906030408 69
    0xc1400000074984005c0042c03462021209000841c040c2c204103e040c0741d00c410030700c02c260b615406494401e0005c0540580c607151206035a0450096034001c4403000c8010032050b141200108056030300c800c800da8019490084a0b500440705441c40d410f030b04081d4411130402100103000c10413065541c0880415214082c1380280004211910089101c001307246016040d110155012580e035065241c14141241810114074040725101c00710302501c2500d1200310111915250b01c4002055034020036400c0742e071100c0c200391194030700113031078032445521803010042007003c140c80b140d0190384004003c1818141c200c07603031151400d0310503203603500d400101d0720600b0400380d43d00140b02ca40c003040c0c01e00c0e00a040800fa040d040350359045402c04584690181c9490404110002103000040e212140001001901d20424400a07441400c2c0414540e90b01440984056114003441202c09400500100b519242c940300d072401803540c80603154100030100a08041c5880e044000c0d03004610480c3c903582d0392110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595427491 1250 595426241 595426259
    0x815041e06092013030b06030c1e03010b0604061d061b0f0111120f0a1515080703140f06060d062705010807030311100c021005330a080303040c 63
    0x5000004411030000740581100245136002d5401540d03403143c1401902d403180e00000e0301c0c145000034003560021000a07a03511114883c020a00603120a400a100742c412280070071039240541e00480d40050348030301c480c0203071558060342644003041c0035040c60325100415540c000400707041a132010f0340b03a200f8940040080400d2042c1c050480002c5071103800c00a02d28000c03400310502410300c41146802c030700422a10005580161000c0314003140e81a0860340d40c121b0081050710b203500140200d0324050018000c103001f405518014240ca41c03400c85c0c01d684401d06421468406484136801c20001e201e28241c1d80c1c900d100f4080a480ea884402e03911620610281020000054500758070f5800d003401003180100c0011030f0002d40e641420700094000c446800c039850305680c5640c034060141402c900a444680100d81c0030144e070401d401c1842036a80d0031601c41c41251304901412106030361500d04a42c0c0c05030b0088801000c1d4001024007002580c1c0f001d00c10314540041c0d40c180c505000c4a9020015100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595428741 1250 595427491 595427531
    0xa020f120316031a06130f050405160f020705040e071a250303020f120f07020a120f0309121e030c05030a0203040f02090702010510060815041e0609 65
    0x20160249807841c82d06070b0105018244240060081c140c40b00b01c100400c05811008a000103000b81005868000400c500084207003580304190054203081d9011809060a02501d80b00c0c080e21460001100580c01c4d040f500003480130a0a001c50040f4100440c450307136280200070017000090000c044031410080000310412001e408005c41c0c01e020040f0491003001d981850900140301a606c000e00b00c1d01c0d00b030990291040507140d980c2c40700009200051000310482207400354806854621036230351800d406030f984040b543c074040c0000c140c0d640400851031141d0029002c004042c41c0104414034140c2d01c88061049641182002c6445807062281c13950409031507203c0040d9924091184010702e9901600d28840500001d03140d5400100080501015000a082c180e901600b80787c904d240204000b0300820f400e86003242800310b604400105c0c0d0b071146814034094250f603074100000200ba101080005c110340c0790442d8082260b80d4101d02521194450031004244525000c0780701c400400c01c9079601c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595429991 1250 595428741 595428763
    0x10501020d020c030618070b0f2505210d050a050609100e060f0105090d0b0106081803120603070e0c0a091a0315150a200a02060f0a030603080a020f 65
    0x98050b45075400c09560004140742c0220015a00421051011b0049801c00700300740c2104c01203140000e000680305001d40018408104004600b210070000480e00000c202c60802c1c02412551040b012a039641c2c0303075001c3c40845200c02c810501e1608101c5142c040503508101c40e20709000d562942004030a00f00741c0340c8594003044058045000300c1c10b000790300180550261003d802642181154001c0380d000d0304c12151709500c0184440080703a240d1a003180090002d004010004003103401050420442e038400d8100c251224025504001c00310408904070407008114540c1442070580020b07544c0c811003191802403000d02800c50307880700c20180143c6154040c0e44840326104107000b1111041c1d05100a80303800c1401483c0c3c0300c02c6640d03c81c0c0042d20203418504035540d031103030015940003070a40114082c0324160030743c40009103034540355103090f440f02440700d006034000c28104040070980b0a464010007805000c3d00740064465166103440d61550032402045000d6801304892941d1124100800d0380ba003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595431241 1250 595429991 595429993
    0x50d06051b19110313170c0a060e090a0204150210360f05060a0c110303071b08041503140f010305030d0e070e0a090b070503070804020f0607120206010501020d02 71
    0x40800d1514542c40300005003002c1c0e00304424009801940c0005004030355400c2250403c01280c0d07510341c21200f154070742d0f080e01121035102c0d42d8641c480d14144004100200c6d0410f88aa0001421340c1c0184085940d00410040c6c289908220225004800641c440729684499004208040f400c0701c8074400c803041d8402ea03e1048038201200100a8441d148290401d0030001c40e541c0340c128a843c00c02c040c004080b0008009000790410025000001e50000e04c00d20705941e6051100c0d108401526160f220545910001a0780a00b200078036a4001000c206010712030079115140ca5510030000c0260521022074100107500d07801d030740c01b004001c0065190400c01404070501d1035403542e502c50343d8a100c1c81a055002503216680850104401e0080d41700924003004580020320b06a240200205501801215000c807400c0200d902c0a10940540f4441d810503141d001c03647e20389400f001007420790100c202d64800b0b010400d8400046642c070002011203c0c40c0c00908807541850000382c10114000300001c11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595432491 1250 595431241 595431247
    0x1140406053106180f09140607120203090d0e060d0608010902040e010e1f0212010f03051204080604061e0f0e010c0e0f0f031905030a0f0509010f030b0a050d06051b 72
    0x4000b000c10140f440032960020710712408100145c003030303c400782c0050110203c001038202841400701d0454468000c680d5004d00b07101c0c10400300d138102c0c00f0985012450703602445d100040d9600800481c400414000c2c805410400d092003002c05075283c0d50010720042e51100d80c66011410103000d2426000d40807070081c0200501d001030542c1e5400c040c0c10310300c00384210468001c100340351941120a0010345031440c006039070b1140d041165485040c40202c40501c61100d0381220102c08406540c1038844402c09042c15846640707a0401405070312001c08041a10110509030b401120702c1041c1d000c00008101140d0780307224210072400c49000495040600040c20908c440039540d030703c26060450001c0300d82503000308403800071a03d4000701e511800c1d440b000040e040024048000007400c1c00b05a10f41c0c1e0f1858908543c1c0b011500c0f40520522640450850700b481c01f0018080e40140d801ea07000940203100e61503803040014032320031f4042c4041c1c401644d40e00500001081d1150054030b103154641c0d400389 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595433741 1250 595432491 595432499
    0x60103060b03192406050d21090e0f09030d0f0504030f09050a05060309100608030c010506010f05160321060f08210732010e060402030601140406053106 67
    0x4102d5807542125141c841c2d1210710400e018070140d1040c170190501428001928510307140c050300e113081c2e20092040e11108001e8040c842882600c850050320b020100c2d0003100c3d2103101002d0a0411b000d003113100c80740828090141c1000b4148074a09140340e2140c00801c940c2003500b000303408014202419020008200414401611080e02d4601116002c0c0d80407683d0f03544100203542004600400e5224190030700e4000650024004064410808240020841501da810041d01c001c00300d04618400309400b03100780d40140d5405d079507016103e070103410031740005000c0902700c240401c2520711070402d045d0345841c14443c0389569143d00000e881a07000030a800401c1181c104480e00c080c40300765a800800040c8001040042d112041100400c40c110700355100d071400e0a1044041c0305080c9040f99842c0085108500c400040d400d4080c0e90041c0240c6070076400d22034003151000404882a410a0725007900040c1e0361034420055101400d013101c40c020700140d40c09120841c2455612802e802d27814183d00f80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595434991 1250 595433741 595433753
    0xf060c101b120c02190602130806100806070807030507020316261c0903180308121e070e04140103050109211b060605061207030c0507051b01020c03060103060b0319 72
    0xa2011703030302000103448091752442c0c05806032092200f0205c1455001c1c0d000a10600300065803402848000c01041400b0385501c8010b603a070b035081b50294005174140000c104041c0c0281e00060b004100d504c10703a460003400d280c820744080a1030344110307084980c241c80303500034950024a440094140c1c103801c034900702600183c204583d840b07180d4074560f40d64681044080500480c07a646a2000e2a48000c6071591360b800c000b0744039044050480380000e6408005441156044008002500c2c1d0100d6180180c641060850340c0c000d103401d429400c143c0d5a02a485030318420601540210300c01c00011031081c216180900b42050300550707980036810301c01c0d5110b074016001100005000f548554000c00710074142000c1e0068003040c3d0010341c020b030300016400040c0c20500c65a0b80b0801864600303106403146800121a85d100d14100a05260404010458a0001e141c0d0503058503c05104485e5034038504400a170506400380d0007243c4682e51081004060704060120070483c840710101c02c10068050b07102c503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595436241 1250 595434991 595435003
    0xd2102030a02070e180d03020301140103061508090304171e0a0503031603060b041d0c0913020c0715180b090108010608070207031e110a03020f060c101b120c02 70
    0x41400b58040b000084c1d00002e1243d92010100841ca041b00e1221004500c0a0001e40c0b0038001e00e54070404565080b50f881d4024011141214a0f1424410070030000302e500300d40c4260043d01070b116500041000017101d14258a13018141d00c5120003400b40c203c0718018070b2040c81c120049003429500b081050002081020043c3d940c00703003104003c1803c850041c9411002441e46070003081c1000030101c0d010602c098030100c1d100c400c41a076101c5107041d07198405822200d0003151309656002c0c01d0f81d5110301e5408010f4001e0200713003509404480c241070300e444050b0004482c1c811988001105420260000b541d040001c00c018074040300400d260a100c44002880f8000501030a804e000032040420011352003046010000c5070030618001051440c1d048030201070440440c00c3d280c1c1c40d618402400c070707441e103c88040200c0c0d500501c10780c8003403000020304c9819004509224198010840c0300c101140242c0241c030b08044107040000c007040e107002c60280c40c603040c2c1011150082d1401d130051030815000919 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595437491 1250 595436241 595436249
    0x1021c061a03090703051b030d1d150f070311060c07080315010c0b0103030503010f0e0c070b0c160b04061a0a0e06060702061b0613030c030804110d2102030a0207 71
    0x4481c1e925690425103c3c91321010703500041862140b9101000e01181c40404060948011002d07a44500581030382240c003110b144601c80c901c100110308000c030710b19002411811048210301203c5c180502161100352940240e00150049803206006201c01502848260f6020300b902d0001c5040000e00d071036109950200804a01c011004240310603016030045041000c55944008608810740e102d190050058000b032040201c2c1014400d4040384200100201600c540340c2c0d13400c072904008007a200c25907201d101401e2514030031000c00200001400e400d810306207681c001e4852040605051030060103e0304031640030920411505a968100e66541c01010b00701c5620040040f0f50303840300d030b00168061007907100c0203611103c00900c0074a07040e0020001e80380d0103d28030503075010707603129102d070740c118001002c008000030015403951001070b020b000c201e50407038095019040141000c1740410080c0740302c841c0c00d90f0252a0303000380070508107405802519404092010750b0601003c01006940d468903401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595438741 1250 595437491 595437539
    0xd21030b06191d03060a0b01090801110d021315020705010e1e1003060b0d050a0c1803080a050d020a020c040623060c1501030b01170a0c05060c0c1201021c06 69
    0x3203084400c00c24040d445803e090b009041d200d2904003811003900a008140001c5d0100704c2881c80050383d0101803140307264a40d1b083d443d007031034602072402c0c0a00075408240940080455158042111071070004003188541309a0018004141014005805410445c0d03501d03124112611f000204141c920800d1f1400742c80035105d80051151342c007026005048103801c40c7d003591802059110404031560032141c06000c41300010014040d2081d802c8071038960f24100100045002441080050802e02c014008208a45419410040c1c51072182d0140d90024075040010b07881042010810301d06441141d00511051042400d8100321841c0b080b5511103100c81c080c4154008075500c12500001c1c081140741e05a400b400e05a19a1a032814400d81c220a0150401e010300c1d5198a41e045500040c50301c0e180c94110080070030f0380d4504010031802c0c3d40a140403041d0390190401c500c5c51030b10b80c807008030100c240d43c40003d40c580401030300c0340c1003101010b1420b40d215810024100078900100035107007040120f42c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595439991 1250 595438741 595438757
    0x320303240406270b060a02060412030b090703020d0c09032301060302060c2a011d0d0506090106060f031406010302131a04090b27060d21030b0619 64
    0x140000c00802d15980602c035150350102c3e04980440103d00300c80c1c1843c25034042040095100d405015180c01141c04070400360b0300100c003090115400185200400c1c6842c80c01080801152000c948107403025107800c0007003034021440340d06104070350091125418003407422030445407540d01d4001243e1880640c0c03540c045006011aa4070313030400c0d000080655009865075a4840f0040107082d55803901805a4030745c2d408982100c8000e14a203403424800ea14165540582030b511070002c3c1c4002d2007040c540035840b0b01c0c01843e84002a109220300d52041e46400000145146001c001815111518503c00100752030821540c1c100800360100c29006402840d0050326500402452302e00d061003600980c034210840146030709100101c40080c02518082c034400d00c6408403103000e01c185c000607512100b85208461050402c0e010340e4904450380300c6802450381240d10046c6d114021000c0e503003808002215103451900803240d0f0540100780360f000c01643c9551400c040c8a8461b84019848441c84042107444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595441241 1250 595439991 595440061
    0x2d0c09180b030318030606030d17130210020616021f050a2009032418031b060136020904020f040612060e1b09030a320303 54
    0x265100741080380c40078003240d584041041045042c1035484070070700e200303210b0000010024140445d00b640540d640b5260f41b200100c0344940c0d4009034200800005030941c14100c0d01002d40e40b017002c440301201a50b0054096401d200040227440300680103008155481030120303e2400b10070300c4402c14058550700c4000343c0341c1c403804904800b42c03e0748408650762507210074004902004103801404484000c90458190b0340200b000c0021003204c06202051108810000907031401c86020b05002000807202660302c0c19403410f442d2284000712554003c46503100791f00502c804288102d07850441030122801d440c201c1c94140708004641d6610210007402c0f5000318211905d0340319030b01511994280e0741d03203643d00d80b51034443c010410a2038068099403242040c00001e0307a038200407001da0103604240406425101d6003400124140e00820490350503105000c04203001c1907440c45000409000c1e4003280204911052000741003680c01c20b15400183c00c2042131000240903403c034501c28109020341c801300781c088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595442491 1250 595441241 595441289
    0x9050303180a0e0c0318011109042309011409010b0303030714040b03040605091b090a09020a030206070f03020d090f050f12071502070b070c060c0f062d0c09 69
    0x8030f038800300b07a440d00903052014600800000e54454a030009124500c00941d0007010300340c6d00c4114445d80720f00c0c410040010070303041540240c1503044002c401484c0c0e00c10b43c0001500c07400021212120b0995440042403030b0040852003d54102d20340c1d8000744001c01301d038400241c8a01c009000b180611000060030b409041c00caa007510000d0944013182600ea00d00703070424a01a00040b2107000d0903020318104604218075910140c54400406012031409981d17101e5400d005103d41c1d003003a40c0c8515410030000c01641c1d24002044820b1144924618500551902a14103503074409010144201c00701c060180130304181007002210780440f1020207903a01c24000c1030418428000b10401c9018207400800d24401c1c54010002c0090030343e085940d219139a11006003e030003111401000c01054610801a0910804a689845002d2580e107040404a5524803084440103150702c12480f0150f8035130240206420042d010704e81104400b840036000420008040301c4c8640074500549441415031848410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595443741 1250 595442491 595442509
    0xa0b0702010912031206060c0c0320031002090a05060319050414010203040c0513150504050a02130e1e06130f0f060308091921210503160905030318 65
    0x1011020024501d450138010080000150781480303890400e400021218410382c0d003003109980045c412039113582543d80340d60356034130301c1c1a54603041d802007460b60885030340c1032200d0312030146421001a503500040043c030a4a0006034400c0744505000e000b0010704107506101031403640c15991002400ea905e03450003448551030302d4444030456101104001c100072504c00d0074070590700210340c80d100758030911100109895007103440c1c5400701c0f400f101c01c0000b818503401c08d54212142c003a025041c12212035000e85c81a4242d403110320403c07100000d0010081101d40c05062440e0034880718000c5241160126002111010003041d04680e100301000040e04907a01c442c51040e03c004040c0319680c7e61f8101400540c201440d0207104480c0420f030200c603d1040b2000c00700f00e0f040340d14403140d80d1071140c55000084040d094141c403c54500c02050040300c84041d0500c049082c0c50302ca07581c40e414226a417543e054101411041400200345051000355400020340d107200407a590030b03000c1200f0000200f2101c030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595444991 1250 595443741 595443749
    0x5120703122d0e0303130320030d08070806040212061c060c0504050f09160c17030a0603120c0804170a0b010b031603060302060a0f0302090907020c0f0109050a0b07020109 75
    0x1065080c2e0880004140d9100035260304159481da8034a06014082645034800c11040311010107074a48200300203202c4112100f1049022221091840100d40c08641050105500030001580000412a0403900402e0341074000ca0191021800c25454008034910b01c980079000d5445640884000809102460702214101da8052014400c1003644080600650018015184503103420031648040741405d840240c85500003400e1503219000500c0c1c03e80c2c40905c50642600c26080c0c10600c1c070302c12301705600107500501e0840700000340c035461401c1540580e01103c07644000c00146619940c0881d0020b030640d415901d5070454501c101d1100740030f00c1d1802d003000c1002080c03540303020000a0003a900303002461040421002c4400c0c000d0303292400b242102c10502000358030200902914140314850005110f4620960900502d448500c00026200c4041100c900e0300581c003203400440c46040c00a41c81240310403e00700412450306240001d44078a80034040e5100043c008159039056a2080080030020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595446241 1250 595444991 595445027
    0x303050c010b220b0f1008040213020c15010608041a0903130b07060b0a0e070507020f031504061b0516030c12050c06240f040e07060c0501060512070312 67
    0x51801c3d403280d00b101c0e0008048031003401e4682800c4030800e003880000224031000050018640b41e1100e142501c0101d80038000ba030b003007050660301413043d4950744000c11240e01e03c05c008082c501014250008202016003020081140b10004c0c4400146010003504800a10a030a0780050b40d4112545103540500d0400c0038001102041c00101030b04100d004100c0c44d4050042401400291401c0c880c05820610800b030b001d01000c80025000f510030b401804040d44024201c151704400880060b15150781c079800d5034219a10300c070600041000300e00c40d0010b4008880845106003090784e50160844c040c03003024501c99002544c4a03001c2602c10311400b1a01603226491101000012400508036049564440301e903102d141c0c00304050780c0350b01c004603507550300e0b00a01c1481d40c2e000707000303001e020213403459055049511010032208941d0700f0700c81040900310a50702c80c1c6900402d0f040207400e4569036030040c6d0042e0003041044901c2a40483d9890559812000740301c4071541e81a01160800c450140088031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595447491 1250 595446241 595446259
    0xc03030403080d0c090e1501090b210a05270111040608180106030b0103060b150f0a320a1116170d1b03090504021218160303050c010b 59
    0x401a0403400f81a26007a1103108001082d030507182901c0752401401141d4803001c00400080060010740300038070700400180752414007141e4501302010181c0280d1079a0070a210f1031115040c100440944036a4001e90744c69061140e410600181101221300480001c5622900e81ca1900444402d42005682040e400c0f9400c5c1d03110342c1c0791002071107460281d40f007a548444d504d42d002c00d8544140203460030ba0b90032000341c85080e4a5940da450051811041e55038106807000c80200b140d12a1201a0082500c1030901680c0c0d5454a54010300c284044241c28104010084d20f51a40104000c6001480d00880c0d04c460f60b545144201904c00c0100c200c201d04551158000e03900e544444540100100c54484040b01c00c6940340022554071240102508400140c06404403c0074001240381010303e18082e0a000002a4961000c81c0c01e0b0380c8130f090392241100300c1200b407000c0ca50406000001002404003d0041182c042e003c22482100310312000d41048004150803000702c1e8298041c0c180c00200500c00c00c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595448741 1250 595447491 595447493
    0x30303040302071e0807050d020d0c09051504051b0f04090e0c090c27060403020a09020306031c121a06070b0114030d09090f11040e040506012112020c03030403 70
    0x140c1c030742c540e008201504d0303000312140b89540001e66151055820140182000c02d0500040c4000c2c1e0101503010380e8009803502154000ca140c01d607000c5c01801c21800c000c03a00340740010f1520b98480602480390700441c030b402c003080710344200c5122084541d8910400703203550b084c4003c004a205c0c01550401c220039886c041d0440e5222100042d002d50503881a19449540c3d65180360205150090010b01c194607003403001100d0079010004d5070040301640c010500760800d0b44940226141d014190480d201d52640042030104628081000401e101440001c0100e81091030070700030007008403030004040c00e940310780114203207420b490451140c07124042c1035161649454103180e407480d0428031404942c04c9004484096a05021480307011903001611280e40862401c2884002041d114201c0d0004941d903001c0707410312006041c0140010902d0341034014050070a410858102207040e882101a000300c045481b80c1000010541b00015070400b06605165060220980c10401c594100360317894000028048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595449991 1250 595448741 595448743
    0x302090a09021302091c060f0204090e0118123c030b010e0a050d1401050103030c0b070e18060d080c0a061d0327060f040302130b0f040f0b030303040302 67
    0x20307030703060007200c0302200c5100041505040f0b100307070903070140c000c030541c06040c0c049400507810305201c42c465480050041e03840c0d0085012a001600442c40c00c42d1034800c242c010840900640c00c01c1000081800740c0625142ea5800100100d00810802e002c0042c9c5c0c042d0765030300710810a600285140002c010305010385011400502c0388000382c0382c00f003403400c4846041548107204004140d5030240000c01c0141c02c0c4410040c005d0214001220b035000c0c0c50071000344000003801140c1c002d512944451960044a28207107500c80001803a40342008003000030495070399144504100540201018540c0607100c02c004a003400d80411400742c03508a0000340345071070400c00a1101c80c454000c0d003007000041314685039111804070103a0000500e80c8140110703800c401142d4000fa440105001c542d03000c0711f00d00004240c0f04e0300015004203a140c400304080003541400742c203d034840d000300101009007602d41000a5141003000150a005940d5402982c1003030b81c095200140c610001402c4a417070b40f07070520f070003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595451241 1250 595449991 595450001
    0x3050a0b040b0a0605060904090804030f1b0e09120a02100c0509040f020304120503090f0a0b070f0f1706060d020301030b0702190503031f0e180606012a0c0302090a 72
    0x302c07080d8200c0c81c00035248404a220310307001d64400600c1b0910300580e800420000d030560803000e0340e480fa0200710000010701000b030a1800f9a22494074050054060088100314101d035600c1003400d4404c41040008040c00400d8140001d001582e015444a40001080b40780101440302c004023035180940d0003104c4d50f001005440c204508550900c9444a0098010140d001c2039900a12001141c126800b513940140060765224400c80b00f102c80b54100f000c6014540100c0c10010b541180d410020700075419070016800e800984070b411710300352500b90040d00a2600003c0084000000c1c88000440c1866030f54800722100030441510554695071a420449000da40640d0481d02512411144040300c58088950f1030380f40350840040d509646d0f400050040d100b0440c001030040940d144004240300403581e10050092040c40f13841420220404940c43c60000e010382160b05004410014401c030113221504420805e03000c9607503500c002d2a92a16a408209580000f58404921020410035940e16406 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595452491 1250 595451241 595451243
    0x7050d020d0b0307120809091b07030e01031b021f0e0a052506230d0e240c0711030c100804031b0215090f040222050406060f08070903050a0b04 63
    0x113482d08181e80303030f00c0203082110700c560040c00140144002912440d180380701a6114000d45464803502141840558055100610490108150059650031940e02d4459058066500c0300c1d000324480b00a1300103540c1d110f00500c0b0120701440440040c0003480c06030003181d08140403004484019104d450101d80360302c409107043c0107107556000041660000301821008691243c1c90394400c11b0303013025181c080e00a5034428020050b130100206402000184034910700c42e42660040d14015800e590f000010b81d100100c204440a815000e01090a10040845400d280c0c05030030b0030001040c810209051040721440135611200d01070100c1d020340d420000e6148154407959a00c1442c080001d0a0000c02405100c00f0790040341082e15401000803400c01011400c3c0c0081800c0c0403c403c4400180680e03102c0d140448031509588059140044540d0034103001d032800b00c07000e02c142410144001c042103107a141c1e40301001062004100398500900a21001d19044025910007140c039050245000c070040d60 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595453741 1250 595452491 595452493
    0x190e070b09092505071e08030f060108040b0a0c020705031606020d050f0711030114041112030c100915050903120603150c031807180e030712050307050d020d0b03 71
    0x1000a914401400880c0300c80c5040700300c64441c000081000304d4a03078105200c2114480b45081c403400d0b102c401420810281031261165a903a4503103488800d078000780140449050104202c14000054a08207059901c80401000041d04d40c2c036184040340381c4000c2d60300c0142c15001d895004000510800444402c0c3c4846408841c1000b082031001c566a00c07a60202105606007800300384001420103080c100d2311b560040021030210080c0c03400d201d4290007924111155800c01c4500c6145040008608812600907c0a90305101c0782e0002ca0b51240302119851450300d954501420030030500100061800003105810402c03868442d05036903582d4020002d4003a4140d112000070b849140002d102281c80d030b10401d000070242c940d1031008030903400140c81031811001085a01000200030007500d0018581e50103000081c5480070b0005084840c09009424290020010b60000c120f14a411000c0c03040c403480d04558075a01e650b8101d8590080408800c481400001c0c5002d07a03040340d401c02d044e02d00c4102c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595454991 1250 595453741 595453759
    0xc0c060e0a0606082b090e070908030c070608160e040203070302070807080d050c070f140304080111220503071401021507020a0b070f020c1306030f0c06091d190e070b09 74
    0x110704070080485d40020000001e2003014140b010b1402461110b8004036541480c140e83c6413500310710790a54000b203a0881990303129110801c1700030740c030901c0b1540122103500424202c140489009100b0a0441043c6000f80c3e00000414541413103541210307942c9411400b450348881452400c111280c1c8110300c6ca8041034100004546010f810000701e928003a0302008000b0f03d0b80182d5104e004c103001c0a190b451241c00140000944d0700028040c4015941c14040c0166943c42c0c010000c011850752580e28031414100c6240512807031700c0007d2004242c4020036641b801703440750600100e10f0103048098201c0034408500c1405000c1d500004e242c800e80d0712884203904165070300e0100302c8a11034041241360060344142e121a226003406003040002c0f002c9081d0100310552030781c4458000d00103d80c0200c5030107114180c2000301650110194000e01000c85a00000c1030180d907600c4510700b00035046400003020291614045405036000240d55483d65045d1410159254007004840e040302d582235005114030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595456241 1250 595454991 595455043
    0xf05010b04051509070e06160507080105060d2a0909030f0f0905040b1503040302072108030105060a2c03010f022514150601120c0c060e0a060608 64
    0x7405090322400303a0504043c034080b101030804c402c2071000b90150f0300b4040065203084480d15250014503070395082001c3c07010440c0082c80c10718900746007640200002d07407420003030011607074a0201440705582c00c02c4684001c1c01d079243c61b48081c2c5a030550484103010903d1800a5050380035000302d01d006000c1e80f1622400a0180300030384130031041485c1740c00080c140c14024042450942d104444034507016006c440c002280180b40c0100d5401941e055015070301581c001c2000d0009502c0001c5400802c0d0724250208410b82e0b503090b0b1601040c06810b04c11600401e02c9900180310b0003190300384000f01014a012081900c025150400344214914025420030100070045502c034000c40302426200341080c401d8170621681044201000c00089400894082c044003640004126116000044404450b201d080040000d08203801031644200388d21300b001041c0c01d40076000411b800d42903800001c0400d014094681c21800c005e10709100400c00c528082c400302e91800e000948070140c0070f149228190b81c80340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595457491 1250 595456241 595456249
    0xb0a0c200a0303240e090705030f0c09070c0b070e04090204020d090201091d1501020a1b0f050405010602150702010b19260a060e0c041b0207091b0c05070308070f05010b 74
    0x40862404149000204e0030070512540c03000a65003c8005401d030380403a502c601c0064241217141e038a002184d8400044d44185241208100c0c0c2c10048074109058103140036601d11545c00d600404010a112045940014a071603540221680f158020f000315950303a0f20522200c01406050740a034005100c1c500003140c0040d44406d040d16030b85400c2c4e5080b03000d40e00c0c091040c4032840751140882c114060040000c0000b200c15842ea507805103240b002080442c1404560a003031021540540c5c0701d1410000100a00d030b40105859004445581082c009035841d000d0980c050119119004d40040440c012206000e096540c07110036204050183c1210315002155038600b000e1030b800210b01908071021010004000c0c1d4030403145900c0c850241c4045005800002e0211502c09007811340e492985039000c1100c90b4140f05100240194800c10081800017280000b00890311815260070302540312140d04c1403290030061140207561110716169183c04070301e0700c0e61003051410400c450315030a0414200c45458 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595458741 1250 595457491 595457531
    0xd06230907030b09070905040c240f0f090f061d1816030b0d080c0616080c070606150509100c030203160f151b09030b0a0c200a0303 58
    0x480200200400d90840e118003c002d00043c003101c0c61440784000c00903004040307004261007580203440c82c1144900e03068a8516002e000300e0580c0b402d044010401030003079044110901401110314013400d459441040c26650000c003504552100c08514100250305030b030000c4107040d0410142e15000480d000601406003049800c44003200c504c400f40f000801070101c038a07801c0c1da601c0b40741c82c021800c100f1042c00700310b298840d8901540c02da2400503003080094020030000382c004085142d031032840c03400d00c903004048800260968601500003e03062091000c50b4100c40c1c060080c0ca0180c450492099502030701e40d620550311203000e00c44a02a900209005020701f001a60f0541c01a5141c540f81e5050402c1500c00860f0865010f10303a13569035804a403511081c6003d200908500203001c1c0900c0c4102000c03001004141c01c1003001ea0042071000805001c5903603001899400003181e01314805a0550701d140020401030084060f903082c202a001001408110b00c6000e504d0411200c231400b498584040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595459991 1250 595458741 595458751
    0x9082205030a080a2601030303050c2a0a060f0603050607050f040e0703020d18031107060c12021e030909010b09010c030e131a09010503010203070c0b060d020d0623 72
    0x103040704401e1404903030088014600c0320100c1c6407001c1040101189036464a440b0345211780301d691107100500070103030144503441c1c00c20300000420b4100151220b01c51a01039800b40360005510010144450011b400c0208202032580520203001414080794110010030705c0d80300035111031041002040b1100d00a030100c400152040f00349514041c20882314a00c0b211019101c107082590820460441c5620344c030804066104884442039003140d01e050040001d01302e8014006a0b800641c410021581c224121080c0c07554400100d43c03184180345816420324000601060596042124454107021b001c00141481c1800f2142c0740006d90f01d03003401160324000c510303040c1e0200b0700e40590030000c41e028230319100d0740401c000c2030300c241000513612160582c0d50300c07070352035800b0a0508035042c11407925503591805098141c0003141149040c640040c0043c20407417019140340711650104a0396110f9110502c4404d401804148104c021860002c0040c1821410490032420544411100301c0415003005d010f6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 595461241 1250 595459991 595459993
    0x22020f07021302090105070b040809130c020c0f030316080d150e0708061005030a06080f070303030e0f060c0d090812040b060f0f191203050417060f1308070203010908220503 76
    0x21220340e96a240100c00050700c00d40300cae208184203e03149995400d0000402c403000d14004903220b900884003a28140d05001960320509c010888640c15490000545101401000d100149100e013030906404900c07400c5100d0f0041c90401440c00e140010100605045a00f003a000001d02d0740d42c1c8030308903600e0b0303400d4800c01e070310114a810100d5607510400103141c00440c0010001202d9a49103100341ca440d04120245840d0b40000d0000c200703268042c400c0d0841074015038090f006050f0003070400c40d112000141880d41c0c03104d0120302018845030940c04800d11795444560b0598035600c0c0d19042c40c611108940407a1110050b0000460300e0400924003c0100030141141900002407420041031411003805161550b0140c0340004d400c0f10b9803a9081d407058080c0e11242d9641d070030f104901d1844210340701d0401d01a40300b80c0a0100c0202402c62603030b4044409410000d03015018680246c292042d0800a5415824081c0707800600104a0051400f118800ba0a011404444042210808030ba00c504c50749 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 595462491 1250 595461241 595461247
    0x140c07030b0408090d061d28170403030201020702120309010206060603060d0b012607080c04090201050906030f06130c02060a0b03240a060e1522020f07021302090105 73
    0x41c031810909400a115880301410000c03032002285020207441c0041d1111511002d49401c8540802001c03d40001017201a00740d04100c1b2054000c084810041c4082c1c0340c1a11418600307200004900b04040300c121400e0f596103a83d2420006c1c042e400c481030a80c414041d01501d400554400011160754440c1078010708003940e185001c010341900010891504006201044000500e4180f07004d4081c00c2d005082c107404c204c3c040e100d1142681819007200d1142c1c0706120900c00b928000071030200132503045402203031060852004841600851869640000340407040c440109001070b0b13482d05c10345040c1e5000003040c1c0390301ca0300c000340d0360003110a202503000140440e541380c04a400103e1841009412554140380d441d40380700210100301442d010862a03601403010040c103500a0380001c02541d0482d508500f030014a18011821a00040e80310320102d0380c20615120b1143c04440c4085140401103440e103000315184401a071028804170300c2070b0b0f985d6907610803003040740c802d4502d0b40074181d54641c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 595463741 1250 595462491 595462493
    0x1091206050a020903030a031a060c072c0f06040b010f050403031812081201090c120509010f02040611060c0301030c050907020a050d050c300d15030b07140c0703 71
    0x4020403010b4a030020858003040703000c41680b03007000100034920341d681e00004c45030340e004c402841000b84110100e12940c02080790302d05c0e106e00010100151801c1e0842d070564074070f6017815449100110540040d580d0a042c0c00c00056500350b608040c8104400d80741844102600f00045850b8500c00341c144004c240e0500c02130011910641c0618a82007d500c400b0700140d840e8180c683d00d404007048100c801c0100021009240d034424081c0e0741c0140102c20301480540c51009000d4010300d4041c3d0a41c0b10141c1d00c0c000504084400d401840c0c0c07198440100f1941d907601c440e030042c449400b03181080c11501c144c10204000010203401c590403a078000008241d90b500f080e04020240c04040e00d510218030540380b500740803500501400c601e06045484650fa80c6540704011401c1280d0401300300c00e240341c01c88071000304032407940d0170001000705000c900d60340c0c134040c080200041c01c400408080801030071601000300700c0f000b4886401001d540d10b03100e0783e0b400d20407090581c6100e0700890401a4001d020100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 595464991 1250 595463741 595463753
    0x70c0302010e03030c030601120c09030803070e1002060603240109090f1a060a140904150908070501090b09060408040b0d09020909070e07020d0c1101110d02010f0b010912 75
    0x10054510038400820060007900041e45190402c0d545500c007018000144201981c0100e08115883d41c030100a003c100d0840c0b00103801e00c0c2c0c4620026110420001c00182120710465000c002c0400c010501c030780801d00024004c5d07840341d045560b2030203481030703881d004100310902020f03a01aa148920110b8187e013450061400781080c15001c440805103c2d2082c0000340000c01020503582c40d01514100c5441e0603030800940c414146c0c042c0d45200c13070350b0709060a591990480390707600c01e800c0000036502074500100076000340707030b42c1c407000d030144002041380c208201041d001400c482d8062008a0300e22f807a281031103600d41ca01034800800d1458208420810300d180c1030050222405404c10005030b881c02d40d004100500c0003102c1420f0b041d001110180407075000082c0003a0007102c58401819584844407010300300c04100c08000d04222000315812116a100d00214480f5409aa0aa411607200c060010b0b010304403100c1140340b060b060130302d0805654820b03030100c4121040b01c030842e0340380c291589a0f2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 595466241 1250 595464991 595465007
    0x30a1a0c2b1146050309010f090f02011d100c02040c0f02031b010f05010b0a140a050f0c0f011812020c2b0c0605070506010905040f0201084605010e07 66
    0x5441010702c005440f6040d446610000494881e031100355a07443d061400c14211241406a028051f14221300800850400700034140f0130360342820850502c0001c491130b030704811141c81c007065116041040060020364058502480b2134030a650034411001c2c094815100001c049190b6001a4818007035030a000420f0600382c074103422030200026142810342000d000b0b0301d03000d81101d4800040041c02c46480c903405840c0d00301c0600d03215803184c00d14106040091607032058040c5a1880340001c00c4408181d141441031140c1480c06000821540964500000c0c0c400f4007400242c91400c201c51100c80039900100c0d031418010700c0105942440303100340d158080d03a20039a072800303001001200810400035000d61000000384c040743c0c91b0b0607168031705803422a140c010140c00c07201d1104e0030401030000140c001c500c2050910780c2400e01595640d50b80038a07155800384083e01c00245182c08004190a00c260a14070466034041c001d00c9818070140c0003007a003514002e100740e40d507030000540040c441520030150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 595467491 1250 595466241 595466317
    0xf0408072316060f02010608190201020708060a0e0d110a03030e0f07181a0604050f0607170a0806030303270c0910090605030a1a0c2b11 60
    0x401c0041c0100e10703155614100031140c000c80b601610400610465401000d03038440c0303030b00310700c001c4c0300f110304090140e0b4072040141404400f0103030080158045a000348034441c003804010b400c450441c0303004103100015103912404000c090040144c0040c03494424102c0c41da59824280090008031043c1da4110000d007803c0003480c03654010401c15007406032092045000a01c80625000c14142c0c0c0522010200c68000c030703495a90a80072a0680840e44445c410384003110070440e1428502c1c0481004074500b840b032048001c0c40001240c101c040b400a1040c0a032a80b5100342d920540c80b5515502496907a00c81540c0a090080030030b00021160701215490a16000d80b54058138540c2c491030010902c84181a0740141c4440c2464505010035082840340e038000b840210300401d02c0c018580c0300d400414071107115207080b4603101800039021b043c01d8000c82d06545940580d04011821500ca0140e540f11540903007481c560811a8050880c14802d0070780300e001350f101d9008002c1e00c0c5100c0304886110142c001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 595468741 1250 595467491 595467533
    0x31b0611012c1203091b102a020603191508060f0a1506020d031802060904050a02040909062003100e07020a080c0a0b06041a0906150408070315050106090506070f020301050c120f040807 81
    0x5107107004ac1c46900103140600c030b00d000700d8143e100c040d5044c0e00c01d480001d0804c04104620300010004001d00044045d00491998070803421922645403c0c4060305501540704250729000900180d40c3d94009100d40d215a515602004914031403074440c003142d0420740c0040c0d44404184024082480c00342c1c00250803ca141100628207513071400d44005495080100f0796940f9a80c105201c0851a008841418031a1154059245150462801101e0102402030892030303036032100064402ea00810103e9507242d0091100f075154802e545900d542c59200f0201101c0c141c40c0c0c80c0c00302d4000c0c103190040d08004040000501034908142c014408440c800404c3c0c698060a41d841c1500b108444c400144050301d8100003404400c2d06605110601144041c4010005450320780108000c40e801078106060744d000f22500341e980e10302c07800c194180300001407000e5415440c04d01807000350104070000301922941055084465600d04c4000d0a000034110f8000d80005c00c104404000192482404208925110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 595469991 1250 595468741 595468817
    0x315060a12060909020301050c030606030f1f12140a05030d090f020a08060420010c02010e0619030204050a08150406050c04031b0611012c1203091b10 66
    0x8040400d58142d41e2151a11a0f0b44440c11415401c0c20301600d82e100009001e0340385542003003000b18010f848003c00e003801c1c00c020400801c0254544072403203600190400c80045e507907500d500e401d01c402c0010403c00c4540c4140d8181303d168087c00490358801c240e4220002c4c600308503600390100080c0000c09021503240c210001080b00590741d6034802c0307001d080c003403006220f913151601e402408100841945031f000c0e42007403182821a03a01c0711100c5019642071a14840031020354011501c68000c0c403c000c20791510064403000c1d01d6a042d4042d00c1210340c11689054542c1d961100c1c3c6855064200070358100340d444400083c040b88058001c0c540100c082c0c150549000c3e6245c8402032a47e0300ca50b191261300e03004020802001d503002d41c80781d80f1011420000c000c0b1810f4281c102c200e0300c07840c103a0503558900e568111544510140920f403641042058150ba03a440c1c551041032f20343e075007444441d0900613001340000b124200b070501044106426142c90109040d0221415960341d60901e5040b4102561 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 595471241 1250 595469991 595470017
    0x6030e0708060c071b0f05040f02040b120702060705040f090e120406020f070b0c0d0c030e031005010510050a08070305150d030302070c0819030507050114010b030406110315060a 78
    0x40020a02c15040c003420f107030311207115190030f5480000c040c160340201d001190382406501990b400444c22160103ca0005a40503440c801001a005a50010840d06c4000c510000307812856240300e0b109112550030740394195101da20640c3d05018a01681a0004075203405201500c125800705c00d8402d0341c4022a0f001080c00e90b85402c150303003e44c100d440140c002c8800c103d8111070400040000c1c00340d00703645908003000401403d0b5200c4000b840310041092040c480b0060500441c00c6100c2d1200c0a41034440d68044600c070080901020301c5070343c1c007900c803200d09401d000e8030640540d01070540c960703540022615a010200c01034500a0911400801c08170410041c80d559010301c480110b100392070158131111681049006e60001e43c1c4a1441c5412001101080c214004969004258181081a120221410100d0041a2a200340344946414400114140c1010009544198400d6006004412000c2485401400107039032442035884181500c90452501401800c11071a603840c3c40f41c5200d03a2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 595472491 1250 595471241 595471243
    0x90203030a0c150c0c0204020702040f020408030a08010b0a0c030809070e15041b050405061e04030302010615030606021518070609170604020d020103020708120c1306030506030706030e0708 83
    0x21078280d100100d059064050100540c9050fa20060301c04100d04000c0241c1d0070320080e119501300c1e01c000b449558001640d400315940c6520840e0300d011115411921907844164081d541c0d80400310010108903c8c400009000ea20f00d812500d640c038450390766007404809560309403805100640501a28000c1074004102140766014492007070b06492524051a90080e0901c012901c918545505602c58070207141619074104c02160100c9505866066540c41e007500600c010b0482a054003041810008000041c15815000b10342640c1040c48881e41000c08044160100d800f1445030704003682084645c4400c0380545540c1507400355a143c0d2420400304d0b555415424011603420000c081514202c0c24840111045e50140ba010f20700d60040606090980020366100141e100080c101600003601e0f074100215401507aa1000801c2103400180c201f10356640c4541c1c010b02122090409040f0700091807500c640190350141078040e01800506040c030300300714040c0520b05c00e070340910b2023070120000e80a10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 595473741 1250 595472491 595472497
    0x1d13020d05030f371e03020c01060b0d24030f140d031a0105180d020f031606083106021608030f1536040308100806011d060409020303 59
    0x151410704c440e0001c9070428101c0352445400036055500d40140710b14081d4582204c3c24690101c11250b0390001d510114400710003900c207410400c0d16030b508215001481d84032100251880c1034040205001cac100302c9022200c01c41c04400a444089010850104007007401c004000f6503513030040b4008040c0d04030300e01c46039140403601d50134040046d942c0c1007080e55240c580040004162000d00c5c00e035143c81660544440e070008a00c0020b8440c1d10707044412030455039a85038000154074040d00344c400c48003410001c0c4031460340520842011940000014204000d8003201c5202c0c681410002d00a2a00c440107841d846000618102e821540c00c01420201ca5050074103080040c0c030903504c2564030b26000b000e4045590014202684606c0660308003a031a65880c2468550144c4880f880da00c650664261041d01ca1301c4506018440b080140901c001e050784551282d216920218400b041d166480c0c0303d803030790b0300c0003442415060844a00001c0549446207035090704103000030070208940d06d0680009046d64 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 595474991 1250 595473741 595473757
    0x1080705010e240f2b020a0504090b120f0d0e0105040e13020d06020d090203010e030c0a1212020d0e010b1206010b0f0c030d05090607020f0a06050403180f1d13020d05030f 75
    0x80101c00030401d14000e1724040c145c407190324150f09107102c501002c1c20030300075801842d00064640003a4049512185066030400d41c08a048070400c100900106403154580d0390b0400024543e10389001c0c02e54010700440d0212800503106102e0b5507181c0c0140c68801085078400c80e4010307102e845000107d1100e0000e8450241582c2000400403070314410135007100c941c9164003605400600c0f282c4c02c00080881d400d5411900149150003030542800308584200c0c0407d00b1a0b00c0703038404a001c44410546034080381d01c09044200070403109415a0400c101c140350140c0301c00181d40003a00604c5101f2052015150510010100368204140b03880c03880e040d500305a501d000100d0f070307031400c118080408120041d00039031a80003411703440341c0c200a1140c58126910000e0b1109440c2c0c0c001c0382c201845111140712346c08414401d01441900da14450354118503d209032541e00118900080001c0480320409000c0c00c2803603143c080c1140aa424899480d441290079a80ea000510410810030070081c002e002d40b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 595476241 1250 595474991 595475017
    0x2010c0b060102010f1518050405030301060806011101020c0606210c10020307051b090c070309140f09070215090313090b0a080a033f0e010e120301080705010e240f 72
    0x1402d002c240d0991000c7c01c40e040c41514101001e0202040d401306c2280d054903020700c0c1c205500d9548000607180c030b584031489106070358400181000a0100407035081e000d0399040b0380d541e0b8030030788828103246814a6101c00c80030320341105800d4152032414800355a954801760040c1c905280c4e0b81d07140d60341840201080c003000d800e0b0b00000300e011482d00c2c20b0700e00d901c91110b5140c3c0341030040790707200144010468041c0e0510400c250034410466901d000001c00d055000810040307a5241c1004002e44900e40c00c07000801d0203014034040703544482c000c400e0350300345140149249000d43c075144084020348450f005c0203400c035000c000d01082d00042840001801c034000d44a1808400312081c0d2191840e88060580110042c2c4d0200404a8403420201e20102040c0309400304001c10100e000c41d0041c81000f180004a1103200c08a42d14403800c040918100d0300d52038280e480d8035070f89900548800c03c06d2100c550740f00340c9001800412004008070455514444840a401d090702c082408455a201400b80b1100d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 595477491 1250 595476241 595476281
    0x16020a23031603030c03030b01090506030a140f22060f110a021203190902121009021c030c0308090f1006081b0f06070203010f02030a05040b1302010c0b060102010f 72
    0x4141010405080040b03060b8881104641c55910000d0105905040040415490f4860b04103240e105100040141c41d0044c00c8035524140022400d000707185211100705220b02410006440801e0740d0440d6214030f0021140c801c01c808000003a802440e54504103c41d06980e41180c1c0d60418898411003a102c1020741038283d4440041714060305e003091350410403810401c200100543d08003000515845010b081e800400d010f540c1b84001540329094601e00103081c841c00c24402d06030003490b0072031000340b402a07480081100c00f0303800c900070802c0362032009000b20f440c000d942e5002034892081d46600a20040070b403064148064422802c26188256928a154586030140071070b070004c0c0f1400700c01000401e04e10342003450000116510149201c42e040c401c54002c5885c1080d52429003020b201840c14100c1103549103454880344c1d000b0241500e0691704032802000040f082c001000c0805c0c4010f80584a544aa4080c4c0d5901d07450542c00400301ca045540342c0300c2030710b01902c141c064070b103d01004001d8011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 595478741 1250 595477491 595477559
    0x61c020705010608070e0906090d111504111c080421170d05090606090103020114040518090d05180607020a050d050f010c1407060c0509130c1b030516020a 68
    0x180180a4442030340798002c50203106ca80a400600c1d400d490440d8100f1100ba43cbc90002c0040c141405600624440c036810000c2000304425940071904078141203507420454500002a16414001400c000b400c018013000144007002189507482000c0050020b0302d101314121390b40c1c18880d10846031a20040d80000b2405140c6c00c030090203415804801c1c0c0740100664603141002402c003920610029040c004820000c42503044900d048030b015000203080300c0e484401e51144041c4881781214401182d004058107038036014490002c88050055140018004141c0482003113844d0340159004c0341e020100c010f0010303039901c0c1d00010406143c0240f001d40031050181030058251204008444104400e0404000c1036215100683c0c0e40d80d504140f000841c440511010340c0c007171140d40c018581c041c140ca001c181ca20441c03078001003080c01c075590756040001a14158860340c0408101c1c0180483c2d0184490030765241d0344040c02d000e060006108902c0c5540c5c0b4450126060034a92000c0300d00950310250034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 595479991 1250 595478741 595478759
    0x4110f091509011706060d1401031214030a15090501030308160e1c060f06171b150702010e091602011b0203030c030703020c0d0507060b0906061c02070501060807 71
    0x1000c003440102401e2420b100240001c00100c58068415904106100403071080d48451040c2c40d8064500d050411180b855403807181d10002c02440101c1301c8141c0d4040802d090752180e80100c01ea003445000c1e050940e20b0350911680600070f9868040030ba502e14440c00681001340c0c0c001c10b80294002e4440c21410705100d41b00c044a885400b403007905012617210104509d4445d8200352142000c88041148014410b2070000090007400c03508100d40f908120001c18a43d00000300c0c1b0290820090807103075008102c00c403080900769444046a0301410000c0d034030165104074001856058070514200008400e0b403c0024011001038520340f01614040d8901048150244268a4440406074007100c1c0388280100003590f03484003c040c402002d13070110100349254020f405813000c00c0180c00c00d507501e80c4c0146e280107200d904521003d032100390509582c042d20703084c6620a10701600015251600c1d19814000105460300e0700f102101c0841d90030807901010910a11851011f80043c601506005140240c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 595481241 1250 595479991 595480009
    0x313080d140603010b060306010e040e0607090602070e01080304050d0201030e10061401050702090612150a290a0506030702070504020c030406030507110c09040f0b04060e162304110f09 81
    0x3500070b81c540062030000d9621b90b015250311a5013403902849107807081e030204024000c500f07201d02040c824a01401030b00c64004442501f60380d02c0c0d038201e6016560302e0090040d03084080c8103401349500100418400c50400c02001c3e03103a00d006040200700103415442d00d52070f00c1243c89110714020796841c42400146681032020b50906404d00e40107081041d10380014140304400b44c0742c0c0b840381c3d40035680c012a014091107211044140e4a4004400b07203468019a0064410f484402070144842007241c250110002c0001a5100c03014200b41404c50518062200c030b9071015020409502c0b071070600107019a0b42d400104842c40d40c1782d02841e1501c3c80c040700030b000c1e2080549031034180030465050703002d040000626080008030403105002d0b651158149031030043c50303d0744080d110420b000c081100384041a0081d04041040000700e4000c07010500c00b40048007050f00420108036406170312084900010280c510201d071005100052413000300c83e0310201c590000300c800a1500010031a00c000d4605100b503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 595482491 1250 595481241 595481251
    0x303090503180a14131812080a18110d0312020c070302040b0d0b1603140c070302060f010602070311040f09050a05060109090803281a150f030c0313080d14 68
    0x408280320f45801c0c0020f901a01d24061001559500d880d4400d40c0940b03084c146c00e00f036801c984407411440c07074190008c1406504488503038015080050012040301c8900010102c25006800c0d180c031148418200800340700c80c44015070400c401001c604491440c68130082030203135220b5008101e190301e18410b0000b03640f0700c00c00551151803101e03c840c002c18043c00c0000e070300c81282140c0081076401080158000c0500124202821305041304100320591514028603556003c0e40881d002039440350004e00e09500c09004000040c0c001e40f9082000600c0458005442200200041f034008580d095803412650480d8098503e80c0c80402c4003c10301c4810301146000d8019004148420261500c982c02c2c60310024220710300d048891000141440c0c201000600d0709404001e0610001d51852480d2980e01265803200d8410b0744522140513903250030038106c48a40440280003411691410220302032504024900307200101214030200004050200401c42501c05800016000c0c0301d0401031001b802c00100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 595483741 1250 595482491 595482509
    0x809060601050a2a0305031f06050901030c02011b031e110427050a050a0f1413020a090603120f020312040209060f131409030a080408070303090503180a 67
    0x10520610380d03071210803240d1a849a060800007030981500d10b0b107440b00c0007110071031020070030240c3c8410594800000d501a10100d818048c201c18228110040840303584111404a0810811280c0b039500a8100507072140301c6000000b81d07115504180082c6099007410500040e40d103403094a13008050341002103000c40b400030200306241035525521010f202d180204240045440b0b02108500c0c907000302441c0c100d403010020f01c0729081c02d40c0e1990192200785c03004641c9a040c03030490b48028209208104440056a174040a15255411102c0720480440410790300a90103900c0810f482820b4020000118030a072a0303006410740d846001450901050340b004115002000420001d86840404540140e012201c0384015101d140015070b00700d010022a80d00f040341c1c07001c107507415841e0340e104084542e6884500c1449a82d01d02400c1d481c2d1241c941c075007000c104010045000f04404c5006000028400d00380013920311190349619147d46c02c0700c041c11180301c880c01402002030401150130720003007003841c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 595484991 1250 595483741 595483753
    0x41101090f18090809030a1a1e0a02070305070f0807021c05250f060507020a0e0603100209010c02091f0e011a030402031002070506010f0806040f0303150918030809 72
    0x90410101207414511190099243c01c000c4040c821104104c070031800e00181102e680c04030a150622175440000951205052044c000410303882041a031022050034898001d840f40c1d6402d01040000d4012130401d6040003024400400080d2180403038000d210300902e5829200c0301c0c035104000700300711181115aa91039000565500040300095503801000b040030a40140d80f004100203401c130011030b4403074812458088000100700342c00400070200d650003680d04844403602da4440c00342c40c034016113140390158030241c80050408c04a0b40903292844051402c0101c04005400150000c001980da14044c040786802c21082802103c0c110740c01402d001c502c0b03a4866240007144049000a496a0740f207051000001404540e010310030840d2400070040119140e0005040250703071101c0901440d401d0070202c0d00007084681c1d000031003034400c035842428062180e2140c1e508401903c0c91f90707117420b09902c00902c0030950140600941c14444410b01d61179840380801c0c01c006001c908003401100091b0460 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 595486241 1250 595484991 595484999
    0xb01090209061801110706050a090b0c03040e040804030204060e060909060603060a0b01050706140f0a0e120901030b0a1502100911190e0903041401080f1f050306041101090f 76
    0x6543c21010307a0105210140326240c01a641e80d91001d03480c61140c00342e050041280e64110010384001c00c1a0380d41c0c0d10004d89c40c0d40d0404224425001900f04542c01408208035000a00321030a42c0136100c1e544450401e962540480c055403003607040480c001c1d07001d00420500341050b0200f0baa00501800c0107259070304044002c02d03190b4501409114920381c503004d040e44207901410444526903803007201040b0b1022018140741d0f00450a50340603010054520224680e0441d50081e141440058405072001c80d1030f082201c540e80d803004d21101c0c14940c40d001d000d44140e41c0c403081c1038001d01400d05410f5105141c0b00000303040540c0172041030b00051508901502180e02d02200c50000007094481c001c1e80311002204001d51a40c50303100d510f2020114003000750404000c00500120f54054208040c0402c040c001503601306c01c02c40703c5140c611008400242075101c048000a001780c2484041c128043d1a040072909040c2c00f180e05480306081c0201c01e081950340081200300802409070100110350034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 595487491 1250 595486241 595486249
    0x6091a0616080307020a02150415090e07180902130f0b040e181e07060806010306030302031c061d101202090109090602130e060102100b0604170a020411070b01090209 73
    0x70125014040c000c012000401c254000c0288414032a0000e00c41803182c10407220040c407552050240402d4040701820480c40140110100b100760340da540e820303103220b07640d1180c1100c501c42c0080305c500454603114030006071000301e44024a21060075044602046041c5401c4606841c3c5940c05500d02c000104010003061800703082d80e80d000101c5c480712480e6105400c00d12071030502c2d1120803500700072800f0b03c842030402d400038002c402c98449860b204804d0f951900190111411807001a0168004012000352500000f502c481c108094100000300b8070f8440300f42d0f1151802015100600f1011601485140404040d07407000500d6084031600c4900016408500100c20605c61112140d1b00d4909031000c00207e40c054175851118102154a15599440080b210060594015015015210706a0110512030051a08060300540014035052812750000c40e00124003007850701c580902040b0700c005a03180c2c004c2d0442007130134520700368035103515003092a640302040c2e010100f1144104496041511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 595488741 1250 595487491 595487527
    0xf05030c060706060e01150201051f0e0601021203191b020c060304030c0b1e062409010512010b040302100806030a11040b03010e0d0e0307030c09150906091a06 70
    0x20103941103900c0b4440d502d03203200945550b070030104506080350004584044074a140b54580b124681c000d001a45900403d00700290580c1b0904504110700c060512461490401103a00543c040c070442e110704000341c0407001d01760008d44110216086002c01d2003c500d051b4040c0300030001c81c8013140c0d4021100300740040c2d0384d0003407146940e006260200009081c1801001503100854201d0070300407003450000105c00341c865402c0c02010602a015000c1121030402145c504418040b400500d24041c0140010f181243c00803070740a4100081005500810041c10b0b2045000b44034200c40d05440f1415441080b9211300a00d40b45801c0124040400c1f00c15940000d134940840d070049184022481c401e00440c0c0502044142141c0641c00d05075408402d48c000542901c1c4100199255584d10b0706020406849001501c005014400209011f110008140d80300100c80180c1c540d80d8003840d80c4c1e0b41c4000080e0b50060348064201c0d580c0c0d49020100212008a00f4140307002103034405d103080680c00300038180071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 595489991 1250 595488741 595488763
    0x14030307110109090c0309060c050c0a080d0f021204050c12070513090501090f0b0a06051503060406030215070c1a071b08012c0111121b07050102070c0f0503 69
    0x39812000e981280d0140000c0e074003900c0320350380c00c3c0700c1c2203920301740500601501503086a20b42e01d440042c82c6400d105500741c1e4004d45620016010100850700c0f048683d8205110000e41955120361400442032244001c00c544050010003501174078040c10300d80d0806a800300e90b50302440c200e1809400d07541c0003050201c26030704103c681c1c6904030f098800c194020f1820040042c159860083d00c0b000b0300945450708020035200d240c2d99030341c590325441c0390000c0c1c034502c0c41229040301e007000c111954081c0790400b6690006000e4400558182c1c2c039000a03040e040c0c043c4130b0403601c0d0000641103040c0f122400050001c1c04090040d00d04c030102110140701c3d5803040322030140019a1101a2000004c80001c441009100c40d0b0300902c504403000700380030300f00e203621516450b40c0782e2528030154106c0e4041c041c522a00d02d2060a19003031802c1c1091914641c9801081c5d040180d002c0f6070071400710f20b03c181c09000d0f036902070400103807035515624200f100e05c1c00c0ea03000140d40050071038080042d42d0380007070400845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 595491241 1250 595489991 595490003
    0x402040605300a12031b050c03120c130308042c0f0402150406023319150b07030807030905120c07170a02150f0906090f100f020714030307 61
    0x500c1a00b91031400c1c41c0c00084010048404020011071045c0d05401160000c80e071200c01c5c1c3c001ea0141c5c0420356030f51140d00480c101c190011310103a0001607040410079840448461140c1c40d1030b903000011082061140c104035040b50b03000c9801e000b0448e81c43c40c501d41c049410041130401c600313180444030054100038100907860300d11000003821501c4042444102d9608155000d49136078982c800691240b1181c41d5078101c8171195107070000480400408010701d02040b044500058540300355141803115540c0702480215101c802124000c60300b0a00c5500404c1243c914588841e0540307001017624001400c844105801d103403071100821004550140f03010b03100c1e0601607507080c0400880f42804c0d0300d644032903071a5001017011070783d0a801056075080303640308958007503400d90726030429440340c050703c410001c0c000824011000315080c03490080c09100c01c0184562103840000c0001124000701f079500d500081d100101100043d90104464000380642c4920305501b40c40383c1d0042a42e038046c0f00400381030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 595492491 1250 595491241 595491319
    0x12010302040b120d08340f05070b0403020106030c0e0708180c0d0f020301060618090c111e060a0b130f0b06030f0708060f010c140c180402040605 64
    0x380e483c903510381103d0311807800340c41c0721200f12100984003840445060110164950f00f022010350b082820308801d02280c041c00d26001d030030090885621000c0c001000900c6410041300c0f0200e089021124401c5120342e0002c5402400c510f801101000c5550010100940500078000c5107a0024508c5a100004805040300481800d0440c5e142020b284511500700c1100d07000e0034107100100c002800110300940084c4140b030b950300c1d400c07110346440c141d2820051a00030814080d140c42a044044400301525000d0349403084100d41a00b050900c01250407044c10488070043c15200030300c03159a210b0421076040010312040340100e40300f600c0117907107038030003a6982c10311080c25482d503030004118250142895803a807030300528240c2c01400940f42c0d1804500102d0004d050351a01c406403102c01d2106964012200304c40d81d80d03030301001a1203042040036003c1c030040c05419417219071100300381e12815180c031001c0b4105801803008807074241d00901c2c000d1010740c0e9a000d40303d40344074068442107108182018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 595493741 1250 595492491 595492511
    0x307060507030b06040905011703040302090106050a18080616091d060402040b0a022503150203041110021005010b09090f130605130b07090e0106030c05090604060201050708010b1201030204 83
    0xc0c150b0309a0541e1020001c540800d4146c0e035a03206030f041c2e03101e00d00340341d0a00d250000d00aa9034021440000e500018400040c48003034811000381103149120308003524148072010301d40340d050920783c115441c01d500c2241013140369502d07084103040065a0f81003454070241000020211200001c4024040c1103c102c0070450b2a1920f504440041c06103104068841880701d4000b0348880c0d40c0c030411410300100b4410b007521150040440821254005250019000c40390b2145001c0d400040080c1c0b2032000d05101b144ac2905c030b800000448400e59400f40c0714071880e03503204008840041e0071410340d851003441120315603115010300c0c5411800f42030031010144d488610050340c1c1001181c0084c003980c1410140040d034080030072827001c0b881c45202e103415640e40e00c480031940c14455210b003810000c0a40c004101c00d6000c0e9200c4102d503691480c06915004d030110120384181e005074411070050b9518810051450f51060b000b6000d4481c807924145001004014011098410301000c0c2c420380e5241c00c089 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 595494991 1250 595493741 595493747
    0x90b01050c070b040f08010b2b050f0705100203030f010b090a1508010512030c0a320d5c0a030905030f03030114210c1306080307060507 60
    0x15002180d2041240d841d962103d80d2840070303070001d201d540045100490003058000041c001e5000725030307011340007002a1011251070341800d4030b00301100d85420015500350f800b0610500103003c103842804000e00c509071802c810b012030054000341e418115081802031001c9851610000c504650000044a4952142c0000194500f4031b40d4480512078826003036a0941980040e050b40c1261401c40300202040c90010440da203c1c4518940001e9a4202a07400400a00c510320800f150ac1d1a030880341031070000d0078620140d40204c1255940d034541c03041004a501e540d101045140c0b071907180007095010b4003c041c0f8985c0d122000d0b08a45001006007440e5403810b0405150110350805280554541c00c3c174041c0c20940716408081d040d000100d40c0500882d0078140010320000784200040190b01c2d5a20300400810341d1241d6140082e446040c004110010103442800c010b010201e95010305a40406001001000c0841c0c01c00000f800742020401c105800022045e03a502c2500700c2404509641c80007421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 595496241 1250 595494991 595494997
    0x3060e1306060e011707050103062d0504020d020c010b1c0b0919030c050606041e090204090803090d021b0d11040e1f140108032b0504031d01090303020601090b0105 72
    0x1001c581c0f02500010310b06000c91030707503510406014242c46001c3d07110001101603030071900071441d0300805401640301809091005010f00103003199941c40c0700c2c1d1207a0000301640c2c400d803610ba10541c0c001c146941001400c3c03141070710000d021100038642c60140340b000031a40d20840720141118107040c0001d040e80303206100032082e4121b164110b40c2050708514014000e030009001c15100e61051030002a528102841103440014003480700300400f8905080000c040d1600d08001c98100740c8034402500000c003110003071402060598050000031384c400314020700c1c00d42c1e4101c3c607020104c59928080003036110031032406000c03504910b54000c175402800100c0d02500c00f041d0b804c0e0151040e03403054680c0d010300d003140480b2000d40d0392090040640c0300300700f1407070008280180300c030580003084000303004840110b00c0401d280c8102c489148005081d0840c00c100c404c21601074011442134070f46010a1180712110395803a09003424451181c0f401c58030300a544110501805244a6030f46e41c0b9243c09a00410035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 595497491 1250 595496241 595496249
    0x102091e011b0606092d050c040506070c0305121e04050603040b040204091401020a090b040308040e040f080d05040c081b01110c030a11030c01020a0b0606090a0b03090d0e0103060e130606 82
    0x6d0015825241e119803c00034100400d012103010900f1b07595011544d80500e9000f9941000300c9400c0600700010040298082e02c4100c0d444c2d4810080000000c01c01d0215840c01e1001401c000d45500494813020449540f0654110420008002c203102c140d035001d09403600a0b401030030744441b0350b440d403020800500c0d002c00007902d0f010040950542e641700540050071101d0040e81c90a01c25603441c002441c0f90300a6000040c0b00722420300c024044a541c422001e035002d400351400074001c4080f07440700060380e4050000d4115083d110b100300424008081d44a10082003510002c201500000302148150034172101c0700ca0403c1030564080c1c9a0036002c1207404032280d40102910340c00c410700d00d45070328102074000446020303000c0c48005a0180d0700206e42c5ea00c8554004c1260711241d0b8800c000c00c61207034014640180c2c01140c4a0002c0750f8510004003a500c11540613000b0a01c210403148040e10150410101c181007605100c03062000d0b10300010940c0d00608020b40080c9800b00d0380c075240340a0842504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 595498741 1250 595497491 595497509
    0x71a0408010f05090705030708190501020f0d0c0206010b07080711010e1513050d03020307110a120f062f090612040302061914180a060203090102091e011b0606 70
    0x35070900e482c00b90b5000d640140f40500c12182031543d2141455119113a621515815070440400200700d155009030200a051041000528280da0002c01d8000d41c0c0101000e02c2c1e1076075071809411100c5804000085c0501b034200f099074101811546c0e041103e11032008000c140c0d0380001c001d4400c0741d0055012020036040104128020b840380300183c600b43d00142c001090154005d00006202c1c1485c40c81c0e062403039010740c003071464410162140510300c042a51030075000a005000010f65000c011a880b00c828840c8270104c460700107605081c010b0710300e00f00b86c00f90100300008400e200354043c108000381034440d0b034803100e840345282e0740010700a001341e0255041c0e02c1c146908210401d9400b0031039602c20b42c44c1da4048410444110151022559403c0c0c55101c0c8011b22000714a600101c1c0c810130000790f05403400c403130101c0c0e029900c0300207030703081500c1c088042da4010858001c90b10344510040c41a40040c0c00c01c283e00031440c40024801c80c140045001102015454a014040705403c410040c0043c0d1b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 595499991 1250 595498741 595498751
    0x1b0302030709091a04051216080d0509010509010605010f030903200d0206091603060509210a0e010509090f070903081603030507170f072303090c060c071a040801 71
    0x810200640a290300840394100745030300c01c811a22134160180d00454010b001000c22070642c4132070800a600c150340403541c5800850115001400e2280100f2107040c910302c002c241d509000e0300d800d0270340c0c8001d800101c070359052030b9040c4801e9070703c01410b030241c41d0b042c40c001c142c8400d181400c0d500c0c1d0b27026503004c260700011015030f030501140010351200e05007581d500304c40140c3c1d03c1c654420f8440d1541c006841900134070110400218210f60400e68208404c442070300e02e81130402c15480c3c00c049040c1260722191a02080480f0001e80114940c2d0b2922820300b0818505801100013968504004002081110344200840c94017481980300501850b4405d1003540d480500000c2100050100741c400c500007030034040081c1c40c940c0300d41030701100301d4440292462140c07100800103003146001000103040100c070080c01c0302074030701300171501c81c1810011004603504d007489021b0a04082c00d0b0100d00c0d01403081007040315054900043c440e0b0407a100a05010107012030b642090b000c0d80300c0c940c050300d0345600305 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 595501241 1250 595499991 595499999
    0x280c061d3f0607140724091a130f060507110a0605010e0106090e04030c060b100e0a050301020319090201090f060305061801080c040509010212070906080c03010e041b03020307 77
    0xe07407000303900080c420100c800c940e5810b142181c003440361610080d0b003101c0a11410f0001005010a01e8004a0b00c0c020702024400300c5260308220350301c0c600b0941c1c00d12420700d040b0002c48a07071640c443c0c004100803132046202909899964058107058801004070f6a900001240c8a02c20704900c04080000c0c0c0c1a40d140381060b042100c05000e080c020b658500e01120b00010340780e4060036500c0121604800302481507512510b003551481e2800701c081c2c2d20284c0f5015030214644d641449594803064035141c251840c40e0003001d22001d460641c218034040c3c2c0c810001c0c44082c4846042040610001900204140110f8801210007103001d510a2004041900000c5040354050304503c1c418502940d65070880e070b400c0c84469280010a00c501d2095400c90300d04402581081d410595015403c0000545070141e11640304982100896114001890780c15040c050350303070302c0002075070004070003000f2a00b554100040307000710820152004003041c0034948100ca111021a0001004540003410b460107a551 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 595502491 1250 595501241 595501339
    0xc01110301150e010302070f0605100b0d06030605061905150c060f0601030b03150a2004060801030218070215041a0c1e0f0405040509280c061d 63
    0x40d920008140c660343d6888a031351082c42540da440d9042034a0501030300311a02d445000b410060300804204007000004078600c100311000f08a54102c03610009405807648c02d1107001c988014098038418411410110501c01c01c0121a400742c480442c0c01c81084101440c0d5056248252030031082503000d04000c000c490000f51000c00d215600a0f02c0901088155208041c0c940f06443d41c0420300011044c042003c503600d552080d1001014070920001c030780356051000c401c0760456070103e0f001840314001030045040001d4590306070320094046c1d0b800c80c1410300007e0348a50202e4144a1080c4c1c00000007410b0044001d03004d01e050310151001c40c1c1c0c5007001e0b950191a0740c84091400e50f032850203801072003d0060f8000701d41060940f00c515034106818401000040d007006000900a072007941005021040b0002c2c039101d1035000040880300314242450412030944c56035115034280119401d806410540c0b445440240d02c00884104802d04441505001c01d400d82102103400a0986d6003500040b0709 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 595503597 1106 595502491 595502519
    0x901020706020403050d0e09010308041415220614030a1508100f05250c0311070b090301060b5404061401020a0201050c01110301 57
    0x60720751200b81d0300281c10a941507080602050b40031900b044803a503504805445081c40c0d9031642d12401624065441050392036840f0a076406081da8a0641030500304192107000d5868044045c403082100c281c4003000e0001d402d8441001c24454010a0040028625005c3c000e1640d03440c1c8629602401030f2081041860413a40300124600c0410b0100115840d0008070005505a031000104141c80d0b000d41540b03140c0001c054404d186605500102181004905043c4c0030a1028a0121011580780c0050141805250000b244424283c801000c0d5045c04400034081580ca41c02c175400a4400e0150030040f0455041e000303203604900c4108040d11811044c0b485400a884e508407500d154800e101603448510b07000980030b1340d03180a10a101c06042e02c040e103e4003425403400081e648942007a4080e05201003c20728010311902500020800e02100032915240c2d6920300701c90304842 = true := by decide +kernel

theorem cover : BRFrame.Cov 595323741 595503597 := by
  have h0 := BRFrame.cov_init 595323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 595323741 ≤ n) (h2 : n < 595503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
