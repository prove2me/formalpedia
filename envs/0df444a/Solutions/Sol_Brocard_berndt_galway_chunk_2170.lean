-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:38.626587+00:00
-- url     : https://prove2.me/submissions/e1c844fe-bae3-4191-bb4f-4753d786c845

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 390107913 ≤ n < 390287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 390109163 1250 390107913 390107917
    0x23030c2530030c020612040302060c040b040605072d0b06040209090a0504020f19080123010303120204080307201002030d0c03090210080f0109060f0e090c040f0203070f02030708 78
    0x6a0010300158041080815002d0300e80150f045030020703e916200d10495004100c2500100c0d0110014020880058107000c007000a440545080d0070300c0905090030b107002a200381e40715001c00d03a410b007900a802c20801c0980c064038211540440301b094001c3c201c5140c08000d2120140c5680e10031401030108560640700c41400d9944840801800300f020f449500100e1402229540340540114441040f21a031158000750f440850344100001c0202c5205052211401107100d0f10023a0303001c406100400c0485c0c4650000c1015141c078220041c40c20340e503035842d50320b5035004100868102d0320100100c00451000320141c2d00102082c0c96038030708100003101c001c4d100c5c070580000551aa540750320310650640301c0c0d884142e43c2c550150501440219855000c1e140c1502207600c240345940c9000080349002d024007545013111441a14141d24504014014548207401043d060340392007085541616030303803240a1101013600441c00140c2d6400c00780d8004007001e90440700c0300e00f03640c8200700c030340001040002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 390110413 1250 390109163 390109229
    0x102040f180c0512181c170103170c250501030608030c2a03031809180c0d140109120305090706090b070c1724010323030c25 55
    0x2000120940d10411760414a05100300c0045240c41519004241604520500c11110070661103c90301e401e81490fa65517890b8007400005d022102e44604e601100d0441005002c8540e005000e840a4550781100007000300074050701107405034800c1070200503558140c030a00014003d114050341c64092401903c40c1d1b41c0146a40400340a0240259041d880c40032901000c03060340b0040c240da6841d00b54920818a486154100621905105010030382540c880d409200c89051010054504040f8040400c500c0840c00c035415118190045000320503040f0038071400002e0b911414420f172a8610172040101101c40050840380303560b00c1003005000d01034220f0982e000319403a40f0a0340b41c1e2807205182c5440f04482070752000c444041403004038201c0800104045031940c41c0310030380c00346000358103020008041082c800540030b0720180304c005105644402c0001600d4209c10112458038800c405660b10b030030000d130707075044080c2100d0119805281d8807038003540040943c0c550031102e250f0845904005585968 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 390111663 1250 390110413 390110437
    0x9020f0a080c0f0c03030a05010e07020d0c0c030b07121a0f0f0a091103010915050f0108100e010803040806010b03270c060d0204030204050a0c020d030c050405030102040f180c05 78
    0x4000940c0d03070b802035012078101038820500b864994090900781070b0340350815611201241d01f00300000c0746903980014094481c021540c01401030020820065980b148003100c15684003000c48004400700d082002800e0040582d0f41d55050704010305042032084440491102001105250b01100150b41d901ca5500d07200c8800c650200c0000404030001341d004555602800383c81e418421144240041d200c00f86040b5403000d4000d10082d181120210021800307401000da01402074083c000c40f80d403042003150307808800d0011014515407104d0309600302a1003684500d04503440040c040c0700300302e810700c00740780144604207055056040c00c1c0742c1c80070700c400401e0400788842c01a080c14036043c60200042e00940e9009484035560f140c1c13100d00480a0b5005000a03402242000041455000c061042e441898100d5018025000398500c4c100d0140c90b007180c0080401905104c0401d040d6004c1c80240f000b0700350a1030f001c1003907141c040030128005918000342c1629140240030100c25802030222008401e0038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 390112913 1250 390111663 390111677
    0x10509060f0f2701090b12030304080313230c010908060c0301052223090d09050f0a0509190605011704030509010c080c01052403030702060322110a09020f0a 69
    0x40e925200100c442542220f440600c002d000241400f416481841410000d84080013208002405103503280300989004020107403c00000709580d042e0481c090302c0a00c158201e01446e203540068002c291100c0c0d007808856000401891890344e0000f1881004142c0900942045c1c905041030340c1007808140704050040c84a45c9030110056101202d292209070304000411541d001c80c021401050f03440d41c0c6a4107610740e424041401c42c1c0c00000d086080f06a2640d0f43c089072400c100a003c08507804004454001e18039080c01300d400e60b60004814402d90200303403090140d6240040c1c940542c0c81d0742d072120341400f6140c50703030030541111410016401505820a940c1d41e503815801290102070340c0c072025001710000b041c0c10b01492019044140102c415192401d08149009007910a0701d9034822450361550042000d8070050500300003440e480017406441001000352202403c01e1209071801c2140d225035400703000303101071800071407560151946010440c1405880d0822611a1140011410a000103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 390114163 1250 390112913 390112939
    0x3100b03031207050403051203011203030e12120402181303260403020a0302010606020c031005040807140d09090b090601030e0a0204020d0e0c2b0c120308010509060f0f 74
    0x401c00c115008258001441d03a45850034640c018000d0f001408215460b00800800302d04000340032050301d06030760014145101040b2035907001e9008000b0043d11074168041c0b494442c1c44206103a0103800f66a406407043c88880c6014410005905503040e404a030492001e0f041c003403103682059a04a07625414101002d5000c4d10952002450001031112401201c1c0e000c1000101a800b00702100c159210b50000c1c8015038a0307203816a00c4401a03440c03180c141d41300070080043c500303850300501d410038001d180103458580580c840d29545041903041802e1603008000100089500021a5000780712007141008041020340c0051400240a03040c00c0c105030321510042c00d0700c1000d00982d10788030f900500856803425640071540240490300d9400c83e44d40140031450700203040041da003501c8040c14140c20107400c10070b40e1080c01507901500c000d590b040118031b404200c007200d5103095040c07140a520341103010340c5807008209007004010402c5018000d84c031980342132611078112128684000f141e1b500810b400e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 390115413 1250 390114163 390114169
    0x806180a0b01030f1a0415110c03041d0a0603080f0901120515030d0206040b04082802010213090b0a09050c07061a010215010303050a0f0302070203060a0609061403100b 74
    0x340680141014562500003c00c11140040e84110355100d89818001d14002d41030300307010301104560140c90410102e1503170081910325804002540034803500642403030f41d4132030070301e2950f041500b0600c1e500d002c000c400e50004400d05144ea502122030a0280708044c1150359207141401000c4000e0078405001c40c59054980c0110200300351a042e13410300700b20700e180000001c80001288202e0724020301900c104049004e1001c00d0403845107410190511061325955504155984a03103810158a034106045a0b4000250b92a41c0d100039843d500160721100b580f43d507142a00c41a50046611514040c07201c0c002d5154006204211030030010002800e643c2e1982c40c25107485170301401001a4074168980010000205951a55100aa080f01d150980d000c078a40c0c810300d02808040c0110b0401e12008606030300c14410500d00c401e41e843d0150400f0725031303800300c0c3c03500009496964009440341000d00c4080100d100703140c0100340b21040c599a055609010a449402c4d004161418039101c44030000603407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 390116663 1250 390115413 390115423
    0x90c0503010f06031b0608041103012705120715090302010b0a080f010c050a1b0312050f0603060a060b09010509060f0721030b0915030f120703090807080618 69
    0x8400503000344400e401c0340341050000d205501045810110a60b0303c1a45076806130b40e0321059400c0c54603414a240c036180c40d004007240c640c008040d03056403121204d0481049400c0c0e000c1c226200f41e40300b141c4200c1d40d403500034200072040000d5011020140002c0d0045421460211000348001100103511680340c20704034054009618865000310100300001444100060145164690741000b00215010100b0440b40d900c940161138000036107003180f072800e0086082c111414207229040c422101e00024040c0300680300125440f03148419503d0803c010b6003000c0c408644e2000d07200e4000c02149040803519411400307482d403640c1c104040403070442c0850700c4140488401401c000703507039a00c5034200d240004410941102c4007035107009907441c21030707103c0c000e00849564280051400c0a187d031038050b0010003003480b489182c0d00d84140e5020b071030300c20024400f08200802804002d40c1d500349034280502180b0080d40806002d501c8007508110000c008100ea03500041da44003081c0c240c0c04841d0600b882d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 390117913 1250 390116663 390116669
    0x4020105132106050a09030e10030207051507031406010801090f0e0a060b1003050103020307030b070c200307061103030703050603160905042013020f0d1a04110a0e04090c 75
    0x101882e0006005807000030401c4030745922600e0248036950341c1d40d0020f010b0300c00c0144000c0104014801a03041da19180000c0e0f01c1410051400504026881d2a800c0c980305c0ba030103422242c031155000b48080c9660501415541c1c1c08416210802400c001e400208a403a0522400d40600c4d52030401c19034000940d00243c03000500081280c03002d12681c200b180040014a01030713846030409a089144c418000e01625040f2500140906015443c50b1525048600014241b100300484140d41c080003c0344511079500740e489200c0d50b480300b114010709140c0b03046c03070f203820010500802680ea1030024030b0000231a6489074143c940070076180c031401c0200e848c001120745851259041c003a40450400010303882584114051201071049808100650f103074486040081e0780c002465003162607045c1c0c08c035001441941480980c40c1d107000303107200c035a40072508028206241c4034200c6442090500c0d250103420020488251854981004200d010348082201d59076a401107032120070807018804503201d15001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 390119163 1250 390117913 390117929
    0x11101061a0a0e090403050904020901050d18020901050607112704060f051b092107030b0405010c020f071512020f1b1c0c06020405030703030503070e040b01080402010513 75
    0x10750740745080001466000004518009203840300e8a2400e8606540c2d49806907825403612841d16400c2d00c02d02002e0b500c60601581400700c20420507030000c4152013214a40c0c03641c1400b801c3c07090168130420048000c1a840a807103a803062001c0000710b1641203809062000450300d0711a024041e40710540040a1403020280000304001003200b4026144c020700300e00b0300f40220030406952485d444400700c00740b84a80d07414400041c49108114102100a41003a1011000c640e81150340740c0070042c5080c4141c2c1085880040352024441086030074081d041826207180040c1c81d5201441c4041a13448084d84240e55030345240741f00040c0124002c4104110030f4032040350956403a00304800c040340941c0000d000d08100344420311102142003010810781c031020b440c0d0000c00000f1a2806003228001810682034940c9070742000300041a940803c00340000b14426196503441e40b07801d801c05001c1001c10034101d80510300b0a020a15a07a80c0300241c01c0e4400e9090800540b103020f040c1180240c28415000034038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 390120413 1250 390119163 390119189
    0x3091207080406020706021c030b030c0319060b0f1008130605010603092f0d050c0a03030201060f0806010b09011b0f0507180b0609010c05211308010212040201110106 73
    0x3400780301001802961a580c00b1181102d569042c202e0340d0345601c20100c6140f012204490694130301ca178014501500008040720702c078030025000241048001703500790f4000120f00a041d000c004250154411640c1301703c1e4610041d648280c00b25204a5114260f601000003200c006030141190008072543d49400003402c2003190385904020b8005c203d4448103880035003da070f4802400180b20101921280b0071071a054414616031f50522582c80c140c01012202801509049010f548a40c04038400942c029400820900e10703102c2c1e81d0f0031001494001c5200c9401440041c442003003518100c42c983e0000f843c1540403c3c8159140e550404c07511a03004102e0a0005901010310000003000d034180c40345a00302000756540f9002c403000729110140515002803080c00018115070140141c0f64a5078005c90513944918040642c00200c040044055100c6040100e8491b14540400c01504050480c000003145481004419403001d81c1e80144002d040003141440a401508203410200080010791542c0c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 390121663 1250 390120413 390120427
    0x10050d03020a08121509060f0405071103071a0709081c091d0405060606160b07141c060e01030206070f140706050d0e01181203060e011403060c090a0902030912 70
    0xa4544134184c40c41c111480c210400090380b86032490f805402800014030090440540c0070510000d03050040041080c0407001c0302d540c510120500050080d188100c2c00c5100b01c1a5594030215006009400c4e5404c00603c0c050601c081c0340d000504194041c10041044110180c00400b150704840701c3c2c10a469441c021f1510880c44050301904a010720300c03034803e88556a44103414000103006044500203070f540c1d19181140414100490290010301910304890b40300240034000756036a2007181c00020500c18440090300c02d0000d0710441d800b625403c2049115940b4580014909001c0c1d410040c5c60b9a81c0c001e107d13020002d04002100790f80325084e041d201c000d6941d0002410036000741a61407685400c1c8040043c041c0011b1290841c2c035500c0b0341200982442c80e464031082080216218410305944082c0842d4842e040501140289074465030f40810301280014141012070240422880060034003c0200350340d00d1884080a44030540c60041e05c0e50743d15030314149003200340500700074000c030009089 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 390122913 1250 390121663 390121687
    0x3021309020d0c0e1c1103030c0a030224010609090c111b15030f070809160e01170d02070b0702030106050a0b0306030d050a080c0703031e020d0f020310050d03020a08 73
    0x40702d401c3c000d40c03a00004412490705010507401204d11013015071101e030f01d0380700000d00580520200203101500320387c00c120261002d1450400d804070203801580c4040c0f10b000d14a40210718074142c02c489400c0c00446945400000b411fa00e04d640213920020380c41d513414440c0207201300c65103129105040111441960445444120030403003804180c05280031070602240b1040080c12280070b0480240c83d2090307542e40309030440c4d4421001c0d1094445010b198070302061082c00001d0390018000c0807090408551504032011405204101c0860352500f10074000003001e40c000c10f410044070001032070380c1c1da84e03182440024018074585e0003141d481207260078080349000e0440051442035905500700c90207038508003404e0302c1c0c9005000303000000514000000c1c02082c2403001510440748079041c045a10307400c044200d4080348000040f00981c1d50b001c10b03030290703070485130141c140703042240d5000314a10300303080450b004a4100c070300034240540c1c10711030700b402014400c1005212854028a940e91600854650 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 390124163 1250 390122913 390122921
    0x30921120b010507020d02090c0c0a0c050f01260c0c030d0b010905030a050601031e05030a08040b1e040f1e050c0f01050414040e030415090801051506030703021309020d 74
    0x4180c40d894040d14040035401001242c0e1216001010750102d105142e007008070541008010f26510303030051211010801e403c000c07100805204840c0115007a04000074040c441c2c00c440303a2181040456683d900d520400d000d8410f207015410008055559201882041e09100b80c024600309407000080401030484194448131035141c090740c1d0030282030b56803400c150780c805000380040e100c0e800000041000401c140d240485181026130078101c050700d2030f104c0038215005001308102140c580402c010800800c02921507201d001440b40048001445202030030481004100501549903044210180414035003001c41000d01825105403c10813403034442d44801e10070519500442c2807a06180e903070760082041d101070310f9440c4074015000350b0042c2044003801c04800100b03c40d010800002c1945020700e08204000030907601c9884026150409080c2100c0340100280040c0c03a281320080c0b003030340d50041201d4208049260160f1511400154202c046401e44e12002000d0f20001d61030150ba201500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 390125413 1250 390124163 390124187
    0x40b0a080f1e070e090a0210081506030108030a08040c030b010f090f0c0509130f02161406090c10030605060304030903060c0207240203041208090a08011506030921 72
    0x41c0d500ca4108190208408900521681c0c243e030828075050119208408070f181d40506403900f1aa40c00c880d40c1c0214030f030707810b100c411074000600310310803c241074a0004000d8412441078450f203140d5890b1548085d100d0107042084420003011401250a002c5100d20601c05550800105c1d500c0b0359440010410b4a0414860707052051704122800800d03143c54401c401a0080d80e0301e07120701e460604020080030a81568100316081da0b22418010801c03500d101600034a0303030441c81040040d8885c01e082140c01840c03601c4401e5030b4441c1c0304101d00076002083c914074114094850741c05400c40e508084c0e0162415400450304584088100000d01d588060300b030741140d0107035a0420080200640c00ca0301c503602400f0f001109003003084243c20100400005003a8054284190785c140703a203c2c4586000b420004506a6800030041f83c42e01031441d080c280000200b5441000f0440c9020542c94244000203070300c201014542c0da4031110042c09645d600306481058001c81641150014080c09010f00c03060f05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 390126663 1250 390125413 390125443
    0x6041503050118020403020114310810060803251202061806040308061012051311060307171b1309201c090f050c030607031404020f040b0a08 62
    0x444146500f54462003101d055030f40680d03c00c40c1d10048101c1e0b2191580c403064420480c00201110584030b00080c04400800c01c030380f85611f216107454513a802c1d00d0000407808290401e80f90100c10460000000201c41d0200d80080f07404c03001e01c0c2403483c03854441416403000390061130400400d0366140d9001c206c1c0341c8905074510514000c20020100b1903994881100c004004c21044030200398203160003118907019142a00d0403119411f07d265094050340d0003652080b84103d4008447c1c0100560790240a0b07910b60261000390840c40e00f10b500600d41480701507101c00c0381d00400b010480d40c200b80c02c034a4210789000402c10ba80c8a0510410301400860381c030512480b180781512866010310020034110450308164032850901041c4020854109203d88541074203680e10811140040c0d080c2520444c07143c084c0001e00310140f5000f0070715003002c20003080d42c0100340c5850320920349801d0706001e0350b40107034054400303840c404101e001003070080c4149480d080d03110442100000701148001051450300c0081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 390127913 1250 390126663 390126689
    0xc030204051e0a0e070206270a1506060215070c020102010b060403081305030627070509010803040311010507420e150c03070c0f0213020c0105130b15060415030501 72
    0x11320300500b03819800c4d207250005070000c001207001002c01e010174a100b030b50b204001c17828403010411300301e290469080307007140c10031504440c0c45e01c00031a07441000010982c2c0e002405191450b4022000e00c540018102400d2050741100041564800d41c013403c50340d01c0140225680d42d440e0700b021812a0040104011042c404071804200c1e400c0100d00c2502600e0b400414400c0305400100122802c1c08050395188070b803080460026849c0c0d68110342030700815010001c7c60740d550960070030a9042c019851203e0500c401080514002114400f00c0c04020400c4c0044c106024040100c12a122003805107181d5800004000c021460b500c5502040540340e040e8210f07413002c1d10000e480301e50040708541041d0400c03814000240b60038020000311850b1413080ba070107000300e8440c3e40000d40d0041c0070310048800c81e601050618200c0c03024414186c200c0389001c0384442060060751400700441c001071010701190a402c0da50481a141c0c50155005442c0041840046541041d00240181000d1064094227214 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 390129163 1250 390127913 390127919
    0x1303061103180d09091e09060902010207092d020c0f03040f0608060d02150f0c030405010f0c26040504060e0405012009090c09130e070b1c0c030204051e0a 68
    0x4005081d00c1802c0590710b13815455494100040010701a40000d4200ca000c0c0c0d40f565400315800c2d01c600b0b0309103841150005501181400024980500e68110340302c140e2400b1005118850158000162000074010000d070356111603840001a0103108214455071241c0309400b240840b0200c0a0025904000c200403106961100200c070ba180d01901c1d800d801c1843d50710baa03009401c1c94500d016015048407121494210002003110382640b20010340f00c01500040785c180015a484010b000400710103192150203058941c80d80820660780001da40c66880343d03c2d03030418809082c4016a0010200100104001b40d61505003800c03540d4100c1c0c08030f0700c6510301712040c0741007400b40c203411110701407120115044c1300b84c2c0b509001b501503000d041c400410106004010043d40c51444000e4840000e580204400d00786c00910b526001d06600710383c904c00b0051040b040c1200004242010800005901160003103110105038001c1c440c03034020b140c0081300c140107200c49280700715a1101145003078909400ca0303a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 390130413 1250 390129163 390129211
    0xc03180302060402040f18140c09010b03041a01050f040509120c0102071b0f0b0307020106090509010c170606070303090f050d0908060c1c050a2421020a0303051303061103 75
    0x417580f142203a241031f0410180c0850f0840b405007520542c2d4000312020286400c0c001000c58074268018071a80c0b800104000400c101003549048440c228003005805504102c00589100d5565400c1c0380140c2d92031000464440c0c0410604000a081030301017035071a05896003c034041d512002d000e07550242140032102c100e0a0365a81d4400311a000304030340c00d03554107101400d102c0340d1001d040c01301150340b40c48000c100c54920f849070b10302803c0140000120010068800340c15111220174080600c25071900300603864072804103d6011540c580341c001610701a0f45030030356280c0f412000203070041c0b0911000780f0030550084041d8054510b5001207450700d549850848100b44168404240707015051016100c0000d455048a41c00005881c0e0100300da240e125102c03808807901400f40d00d1713581035400c820070040c0c1c0e00803081046c48210300ca06500015240d0003188680303070203210082c02c01c0800116100d4a4401d564141c2c065036001c2c0007031156140000200e14913420a40e95092008510040a00502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 390131663 1250 390130413 390130421
    0xc030e01060f080a0201080916230a05010504120f080d15080a0f080a0c15020a031a030a08030903120906011502060702060c090103090803090303040615030309090c03180302060402040f 81
    0xe1000300003000284226401141d07d00307005050641584107401e054002e1400c440da02802401510a26500c96480390304a2940d002c004030040f8041d804241d001e100d01d90740709003142d081d24088581e009081d27801349010f00c224424181c02924422000c24110103d038001d40104042e1082c0d681811201c0f030300ca1900d10b88480c3c2407880140800e001418640009600b1005803210700e80e0343c1010345001d41552101c404850980c000c025a86070300060039210a509071142906641c49107504603c0001181e0100c0d80e0340c9400362003d02108030220004420200030811035411080c0c40409040600785070006542c2c1e13080a00a0110b40c01c0c01d1414600c80c240300180071072156600d6401809a030303c4100c2c1440c1d49a1000144604250700d4074a6100452039141c010b50040c0607041c002d580d04d25103410070f407044814005004211002d20001000465807000e200f07425101e2028000982da0b203064004c1d0f000303100d44100f4580403500b0b041030809050300450b12912031402036405001490346107200804035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 390132913 1250 390131663 390131669
    0xe0105030f07080303072f060708090a0314030a1e06050102100207030f18052d0d170a09051e0f0f280911041502070b04090e010b040c030e01060f 64
    0x2503006100248000c0c0c4147d000014100440020000ea004140408044007d504603c4a8541e009500340040550302c04450b50303115008002030480000e060360001c00302e0301114030201050a000c40421aa90203990241d00801101009000903025820b0000098282da100e0365015005880503890b50792401d00846076100d0349540d410141c01c03e0203809503580d102209a0803030103c2c2004000c50a0b8460035a08100b06a82c1070402840307000090901011800707004125002d00c8018404800240c01c00207c140b0200d100b00d01075844080c00c02e0f08031080c41c0710b540329903801090440e00d2013000c0e2000300e41c41c2162009079480c0403c038540c4d03001d0000b0303141e4003c281a000128881c01464442036007070031190b4014a01c0344000b03110f56a10303112040c1c41e42012180710040d00080d04018400c032035040d25012041c0780c0040c1410500d401540c448500030b0f44201512544c44400000042c01d00b0352202c40d5042d4004c1080106c81041c4000400800340e04845440070b6190004c0881e01c0044110181e0803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 390134163 1250 390132913 390132929
    0x9032214190e1302060f07022b081c1508150105061b0a0c0608090d030603080306060307021e010b01120501080d0f02030717090a090e2104030203070e0105030f07 71
    0x5510315000200e0000e03400203001000200304992003e0050342e8010080106a0700540d120b61a04030900400c404030200c05541218124841c0c50141550f5800c90303d0030341242c00064a6803100d0800480e030540761601c040407103590785412504004d1003038088014058800380c1c012540c00d40000120303010b0303a40003070080690160050240c144103190780642403610564120554400c000700e503807000740c0045103401000108151408011101d0400c000301104140780340b074180441032075a12582840c1c44003600a80c0075003030010018210900030404110040c1c40c000c0381000340c400894502d0700030030500c81401d00141c1d00811718002c40c40306000c4d46040e41d801c1d4001d02601441050b095496810042a503c2980070038007da0022031401103604046001100a6aa0701d808000402090385140e410503501c081c90039412040354400050616032814101c5a4028a0540340c260140c00c0d0080303910081d498455144041020106211458122001903080b281401126004243c861000d80130b07410b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 390135413 1250 390134163 390134209
    0x628081f2d020f1308061312030507050c0f0c040c020718020a030605061801020d0c030e1311131404090f03030506040228020f0d020705040509032214 66
    0xc220700d040280a00c1d000000000186008480d02440741c082d005581c601421042c0c40c00200000e00b020300039070340d01c003901c1c07200a2200e0000340c1e06c070030782c65120f6884070303003015a03c1e0005003090740074000300c80c050141e000c100c6032415000a10141e40303c118000d02401103051140183c140cad400059401c050307602e2003ca144140ca0780d8504e0764020342205004004168071480b0005a5481e43c02c000c103404a18032034480b0449080304006032416a0f150061410441c0380c800070800320354400120003c0c0c0c14101e6990305181d4080110030090061801e507004403a00c005002c061003215a0b8200c0c040354100311043c421020940c04202c101c4040e0710000c1c080c0c82c034400115000a1003548580d0340190018801400c020051910060540741401d28100c0c100c0304601c80c0307910903010400c203212000b4210040c81d1203440000020344940d1301e4411039028540b101c0114600c3c44051099503042003981c0c0512482021075101c4e14418240380c450303140e210180441a080034104030512640c90102c04080107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 390136663 1250 390135413 390135461
    0x901050a080c090604030b010f14060412030c0b2e060912150f054003050903011104050909030a0c0201050c010b03060a0209041d060628081f 62
    0x6100d015008195111a900401c80b04a035913890030040c0028600410040c2c00300e41c14011580011002038000f8a01e0820b160501180b0341e546800303c0d8142ca040c0c003205014400c19140688511a51110080150f400f1000b000783c02142c02001c1040011910429038001000b060301d0030300410203001e00e04c0002d510000c00c0c42103c0365040280e0740b1a208001184416402210780001c0394500400d550604d034850042c8000f0501c02485030b4410507841082400c00c0030740380c01c0314074114a001d0010425444440300344092500403001e85034101400780007800300405110100d050381d031040c050703940f00780741c00d00c0442d810348000400c5d100312600c00c0d140c9501505240d0015075141e0481c1c40203410940d02c1d200c140301c00b52410b00202d0f01036580604050380b04c2c1407020401007503424510307005410780030441d20b14094000003d25180c12107800d80e140d001e05080400082d00381c040f18022040b0011050800184140000540e040001c03001da104039440f0900052032019a41c0b080881d080781d4540640b24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 390137913 1250 390136663 390136667
    0xa06030903020a0609080904050610210608010912020d09060c0809120f060a0f090335010b03060a0f24110a080c0609011e0209060d1109030c060901050a 67
    0xc0300154000e0045610b100081d543d508262401c02c401114003110124a10080741440d0090a80100085910b054484500ca100403c20900071090540b05040f12411107106180c5a21110103456680000c1c03115805504202e182c0305941c10203180144503468500d11950710894052042c0d035aa555529400c07600c5458a00590300322210060344681c6445203540515410060001c80418240241190b4900401c00401302d50200c0ea0390b6441030300b000003020001394071840c036401c04883d40c4003255229049040f0505110203246441e040c500750310380013294841c030940145d48500012070761146010385841c1c01c1001c501c42071007245244d0b0300c100c4037040141035100f00325140919516100340c403074116094803494000d04650680d0700040c0080c4102c50510144480e039409120301000344030103801080383c1c01c82c1402c2202c00320009039012400d02d180d5590141150f00910107088e05101c0c031580721000c00859030010320100d1003403040000c0000e4a0805800360341d03444105840340e42c2001009001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390139163 1250 390137913 390137921
    0xe0a1503030e0112050f1609060e09100504021626040b07061419050f1017120a1d040903020d050c07080d03060323480f010e0a0603 58
    0x42c42e8140300e55448815900740c042d00c9042c2c812010107040400c40d052031090b20140d0071651100303408004032007006103d915081244011815000d480480c502c0e0f0780c40204603400c1c0c0c1190485644035000181d1460002031030525040340b24080e0720f181081d25805500001e005e0440c111502d0705800c10b21080208001241c040c00c6120b000f54008905001c0303262883c420290101d800741c00e0800e119141114061907445002d600c40d01e902c4c2c03540c4181c1410607441c3c006c1d24040c80f42584880f0b41a4801000050a014a0501d01c9606810540716203583c500506105040440c43c0c0d00c250a00e0180503851416015030008240c0580141c9940908680c5c102c0301c0d035001490745909840f078000000781c2402d08021071084d00004c0c0e03038000f03122802c43c42c1c04100008428a6003249401c10902c50451a01c00300d080d11089100035031611a4003800c103029220264030740982461804400e0b00b01540710307000d017040e80160504513100000c40900ca00150b6001e405500100d40015032110309008041c00b030343c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 390140413 1250 390139163 390139187
    0x180109020d080a050c1618202a06070f0512070513030c0902070b0612060109090c050904060905010f0603110409050a02030f07030201030515010203030415020c070f0e0a150303 77
    0x900245031085c0c02d250070b032070100d88024044000c041d104041080e44a40c44035841103400800c8288820424400010031a010681150301c1548001550110410030240c801158002c800c20b04144012231400007611050200c2e42c1802003181d084104403500c0c4100c0440c0d82440310300304940640e0301c80f42011540c03508454810001e803a213181c00440810006a1054010215a0009642c0e8040c5242410241e0000383c900b60080315005c11540840394080b0f201810754505080015010100307003030440e11713130004e9400207400080070410f000a1003a10f400200c0c290b40140000d024001c1060340c02c07811a072903072201134143c000c0040c005086242581152074101d019800b2260b907145940c001900300307030924004e07508980c4164003c108550b054040ca69000b88084400511148041c00103500d03484010801054650945070309040302280380d050710448010807044804154580203031369403401c0f050003964a5446104000341000409004146100407000c103011652441c55605403a1800004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 390141663 1250 390140413 390140417
    0x916030b0301060803161b05030715030b180702150105010e0105090a050423090106030b0a0902030f0601120b0c0301031101120209130204060f031b0e0d0b0906180109020d080a 77
    0x100f80000c0c1004204003409102480050a1100030b446203030000d0341d89070001c080b281c250000a01086241c0d408141c0e101160b01005200c8205000c8000031001054071801032680a50700b0780304003805031405280325120398040c5d000c6030b075002c01d12903034414450824411180000c0703031080c0c00102d9510400c042c1a4800d030150031682c0250f1544c0014043c1c0d02c47d1121200c50a107124101d103405154505e54a401c05ca160f40200034684c02d6403140140040b000b000c25080a4071003080c08215141004414501606201950301c1c5585501004d440b21070020800d83d80040c00c1e1012550056040088034100e9501860510b207410341880151503904152050805841c1d0034855984a034580a8540400020001005035210b00341318000d8030524445c4400c1013054604013030b0342154141106615003545440c10004010440b640000e90200e01c03c0d50001c1c0352080c07a9050051580c2d0000c0da4500404204a42c0308218400030042e500300c825140c0d010b0350003501044c2400118000c040200034016880c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 390142913 1250 390141663 390141671
    0x809062403030f0d0b011e140f0c06091c031b0f020715020a0308220b090102041701060e010506120c0310031e0309051207030816020d060903020601050916030b0301 72
    0x31850f040890707001449181003c580705c8044106540e0f0040d500b4000d500301c4207084044080b40350740100f42d050f0a005d0804030070300028400d2101700c240310548501c0012a8104c03066880d06580b080e8540d80d0002980c60940d26440c6030721402402809000c1624040381d640c1c0e0584c2c0c81500003100d041c00100c0d056000d50103889004902030314074015106515800750002c21021000b031400401c0c40d40003e200c0b8944200398031426111541e001382d142200c81d0400c140e40196122031040a0082c0321326403100d4140c0d0b1450f00709078002d94044d084841101e00700c040c91400c2d680e84100344001ca105129020210042036030000d10b40d842007002a580006c50450400391031a00d0740c0e00c80d0120780b2658600c017078004030040c0b4902015031200002c40580b000343d41c0c001c0d20b0203580114513541c0103180002071002c540030401401c050543d254544506400070820b15030109541010001000c00080550050141c0000411344d0b0800158807030040d0090700f621100c2200c9000204d005103a2101081c1d815522 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 390144163 1250 390142913 390142927
    0x405150102060f10030f03110709051501030f06120309080d090803161a04080d060f060e091506030103080703030b0d020f09042a060219050c090c0c061303080906240303 74
    0xa1b2820b00c01c1c07407500c45d864022540808110301c51920645a00c00e1000745d051a0800c00c002400b580c207001e20b68020f090114591a50000030340c003410703d03a04a443c84414a450780d0b014075600c0310606044400c0507050f2040d801510b2070886d6148081e00030103505074410054958500038440520624501648128180c078411102030302003140260b40907640282c012820302c8a140707140c0700c2c40e07004180c04440b0a07000d920b040d1025109081101c5000d11605c00003002901e000c5244541080c0500b0042c10b0326925a16480c10341d00e0741c2c10a040c285d0000b0b02e440070202c51030800e44002000550001d000c485501010010040c0c1424010012070f98110102d4482c0d8450306005c1d51025424614019208101e007400c00c000e240a0030016518202003034101c0c0c0c800840c101082c071807132030745081d1600364140d0342c0d01c1c25203401d41c840d1074000c10b20340c410712041041c000702081001c194548a0b90351401c03140c440000031f560340c00b4250b8900d007682e0320005104c1111480071149142c0e0440203401e0b6801c2c030708 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 390145413 1250 390144163 390144173
    0xa1218120507170111041502061303141c150e130218060f03061503010b031203070509030f0a0510050703140114012616050a08010509040f06020c0c0405150102060f1003 74
    0x20075481f65403011500505500f0050f010b00c480c0d5803146d45000603085214031500d0081802c01d41411201031402d0021b201d03210800c183c1d22402d154800380b42d062041c00b41800000120020610a40b01d0420f001400320b00c4044160400440e465001003060807079010a0243c40c0900402600d01e50740110704400074401a2024822180b01e82100141081c056610720140740c00e4802c5482c80390b01c20b0700311841502c0c00c6040c44e02601d400009516042e610b8000c0320b008285810f140114100e03440c403c400000040050004204004d6000054180102d4a13550801e6080e14000d11204811460b0100180040090814a4925030405141503c088002c5820700952030b0b00c0b800c410108083c00c6020070041c00d0b4400228813030304034a85440c914001c00260010100c200600509100c2d00d0300401040901102034402c003010b50700682d0441d5034650002510380d441019080d014051420031740041e0742d070701c690401c0100200041c0c003d08865950040c45010f0114024840d4414031030420b004408a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 390146663 1250 390145413 390145417
    0x21060915080706050406051206120a0606091a010c02041a15030907060c020102060a0e15090102090f0a0503191509032303070c140a1218120507170111 66
    0x31010410800001d040146603418010750f03422420900c0701c204420000c260b4840700302c0b10305030740640403985284c4484e00010303125084c000c8000071030301c641c1d44060300b0310007a03030321150031104200802c11014a280004562503100700107094041225080b02501600b0b05412075020092240f00685035086240c0c0080c0300a0140211445038010201c10040e25050030055900980481c2c03c24901c11344040d80000c2d5500710040c100b081341038450000d800410800c002c58610308542c00c013001140c0c90f0035074005000790010385c2190b1080041c00c018481900342800c0c02c40035524050068100e146029640a860182040c0c088840c4d14644103030090000c1070b4170540010a1103542c4d075480400520f40c0c4091403141e1044402640c4d43d003042070210150300440d90302c07805a404002030b07090017941074071541019642c600240400000c0d014402101c2d03480b0480e10341c2120038001c0546c61680359540c80f6072138442710700024035a030b0180c1024000304804080150707050103640000b00c2c0f13115600400001030303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 390147913 1250 390146663 390146681
    0x813120206071d010c080c0c120c190f180f020714060f0c1b190b040b0709080c040507031803031e02040b0307050c07090e030702091501300612170a210609 68
    0x16810062a40b40b5500cbd000c1c6401d40306110a01c1651411410130b203c1c3e220050300345c8981240b07900c078200082c2d005607490700115010346035040f0440d00ca4100b420100c0d19200e000d01c400c0d40350b00640c00010406480030454030b0003528244200b5040c00103802101d010003036907900600c4184a0007007074481041c4000740810340103118203d240b503503081500d000e011421015080c50705002c0014800d100882c0005030820030301204403404036560311282c6094009202e00840c100d10004000064810305815411415450800c02c141c559001080741000d4102e00440c001c080c1842d508101140c0e1184c030600141142d4507014060341c80300c650781d02c0d41d503044a50300411038810740c2002c54060f0a501c0c001107029800010000d15400b80c2c12030b000000c0c010380d00080d24640d044440010500f4850110400c03500142c02003000304161625640e0f221448101e11100f01e504070040542852000e1681083d5001c003070a50312131000c072180711040f0303800c04400001d18000d02ca40d035000c0082c0300c104501400c20381c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 390149163 1250 390147913 390147949
    0x22d030d06090c0f051905090402270f01051e09060d0c09150f0309061508030d051e010e0417040b090103060603020a020705010813120206071d010c080c0c 68
    0x11461502100c1003d0303c41d83c0c280d210070310245080300001d5a4103c5c1c05ca500552028079183c102c4003484001f036405000c0d94030704940041c0b000c07075020f032510301075408002e1020301d1007001400004d250042044090b402c8103804d000480620108003100c034814004503104020042c983c1c00c204540001c145190444007440076443d131a0700c600300301d15410141a1014002c024031480d100300310310360068400c00868803c0380805a0380e07520707007041c40202d91001f0440030400c5168140241e0320041965241c00088904e28901d140c03d020810020121202c06102c5461601c13900c416031900c04c080d506048010401d588600151045032030108051b0b000b00003130008030800f01d03102d1200c10001012210aa048902410700c10001040c105400140c260304a56003440c0c036400e240e80d02e100d4001c0803158900010075104486040c0e8007040e4000c60682d100d00c0f541e945800004041003190061070300c401803000c0c0403e0b240c00d000c40c04170344003400820801000e80200ea40d003055407008120054407203110358079 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 390150413 1250 390149163 390149171
    0x80613060c0504032103090206040b0c0c0f0f101b2031110307022514090a021b0709060801051902070519061a10022d030d 54
    0x40250030722401020341000d240080c18242107030754403511082c0001918107404025030031417a43c1407194101503907503603020f04480e0711250f61740300c44501c1e0b80201d066411107001d0f0462940c0c1c542030040c144113a07004002d01c14000010b4031802d03c000c0640080d002403c00c00d28408804000742207590181c50507110b6062401d00e003e64600038552401a40c01c21071090070b11221281c8191090802400c50302036001c1d00c540140354000d074000003002a10642c201a4001100300304545402041803180800c003641203104514181c41c54003186a940d00489880c61b0045031011900c1c20030840e00b0798404600701d40186003030344d041400116242c034203460611076404203405201040c02400f45c1001000c08100900c1142440541d0820038814164508402c40d408100801400000c1104440030f007909010f071038201d0042c0c20840c024001d2480403c0e0a0b001074803606006080202c08000d41100a41c050120308c010501c80781c0c3d500b0f0060100c180080102003000c0f016010502c01000c403860f580c40000b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 390151663 1250 390150413 390150451
    0x62c030409140601080708061306090b01031b0507080f070b040b06030c0f09040206030403090b040807030501061409040f1b06020f10111209011e0e0c031b040203100806 74
    0x340a0700c651240316807070391504609128413a60404005d40d044240e9003491202ca98810001c140c038904007111a0035141d0404500040c00385ca181c4c040c9900d407a00383d0b414040300c220b081c0c6c55901c60429000007000146c00700031243c003017095603003c4d010318003540041c5850981c0d60b44841c23242c40d100361010b44140041d2806d000261034104154120705605840321b017000700880c800200c3d00480144040d0090000100041c10144114190781c00f401030f4600301a03d030780c3c1703408520340d94140c2da0004450661800b00d010810086109100d02c40c820b0003042a030650307440d69180000e1182d00107045601d2040a4040c00c02d400c902e40d4100701602c1941e0040c021180561042d07841c11021100c401151460140720030500b090390001c0f01c0c8402c8614842600301d8440916990040c000c01658206c5030b14100c0505031010a1604904803010328242210280b41c4988109034985444820180f007800e04410320701c03003070308140d005990f0203458010340c02075580e680c02005003054411100090489400150f807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 390152913 1250 390151663 390151679
    0x918090705100302120a0b0616020f0a0f0f08060f060d020a150c1a06010c030f05131203030e2b0c0b0a020309070b04030f030c1407260609030403062c0304 68
    0x80c60744001410400c3c8001c04880021507500d21909c080580245a159105019520b8022511b840c280c406405002035540d10400c091141c1402d000d13040c003813001c0100000d840380e000140b07603004007004121101c250322244200403410b41c0b00d5400702c4e0043c69a00e00084d00d106000c03511421284691500c521680462825501c06410901030f0200300000000380021030364804408a68554581024058a00a82c01c11b84040c040d0300c103008501003044201060111054104101c514800e442c1841010380010040e500c039151a500203e07454104a0300d10080c001030f01d0360101c100703240d0420304243d4070320780c807017004400c070480d814450203070000300340303c003580c4100110303c0104580c151650801d81103070742c0c0d8151034212050180403c41001080d1040c0312104c03604144400d508001c880100342d9403850741e428110300150400244c405954414002c46000c1040d0344920f98010145290509560b1058020100d03142944a1054203034030310707105007612180c1500201c2c03086004640311840e007044c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 390154163 1250 390152913 390152947
    0x411130509010c0c051b01090905010f03030f0e0f1c05010e0c0f010f0f03270b070906140301030204020a03020903030408030408060106030b011706040f0207060603060608030918090705100302 84
    0x40319040100464290003c6040407a01d408103404c4c0d404080300046c44d01c0300484260798282c205a21951405000103071103610b4564850407244a92a8000300f980008400d8403000d1140c80c2d52908610002c05002c0545011b94240c1041007154551002406480d02e51307508403400c0c3c1a00107965400340c0c0300f0740424584080410b81000d024a00000e084503629030041c032100c02801c0d82c8051646072000040d40c084400413486078071000e501010078000f124140680029410b4540c10b02140010f58041030451203904a25807180c02d56040c00c1c550b902c0c0d903080c0402075108211400030158203120740301719560140001c00007008440029a1079074100711003503041c000103a0182d4145442d101c20b05201c1d0340c00c4083e41c0840d07828801c200c0310541d00c080100f000303042d15030200800180f00181080c01c129466000800340c0b40624001c001c00c0e526400d00c3c0d07a0b01d106d0555115846600ea0400f02c549035401c8005c9644000300f081a00c14107540e0300c012601c5a9030007069000800d030041044841d00d0041c140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 390155413 1250 390154163 390154181
    0x50925030b0a050103030909111603050a030e03031513141303180510032a1d0901030b0408070c08031222030f030b040204050603012405070b0f041113050901 69
    0x1d803c126a5243d036a0150205596100780b01099441d0b070300c400c034a0341348041555a05c000c1000100c1400d4800d2400908a910035600c15020030b1400f0a80d03004000d00006603486140b40c40c1a0300c010004007801c0141d45880000405541500c666100b1500380c10948003900441110700714070507091007441c018001c04808401082c900c048202c0400c00d0f50740b8046010708a081c581000201c4240340240503000348241d82d502d04144140900e940d4100e80c2c000f0006440c2e80040282c948032044400c100701105c3c2080c4006000084c00601042c04202c0000c000d100c010710034030350105400c0c1d54400320350a50304949580e0310907410a800708400c10004a101441c1e44800f80d1010050004550703001d062221244990b01c10590b640075036400a0b150380d4100c40180500410721074403503964501449030102c400b0210403181903003c2c2c41d05022400b601c2a6800076501840011490303880103040145420f00038000d54200d8061000711400340c40c0c50b5124001c1c41600800459285000c2a01909482c1c4401d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 390156663 1250 390155413 390155431
    0x6090a020618040e01140105210607143702070f030825050604060606020114070f0905040603060c020706260a110a020d0e060408060a020904090804081b09010315050925030b 76
    0x10000302801000860020382c0b0158a051102c13528038a140c80701400e024103038039440604045c6142207072000b44a0b48554100082cdc6254054047c81d00342e00300c2e1180094800c0744414101c140c4180000ba04000183c10402d0856406c00305d000d82d1200d842c01103d200c00030550341a000b40b000e2006011aa00078440074112500090241c42c204481c0d0596404000b00700404110045481031951132040b580d01004190041c02406960b80320b05001d4000c1c40084118000352040f1080021070700d0040304101d0314090f40020710380b07001d004010b0402c0040d02c01443e02c2c0d0400c0d035402030000719810300d40240503800e4032039004021584403480c02904813420842c416200301c3c4288404c00480030001074207075002c1200e000240c5c40b10fa020000c68041d00c4208001084030102003004150440c00082a0311109480121a1270a4040340e0900907081c074207000c06059240b054583e41800c903d03d0f08441d82040312002204c203201c91031034020100c0354090f41c1120b039103810030fa001c0041c000b284041ca0b400283e05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 390157913 1250 390156663 390156709
    0x150310021c0e0a020915030f0f06010603150b1606181403041412011805150106030507120b01141306090b0a05031b0c03040b0c06090a020618040e01140105 68
    0x1201901e0750b109110f510003403184400500143d0070704440d9038554195078020302101c00c0100c0001d010350711222540107040e164802e44000044051003400f660858903045108007010a0a100303150006900680e2412480c0001101b0b0000250741d91242861024072000c0c5007031004814508071001d01c0000b0a51440c036170050000b4040101941c5040c01c01c3c18088542c10042d01010078210301400c00100b2081c02d03d0700d2404d03514103011010071800017912000110314040ea8130b42d603050382100d4040d904c030000200364440d0b010201e0f1540c1c0c003280c14400c05041c00e000d08517140210580e41e50010035030400d0b240074411304205654205030110080c2481081d05400c0282101c4c2c01005400b00070304948900340070002c0c44524103040b00031603141070f020b0000d5a81d41c070785031945520b07180c0c070030f250002c02e030710410313000403006100802c6000c0310030b9000300300328030b410030001c02c07080c200c0c1e080e503640b56209595640c0c0c00c0b00180f091196220480400069450941c507020802840e4150200548544904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 390159163 1250 390157913 390157931
    0x20c150604140f06040e0106080706082d040f08090d080901110304030b060f1f1701060f02120309011d060f060109030503030106030f0906090c0e010501050a020c09150310021c 77
    0x10072600b044d4441d0050b140020711100e069491800740c581584038251502030407401044207544803002c0e030b200c0c0b01401c80e0385541103039a94058104002a840c03c003003004568000c0740000302d40c03400307a1901d00c3c0030760384c0107080c40c1d240750008920f0205204121181800000c0a0b20720f542c00500300507141407400003460802d460351b19400c01031800248054032600d2040d041da4000d542d44d00b05450484118416540c0b0700d90b40c0c4902410000d400c00848a0030900000000f522520596800c1c00450890740070300811000701400a045400c040c002e500d41e5522000c00b0b05110402d01604802c200c0e4020041205050106941803080c0000c1c01d01410800700f4001840859000421a070440d11036180025011503400305100c0105400c080050a0300d051651031f10910204540213030568410050011890740c0e1f410040d2031500c140b601140c0540c00602e12440c1506c0d021640d1075008991b564103512013400040082d003054001342c00c009406a0101d03c401e48852040105c1c2d00f2005410300030004981 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 390160413 1250 390159163 390159181
    0xf04120e1f0c05061b04120204090b1e01051219060612150b01030c14070302030909090a111903060b0a0e1608060d021305180f030403110d02100c0501020c15060414 72
    0x10841c022200c00001f00780e05a400c546442d80104116a046060b40ca07403420702e00075601144049044a14220125000101d00f07464021202502e0440900050200c0341340d0029800000d981c1d220150741d103e50b6800c000460520700301000c3c42c1180b0980e49442c04014852605088440d4068098100361400d041d007070200c1c0d0000c0100010502c80f0044544501c00303032038224618030030440a40e4006047d4024010240f800040c0841c0092080c0c4411600345c01c88001d00a84030181e00c10908040245c500c200041410b942c40109681000307403542c041e10340c44030048400b404c02521220390364145005084040e90b0320504254102d18201c94003580d00c001c64000a080790281c6d80740d910132551700d5011490303000c6101d031200d90141d1800f003580c183e0b100320b0040648030380041c0f0080c1c0b01000c81102e8004285044d10151080644c020507000c10040c1680e1708070743c542c1c80100100d500d50750070070580b048190200911040c80d4141103050009141c810b06100645101034100248024241d040c400081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 390161663 1250 390160413 390160417
    0xa0314180307081c02040f050414060a051c05031909060207060822050a060509010c05041508090f0312010f080607021c05040e0c040e0f04120e1f0c05061b 68
    0xe8125000503100d22a480f030100146861300c4002003280d00c0010001950f140d07000711801200d170126000c00c4404108045025100e00071103100c0d501a24140c024031244c6441107214045492007000c482c0005540d640d45461030b0f01c03c0300703903036110360302c0548130100b20340c0c09040c0b5400380c480c610140203801d10b010000313081842c015054521191183e002a03407400c0391450101f010642081c11140f1011060400b5802400c09544115a95003024410901036000b10f0454044a400b41c1c0c1e000c240200d000011244c0040c094011002c1d0300036024a00e0814000704040c08168901060358211541360803524410044680e01084c215086081000001600441d40041154500a2082800c101a042210140702c2c2d50440081801a44103000b06401180040c106a50b007980344984c0a85038120902d003803c1c4c04880051402c4074092946409912982409003401d4000e0708203a90601c18041c01d403104440b001280d0300007003d040f00782d070510004200c11a003004c1307011060328810503201074a134014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 390162913 1250 390161663 390161677
    0x70e1501020f1b0d021c03030e070b04030b090a0f1b211209050a03051e030c060703110f0301241b11150c1c09060507060f0605060a03141803 62
    0x140d80d5159420383d1036240c5051150340507030b0042c00c903d000007486034190083c202080043c2c0000f441c2040614114000249420039246681481400c2c98915507a101031130000800d1aa402c0c0074030607807200084c00700310044200350300c9018424521070300030b885407100c8110b030381c0000f01100001030756108400b080a4500c05c031f183c202c91009248010b0030000d84410b8042e034002501310225a178000207201c00132541c140c0d440c61003502c0307041c1c244415144c0c136564090216050302c2600268045407142d402640710110782003e03403480d603042030386461440800360826803080c0c0441c0b1460482980600c02010402c4014045081400340a004106c121000351045a8020058440110082d0b450f559602c0302c003c00b800f03030f854042e554410b030810313242d100c014841104250844240c0c62000e268001e406034410746a03d80e45d01400c002454886c100502403031680004540d56469010074580c60f14002004280d0381c0b5240402c0488201b110720301c0070300c030040c00c0060030040c1e220b22500d505000b008903101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 390164163 1250 390162913 390162943
    0x10e0913030306151107050d08040e0a1b032c060a09080705070f0305060c0c0303070c030302070c0305061b0705060406050c041d01050109140a03030f03060503070e1501020f 76
    0x200546180035001000550480ea40c1d903113190464100c840e0b07109140d0020540c420040d80c2c11943c1c1d402c24440000102440149440410300c002d200305900700540320380c00140d0400100d104091030154080120700540344000103034440c4100d41c0300340440c5041d03d01c0c4000484640c010001012803154a4078405010480d046844042c0c900500900405640c0d2054003d410744810685d2010640d82ca101c00c1c1c80115030b507024200001c1c540034041d00c290362090b0b1401c0701551a5640b101821603140f07070621401c80178150300b80504800704000080d04405180701d8401090281882c081070290f11001045101100d42c040017a080007c0001c111190815880000452182c42c0c4425032540c500039600b2400d0052030400d0301e211007858003080581240c5c020b803100510316446661030b89076040c1c95052540c000442c800100700183c0724046500f0764001601e40010590b0701c40c0c00081c105400356005c1c641c4024000107104121003003004000192200340000c00c00004060400f607101d0300b10b4031032854 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 390165413 1250 390164163 390164191
    0x806030c01230f180301061d07030b0a180b0108091912090e0901050a110c06190e102a02060c0706060b0705030c010e010c0e0409050106050d080a0e010e09 68
    0x3044008000a0b03034060b00d039400c016a110031303c09030010507100034007a40c4d078441d60a01d00001031542c25050707031070f00000045054008603941c84006502900c0b007a40d201e03030816204400019050701c000c200180080c5104c9010400030440d01c00100781f4400581118030382e811001e40d5a20f44441d0090298100b9031081103070b60300e01c0601800351104040b81d03200303051111540c0204040c075001075214600c101c110307030300c01c001c1e030848025580f445000754500301e0450b43c403101c0821501c3c80015208480006210000300307250380d40180e0107003400b41d01160502c403640c4072000010320b851601c4010078075190a0b900340f407501000b01340003581c07100064034482c02211b001038031000f4800b464000c0c00142c0780614000c0d94038156481c0c0f0700d50300e5005081d41711042d468140c480400742c00601034030004000c2d55036445072241c040700400004107800b00c0219695075075542d000400391211140c00004034051a100d546414201d84003800e0703125408017160400500280c0f006c107036a00d030100d00b6000360328403031014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 390166663 1250 390165413 390165467
    0x703110309030118060510140906040b040c091802030c04060f0201020c0106030803390903030903010e0c101403013804090b010e03030a08130b160806030c01 69
    0x10308510a488549415508240c1228000120415801c02c2c042c40b45008110716a02c25980070045c2a05005407850611107205400241c90f12048440c2c10400081000031a10031010000d4121104128003030085071401c1c0c01004240f0b6031f110340c001074407900c400940c038625041485690a00c5180221000c0c0080355074001d54152003581170700e22482180c3c00801c8020388908041051341c004503844d00c1b180d03d001c104144e40e04240e4103038031031a0f040445025000b000119441000d82c10101c0c00541601c400d00582d88590b03024090b4000075042c41d005884022005010b0003404020080b462040c0010b0740c0580b0b440421640c203c4c2c0c11104060401400816101c0c002040700580d1042511030452904a00003c0491030f0020b008481c40b0314010405111441c005444560445612a07850703001445200070b0107005824043c0d00180f20350000100c4c4841d5a1828201c010a1780c9400002518500404d112508540040d81000c4210000c1c042c8610580000745080b40249440c246900304d49014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 390167913 1250 390166663 390166697
    0x15031506092310120b06120c010c06110708030c0c010c0c0308130602070501020c072306030105060c0f0d0309050c0406050d0f050f0d03090606061b1101020c090703020304020a060203030c0703 84
    0x120140071901104100d070802410a428080c0050b40c0d201d1044411f940204d01407000040c0c9028042410707110000c0d4222161031350030091010041a501d040003c01c605030004600b40001c0d4858051440250f86552040c0511803c4420303240218060201b0703d8803490220b03400c101007070340c803144245040408145c2842c00c0c4019020b03850b4020901e40c00418441c0304501d0206040c010741b17460000360f0b41542041414080714100905800c5d800c01c10400051005003855002001040381d0310040307070310740786039401c8003442c107041765602070000703962001000c04205c1c051041e0390b00b00d10200c90502c4500c1c1440000303039120707840c904001c00100c00c0c0303141441000002d1082011018184060390039412a00303602401403c080007080b103120b1f1030800c010139030341e008120a030030f501101a510801d0035682d94403400790034100240f50741584610200ca1207196507044180c0d120b10031a50300980c890500e803051040c00f0101da00700d9015034200f442003018902c2e004040d148502d41600d070440095040d00c5007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 390169163 1250 390167913 390167941
    0x3140105040216290403030506191d0615030403090f05040623031e070501021507080c181309060e0106050f040c0c080f0c0d110709020c01150315060923 67
    0x2040313482030107030380030481895050f17800984104802d80c0d080c0005040c0340310f244040d0300c0c5e501855494031540c8220700a02035041c0062a440f00f00942030020040c905a041c2005270401c40d030440c00a140742030140100711000c8020300044c041505d090140c1070810b10780441454260840180b840c440280f0f04849070750030004014030010003002040480c080b980303110b032102614001d040c054070482220300000780c045103015105107510761301c2540e10b40340c503494020b1640c04030b9582c0d0301b0f0388950910544159143d602c40c1d600c05040220010b0005400e103448829260341401c08010340e403519101300f2480d1a4210080f80c0708030110b8000031105015031047c1e50070071180030003411118012a0180c04965810000d2060040320070444805901003013089910209001c5d030303c46e968000910402072000300b900501218a02200007080d100416104500b00302c100b64015030340d500720290042c0c0b4501c2070b031040001a004910041c0842c11364450b43c1500c0c40f42c50a40d0032100c13440a0009581d4070b0000034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 390170413 1250 390169163 390169223
    0x28020405010f09110304020d1103070905010b04090c051903051807090f27020d11030a2d08090d0c170c211020040603140105040216 58
    0x401441d40c4814080307603094050300500b80000c0c0382c032448600c600030410903284559401840342c01001040e944a00720840c003019599003511030014042010074460040030302a1445427005601c4600e030406110984010380702d6002805020451040c00344d0034000c2c5040301c0082401d0110381510345500703c410030080c0114204160245d62004102000307180c000c2d01c4030300000300061110f1700500c200a403075082c40941c0d40c00c806005c0d101c130600509140c40b05000144c010250341290744912004641040c411240403240b1a040c00f10000c05401c50a045800c550100d103138141001296907100d0170307184074440d1840c0c0320b490800c1c0c01d5010002c4140c69000900a0004a8903c00744180d40b0075544480360381c070f242d202e0000c008800b80440c2ea03858400c1741001d8001c0c014040d01303910118100003040800000000f04030352001244c004540c682c0200020001c0b940c00294100f203c881b130040592041e002548102d0040002031400246d4a0140a0490300440300103210201d0848444d44031200788 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 390171663 1250 390170413 390170419
    0x90510150909030215060a0b0a030504030c020d08030403080901050907290a1e020c0f041a03030c03040602070e1e15040501120204050a0e07060c050712052a032802 72
    0x30b580da00816138080745000c00950500d0400e151900d40c0d8080169150040c000e0300003000080c00380c078a141e4030a802040c0c100c3e0203404e01703d0780004203801107018002d100000751078000002081c04101030b4800340041e400f80380d81000308510b041c0020300e1510b8030309922418103030700000040c4a41e004403c451402071483d6416080e0340d0b0750443c2c10040d18103102c510100000703480c041d4806040c1c90000c6405001040c008045500150300315042000400d8610580c41028084201010403078074100000e2418100a50003183c5880c54403900a04e0700d0680d801c900040e403007000c1488058420190041460720880e8112142581c2d80b0510480391110004130a030300c41c2c2014000581c02c4420342050700705900a640600c89607641c0403150094850300d0103054580c0c0d10510042209910585041000c07911890540714941da1f00c01100210032285001521150002d04040ea0728405800040b0301d0070048084500d001c0e244a0000307920390b4410780c900707104c0c1c04000b030b80203c0d940303142d410468a2a03030013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 390172913 1250 390171663 390171671
    0x3091418010e0601091502070603020c101415030a0c0b030c0c0304090f06141302090402040302060d0209030d090608071805040e0c010207050103110d0908090307080a0302100905101509 81
    0xa00c40407140b04420340388140480c20f001d801242400c40221690781149440d0010001540340440803002075208042054850141c505545441e10301c5e801f500e1580c0c6440c07124030140b404c10103500d0348580040008584680d00440288002401c0381c059541141c0300511041d840e0390f515440c01001e845460303644080da010014000c00d801e030080d030100700035030b1040310100045512100c84d058041c1c0c40c14002d580c02443c14110241842c03158005024a110140000d800d0035526404035055800c0700303280102d82c5401050303040e0542420841c511403240d440c42c0c104800392801c07070041d0000c200074210208000003101c421064590000b5644000c1c1b070081d00c200003500450903400d03113941e1785182e0f041c014043d5060001d9250311a010b001c01c880d40c1401c1d128a00842d09100c40010300e5007060407204c0c16800d01080c62945e0702880684001e02c40c40c0b028000610132890020709119009a0003081a443c0c1a600703c00302d03000094a6400d003841a000184102c1c1c0d4142c50001a00c0580c42a0011814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 390174163 1250 390172913 390172919
    0x4080d0e15091209030a020409050c030a06020306030c0405010b0f090f060f0c37020d06090803040501051b07110a0f06090618120803040c050a0b09100201090309141801 74
    0xa4000614491501902a00c4091043c1d030314002c0706101c0d44c3c10780e5900d544014a050054a060751141c0c02d203a116000322002c402241c0042414012100026107400381c0c08010050542002d1024002681084038108110741c104210b41e009800303a00004c550650000c140850551220b00010208040040003181c440310045d1508807168841300c06102c00d401416854021031078410030390900c0c03440700e15000c08403100208080f1508078903240c050b42d00c904d407141402c001c50300701c2c07292040c1039008030041a520f00d06030901c2829545c0c050074100d00c4501074000250074812500a50b01815408102910709503900070011341201c602e50010103091103000d80004641e03402070151000c68050303071905011480400482c13803400315248220301c00301000c06841e500044a120007958043d11906107809029142c10120750400c030140c00940c01d5880001e0740c0c0c000740c5030603406000c1d0a003061000307200c8018655401000d0b680305108004030407003039900c40d864542c1c54550030882002428084006903035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 390175413 1250 390174163 390174193
    0xf060f0501121e02090c070302011b0e18010b03060f010201200a0f0905100302160648082805011d1005010f0516060b040b030c030604080d0e 62
    0x9601d010845803d000070511940501048030310303c01c090f03002085101c8541d0781110304505940005822400c55585d8000074030310501e404c1e503809000ea15130703451100c805401418000c01c0c0380340351862039104280c0d40042007200034103012294450f2040c1c1d41002851030100040c0e026040110403020064000841289041480d101420240c003450783c5a20146402010590740070059000e882e40180301140350a1a65000340c0082400c501c0c03814042410040a45801c0110340c100c400303600d0085c0354210020620a0600f0f41c1a880f03100ea0a50701c002d0105640300304150882d84400d01003803050820006031a00c40c20413000c9900101d030b0898040f820200c03121680202000d0040c0010b101c0c84070344c1740f15600740c4003203601c1c07291000c095520360890800006580c540c0085d4810340c00c1150401030001584000311042c1c0c0b01d14407654021520010700070802040d50102c81e40c02e0b01961044014a110341d900285241d009a00662070300d81d100b01140050001c2d20795040c141e481ca220748042a510740e4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 390176663 1250 390175413 390175439
    0x3030506100c0f0204051e090102340303051f0e060a06030903020706111023010902090604030204020304060902030703050f0609010c1706040e01050108010b18070c0f060f0501 77
    0x100302140d0201c19615907041c180c410245100019010b0320b46904002c0060a00e5400300c3d03002001d140c0e06404600c925040c11100500c1203448401a0750013142000c032503d1640c4450200031030300d41c00d0b0b43c0e050751114001c010400700c00320302030101038807040440c114414100344180c0340c1481c504da00046030340312802c000345c44d5002e8130385a008556014000418078071074410340000c9a0b242d8081c0c00600c0c0340040442c1c3e20415143c1a0f082c0c0d0041040724441c05150784181c445d5640c00790f100810a011442c1704e8092580140e0009031481d00400907450240e44070307400c4606803981250300584070741712424168020040d494009400d882281d1001c0107000f0000383e1054610880002c40f8015502d002c1420f0030f032050742d0481d001107114059151100f15070103030042d50191024100241ca03154000ea61402d641e4280c0c004c0703003540d554450316011410041c44421034100b901c1c050000505059100400640952001924540d000400c143c200b25198203c0843c44901c1c2406000950315010b48607440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 390177913 1250 390176663 390176671
    0xd0915030207170a1d0303090904150e0610050102010c0c0302101e062702040b07150213031b0f14061b060109020a0305011d010306020c101131030204020a0e0d030305 73
    0x41c2ca405c42c00303040d6180002c220740000c0d8000d4000505a201e5035100c1022500c0b40390000c8006407038030008404600200140f51203400c983d080805594948400642103130001d440400070011000240d0740801e40020b030043c0c81c0085800f00103019000c0308081280c018469040d24080c40c10a00d0000314030302480d9541e410000f40c21150082e55400030741601c2244550310031824050720a1100b400880c003990380c808100e0880320009440c214944100f451082a15001200e5000710344038039880e514408681c1c1e41c0948410846448041e0902c64030b0b518803400c1684a61145000103800c0400d00c80d9011041c00040c0d10320b044402c00e58543c0d0300c00c0081d40100c22884000b071700e0400006040c8250b2070030302c0e480301078001c81440343c1d90071500d0f9503000c4d51100b485180304ac032660041c2c81c0c0492241c070848909100a190298452000f91281c0130405024004684104580120380d92164403092003001120350450b0010703a20700005600fa2120318040e165141d1022101100d6810b054050300300501c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 390179163 1250 390177913 390177947
    0x3090a0b0a02120601091206330311040b0913050a0c0f06032003070e21060402040f0c270f060804050c030102031e0c04031707050d0915030207170a 65
    0xf581e507508011106600a4413800c0c07200100300d0303800c0c07000c40c805521007015126200e130318000c0c180580340c4a02c1160007401082401c4d40854030704106001c890070100e00308000c1181d041c4103212031240040c5e01c007880582102c2c0070342c1c19070071a00200030301006080c0b0300c41d51001807140003960b101c80155041c40c003841040042403e210141e0040500328110320100d412560041c1d00b10303251020110360440480c8001750300700303c0808403003040d40c860700e0240c0020a00e200c000c10080c9041e1051205a542c00155405903030306062959922503044000c1001100ca00c006800d00703034a1801801100116540c44000c2c20045a00c0104078075910041c110b101744d0040040342c200141c2002410708038401203880040c16203010094028150004003015003184034100310500b4162a5101c980c42192462055481e0160000b0401c04011050110a800700c0076400d20704e007003a10b0100d074000c4c840d8084007800304041d80060300c6c1081143d80880055a4924800c50540f1960720785005840b81c5038120b0720700c0c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 390180413 1250 390179163 390179197
    0x4081507090b03040c150c05102c0c120c0d0b0609060321090a030c120c09050601021e0102070b04050327060403030c0f17120a0e0a0803090a0b0a02 65
    0x55085410b0741242d000c1e0f9448003032049842e20303140c06c07000ba50107140f40800400200d51750035004a13000300050780385042c5110000a04000c41c2816041c1350017400384002c3d0010200004d40480c079001710f10056107000c1541c202d2254407200c0585414481c0d0501c41c0f592042a19190310309014070322020034403401c019109102d40303440b008205a40c0d8281c0303001101d00d2075541c440c2c3c1c50b08021040c003d0801c40d00007170607070944281c0701d82c1d401c04400c80355004240502c201c0e113400002d0220340e1a10a00500010740104498141280002d481d01d000005403496400103620420166800b581102c070543c0d04142182d400d41420f1400540f01d47c8800d0108002e0460f03c0880b00101885908104040100900c004d01c0c0030300e980ea09130350307510b00c90000390b5030010b07480c1c10f45011445546400302d2600c2c8440301e840c1d0f200654140700d030788040c000c0c14942c2c680e442e05c080415940d1001405d101d500d9000025240c4030740d54202d4061a06c4103140006200000350810300c5112000c540182442c031481200e401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 390181663 1250 390180413 390180419
    0xc140a03090b121519081506100504030b1008030c06250e0d06021216090609031a1f080105040506090604030c03050a05090604060c02030f010b0a03170408150709 71
    0x444a00400c80c003c4149074502000c5401e8407210384c400c0c41d0009000c0c0100348440d00c3e52440030b0700168164410034040c2c200555000844d800c8006c40c0794440b10880d2401d0203040a00c0009026004a010040100c0340803004101071540c24068580145085012079546115580301c958030f8032002d0390031450030100f042e950350200e0390544004071464150354031011584006010072100b000454010f491040d4200a80d07070790440b000301d00274429820014484420001400018107041281c0d00c100d0400400f00814030002e00321501c5500205402000e01e609034a80d42c800f9407034100d4500d440302c0c0102480600003100742c0c0c1908002d03c21400de0040d41c8895a684103100d440e9242124000c1c0001c9040000400080c000d0015011500d800d00d001c2d8101900c0d20046007480d4050b4101402107001e030103000c0c0441c9402c001c15010341722400c1c000e0040640c1000481c0d140c1e16180402080407200100486407a015002643c009040f020110303481c030325140300b911480d00f20a03151080041d80d040804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 390182913 1250 390181663 390181679
    0xc13180c030b060a08130c150e06070308151f0309020f0a030c06120212010e0f090d0e10050708030c071b03050c04020702010e12011b1407060c0c140a0309 68
    0xb611032504050032651622907104000c980e6602c00800d00d40c003c0c841040c03014080740094400b500a0720800108038100440d643d009051044061112441450304000b8100000e40c400100c42d000b0b44079820803031401d4903840c0020308054196031034054103040340d51003940d1181d050f00000300050080e18000c911000314030a100c070400c541d000142c04806103c0b01003048611031a148000074144900041c18501910341c00702844500380d10200121240c0c1e0184400039288050782d54102e015800100f0921700d51a03006007401c030031010b101d03202d030f2102c078220020240681e0480390000c0d8801e0060ba0740e498081c0c04001c0e2030700119001e580c0d25051522121240b0a1036641c48281c1e5000801000340c43c1c104004c000196021040480c100f12140740e03103c01c0380d101ca00484420114200000c038180c1c480140c0c203000031040b40c000030104045003030095200c81d441002c580352241c021383c0106008850300b0080d20b40105000d0002c0185480230b852150641d00850b4041c0032038403a5851485c403995665070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 390184163 1250 390182913 390182921
    0x501090504200f1303030f030e01021306110a060509010c18080a02130204050409030e0f040618051b0304030e2d041505030a05060618100902030c13180c03 68
    0x25954054840e6415030841c540c40a0243c040030070240704203403402181a403411140000c9a108802280074403400d401680c2d010301507600d10850a07070085052501c64801d43c60112400d200d12424003000030341408800704c0a10020781e03100c1e004241800107040858000c1d0092600e03102e15800203140000e80312551901108140440b2a81d02c020706000d0031035001c1142d02052110544401a401c000000b95619180184c6c10118040c0c0c6a00081c1107106e010b012a809510f048548100c0c6094021700010100c20420300c801400c0c240001815551201d001c01d0b50b0000650b9040380c0c030030100810041640c0520016440301007600c85022504000c0700424441c0b0b03504a401c055880301e10306140312420681c0c0b2131035580104050f00303005242e883d03001c241400510034094949800120401080d8101106603101803075038401218081d01d4071000041a00300c260040401c960f0b000404a911141494155900814003072080d1940743e90343e40034400e504401c0300134659014140381e864002c180c040d02c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 390185413 1250 390184163 390184181
    0x30f050d29040e100e030412050105060a0e13060b03153c0c0928081209100c0314030f0708130c050f150f03070207081c0c020d0f08040501090504 64
    0x200400e10306018079210005800109800604c901c014000001c2000c034003002503070241d0249c000041d0a00703002d0144400303200c613030300310200e42807021042c0110609800d5101e054140c01c404000703406012a00000d0811500341c0301d20304000140382c14400ea0a94400010804c0340c9800c403031104000080e4910001c54036814190f9007940c1c1c40c440000c4a00705108024030250100034403d5035040b440388004189035003004500345038089482d0044c000c1c2a0100710040d00c4882c44100b640c2040d4405c0006175030900840461801c100f11808110301b00740c0181440013500c0109144680c0340d00d070000d075400c25402c0860f2400000b900c22000b04c0c0d06211104a081c0003c1c0d0000b8203d1300c0582040b0030302621003100600745411031800500d02c0401c030305200c00f800041b802c40300866568141118002d02d403803040d4001c00781079086061140c881c58601d40310a41030000604110031304007224000280c00446110300601420394035082442000b88a00091060303480c262034000b03403035480710305200403a060303c0313 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 390186663 1250 390185413 390185441
    0x30c031e09060408070303091502030108120403020d081312150507030e070e0c0d0204080133050d0c0e0f060102011104081e07030510060e06150304030f050d2904 71
    0x102c0820081400b100060140314043c0c02c000c900c140140ea11f0080300c4540c0d44039661010750100050280b080103011000309105224041410542550001030102c1260103006000c1840050140c2500c0f10564003c00105800c1510020b03207066401d00318501d00c0f03034203120195503190000150003c0d000348901510030500c0c4004005a60608560202d20800504507e004400900030f00d04107951320300080000d026690300125400c000389092044809080d9a03880300500e800c03d91250301e00132030602d00210f6130b04036064044c034017a506184203c86280e800103001200010f0030009403046184550b405a5000c1e03000308002080c03a841c003913060060340510f511a8000d516125420b110311032107614907100401c00e580303243c0c2c1d881d0b6401c2c1c0b611071040c128812031500d9a02c100102015032414550098050f1081c80550b4220741c5140c4583c400140001e00307102105032281e0380240b05000f510810b949101040200c00400b403001141c0001c242d40750b580500000c02650b000303080c0360180744041c071440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 390187913 1250 390186663 390186673
    0x260301030b041524050a0902090112020f040906030f050705040e0307290907060305060916050313080c01020c100e03030402120a0b012607030201050a050d020f030c031e09 75
    0x140c0c0e1420a8014001c820504941d2100300040c4c10000c000d4040c08440c1801401100340d51800092007100b03400d592101036058810310050b8160303600403025900d000c0040d403005030350b50341c001c0040c0380c40e004641201c80e85516100004c0708209844602e6a401c50040c0100c411395aa0740b4100030a480c2c00508070304543e0401c0c4800302c0012003004c80c6481003000a001405100ca001e1241304080b102100c0c201d10981c005503041108941503c501908014142da0401040c41c3c50001509910000c50012003013007030000004200c401903c0321980382503404a5801d984110500000b4080e4000c82810600e034060011255486a15481041411440d60780650f095a86035000c11115514034034800000e80100c090f5400016002182213000c0c042c1a0706041e08803501b10404d0f201d5001c200c0444400c0e6221070401d10160780c03c0000d403500789640b03107400fa950310784940c035540207030280c1c00044a890401100344a40005454090740c4582814450003090803843c0d24600801401a00c03a54010303000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 390189163 1250 390187913 390187921
    0xe06120109031b020a05030111120a090c030b0c0910210612142e0e0d02060a050c09121c0c0b010e0c0c060f0f07030204030809060702030118260301030b 67
    0x100110f00d8580e84c0c0020a5a40300035074a00102e8203640310000307265407100000425114140203e414581c01402405080091078060b0b503039080c05441ca400054986021800064030f0800c4040481d1400c2002400c0c44031851031521001c1c0401003d003844500c2c00071541c50507000c0003c1c07031103041c003102d140d2460b00c661030504c1c0d15113010b201d64000b0004200e020384001c1c641e030084a00450080c0181c03500c00b032184420800f5000e011600c20741c54410850300321130f5101640642c0024450b4103c80c07d0103001a041e01e44085c20321040c403622254940148501c250703100240d001044d50703c018039994401e800390704c10b0440f00325403041260b1002407a02c0690300060250500d400e2030707903a00140c454951031501d141440d0709454034034107e40105440c4d4101c020010351144004103250401000d050541c01c190455071541d1081c01540e2001c0e000304004138084055617425000515000061070308000032031154281030341c0995a088031290303207142803501c40405a01c0c1508a0b8126900001c0700141611 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 390190413 1250 390189163 390189197
    0x90f070b0c011b0806040c0503040305030f1f0f0906060503090d080a060302041803030b0f0d0b04110d031121030f130b01080307021c11150c01060e0612010903 70
    0x80703003040000c20340d03990341a01e80e48110089541c00440c4030f6100d030360311864032004010607200c0300b40e6100100407040c001d220009070030205880e00400e400120720145c7c0d5462844044641030748411800320442c03645e000514030200d00652080c2c60441c0d00034055a80c071140c09817420320050340c4100301c40c0d200c0f105039a0140c0c807400c0b400b17800620300c00c40800d20399600d400041c2554280740a03454030685060106041581506c1410088001500c00240841120000a10b1403500145c060306110070180000c01700842510410000c660041103d288400982401804d81505003000c89032407040021090303118600176019500301460100952450b510040c482c0300c0990045e0048005226584603c0001340c010b800381406131045030000c6031106003600410000300d140e96500d900c6070344000140b20209803141c07a03e41c4001d0041e2100d454a81000e03001030032500c00c004400c4210351070103601084440c0d400790301c5800390304122500100d04408031200703400c0f034064280060204034500910b5501003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 390191663 1250 390190413 390190417
    0xc1f0b0a0f080a141005010b0901032d0902011101020304030e01180308030412031b02011a090103050a11030f1515100f1115040b1815010501140d0c020c09090f070b 72
    0x2503982581c01600010345ca800544a085c1c102d19400346000c102c3c0159540d02d0702c00e8210000142c01698441e00e1300f0440d1a0900080000035000261620819800c0d039000300c040703200d9100400c008564903c2e1070b040c000c0940746010107850010301061890480c0503c50001d10381565000b90070b01f0310b1900c99544015000d01034a21900c141515100541c404012000c800500c1c092160000310f043e8004542500d800600c2401c0c2e00d00c120411001840420000113401e941d01d6446107110381d084034150000380c03800b071a88102011a119004c44410350101500d1210701501458070001d20082c03080d01004038004e06d020000c800100f04030f80c2d0f40c2c036540c8a107850b0718103000c640e402c0d2421104000310b100c40c468000c44069844080e168244142c1e0ad020b082000c0c24403030a000580f070140f003803014010f8004010703c111810018100080000309885104a0703860034181d8008020290140c900a0b455130740c10b511480c4110341c030100040c2e1017400818007250240c880e00c094803141c0c1c04c0804401d415 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 390192913 1250 390191663 390191693
    0x51207030c020d0506040309050a0b040314011116030305061c060525030203090d03060b0406120b040504050c1201021e0f041d090709140406020c1f0b0a0f080a 70
    0x7001400880142c1c948980ca4003003107014801828140c0b030300e4280541880c2d0650b01c01401750700607c604000b11200401950213480e800b01003081c02d01c0006030103034090312000041689000c40010014008840601d00400c030b02c0c1300391000e101541c0c1e800d040012098025584000c1004450f00c2c4000040c10b40d4011980454050071440441d683c01c041c00c06100742104050700800e600006200c1e000200700325059001340c40d450b080c040b19003005d84c49081c60090744100402d0041408104803d890140c02420a001015000300843d2501e410219550600707600350a003d08541c07000307035066003418000c540c1c1c0842d924a844601d003141d281594915806801ca074003c0840500021070300740e481c00503c0307040340203501501a6900781188401d06000040d448103041500d0b10048500c1c92511100b1158420f401000041e16600d070401c04e18100010451402008007040c0c04903803101500380d01c09880000d0507034007048516124104551410054000c40e407440e840f801d041000035410350300351122 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 390194163 1250 390192913 390192917
    0xc06090a170a05030c03040f050909030f0a1e0c0624051c0818090a0c09120f06060608100e010e0a0b0d060c2312011511071715010305120703 62
    0x8802a03d0725244d08580049140034080d07000000c003009646000c3e88000050b00084415000e00c2c24a000210f40d00c0c4034012081d1203640c4080349280099001c0c85c00c0960344010030301c50200c0310040c140c0040000e44511802c03100d051412510b450990410141d00c1140b8500807421103486003858100111910204895110500030b000084006840c20002e0000e00c40303c40200002ca00020080101044004218040715860041c0803124140e21101c0041101c91728070681c0307040d403440d007020310500c18460000b4218504003a0f00040c880d903c40145482016008a1302040580301c1c1c81e00c01c103000c000c2c454059101c80d0040800c0da6213034071b54068501d81c1c40040c110a014507550390750b50242c40c0d440390741c500402c484244101c01d42015030304a042958540410070b2514695041403e5101010700400d01c408042034000010304d4082d2a64040c1c0f17141d141c040303a00d0255039224002e100c503140e02c0d054656000300c02601008090340d1070240d0607603920030040d1040752010000c1c400390703400c07410003501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 390195413 1250 390194163 390194173
    0x6130e030702180703060b030c0702100e060a020606040c020304050f040513170405040b04052422051503030406052203060906020309010c0f0203040e0c090a060f020c06090a17 77
    0x107942d03000000c003605250020140051415804c09400c039000e907440311900c01010020400c1400080c1c040314507565040b600c1e071091200810040f229580d0440700c194000f1000103000d0511038001a1301845000211400c0c0400544003004907164056132140c03503000040000a41d4507490181c012075440010413881000b0f2500d00d481d414081144010744100e0948005030510841c1854000c15940540c2510f06001d10b00b49002000440303a803040440c9905c019120103c8582c1ea02c1e030941c4440058854400b5020400c14a5420f00030300e01950200e0781d120401240c2802d03401c000c0f0135101200d4880d1200360409007102540880d114014001c0749500d44202004400035050b8441c10440c40e002d0f950060300c81c44d19114036070854a5414a030380038001d0301440d10854a500104580c280c64824a0281c101e44607403860f130708203020f1a003180368000314031100880c8071030f40b024002c5c0307844e1600c3d0708407016210107505014980c400c500388107401c080400010f01c04030000281c111108107285084034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 390196663 1250 390195413 390195427
    0x3090c060a210f020a091a07110402030a0902030f160e07140a0201060305010f1406031b121e0f06012709020f100e1503010b0a0305040212030a03090311030306130e03 73
    0x10040b40c1c003c042541c007061100d0818403000748429603508207040003910003403074000241c41e5140c50394050031026206076000400603503741d1050304504c06040e405011203900c00e1003500c04c5905e884001c611f00513445039210340000c00c00900d0708201e0040c070482d100c500e00c41020340c8228100380d0014503800255034840302c0010002c0c0091041c40300c02110010009101a1440b4419001c41009030036588680d020304005600c0300b09200c801c01e0302c030208aa15032601c0404080090500d005100700c40d080519850604252410215a5a000203160307001d0ba41c2d02d80e00c9200c2c090a82d4040001d1081808402e607504000e45c10035482078000d140000c0402c25072810303160016500f0100710702003100040136100304000c00e04008040c1d03d24a03a00805150456040c196419094029103203840308140e25640031806544413640382e0f07030b200d000c1401074a0f6505040d800180c080c0000c820110b0005074424100043c2c800007000340e034003400c0c0041c1450103820b1400070120107085da802c103618050000b000700f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 390197913 1250 390196663 390196691
    0x4020607080a090f0503160603051b070809010822020108060103092a1202030303130f02030f01021903230907230406050105131e12060203090c060a21 66
    0x1a08940210f40d0b02c1040c010f0410590480300762155208501944c00818070305030892500c20020107a4115140003c0c03e9a5107018801018040d42814520080009003a13003d00c4580300041c403200d1030a80303a0301100c0e1202d580060f006248801c81103d01801c440c50f21005600c036294aa800240c141341c0440d01c0243c980b920842070070051096614040301c010742d200e0140301070361114001d00405146490305102c0c1c4d00441e40b039200040c107002c0d048491013518410032040c150201d01d840d0300a422615411040100c2ca4000d41c400804c0b0038003d8180c1c010b40c1009482030041106042100000b848071000305a41e0b6042c0c3e46014000315a00d004ea400d0109250542603008541c0020104c804a6040c03244000c0c082181e840b90085410440b082186107401a049800841101c1c135281c610790506070014624503418034682c03c40120007920b240c4035070600003a034001d5400344401d00140c611002c4070f80104070b980d114850080d80824251103c0400c4914020502d2103a601d0600c0b000c50b080e0f14000c14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 390199163 1250 390197913 390197917
    0xa0207020612151212031003060203010605070614010b07080309070509090c04060e010e0105060a05070b1302090a0603021339020f0102030714030601020309040501031425030b0402060708 82
    0x1021a90800020070000342030107000441030303115411340384111091441040b60f41c80741406400003003c1d40000020440403190307007040800541e00200d0854a81d6120700c0e004125a1040388155040c6050100d55100c004805800904031405034458914001035a0360752005a0801408100d0601510800198548907802001d21030b500381030240001080040402040b074031107030080c062b840e42c0500140300b405250703120141034034011240307992a0211500100e4080c45215402000349644005100030400004800c00f1300c03038401c4a810b030b105c0d40c55048040454819210103580003448a05903240d10f041075101da924000030810040500615841e0000014040421310702c0c3c0484032040c160f43d0079814410040d40c0c1c000c25000b540b4504081400508a40400039800950440003000c1003103a070080003202c2c4d101e50050001d201660f135a040c0000700d800045a0840c403070240c2e07998440c000e1035500808420450b098082c2d6501c604648482102c0030009004176040381c0100301d80fa0110b00c10f840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 390200413 1250 390199163 390199177
    0x3c0b1210020d0c080105030c0603090f031603030c03090b0705030a090b130b090601141003020d1506090b07020a09090228060306050f030a0b06061b10060506040e040602030a02070206 80
    0x100942c2c1c400244800008031080184064100304201c00144515600480c0b02000340d14100c42c8a912030b120010380d941840306c00d048a0106210004001405050201311000c0c0d05002c0d4408015610030340341c0980950746101c0000b440d580da03d0380021000c60180000c0c2d40c00245545000824202540d54954414800d0700c007510f42007030194270312040041081140742d04c400799801a1684e54945170300c3c040061403401081d44070380031100f44160a14800c0d4150344032103560a10a00015003410055244080c81d4002c850003d0364590000c200100070b502150070340e950240c0105080d5152001c200001c2c82902c0c001ca9000c91482d2907515580d0355151071140d01b80032220207004192820798007070111849640260f0189a5547c0607a40301d580104030444c849810500d20b44ca140d81d00000100c040c4240308500390400340d07100d02500400000241c03582c182803104030030030a00e9140c800f085010301440c07040548200d00880094006051303900907641107170710503e000d8180801540000d0080d04144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 390201663 1250 390200413 390200443
    0x4180e0f010f060509100506040b030901020d11030604051f03060b1f090f080c01080a020705011b030204080c240a09050603010e2401020c0d150504063c0b12 69
    0xc3c0910042c03030210b11040d0001d00440c00d507400d240c0741c0008a61103005500c1841c4030f0341d00200015840000070340445a05400700304e410009aa401c08500350030750410b861460140c1e00d481d0001c1c03d000464030401a2240280c002144c2081c0b4580c0d0b0003000d01010144980c10211900068291000c24a480e400c5506191100d1a98a0600e050910f00f40e440d0782c00014141e22402400302142d822030728a40c0c206407007000241e584d00490501c107026103616004111240c0100c036812401d164141d000d8010350340050107886a4408403810007882c05036140d80e40328044013022000340c148580c0d100411020300182400c01c7c581c1e9440b800a040c54101341d010503c54000d4008210840528030200c225200788000304009001910000079a5605100c3d080e90284601401c601e0078003070003000c841c0d4518190481800799251514102010340080c50b026100c00c4041c10104600324485c1442c900000031849a214252021000c480c0c00340000d01e20307194000030000c0d07a0106114041c40300107003420400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 390202913 1250 390201663 390201671
    0x60c03040b0a050403201302071a16120911190f0609030b0121060b0109120515060604060c030f0c05030d0603050729090103020903030a0e010e040204180e0f010f 71
    0x11b0805011543c0e406840c200ca45030400c41d0300e9410b03698a1000d80420343d50300e00040c0c4940302c6191185450060011071048581d003502045145c0f0700c0303c81c0803021000a680c90240418440100c070003030b0f032a403202c0140318404043ca0540c03e030908141503403000080159840c10159101084080c1c1e11044d000300c000104c240c0001d005105200038040c1c010719542d01c55000703454203062285402d02a0031001030140d502ca222200b116889056400f010300a0814040740c00107180c85c051b507848044400310444ca41320302c400907680b8030309401558210780c1c0b1516142c0703800030182c0e0125050070003400e82c0018800ba02d00010040340c010800f40010003680400000c600b411402c00b41d18050455204050340302101c0f0b41d004103001c001d21800000807040d00b076680c48418010050300a40250700a440d05880042091141d45510000dc0b9400c5c5d142071300d61610240c1000c06220a038401d50042d150a0701e4554182030030b503803840d881020041d400c030040e00c444403a1601c0342400c0d80c03c00013000b4032954903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 390204163 1250 390202913 390202919
    0x103120206010b0c1b27090f0601060f0c0c0b070503070b09060705070201050c012d2313020f03161a0405010906140403021305070f02070f05060c03040b0a0504 70
    0x1008010b000d0407a515080382044143d00d5000c5e507400b20000450300038100742e9070812064640004d03540d051840f490300030a11b510b240d1103425181c036007100d0400c100c4c42005841d0581d50004101103059038841daa801031200a400d8040d2a02c8400c0070048551101c03e00300010701c017080c4c2001d455154031440c0595550130281c1007484040601800301a030071b0b00100248200f80740c004003140c080c590b080c20555110114192900e0040110711200170240b0b014442d000c80c00c039419070084c0c4103800c41001c01c004103440e40a10a0f48084403a041c0c80c0b041c1c080102140d40303015110409030b42d00d4070042805d296068800081390410641184121994410f00814403a04035140790710403184400d19810780c10700d4034100c002401c54680f44140000d0101c802c00c08080c4200714801c070b8011b50303006084801202c3c107030140c1800900f012543c840000304800e07102c038246031010980310110f84070b0400800f20142824100407180c0e020002500891208102c00110031000300d0180c001c440d011b4603515140c501d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 390205413 1250 390204163 390204167
    0xc02010e01020105220305370206041a191d0c0f030d0f14040609140409170a020115091433040207061505120c030303010506130e010312 60
    0x481036126a056904010400c00c1003669000308507104550040c2c0009405500d040540d00c0d88a40c912490381054032801c441d0781034a40070000f00d42100424a100c290040d07084003261a4a01983c004185e420070410300c902d0700c50125412900069800c0e0b0520060400007200806c98443c0c19051009100607041c0d204e10800078818100c0e2014140c03107a50443e52014000b81d140c8800c215040248032505113268000e51082c0200c18908800440c12581c55841c0c04c009840010548680341c82c1d542d03107101110050405003e500b5050780e12001e06400d4005294140c8040d4000b03004001c115980e8a4000c11006101c808100090940000001705420100314a200d0660024540c41500c4120411809807c64130307007242194400303580c040c21306c0c20740690019000e44104040a045a4144039864080448640c1d001044442c111060502c00102d190b109450301d240020032a13254006000400c245d05205006041e0002c01c900b00003051512001c4c40400707890300380c0080d90188071100301840e101e6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 390206663 1250 390205413 390205427
    0x804210b070c051504030309050d02010e0c0604050634060f0b0103090f0b0c090d080d060503120a0513050a03140f031e1c0f020c012403030804210c0201 67
    0x103110340c40c222102295580f20965075a12040504013114101d100180c217040c8a03600108016901c00e00b620000e03c50326000a019141900400300140180d648a04071031508000322800ca502c003a02d92401c1c1403140b41040b60309100c044c8802c40c0404125480e240d0310240d104040b1040d071040300006501c0c0ca14040d02800c85030350104640c145441c00c0143c2c4003140704026a03ca8681c1e000b031000b90783c5d070f42d00755540b01a1301410103a13941000c07801c00d40a041045490250405086031201005210356443c01c1568502d189061250382500070454a41200e20a00c000c00c0003860780c882c8040010f64903404528a001294020744100704d80b65000c0f1a044828000c81c115010458002c0d8200320584141c1c295400e01910648440d050005a80181038990740302c802020700144010458250814610b0000c1d6100035058140e5501c3e0681c88420400079440c4d004647c031068504514090450b036003030355030304006807060324081e101282c401c0303002c1051810700301c10105c0c0d0b0fa120640c84440c0c0c8005005a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 390207913 1250 390206663 390206671
    0x1805090304030812040302010905030d0c08100f0b13050d080405030d050c0607080a0b04090b100603020301150c0f140d030608010b151803071205070f060e010c0804210b 74
    0xa50810002000801e041100b607030351040380d4003802181c82d15185001d030b0042c02c15047c02400d0b400b01241d42e070700c3c0400030380c0100300c41a51070312000030964505543c01c204003514061840d40ca042c5803c01c1c80340680c40c40c00b8200720340c400900441240e44800005540d00d051800480f4070b002e0004043c81281014008000800b010303090880c24520700011182e1134220003130980b81080082c0000a4078a002600481000702e0054010402003201e41401220144105c80c0c4441d01d119105002410074824801c40b070490300d0402c24190518000b090031560301341c06240a64100c0260304401020410300b10011105100850042005001142010302640d490350702c4100240d141c154115025115660041d2050501002c0b1954803030404030886014007142914070b0309442000d00c04a16a500c2d03103400b82500f40240212947c140e038030704ca85c0b80b5017500ca008100c001511511455450750040b440b494040b80b15131051801c0c561640b1412090a0b01800e20388401c02040140c20306000307901c844d20f500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 390209163 1250 390207913 390207931
    0x409050a110a0e010c0206070f060b0f0102030a05070f03090317030a0b1e0409080f040e09060c0a020703030e010302120705071a10031403090307120c060e13020304031106011805 78
    0x8001c01414080c00c034008942100b410b0220649404003195103400c2200d104951204a58a003422786040010080c411204014055000403083d0303503c40d0b000209603007083e4580d40d1010302c0e2a506903905021080388807004c400344003458074080f0009044030060340b02080080319036a1603180c901c002406860107440410701814002e00031841e103000520034800414030a4a000c5003290380d80ca00011944104d40e4010100c240c086000718080c0c850888290203000d16404451003602c50030070301229446540301a0340940d108001c00c000090007001130300c1380324205040060074000f685801200340181100c440c0009035000a10038104880412a0351000c46424080300b1070b450444a0355500440302d01000c0e0070b1000101030f000b0f0b441d07001c10495000c0e1001070103640da406e503240d911041846a1f02000c0703420422403800403840d01d104070b01180e18080c009110407801d803110a8101c0082d440908280c003041070450300c0903d2002c1c2048098000c12012142c41500c00210014808884018040d414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 390210413 1250 390209163 390209167
    0x10509060906010f050a090b01020c030d0c0302061008031603051c060602060702060106020615031204090504150506150901020c0d0821010f1412061906060f0c060209030c060409050a11 81
    0x645d141d0b0070b803446c256500d00000007807009800300141d00e80700785c02408a40c18444d422455040c15030203089924078500c03d408403455a11403d841811940c02800b0342d164980c41031120301c4281d481d802200d04480d009080151410006641d580c5c034070b5410f10b200c80c2d803d0303894610812400d40e04000c804d070701074180d1029150740d5060920084d100c40019060a04403c0240e410300890b5a01707002001c0080c0c500a1959551956801c2d60340c00752400f11415640e0541e500d20440206003035001c0c8034440c1d0f100514011800c00c00280280e00c94104000c00d034118801c841082c030260310f4550b42e91403018058420941c803444820b42c820745d204c203442c41d0081c0d03040c02d083c010040c420020342c0b900152002c02d100c00000e001041d0220b01005040000e00685c0c0c4986030605c19042c0c0405540c010600c5480701c10320000e07480d0901a00d6240c0b240b01108001468282c0c0840070030096805018a55401001d40b01854540f00025025400582040c24950380d03920601c070391459540304100c080d00005240034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 390211663 1250 390210413 390210419
    0x10509010e040f110a0b03392d03070815030102070f0213110f21060310092306090c040b0904080f0405090a0c1103040b04050f12010509060906010f 65
    0x1601030681c035400140000c25131501d61440341d5030000740c80c024020314214241c407032034071003036082d40b901843c810308c1130a55641c400300011400c0e00c19846409a00101d400c1d00d801c0e007011a035045049a20b0308420b15120042c1015118440f12000f54054441303641d420001d410021100c004100340c0301d0360346219a02c1088640c0003c0d403c6078201c03420a40460780f2400001c1e5113105071018021541d0f041c3e40410700090b15500841c008170141ca0601c40305c0c401d20240f40074842e81444c03203000c2980c8c119070507444540310081c400c03100d030400e9111512600108250301310b100e80820300e0303400c1400561f0f1142c1002d810011405070401c403448845104941c140300c115181c038049a41c80c5800350019190303031800503182c0081d242c141c0c115802048040d01ca0304241c64861000da005003452800403000420101011800280000598064440c0c10948602d0140f901c81000380600b134a080c0d507030700a00d4004003c100c6071700070f10a80e807040120b00d000d00070300c0c90810a55420b00c10305800c4011501c210306030074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 390212913 1250 390211663 390211673
    0x20a080709170d080402031203070c0b060402030411040e1c1220071e050d0f0f090b22030f060207021201230a0e1e0f1f0203040f080403050105010509010e04 69
    0x250010790f1420074800300c3e01c1342c0c00440c0c18215411904e0807035180000500058580c40340b42c040c074807401200796801545900c0100f0041c0d100680f4040c00b070035418a03103100c0515150740300c0c0440d42c05c01800c03552900c1c00400c80b00d001c20b031000344c4940402c3d20800c6c0800c03044118010100040d0800b050100010414446030969000704040034011902e0175050138410300c4403000310741d02c154201040380c4090001031001426848403000d8140040c018420313407017506000e240346c102a0f8003c0d000302401c03d00000050f40302c84440542429001301150700000c08216031000d4480d00034042c240c05030b0f880403107006100544440e41c0f810030641c3c1c5000d448243d050b44024075091a0306004039003a82c141c5a0070348070805080314403034092141c0103c180380d401001090071113000030081001900d0140805050854880d0114007184c240360644275122101640030b41c0c019940144650840d99084617940c441c448990056003003140c1c81d81d9942c0c018000c1d0320f0f201d0075441c0140301c44440255589030030391391 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 390214163 1250 390212913 390212923
    0x2010b030607050f0409020d020304060b0108040f120512090303070f090b0304021c050303090a02011d010206010b030702030f03100302010801050409021807030b03030d0605100e10051309020a08070917 88
    0xc1408000f004500c0355054440b2008541c000d02280106644445e00c00310500003d40c41036408035562460314080070f44550142e001c1900c100d400004c00140d980c031036140c060406070154542000c207c000c00c48588412101148140140c22141c0103640307a20309844090001c40d0021010401d0010441040082c88102c50449a00c245c1c1600c24038117050b5144040300344461101c0b0002c0c0140004800c018080b503002902c048018000d0340c1e0343c07650032200107604404501f6510141d0040c2c004000600140c441c04001750b030410520700c100d0385010542a00c0703040c0c5800660b0300601001040104106544e0b004d04824054035045404005410081d800209807042c019020441c1c062114001a282c0d03000340e02000481c42c010702665a81d4440f44a440c000306824060280710303621034004502100e224080140f1040030203481f0400760790044c20240c44a0300006164610790344030410102c0d1401050010340343c40c82c02500c0e01c00f8682081f400192650442e07400000c294440c403210744403013042c0014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 390215413 1250 390214163 390214171
    0x70f0f080714040906050f0f011502031b0f060103080a11010203330406120209010807052d0a17100e030927090604140c03100e0a02220c02010b0306 65
    0x34080c15403001c01e8040f8026001008014090038034003810000400119000240701788411620501583c0e02d40071240f600e816810812001a40309001141d90100c50722141c0a2400d01c00701240d10049189000501d070003400d81089584001c0403c2d00911603400c01d0111811b802d089000307508600c0c0c00a812aa80d81c00194154850541c2805c043e15143d014100c0700800b84020708144030b41500c2d1000e41007100311200080f401130444c0c500008200d880800c02d4010b540c1c00403c0780481e241c48140c00c0d1181e280c2103c0301507002c00c0c80701c1c1c500704668440d0303208401007034510412054103000c007180c40e0408040000c00b034031315400c050b41900307400e07408411500400000c40d000da190021100301c6c21002e840c8103007030b440f400c074805003071208018bc00512070784503602c1400c84e07900c1103a1400110b505d424050b002540c1560003c110b800074441709801070408400c0c0c40702101c1d00c0681d03580000348200c0340c0c0c070380e0445003580800f94640004058018160385001d0740c0001e01c04d0700c60106c040307a900e0394010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 390216663 1250 390215413 390215429
    0x12071a0706020d0c0806030d1b0206091306060e181512070b1303050c2d18180d0224090c06040306060e060d0f020906040e070602070f0f0807 62
    0x6050007040501d9040d0740c070407882e501c800c04c5440c041e071001070a19201665038600c00d00ca1200d865000512800780c50b035149040c4204803070303030341c503250709100642e001065040e41c0071403d10b140c03640e140a0341c440e03500200465525005d12881d040280a080da90b91004290074503c4802001103080410341008076510044d9020b0410358054804d050501002ea0404101d02900162020b5111041143d0b001900d00402c00c1c2c030100040700d410001901d045540b200116140a0038400303508000d800f01d80c00c0440c010700040e0380d0040d90207001d03040a901f207540035400c1071240c0500c0b50203081040b1040d41c10070640000e01140c40440c0030750300c41c502122340540e140c00c07600c00000d007909410b018040c44403001900b4103480d9070b00d0341380c440d0207441c182c060340c0c103038034000c000140452030700030030030740100c0c2d048548160008056001d00c00b4403000200001c0d08692100740b9442c0d900410004940207040b280e000e420010f041000f656007030b1400c1d600107440e03e8080c00040c0003d0f42c002c9442d000310390903d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 390217913 1250 390216663 390216667
    0xd05030a0807090906321003021804020a0804060b120a020f27010603050a051b03040606030c0906050109050603100e04030e030703060506040506241c050a0b12071a 72
    0x60b03003080f610f20509030031001420341440b100140c020350200304443e00c0c80310440e802c140384001e4000e0307055480340c4812599100c5506e104000c1014080d50080c40d0480801110182120003040801c0583e88036000040014a0300010007061200034400c00201a108442842800d030f4404a0542c1c0c8031280c02c0040c0c414249088a00000d980715507008441540450305900c1d03c628180e5609610700d000d109200100342004006a0651a2445158850324042059240c0161074512048a80d01b000b44102c4102d580d03440007101003415646204014400940003007044d40c2080c4c001000c505940d400300d400744070180f0901400e26800c1341244240c61104418480c1e0b50b031681400c80c0c3c1c10b0010f9034001d406004007017010040c4451500050310a2106803414455a00e841c0280100c00006401040c400d5080a4828591401c1d070700040c1a04034140702c02c540343d2102d418134082191400c1e2251403402d542c4500081480c188001d000001e07151840182408518204840780c141d070003140715040261340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 390219163 1250 390217913 390217921
    0x304140a050705060c0a0b070e0a0806010b0d05040521180406380f0307080c0a0f080702100e1605011404030602030604090609062a050d020708120717060d05030a08 72
    0x2002040003d60304100b01d00107500f8610700c060980e40b5060027981c0610000c100200d00340900040140c100c0d00b80024042c6031491030301a21008207400b40044881d8012a0f139914506810004d090001104100ca0927603071381c00910b0003106020003155154000c9007031200800254071034a80e642450752800410700d402031206141c074409503040c040442982c280200d15003141c545100b0145100d004103817602c06458845180500e006d006100c442000580c68030124a1198420b101698112140740111031500d17884503030810540ea00424424003540c80b0b00b1803600b01c00710026940300184802e0030124025001c0007900449072082e0300025014a0b0000045845602c840d440610aca68003e03a040202c0300c21481d012014117800344600394204070321602c41455a40e2006e20500b00c04031031b1525840c080130300d00801d0203500240002d4902e100305108443c0d9100340c00d0500342c8152415a9140321008200b9140080404050a50781c015100350300e07a000050340c0042120b8814186040580039640e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 390220413 1250 390219163 390219187
    0xa0e06060f06040308040f05090c04140d050f0307050109110609130903020a020a0306050f01150903020108090a0f050303190204031101030b210f0606041434050304140a05070506 78
    0x4070fa5440200b118500080014041c040302c003008081d10021900104c040c2c4460f040384166006d41c0c00f8940000d0219001d006841c0740032400c2a05d02c51040c0f081d0b880300d0000d800c400e4195001540150f4899441e21089010031240d802d150607081c500312903442c244141c000124601c103a01ea03c0400c1110b50720309103a800c1c9802003080020b2194003d0401c100c00d0b07142e1400c03001500007940e681c2c00c00b5400400100340c040c1059507409118010b9135800b503446181d034004442540c0e0140c1402001e0054080b100003080e142c01040024501900040d42d990805515a07a606084042d2403070b0502d206202c20f0000030355031481c1105180c5d0034a8007007400340e10100020010702e4802c00d18039140000c40712031031810001180c4844091210300c190340701960342c43e042c0400c0d5a01c004c040044510164001250b16014965520a007083d00c440382a0b8036221105a5900342c1003011110b02054022041000b0009401c054011540c1c006010300807880180c0e0b5440d5032a006409054810700c404604440c0c000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 390221663 1250 390220413 390220417
    0x2100e0601061d030d1706010e0f060d0e010e03190f0801140f0a090f060e19091a04060911030a150b0d0203011e0b0a1815080a1a0a0e06060f06 63
    0x440c01000e503215030311031a1019080c90b002d01b10f104000c2c0b07195000920698089c5140060402014049506c114251420009160700610644c11555a200341828040c4024454880140018401103640329112001d24031400710350150401040107424451500545c0a00a1030440d03201d1140d516032115140001039620004004617030300500034400001700d20801d900300382e992460901c41080071035103800401343c0c000400c407040d521500701c1c0310b66480c0e00c080641c003012015001d282c00341c50080c101504046c0d030303007419101980e096480c1c01c400700500910b40601c03250201b04400600c6401d00c20390b10b0403102401031302c01c440401c1e552a0800c41a031129112807521513030040c020001030400c5039410391540c5a81150f01c40540ca03007442c0010302d091244100c0192040c4003911648a12000c107c400a050085000c0402c0103034907200042c9041c04120210074940300300c2525041c040c1c1d203442c0d074801c43c0e8014034800380c031400c01041040c22030000c42c1580d08240c1c1a1488000306540b203005ca8924 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 390222913 1250 390221663 390221717
    0x313030810210c0501030902030a020906040204210507060f020d0c0507050604230607050a0b0a09080403030201050603010c0504060c080c01140c07140d090b07140f0307020102100e060106 82
    0xb254a807410001905912111106910914101c20388a45034401142211042600290164003041c0305401520746500da42d40e0060000300702520303144c0c03607803090a440d10801c04000c0101c8100c1040c0300070864140164000341101e49420312500c090380750000d50f60703038003550080107001404511505001041c80110050130000e0a4183c0d966560041d100d0130440c14000400502c800c008014060310b00b4408079409140c201c4010004c00340300d501e403103035422005040e01070f01e2540c81c500c80e000911144013400c025406600002202c0c46e1680626081d47d0401e141c9008100b020402070107134541091803203400301d4000a04580301c0200c9001d1a004140102803a10f400100d24100868041d003031004040161058610070241c81040c400c4558602001c1842004200c0320401400002403500145c90000e0007050358050b40c1300b8400f11182000e50f600d00390601900001080303419940c040201c02c1200d0515001004171000c01c4001c19260001802644100304001100307421030f50010381d201c044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 390224163 1250 390222913 390222929
    0x60602030a050f0901090b2a030f040b0c010b03100c030f060302060d0c17040b091905070e04021f120b06030105310e0706030507020619020f1e0c01050c0313030810 72
    0x507801d4000030ba0800320465a1800ca8808c1c0340c003400b00d4445102005440100c1e0840700d88500306810091082d4a540040514500b259030b038a040084079501040700506d440c4e00c1c0080007401502c040070003010366020801090791103081c24000c00046c1c07070321411149080c0b44100e0004182d50400d4044400507003d01c8000c400e08a61780a01050004400d000343c000c040100c01c445211034a00104900d1001b400d01c003601030381010104018203200001000d038000d2000f07001c4c1020700ea8110040280d807180f03c00c020009002665040c42c0c4a445108131004200b0481d4018259854070000031403000030308131181c040528101a10310803e80c1e002248514a4403040c040c00410081441d89039604100d01c10400080e01300b0b004684540e0011a105004040c14000030f0045401e035040d50007e988424100b00c1d509604100034078842210b180c1600764035100f0702221b0703a40e4030a03245d20f60942d2400741000c0310146040080c4180c00708858181100e150345400c00458070766613180c85810154042c0c2c46001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 390225413 1250 390224163 390224167
    0xf0c0b10090615020f1f05040c090905061803091c020604030b0f1e0930040f030611030606030103030c02060f07030c020901060813030c060b1002070306060602030a050f0901090b 78
    0x541d95100024943c1c001200d13800c40c0c02070806503007603d64076440403540074018404a40d070a01d0342e803410b070012580540a00c0d144040e441e99100c000084440d52031050b2100e400100500070b01a014000103c1c00400c0a00250300380410400000c400d217007084c0d004001c2030bd01d90400011512a001070300e0085d6000741e28040c03103103040b11030800d0002d001c90313040401d400c0100e410041c400c00c00d14018090f601d00700041030f02f404601c40380ca1840d40d82c0b034102c5001e00030308a003c0101c0c0500100800103410001d06440140e451403601000365241114000c0300a6424020018103444900c10341e411030b501894402154040745c00440e8140c81035020347c01300c000001501c007003403641001c03d43c4000351095400c1b2900c1d03a6200001c4038115425110703407e404082110303940100f40704050300c4000d180203a100003201e12901c030000d00e0a047d005240400f5030054201002402920311440006041c00d0002d07500d0141d42540080c0240f0607101d207212008000300b0462641c0e480340318042c01038404c41982c65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 390226663 1250 390225413 390225419
    0x612020c0a14030d0506150a0e041401080a0209060604032103020d050a0903080603010b0603070f0306080a0308010815060108070f02100906060f06021b010e1c0f060c0f0c0b100906 79
    0x283d00ca0380500f6448a60900b09800714001c0c1c2803500c03210340c8a043c00304131582000c1e100141110102d00425905074002e032906095040003441c40314040c002c0c20010010700b07003e0b607a44107000402c040188001d2085034240020004219680c0c03460f0001100401110b083c542c9415080d402805a1203501d10b04a140904110f00406076501044d0b185000346c03680c00c841da40d41410507007030361041030304150084001c0c80801c2c074650003010200c200f200117080218400f034807003484526001c000340045e0005803c010040210b100188010308404007051440c0101e840c20200203020104050031010070030103029110b4001500c02d1000220a42040c0000d000c0741017242000b4020782900d014101c19407601c3e000010345a400000c0d41c40300b1a40c0d544000e411800310300d005444150b4140080d5070001c64102401e610104d0f10602c07180d5843c803420809201e41c41703604041e0110740c240100d9406105040c0c1c155000150843c011280b450780c08804a020b580e41c6080748510a83e40d5071058000d281810008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 390227913 1250 390226663 390226703
    0xd080603030c1f0b10090612021b0d080915040b0c0f0d090c230f06090909010f061203080402040e010b120322050a3302250612020c0a 59
    0x140020440c0c10b036042c032800c1442d10030030140e1000040b010b0b010805010003003189034000d040c10307002c510920000505040b028641c4d0156810742b07644005541d00010840e0741071726006821590401103500092400e80d01c3d64122100c0070201800140050160a0015408a001d07404840c144200122a561a91540304c01c01010b4000b004007211241c2c040139000c40e07000c2072400c5180c02e03a40b00001c17640d81e075070721081800081e4002c1d8500680102c01080b8803072048d141c410f1864040d0592100004000d50a80a80012182c85410041011a84176040c00c003090f800100e171a0044e030115000078400642509044c01030803130320010394100fa0004030814884201202901580761682d00040e5200c0405440140c14162802103642c03250703d4000074080c0c03c00f446030440c00903034a12843d240010043c64022494940c8407036120050340725100d041203100c4684034640e41d00c000824040c09541c00c00710081c00d021001e4aa00301c0c003a03404115020042e4040115030002c03500000d10666030190b035204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 390229163 1250 390227913 390227953
    0x2d05010e06092a1201061e05040212012105060c0a0306170307030c0812040b0103060b030105040512090a030b090703030f050306010f030f090b0f0702010b0103020c0d080603030c 78
    0x49000280100c07400208550b40116001c2c180031101c070f031007015100d00000c049851942c2c5002a076007194510b000c110140601744039042c040c2c600348107894000400b0200c001407284068012602503401400828803608840b03e101c8e05407210401008401c2c803c1d1300d10300540340e40a11001d411440f0742d00500010034201c00007090510a16a1b052000c0313600d800c44a0100206494020b25a41c420171440020074440c0004840c20340c45101c025182400d060341d0f08802c00e0058170b040d1048912a4010800c0010b04c0c480d1a5002809400034022031078641c42d49502d444030117082e896402c80009241055030f44e40b0704000003a69206450503500e040101201e5034445042c00110b0100d1215a0200c5040380680141c80c0302d00c005a440114400400d10120f01400034a24a42840c9445140300000210000130340c0344241011102c0302038078604000000d00f92004511840e0605104003c003581165011030458059042d41c2070031042d68907000082480d40c401c0440400b0305005400c48004d0812400c55 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 390230413 1250 390229163 390229181
    0xc060509151801050a09031b141804060506130207150c170403050f0c031b0d030c081807120c1a1204140304090e07150302070c032d0501 60
    0x1407064044480304103414050320039a00070b115a12801030040d0801d6105000405c2c0700700e924a030150780d0340e5907503940032a070310f0040124584000d0401e10a1141c4001f18148083c0390704101c2d84a5851406075020b0204030401500241c402d985130702c0016074940f5085211204401c0d000011961101c082c1400c0d0000340036106410045410020741c10f003424807c1881d44004451001d0031800c0f9191640d007594154408000140c40f650706115090440109001801d05800400c0300c582280381340d540002e003000083c00c1000309052600c00210a401d03030100504d54000c0302114007803090284c04018501e080415070113140301d6002101400c0800c030385120054120340802881c04d4241c0580c1d0f00317110450050881810464032030030000360110304203401c0104c414001c2d00c107480c90180c4a00c0e8400c1903582d0020f00a0041e4040c01c010444113070945485240c0c0310851030304608160b0786d0307694102e0500d0140f00141007040300c0e076400d610700d8154050a0301035001440040c80c0041c07541c6441c81c00b0700320541c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 390231663 1250 390230413 390230419
    0x20a0c050301050402030312060a090c0e0901060201020f0d0911060429070305030a02031f0b040e0105030604050c10090e13030201180308070c030e060c01020c06011e0e130c060509 79
    0x200010352801d050003070307a01561707000300654100500d09003284202d0324002c1c03505500520209001652540740e200b00400780003180d540303440c40c0517610207000c0c03101c030182d00072800c680c030412101a0a00c1c0040544058650b40400070031003e018bc203240f11001300c45019590f00110006000944581c000320035000203040f089260150503183c000010755014494028010440400004211103205c0e4011680100c0b50a2071a0903201005856940e00d5103503088040f04c00c500240c01e003c011041030f20280141b004800804036890b00b40d4407540c072448465075a5004042c01204484c4c2c10303014403401d50240c205481540c0b0380d0702e06200f525030f03001d00769041a400755181079200114440c9210100c0341c55a09605d0b0a5200d44464000311001203030f00900717404100541e00350000d16a10f11004201c0007454200268540c0c1185c0c0d074190801c9011380c4040c0c0d6540c0040d001c182108803c45105c0115969000301174980c0c0ea60120321001c803140e40c5002044007100c10740c0443c05a401078080c0854040c10303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 390232913 1250 390231663 390231683
    0xa0b0301060918020a02060106050702180a0c030b040e0307080a050c01021c060602030702150a0c02062a0a260d150f050a05060d0f02071e0b0a1a1002011803020a 71
    0x309600b41c02c074841c1702c400360b0068100e00700500100d40541c0041004c11310184c0030003894580644071400705501520142000385e25088400603d42d4140660203005a048034100b00c0d451541c42225030b00d21603103400070070390b440100700e000105000d03d05644013486c0c2d00340203555920105140700c901fa0300040b0210a1a0f28221001c0761682c07000080d1440660b014100d6680c10400110b124010740044103940200141448c010005803141c8024100c10404007020072250400e06074250358201da495803801841d400f401105010a58070b0344c0700d21040305100c0d03010104d0200a00300e101c440c441c210303040b10301c6030820b40300b041c18091200c0c43c41e00311194440c40400b403a44500400501450314403c8a5002c1e5052001c8442d07000c40b90b000401004000200514015281c0e0b20300c42d1001c6418403805094018190740700610002021941e4045a01d210412044a05540401482d04a01061030140c442030300640a954000d510600c01030401c2c01c402c400122007850f0080d5103e0380e500041741c5124113 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 390234163 1250 390232913 390232949
    0x507030203011103010501050702190504020a0c1101020f030d020307090512061b0a09090b0406120506070e0f0a0e131b080f0d0e0d030e04021b0c0a03020114090a0b03010609 76
    0x5030003503174140c61b016511140b51a125400304000180c80416440c0c0300c210943e80090300c0e82d21407000704101c3c03205403101e41c0d00c40111b003098622882c5014245040d5000700c0a50080000d020045600c924030441005032a03403510101128045480e400075908800c0000108080c039600207089803103001e08155840d208003c0210810590240d41c070b03991f01080480c3d03428800e406031900702c4048442d024100140c0d89564404007581190500019215034118005001419038448001611907206640010980c010a0046507000b00d0a204000c1010990804603060050090750b11000540002000a141c6020415244961418865503015100c0c01d4040d41110f1f4010541c1d003404c03442500c0341e4420310b806900f8403199080030b8004804211130407199002c603a60314406080010b14403580e486040003500344091410344140001d61040d18001020001170307074858504620300c0410440700d5203841c0f40c140465240c00294001700520301000c0000702d40c0e0340c1d100d59a4001c58000889050740030074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 390235413 1250 390234163 390234191
    0xf020c010e0c061b01020c0109060204060908070308040b0307021e0309120c0307030314040f080703030f08131e081602010f09060e2215030605060a0602101109030604050703020301 79
    0x39042110b40c3d0841024880006584816594482a0a5100c00140c0340c504074220f5103085507907062007100c10a601207800d00005500403d240d0241802d03400406820307040d6102c0c1000c5004034422900e15031400400903492610074400b61a0341e0404d202c1c0c240a40b030341360802c55100d1b0881c1042034003480481480f45000380c800248055854400380152100d1421600d0882c1d16000700c2d1018020343c007040000040351400958000010102e020280c0171081c118a4000c0c07014100b026400c081244031414003d904400c049545611070740103884c1020705a900c0a155110040300601501404000c5802c0203143c80b00590061164404d988000100303840060684481019000c0c075400110b403c03805c4d003840d050109403d004400c03841d400c2c840200204080100740d42c00b8642150401d44001810010006c41b4064103030403030300c02c850301c0001d0384c18001c0096441c007018242d104855242c0d031200416081d45001c45209100c00f800780d07a13562500382001e90340c03250944812070103580391140b598241d40c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 390236663 1250 390235413 390235423
    0xa0b0319020904081b060108030c060a020f090d032001020706060b0705190201051308030a11120f0d06080a0b04120504030b06010c0311010501120c1202030a03110c040f020c010e 78
    0x2903008002c0b248940310b645a104441c0c20800c90300d410f0000140060300c1c1140104101c0340289880002184c0d28040c0c4000c650420070090300310b000150060050000c1c0d800c042041c1c61410000f0ba40100c0542243d00b001c80b0031081203007503541d58004203c090003220703106400a0070001d014041c28411036a41d2038001e41d107403158140103015504582c1c1220310680b80826801c008a005140c250f0410a0301d81103031440c19a20703884034070f040d0f00c0041c0e0a500307150080301001045d400c00001d00301c451541580845544507c80786107030310400010f0710046040d8243d11080c081c0c240342003210713075204240c0340c0703922400b0f01940c0a03150030400300d1110703450921550480b0180c990001e54180162076000064540c00e07a245011000d0005038500c044940700f01748261402045d010240c41c980c1c0d20030b41007101580c0f050b600004014201420600301507100000c3d0000883d40c90300d0002c01e00441c819045060401c08058140c1c030904045014000040a4024001090820000300310002c840d500407a034038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 390237913 1250 390236663 390236713
    0x60f230408060c2d090402160203010b03070e01140111010905060f131703091005090706140309031b0a0c060302040905160801030303020f0c01140108071a0313020f090a0b03 76
    0x3c0c02060802e0420b00f00d982400c115429104000c15040450000004052340c000044481c4544e43c0422844258038090044a030a000250054030f851400d2001e0200e1081d01401a221446c000d540c1086299102d691241081d5114070001c0100c1c410520b01261905410340310384c401d1103000004102c0700d401012069000591046440742c005200d50f0b140c03c22500300611444560045c2ca43c840d070104040d0140c1c92260140780c0c045e100060501802400102000700c040310704c0c03003080c01000b1010000000700c502809100c82c83d000d1414640450520300b0380c41c100000c1c0400222000021401e40540241c03080c0c0d004004103000a6551004550b1241400d07034008000035150401080404c0c000d0340100400f6017035481c12840c1034804003c25080d03841c0c0880040000540400401c0b02d40c4041c42840040e1105031126410704070062010741280c000038242007400003025442808640d160b040c01036100f10081c11001c15450190107000050644040d001c0c040c1c011109440f051101000301030b842 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 390239163 1250 390237913 390237937
    0x4080a030617100c0e210d0c110f12030c06070f0309020d0b0a020d02070f060b0907080f0c1201060e030106060e010504060e0301020403050304170f010510060f230408060c 75
    0x140f00840c200141c09420b50801103414800c0391403039000c02e44c542c07260b20015461080b80c40300c450495503185518254042c0c0c0003600700096110400006a990307007031450910703812980219141048000103c0042250341450043d00c000102500c2c030182c0172660612a04054a03604003080c04c0e19000d4060350382c0000020f620a51050804000922441e601900711a1001c801410011481520012648003034000c2d2515802500184e0402c4036038020000084415101e921040c148150064050b65014007011035900048000801107414842981e41780da19044940b10b155030343c0c00c00600701003920829030f80030f5420941c02142d42e0313004280441c00200107950b100d28040c9000c6040307400d843c51901546c1d06540804c40000403490810142c0054501c92a6101c4245d0800000900c1c0c81103c1c60402403a03410201009a10000080107108981e12410000d0746003100030303412030300c044d00000d60788a0801c45141c80d02c0020a0400a0020741d0f0100c0121021512002038100b0320340907010001d02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 390240413 1250 390239163 390239173
    0x105031203041b091a130204030804030201080a020f1908070201091101050a0207050a030302010c2705040f0f1b020f03043503071b050f1e010e0904080a030617 70
    0x76010807051a5042c043d82c40c40c00540f44c940300c0341001c0e00e01001c00480c02e16500031075207019243c040c200440b4429051411403501d840c41d41c0381031a6009512019041c4804800010241030081c0c04440f070128074211400c2d60755240081ca4a0f0501001c0c0441001a00120000b0042401440b4150000313400a21016a00b03d80e600110b44541c070011101d0210f0081308800aa662590203a0700081c500c07940010412000d8014010420080381454000e01d1058000ba42c6e8200c04400c2c0c54402e9400a03140801c140705038070502c2003d403203000c690182091078094081102d0701d9241000e42d14500d20f40c280d07040d0030301e0780003255582d000b140105410701d503595400d003001d450615002c0052400120f40c12000755082c803801c40c10b40d00038240c191a94480e100303480559000d40031100024000c11191010140c0d5400d02050040701042a01451003010702e5890707407d0703801109000c041d1040181141400c0c6014500014282c10107461040801d0400c0404100d800040614918904480d80241 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 390241663 1250 390240413 390240421
    0x30c0b0306031509101d011104030b190219020d020c180f060a0324320903191d0d050d2a0303021b2e06120b07080105031203 55
    0xf00305414080c0080b00c06120381c00862101400c180031700d241d011415034166100f041da0803452400d585c3c502298102070082007000380f0004000d404000d410125954800da850a07040101200a210b0000320310700c0010204851102c1071360028011559a41541c01d071049080701000388580014410340b03a816400c082800036820540c000052988960003c02455500d9501d8449a1069000a5003034100c40c0450b0444140710000d0f000310b4410704901c40760b00300d0200710150701520145600b4440d481184082010030305010b000c0080d079504103148403424107080d51102001e0055000c1b0040307050080503e81094403945000c608101c000d9401c80050000d4816030741c411180d803013034011091410990821048a0260362886083d8168481d03140140d481c071403452032802a24560b1003001c03a50780030420103c0d00710400300d0012548280b41c07007404528580400e511003d072600d1f030403103041d90000369014070920015145d040c0c06000151034000550b40c9a509140d00c4602100850300400000c0000c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 390242913 1250 390241663 390241693
    0x40b09040902032b09060f0f0518040f0218040219080a141026030a050a05040902030a1d0c030d0c060e1606020c01180302090c0d15030c0b030603 64
    0x20250501c0281920311820802c1d0b100c000c500100e100c6039075183e08803400300f14000d03001762905010349918240341c2c3d0190303800f4074018102000f490100303040180200f40c072121907819074202c000c07070240180184000030031014040e0003074010403102400e403600752880b0f250500b000d1080303c4150065182c5c00d455118680d00a0750410000b820540815030785d107140e08807040407030710a03e00850205c5801c40c000c82c9000d04100c0c207441901d0400078040350401110100c11000400c0b03400d003401d40d08129498105a000940b5103026680c804512280000100034070741400d503100d84c0001c1c42c00481c10f03129001c580d03001079444107a0354803180c040c3d014a82c03c00c41c9500680860b000180301d11070110300184045e00140c20000c500c000889940d90544041c004143c0500000e054441f0a117000749515806111128400100d484043d00641990002c00d036550032402c00c403541d404040e0020f02c45025040c24980200310303d0300c02910300402c81c80010030480321400403079000f50070003001818141114210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 390244163 1250 390242913 390242921
    0x3040210140c010501030b07170117010e07090b04140103030f050904020415111b01020a080d0b0918011404023d02030403020f15040608101a090411040b0904 69
    0x90424400c0401503024407001c900c0040c840c0100310400410b16502d540382c502c00c22440980300744244940c4a44455048034503800307040c1100e510583c1e51551000702c100490041030741c200303070301150300440c00c0225044006400c000300c000410340c1e0402105e02c03c400740c1510b00340c0a000040000d860b18000f002c0c0980b0510203001750000081005140c26599245d540242c1e1748140c0e0701d804216110840010f00406000a54151051041d0000a022a840003c1d00d540e15130303030028100f60303000c01c03030003040845940241d0a0400151100f03072a4200042c06da220440b422442103050b40c00d10741c90780090f0017118103e0340156409060801e82400910b01854544035040b003080c0070500d802c40c00700c58a0740758010542d0880d0113801640d40d0b00e040d030051164030350780d0701c6215010b040c40090300502100c803031081303c0407a0102d240044031a100c400310711203216a9030344691004a00030100c08110799140004145c079502c1181c040002c8078080d803d011260140f440741081d4002c081c400301c00e003800e107600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 390245413 1250 390244163 390244189
    0x403050a030207150603031d12070e09101103010e07051e070f0215040806060603061018030804030303020d05091b1512010e041412040911070209010305030a09090908030402 76
    0x104c6000540001954002180d00a034400e40001d440c1c400d1703c880d0580c030300f80c83c2d1200c100103849404407490a00d01d0256920035500c618000c00c0213030340001d2540034041c00781c08591106c0c0e88003804500d4444807000380903002030082c510003101180c0401d1265000307008441048034841f0030031119203001c00103544160040070f01070321a031144022140c0103a80d01c2201e4925100c0307841e0a55112424880814500300b80100414094002007041c040542c0c0c40100010700b40340149061f00400d1864107202403800d502c0d600041c01520302060220070141c054001c1c100020340b034a0100f100d5650940c070b1503034401480550790810714442080905034245402180d43e41700803000038510301001c0102403640361a099001c0251010341c00c040c881080134001ca140720380e01c0da1600030030301d510000c0754049141c4190320a01842c141d0350880c004101daa007109544000350010007001140da9a410003e480754005903407940042d07914100072544841c80d01c9200c02c0203401030100c40c2585d07030b640d00b44000003035081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 390246663 1250 390245413 390245423
    0x2010f02071d0c0d15090e01051e0612060408091206060a03150e0613030806100e04181407210c030615080703050a05010606090506030703050601031806050f070302030403050a030207 80
    0x400d2114801690041003007200b00102c0318503885e4074182e02681220101080c07500707240d04080502102001003100b0802c1464911030400107070b1103d800040c005444102160940d000301e808101c1800751006c003601084500303880c02c00e014142c00071a41d8585000322480d5a005000c5001440410000c03110b6802d800074907000000c10705840171281d80340407811103603410700521143d001410180e1004442d5002032040e181c1b08020b1030102000b4010081403a181c50140b0b968401461007030181c0080a003045410501e28580031a105024a450f0413844c00f501c03c244a50700d222100b004040810607015642050345030301414115680c01000e400c075082e0034207100b205804045030010090060400075031242e40180700d061242c0c5400c40c02d44590b0380c000d00500100d5101008543c44481c201c9034001c3d041e10300095590303500f00059004128610904104008111102c1e041003030f607500482c0190040e5003244050399600b00d049099200440300180040c00034000404003034044d8003c1c0c010b00f403080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 390247913 1250 390246663 390246667
    0x726060408090f105d181202070308070311070f140405090a05071706010f0b0711031005010b09011b050715170406050609100506040b09060904051302010f02071d0c 72
    0x3500d804061185a40101703001c0030b01c1c0c07403118004c00414404d16511469254028030480c10000d000180030001268003500142d80351926020300751090102001440d40050141c0c0c4400c41d0b4103005210100e0756044225604c181c070008a4980c001090440031a400c01151000000718501804054180948100c0e01840b60044100006400f4421348001e05600103022824144180c42280340c15010382c40300600940010f428051940c0361022925110b070400070196a27160800c01080c900b00002d0b91401850b494880003082c032004003001081d2445c02640c800c14641032602c40d8000b40d18401e600184568840d10b810410101038250004034034140e8109445a070f0044e1806440d0003800703c608440c0d940e0380b1000c006180c5446052290031100d030700c0c040f2003040e0400d804101c1911a03030140070261a000700d540310081d51117034112480b0380e00160003880b10f8182018100355854004400307c1c007080c800c06183c8a100c6c03001490100302c5503000c88012808210f0790021410b1480079012850003201 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 390249163 1250 390247913 390247997
    0x2609120d062310080403021203040809090106030605030d05090d1704080109110103180203070306020d0b03010207050a0614040c0b031803070317010807080726060408090f10 76
    0x841c801030788002100d00700d841407000b150200145a5000c8000406011a40d800e01001c6640045c010703e80301036401030540d6030780300c2e0305042a550241d402143d500c50041c01c00804c4141d4190441c5c0101c1d4400c0d001c5800061070300100b41c0c2d00d4019255902e41194442444901007003c1844c2030b030462140c1e000e1207152036211400c0030700f918400b0302d0a0320311000c4c40d01c00402c1564903100d5210602c80e1541008140c4007143d0000351500c00078800a040e240d008220000c16680301d603c0842c03d80b0004000715910505868801d4a80c0d45604066a6652a00c10166010300703103100c125101c1d40e40010301300d03800781c102516500c103904050a0355159082c08881401300000810052200340c0c004e07241d2030412000c100c030084403180143c01c10702c9203030400081046054070000d84001601c0b10088941c24005620f000340200d40d03891840d00e02c1b113205413401d010034040840c004012000054600c201000990420700010701c1e09002c0c0f1000040c1c42c2c10003601d00c5030b41205414104440c0c0d440458100c82 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 390250413 1250 390249163 390249179
    0x1c030b0a060908070501030506011707090b1201150f0c030f090e091006050f010e0d02150415110c0108070810090203180c0a050a0b0a020f01020a2609120d06 69
    0x20340740c11210100e851800180101d500030003216004210910b024403a500d0500c000814403403c80d1007841d0442130304000300748124004c844113401f52541c009099142c1c1c03854140c81c60091000e00c0f41800b80b445001540c001144101214003071400e0584820304c0d801e407903603000c03100d185030700794030b6000c00c5a021004159080341e4010180101c216600400300c400b006015003007288d0703081c1c0c0003512854010007132002030798004801600002085420142d80032050020030300801403400c0800300780e68001004581c112510b40c5105242c4619594148003407141c500e950b07501d88a24921030b01181002d0b00080c15144902802d90b8071400d101000c000807070362101c9480507a001611071030750f441c5003030805c40d042c076100308243c804151040b00c005089500e00f00c01705681c00c4d010b00801e100c10f0b01c0007501042c458005c0040000e03201c1c00c0360007150741e80000a03004003e1249140c08600394001503000c40150000d040a450058051002402440c100103520302d01a038400d0000030170103503c66200142e411 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 390251663 1250 390250413 390250429
    0x150415090510030603030e030a0308060607021c05010c080c0c0604150f0623041b0c030c08040914180d0e130212010603051605030609070c0204090f0b07020d021c030b 73
    0x8500b41d00c010a0040c1140b40180460b0074010146020b948200c5418004c00c1d4010482a0055010f6809664402050000c10004034600300390b061119044c500c1c550801c101540080030030b00c1d43e5a205021a1a0661001c8680c4902c441b1410707941c3c400f2010401055212036078000844601c1000035402040038000c005540c490343c84503d1745440420b00c40341410255900c011000c8040342c0c10040b1780520310380300e12100807860382d048c1004081050b00c0d04043c0142004500c1c1900074035080d44850b45c54861801400544e6040c0c0b2002c801ea201180050f40024100d0701104052005400d00038526603007110104030b840c16236a0721550844014010f00403610060000c00c0f1490180803056050500140549070007071700144c1744494100d91451200d5224090b20f4100004440d201d41a440d04901120700542001000c0c0d401450320404104220080c4c44d810708039449019030840958969500b40d032039a440f4070354040075030060794229405004160016040000f58140000c05804282c0811110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390252913 1250 390251663 390251689
    0x121b03050a03033e0703090e040b061f0804020f300c06071703040606090615021b030a08071403040807030c0f050f0f03391504150905 59
    0x71940e16001d1211114180061541c680740400344549800119607910000b030010303540700079404001044005c01c2511400072580140758a40e00d802d02403d00f41010914110240c1c0c041c0e11654400404004401812202c1c00801c0501d895200b15681e50b82c09100d09014a4114035078040201d601043d001070450804180b0188442d10f21003803030342000081c41ca0145e11342100c6d4400c0c4c10a100380d0000a040c00d450034066003000b020103031603898528242000e0601c68000c404000d0030800085603000c4490717103883c004200f580c22500d0240e00310056041034012410074035003582000404401040d401e000504016209109141c448050740c6803281c2540c20617000000d05030040c80081003807041030300300100500303d080340f601c0704245803000044600c3c0e030040005019058a14606003642e8040c0b10002c1e80e140d503e1040e4050780ca54815100403281d400070420f0140150360740305441410200e4500d004102560320721403605003820110030181c040480341501b004107031000851543c40d804200904 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390254163 1250 390252913 390252917
    0x7110a030b13110603060604180905010204090c020c0a030507171606020a03021e031603020a02040e0303011a0f0a030902061b0a1202010b030601051e0612061504121b03050a03 77
    0x2d0030001d1800c1202c0c188045000ca105200c2481030004503591a8112400c40382042c0880400710040300703081c0e016043e01c04e00548035510210703000450b55165081784102d401e441d801d035003c3c0c00d41c000422101041d28000544180e1000c03409010003030503400c0c1051100020401c0311481b00f00c100283c0f440e100e01f500100c0068000d0b010090400d0b4040000d01102c02d030050214209e0106c00780e0b01d030b58902070803a111070041120880c103810315009202010805401038418481449005a080e0b0307294420302c54541000f036031050304040405c1840690b1b000c240650131003490b20030440710803009081a40d034180d0f40844200502d41404540d414030030030024400700503140c443ca550403c0074202c80d04002182c1564100764415046960210b6454152041114418040c201c50b49a601244c8005250301e42c00101c00101c0e0060300c22045e001c01c1c4540301c1100d40c140303255126090034506005501c603036201c0740103c0022400007480f040e200003400504520811286a40b03844813440c2881000c02500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390255413 1250 390254163 390254191
    0x201030b030726210921010e1c030b0d020d080f0406020706030f14041403190302040305190213050402190303080f060901060c081b03030108150109050c07110a030b 72
    0x10481e00c06015021076803d103071444e1204a00f500c0c1103242c1910401801c0c601ca403880360260b541c01001d144d0505809684c0c07100070082949015009075481c0700604518181ca90900e41a00110344280242000300802405004c1c000081e039003030118095039180100c0e6580402d10042094400c0744014000825069000308084c82c03906501078102c480e1072102010482c00d280c0d140f4650082c02e40420b1b00258841c02c81c441072203500e00f4050843c01200844c0d05c55120039101c034101c855042c1c010b0705c1540d0150050392061003030201c04d601c00780c1000c80d00a42083c00c10002c070404d8130050b071280d503226001504081f141d011000410700d00106035007003100400c40f81c2c1d0902c0201c034814201d080c0c1c0040b0550f844c440035410500c7c0582801c84580b4003d200c4000000d400025110088294a58594010850b5241c0d42c640849945035406c41603894003c40201000107045100c90090b00c0c00744030300c2c4a4851500b06980c4801752004140c08105800611810000001900c5003940341c3c4a100340c020f800c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390256663 1250 390255413 390255479
    0x2122d16031d0a0e070c0221070f090c08012c1303110d050313141603052a010e1c0605060f0a05090a0203060102120706061703070f0201030b0307 64
    0x10354000c4109200a003d031820304818041c840c001032046410048908050501c450b1910018014036140e080d44600c4c013844007040401e500c070004244090b51984480001c0854036000b05000b111211841c180000309130700010014401d803800951100c24400c040c02064842810070300342d643d10301356244120754500403408402e05a01010080f1401c440d10040e06035244010801032490101410144581130b444102c8020017801c0c0c0201104c5044082c2500c0c0c4030001a2000300c0c3c102c1d0540310079286030168000d040c0044101519001400d00c0201c00448003994040046900c030611401c00354100000c8160701818280c0d1020001000340306400100d1113103003032802d1012140e40400c0d200d000d04401101401140e880c0e101d03080d8014004600141c8a582c0e00d00100e02d00420305a024000d00400100c040c140500da810880a403600541c580071010080c600482d6248034441c2e015043d030003c070300c4000040d0b1280d0031024580000804641c08940c03a0f515091440e840c10900920002d841d404071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390257913 1250 390256663 390256697
    0x303120702060f18330901020307021e060411010903150501090f06030c0b0d02120103050d08061509040504050c0604180501060801050d08090d0b0705030702122d1603 73
    0x46680000b03644c03950081900540c83d103540e604aa90006408803440509084c882e0941031304a80300020046083c10a60074400381a5000b58820380d80c04c070040c0248021824131080501e05440703101d508400a00f442e90742da403581d1451381e60900c1c40c41c2c1080002c01c800030204850070445d5585611507030380010036514000084040704d400400701488039043c8801003000c41e0381c07a0001400c480e05c0c0344100d559030030003481041c02446004840000b4085010000c000d00c280001e213054131058548920320300e600d6038020013001c41c01c507031011307502c1410402204a80d0709090300207a81052242040781d086410000c0041c015412580118040840001d0420711103026800703500d0040c5400e0519844c2541804086159995006c1002d00b4482c4000f89000b02621404840360383d0700e421600395034003070421110040c51507000703a5030003005106504480d61083c02d00011140e42c8a606004411000d01170300e0403800f0381065190b040750a140600c103c0440390b61109541004500c0395a607040d00c101c85146d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390259163 1250 390257913 390257941
    0xd140f031e092d03041a0304060f1404060c12061508150f0d050c060a0908011d030a0e030f07080303041401091703060f0a09061a130e06030312070206 66
    0x101e510194003c0340c3c40350b081d004080800e45518940b4844407003030418007900c9443c0d40b10b96400f04d000c6004068003440403100030000345010b58480c4c0802c1c0000c601035aa440103580303008001c0c418000e0411f0100d000900c80740c1c410313803d513451420040b60080740c4110840c00c82c1c025034440c1c0b42e44940d0b185030480246d842200c1650080d10416002102100d0741c020982c000414524207005412401d08402840001c01001100c18402042d89680d0050240010f06140c070a01c601d440079801c18038250308901d070095440e0b400d80c1c402c00086007041c0490000f203480b695000031040e018024800802d08a001c14441c1c81d019020000c010355480c01d244c47c00b10494420f54035402c15607403400061030001510001c044900c0d4950100c1c0e80c0e2203494100000e40f80d0345032841c82c0b550052140000050143c01c5811220841e140711600100348280240e01e00b200703115440d400118070040c2241407101000c10b002c03c641001018007100d007031028040843c140100b0a83d88030001d82d1003001002040b40154103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390260413 1250 390259163 390259171
    0x120606120b0102061003030e18070309020a06080402030c0f0418060c0e010f02030a0f030b090a1505040b060904021b0d0306030b06010c020618061330050d140f031e 72
    0x700030402c51400a28201317000140703010007400c1082d5030607242c00c19514a4260105080100001110f038100040082d000385500c0100300d0040784110750010b440c40c0602e800510858011b0060211004035800b003100c032101c0300b40803680c026960710701804c50340700154801403014420f02d0300040085807090054241c24902c08070034100f01d103204d09801c00a0f1702009407002c80085090000280c2400001034000c5c1c80c1d03a004007500301c0f848104020080a803a0071180e0344101c544002d051458881f010f10007a03454100c1c955030450340403c52603055003019402440c5410600941c10581402c6540140c180580203070781900090b150361060090211081266401108c00d013400141044180e0100d030090149203c0380241603500e003816181c6071184030480d106130300341400d0442c7e8151686584101003205440320020305501e88007440059105040c2c0300c40e5140c01000a1000c9040b480d01100c0201a2141c0425001400e00c000031075281114040e500403002500004104060148102640d0300010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390261663 1250 390260413 390260417
    0x70f02010f09060f20071101030f1a04060b1e07020a0e0c030f0f0f0406200406050c070506040602070e040812010b0714010902010f0c0f080c070e0a0204150e01120606120b01 76
    0x6105d028411845004079007403164400303528012a40400b005900904481034a521554141203d2000c06504a40c509100480c111002c0014a0300e40116003114010364555102600450301c010100140c0b05000c0c060f5148000d040c40c50701c0780c842c181000381c02d40070b40b107004410401000b407092000c9190b03642da070f0008060f10403401503d000002031801e80005000640026624502c880580d4044c0d02c66543c0641e120801590380c40d59210020b00c1a40002c0e903914070340c02844404500391501001712002ca503403540c0108402824207524007030244025100b110f400341c0801990900c2946490454001e051015071103445020ba402e05184060002c2c00f22000390f403400e43c11000503a0800641410031300c503880d20b8040d02840d8940701121410040d009810301002082404100900044201c01d0b0f450450020b01e1944440c01e811060b80030354043c81000f45980030080ca4140c2c403524861000c810145052000400f840c415034049854580041002030100c4800c2c911003010f40c041c604415200b8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390262913 1250 390261663 390261701
    0x150f17060f010e0f0a081b0a03150e100603030f080105060313110f130e0f0319120b04020c010629070204020c030c030a0903030806010f0503070f02010f09060f 70
    0x10380000c061104030354046051010b50441d068a60301d401038100514000548002200b84d00c4414443d0f4030800b591201c00400d4510359521030f10b040814503603007143d0348004499021013009294402400c00744071140e42902c0f407c0041c50044c0c51070301a04000798060b0300c400e1001358030100000c09c40f020580201d40148020028014100520b00ca0054055041003d02d50a05060000039510700780100c1c0403584168645040d070540307103c0f41d0040800710007540440f4004402c2007082503c07406034041d0001290001251005068014031600140302c14100b00000c0d114003c00004089800000d03410071140c0d500c03c0b050019540c20042091241980c000a150020001c0c01410341442407250090045402181d00700c21107008006a4540c09c0752841038079101d0079292001061018984000d40c0041e03202c1000c20a20350203501c0000e499030082e562185541d41e450303005d441c0840c84200b054110b41d0303681c02520381181e551140403241c03071003244041545051105003800fa5014010075042030151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390264163 1250 390262913 390262921
    0x203070c0f080d150605160203210d060f0501080f0403020c220509011a011805040204080d080105010810120203150106020c010e120a1205070c030303052e0b13150f17 73
    0x147d03841d901180841c940e61440c6440403900b17050035815200456840c152440c0f00c1050180064030090300c40c0c1c0010458280c0d624031807068400d20b80715072400304882402041c00040141d00390b903401800703801101c0c1d64180900210380c89542d240c00161a001d81000301c4d0410810358025203410486d120002e000c405858905103040b490808500b5050004103441c0c80000e52940e40050000c0c1710081045448540d070303407016519258a40949400035100200200c1c43c2c0d80544407260107610b01020140e0203500344808040342c1c1c00c0101051341c0c58421a90004070030603001c05080c1c080d10581d400780821103814000541256155074506200b00c18440310608250340018040c00c0c1142c2103400f0484680c0d600506032150b1243c600060402111010044140354060300520b026481d16066002c400048103a100c0d0040351444079803210340c0c190541007088071070800c0602890805c68480300662a510845900a003081c505e41a01151054641145507900504410b070310f56941c440c0d041c0e01c0c0c42c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390265413 1250 390264163 390264167
    0x70503091908090f12071701060801020309070e010b04030308010e0c07050a03090812030603151b0703050a0906030e060c090f041a010e03030a0210090606120308010302120f030d0203070c0f080d1506 87
    0x6058047c03060001045d00075542042801d410060003804010001c5680e41400d01d801510780600b401154440281c40c40000f40f0180146c04a4044039095130740d81c8260707400c20a02c01010180940a0a0803420501401c1d010440501180030b806100e51190030081380b03040719013401d0411841092840c1c090030303c00c0040d980c42c00b040a15001400c6034600311159a10341c0c039080700005480d080c540450020035600e0406400c50020001203071503807030b0350241c9541e40d4070840036501c0c489007102c03440d00b101006c9100302e100c4402804480400400441c40001404040b5040300c0c0c980c0c040e040c54001042d0032860650304501010b1403d681a405540750260b8640d0180d512680c40345032098080c0e03a160324006111842d8030aa01801a511185402101500300100f1343e241c01e02060f8420080c0700090211400e00007038011070825504081c42c01d065101800c000203400080c01c0350240001440024000f41440000405152007030118a48444101c2688021201e00c3c001c5a108800000401d01a5039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390266663 1250 390265413 390265423
    0x90c1110090512030402150a03050709240e130e0105100909031d030a0f11030105070906020a030827030d0e07030b06120a081602190e070503091908090f12 68
    0x301c5503440d004d039a9191880400c00ca0143c0d008000704c1c2d8880031841ca0110355054002a00494040e03540d00007054590341c20021503100c4c4d04034a84c8500709107030186581e901621408900310002420140404007000014040d21031140480d29280d554200b080003c0717141d56100005020590000c0020414554015001c1d1003801c0c1000e9500300844207280065404001e4116420b9000c0c030120314044940c9802c0062074110405c00f4480c0d424113001840840c41940007074101e40c00b80d4003d14501c00162405d84040c1001740800d1910100c03100c800c040b1403000900b030b81c02c40360044e004650321104200b280e0201c2e070480c40c040810b60408c00301003010403030030051580c003c041142c10700c41d00054080407920300070140400034002d0101040d0555140a80c0c20354032055402a9100304110000701068540ea1880e030040d0a400d00742031000c00c803094030810140da030101c82c0000f203903030462400c42d0170030100401c4a4229100300c0000b034900001e04101a0300c03100c00a0540301d50480a19485c0c0c050380b18 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390267913 1250 390266663 390266683
    0x403051207030e060c010603050a12080601141c020f040f03050d0c0b010905060d060c0f020f0105040c06140f0c0a02010908030901120509010902090906090d080f011a04090c11100905 80
    0x10b10070105017403032208000c2d071020000b16440300031202c000426107400840800ca00c40c1880200d017460f000511654010342d82140c120040b4007450b0300c0d0410055030540140c03856070040c2c50340e90313080c0034081c0e43d034001000030005401c541e04001d42c040d145182861900300c0e903440c500100304c0d40443c900009142e101103141540c1103860302141d036a1700d440202d840c1040844c00070b00000e003001e000d0300460740c10040742c0f00700341096405d5800e00c148c0c128070316003600c0003650005c01c036a204950400c0068464072055103401912440039161150202c040d4540e80c00000e0400c0882d0040c0d1005400c56800030740600041ca0520302950030002d101c00043d140c00880901c80ca030850f29000081e00d10781c401e500c001220384e8010a200224100204270603a2064100c58200140c400c00f0750a16602e030013816100e10401c0c0c0c1078160569a030800000c4075120bc45c80546011f40c1d5004c0c8808103001041e80540842d010309aa1002080c0381c00c0e1003500c1c40d00c0c00b40582c40d448140360860700004030300d0100e500191 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390269163 1250 390267913 390267919
    0x1030c080a052e091b050f030c04090201090302061206031006121211030705010b0310050412050d06091a01120b0a1a09040501060503160201060f0612200403051207030e 74
    0x1038401c1e01002c4000c0c0c3c0342201000c00d03202e01d0421940b0401c011500d0300324418841080d2000c00c0d0317896005000701d46024003601d65051780900810310721494240c1004825a1040c941700140707076070341e41c003090700d80e0490903001c4400354100d0100122400c0030418034401c0b00052009104113031906201d0f01000d803d008001d494802060081c07440c55000c0c0d03482820240b00401104e540e0602c0b070030114000c050070507896101740a02420060884902d01a80d40910f41100b8859526809490240c40b5035000011f102d02c4191a48000160000e243c800d030340400b500715010100c18480700307000502c4401c00c0038103110014074013141c84141d6216100000251340201045040105082d000c1d0300caa4016103031366960260030500040b803801d80c40000f4500445010b87e206900b0b50344190160b007a41c0031406040200c0303405010400c5050b104200c02010549003070400100c003042d4917910510001081c03180103080800040030403c0210410411200d07200c2d4100c10341c200259964000d210203074400d03e07188 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390270413 1250 390269163 390269203
    0x61e070207030c06030b0f0603060a0e180a03081f03030f0507020d0f0507170604080904020703030f06081c0201023108150a0f020a020c280b0301030c080a05 69
    0x2009038020060040075641001d02c50300450b5413218010050881d50450a01a0b090702d0a80c11160800c141900d004120041c4040001410080038030003000b4028020400155203c2880c90405000d100000141e4000c3c0e581c50010710706813480103170040415800700c4000035045010004298003658003420340d4100c0c07070480e40c0c034000c070300002c1c451880c0200c0241a403542d081e2020f04101000130b0300030440b50045104101514271041268403203500b241e0142964104105001040c906680200402072082c14001a113809041d20041200c499405c15480d0b03502680e6011003c400038000d4805c4408540300961601144140c0c00351101070341710101c84000c40450031440e0000c103545016010305504011581da0f00811034280030250015103100e00302d1442c1904011a4201038000c5031094034036500103025030b020400500500c1098004101e1602c2810a091040052810b280034000c01c07200024030380765410360a05a40c0d46403d98444095a0f100101c650005130000c5540500e45240b51071000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390271663 1250 390270413 390270421
    0xb01030e030909011e0f1e080304080613080c010203190f1505240a0c031706030c13021902010902030705010305060a0b0a09090f09050d09050d08031530061e 69
    0x4134000c2040c5c002c0e40c40c403030701b220000c1080958590348102d60255240064550355941d0003c681340c2c4980c0c081c40d0302a4112078001100e2a040d041119409440303080ca042c40c2094091881c0c3c00c81e00169128010174442e40b1103080d1011490042200e40c20ba100d4040020010004e00c03e82c0035540d9200303050080c402010201c3c02c03003105200c501d012291001d0643ea031a120f6000c000e1800b040c242045000c80c110b910342e00050302d0040ca100703110340c0000e0010010b034000381c01080709449982c6c0510548030703002c000c0000c07807030f840340741070709186005030008a107088251042608002040c2c00c103c0c1090301d064108003299555194403400c4408034801c040c2c1d210309528084540d05803c2d00455101c80c1407420103000c00e42c1b6640306400040c000c0d0140d1b041d843c9800c2017102c50b400e8a104040d88401e0b627420b2000455058070055811411001c41781e00e00003180780209034000200d0703480c49200c0c81750440307110701300401200f0303e07100c00b4000000c0c0807145022040c0d0700d06000070b1448100c0c2001000001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390272913 1250 390271663 390271709
    0x212010507030c031e091b030b0403020f120d0203100b0a09060809010507200712141b0a180605041d0d0207050612041b180b12190c0e04060b01030e03090901 69
    0x410f1403c0c5961f45946c505916820811407001c03040e2400c5006102e42078420032017a10105440c00741f48030100e101c52070003298415580107900090030b41c0a00a85103140054510714103002003c6084080d158401c0b00c5291410140078480700030440503150f4180402c124403540d00038251440301e410b81d11040c07400e16101d450945021400d8200011051052190109120b01510101c1c1180c546900701c2f8144941019020700c52550300b10708541020f030400c001d006600c0e07565440c043c0350b0080d4500054155840c2c0000d0b01340c0e07003400356822198503045025a050041440848130a034524002005121f00d02030105100d8070070b40540000d004014404a0100001d03540c100b54001c282c0054841354075115200306505000c88452214203919051810b9221f0410550306212220b0341c502508a0701008442962140c0100310100e0f00380301015001700d408682c10301c45502880c056200001c000b09200f00240c101c80b015a08980a1b9105011403400c0750350300100f160540e000c0c10142e06031800f0203004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390274163 1250 390272913 390272933
    0x130209033c0601030605060d11090613051306060b0412020f060c0d0201050603070501230d1d0a020306010905010e06100201020f0703110d090b040902090d0212010507030c031e09 78
    0xe09140007805060507004210000301c00341600d009000400c90f9468000400c990b000c085c440051146c06010340b0002c03c1e144c601d03092640000f000e090800d901d9200181c440844604031840310b03c540162131814140f00e590711030741d0040c01c003a410300c1c1e1400c3d0074906034060142518400074483d130f05429115002da11807000303580740c184c500070840d032008141c0600680680303401c031201030181c4200300d000039496103d61020291144100104810b10000007404801c1e07500440b0110940340c0c44643c0c80c0c080c0742050340c04a078041c4c1c40001400b50f01e0694410142441d0741a88911540c1d07082c440144091076103100d403542c0210341250b41e07082c0d142010f417041c0e0190041080a40c24140e000c42d0030f009050b040510440241103000962346410800c4405a0311080030307024620300880140414400c09420394010489444010b04100907521a0b034002045907a01003591202c0b40d4407041441403c40c0c00d400b4800742d40328142403d1000c1c0c00e8000b0341400700507a400e444510540c0b5251070303030140824084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390275413 1250 390274163 390274243
    0x11406040e070c1412040e0c0c0d02100f05010605091324030b060607050d0c03020c03070f03050d0f0e150f0c030c0601090504080a08150d1113020903 66
    0x40844007490810b8019180499051080c0c0d0424082211000c003488085030403103070040c100c2980c82c10a800c1c4030325149240802000e869a500301000a8201e210f4204a9602c50303507020350080a803402e042007c0e40645040c2440100343c61304001c01400060b800205503003681005a840d03403d0005075a42007009002400c5164130400b2800403030341c1c41010100c0328001943e000c0c2e61035102a0301d814042c00034920a5000191403604000c185000701c1d4403546104041d80d01900c1104c0801c00c0303542c0080d080c8406580100041d80c0e80007020410884280030241840100e400c1444042c010043c0c041d00720f1011038102482500b2010104048506010580f08039003400d01d14540c90381070040505030b9035070205c00302502c140329140000640034114003a076440740d54040205820048140d2041c4c442d4000541012218030402d072408080b81c5034482c4190185008440b080301541500382031012401ca00004440c900d4010403051410f520006000341c0043c054494612009100c1c901d4032404200d600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390276663 1250 390275413 390275429
    0xc06050702131a030f070b090411040e0702011b030c02060712060b0403080c0708161806050d050c0916140d021c0b030d08040209060d1b0e1501050c0601140604 70
    0x1620b00c4090f44881d681d180c100400c2601268554401c45e101c1d15907440b076500c1080140348007000f1040b010f0605800403540c12030040d845d9030602d52203190440d800380044900600503995040b044409810404100c09440620b017800c001e0320000e484003d440301c41c024030a00500030803100d501c1e00c040403540041c4c001c00701c40d00e10701d449503104d1a00c01c0541c2e00c0254020986d1003444000708801e103021412103014068032082c40c0d9014075118400000117411080505042d43d075207000140394481403040700381030703101e0380250008240490070004480740c054401c60400021b041d00303000d1107400801c2c06402440c59504140c40f00c1c505100803010388111811000462589203103000c42200313a820290010804405440302140c0d2a0400c9490701c5044501070344c0507040801041075828024034024580d40180d5104a801c598103000c100620400d52008070394282c00002c200c003014500303404860102017441c0241c60403002003c041d07900c100c1030042201400b030b034200b05655503031484101c800500c520 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390277913 1250 390276663 390276671
    0xc020313030c0801200d0905011103070305040c171018121716050409020c21091f08010e091c03020d0e0c010801060302070204090206070c15020a0c0605070213 70
    0x1d25040e8035031242c5114880c242e60901d6030400c640882c8000c0c0104055103152406d052000407122900600608030041d50b00b5507030f403c80c13a405a0b41c00740017103110300c059071004280342c241458100c04e80c1845510020100450302d108001d5070f03000dc02e00107681c5070b10034008aa2040c2c030000c1103190b0134182000600d800c0da540100050640c0001c2180041c988081124800c0c1e55242ca248103520070845142001030402c00c42848418001d6001d058059150320455034500054141080c104c0381c1240f580702c1d010000300d03140843e860b08845c0c110b480002d460100b04203040d07066000d80a101c04ac06080e11032030f607100000314030b014100071280300801452035400b41174480ca4006002584049010304105040036041030740884005020710b100342c01a9205141d580c80c0c000210000d41248504aa0240d200c4244001503902d0310301501c400e074000c00300500180c1c1341c002c81508a880d104a10010b5404c02500a40824091a01807080713075942c4c18060ba03070300c4a0303100240e1180c0142c0071200c40540741c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390279163 1250 390277913 390277919
    0x712020f03011802120105010302060403290403050423150f07200103180525030807080301050a0e0f0103020f010e060c06010e060d110f0a03080a080406050c0705100c020313 76
    0x3c498088a0300da0003501c0189100303c2c80d60006003030b500d0902000e508101c04000400001d4500b244075911191055035003035280e10200c0301c080000c001581c0c1030300014004207091040442c1410400000c4010030980fa407540b00090104070300c501040220a5070000c042180750b0520940d00c11034020660200c0d4554141100a900101c2c18500c0504a40002c2c030b40340c000d900300d0820400502c1304940140c010000d042d4107103031190a032082c0290307800c0c04103412800003002444a0003c0c0160a01c0342c101c0f144c0765814801401101421a80300240c0d0801c403006026107103414104442c107694040c0ca426242c2d1540d40010703140c0410b0700403400e070001000180d00006d13290126401307058031a00e454a00e0503441c0d480030481c0341c0d40a40005401c2c14546200c0001c145080d003403051101074054404d6003256a41e0326154540e410210201c004600803104200400c60380784a10350388040d144039a03608024060b01e510307a0715440c580419000c182e546800704102802002510310310413940d00001d40590b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390280413 1250 390279163 390279191
    0x204021803070f0e060103050403020312060f030a03030509060907050a06050705011d150601051908090a060c0215090106030c0b130e0109090b0c090f011209211d030712020f0301 78
    0xf102e4411103c00c0f0360f2913400304002d0342c4603000720342c00395030994011420949184455040c00720050507143d413040190314080c441d5203050180f220840c0c001c2d02c0000300c604d045280307107003800c100030807141c07480d0040320050003250b031981c42e450705840003440e0542e29102c580c0780c528014a00c4088140c1c0d440c40080c50030b24815800a440052034a14a0a407a07840e180c02005492a02903401c2c185c00042c1e8105c55242d00301c2c8950a016404000b4030300b1140494500d484080032a0450100000142c02000480401072008040c2c560000d070110001c005c242e14503111041c921000303024030000080001500041141025920409001c131a0003559095954040c0309004010f02c0c10122002c2400341c000485080980003601c80c00000900501c0d01e400c811744c0115a01c002161400c40b402e03564020810100790304802c1034010384007208944500c010b01c484050003103500041040c0c094142c09501e20700d0341d20049009011035031003e04014075000709200255043e81300d002e11541542c41e0410b984c000e82 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 390281663 1250 390280413 390280439
    0x100503010b090f0c0d0b06030406150b0c03030103110d051c0e060909040b04051207060c080901020a09050f040204050405041109011d01060f050705010e0a05071e03020402180307 78
    0x14104a0007080040e2140052140180c81240c41041101041001907807080141004040341c260b072080004030707062070900280b0303950402d131025034080b0b070745544500c02c0d0f1122400300300107400c0b420b40c01030a003041c00a12030b50764817050100408414104801d160107846562074581043e03070010903988040461015002c0d1501c82004890000301034030b1500f055400e1600840d2490031020701140c030250398940ba00c00003460042c0c000c50b00e51080000395800e020450380603029031885400f006c07443d603208a00090940314081d28610145e407040110240e010781001c00b40c0100c610540341c1080354008032000800034001c50b844141c00600301820042003100c00f411000c50001300702d480480a0343c075041038901856204400e4400b1400d00c070010b10401e070080d0441c1d03c42410034039202d403400303003583c3d20307a800e49682e240d180d01d01d0786c00207030000d08204040c0203507000b0b0414403491070080c082031040081c801049100113405268005030185043c590201a19a00c1c0c4004d41100d804503a280858032041e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 390282913 1250 390281663 390281669
    0x3200307020607023703020703080f0306011e1d0a0f0806060a0909050312040c05040207080c06060402030622060b032703120601051b0d050c0105100312080406020c0610 74
    0x50003610702c99201c00b100445e00c00350200405a00a000444200320140502031a880036030552140c103c000000401013401040070300e4201c41c2c176a0316804d0543c000f529001e40c1c8000080c80e0040303446640041e80c0e01c80c04c0801c1002103a06214180345d40324002c035038001c4150300400070554035108080303a04240021180e000e480181e4024100d560340b4042d61046a0300f0410081154004001c0b400030f10603007030303450341c3c203d400ba58004011503501c000103030490b48000c504071000c0c5000301350b1141540c41031001c039901030015641980b8500c2e026002400085e0b00c6071040003c1202011103102c0c4400340e901c0440645040c1407e10354a0500b43d9a000021038040c01659005600e02030321040300c0404002d403011020046082841c41d201d041c0151020b401034040700e00899405c400d030b90401c001c1000141c41e46140c64036030a940e03804950040d829204002e1500d103070010800820030020740c643c44110340c143c0c018501208107880c1c074641a00640314580c6585614402c80092154540007a513070743d411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 390284163 1250 390282913 390282917
    0x70f0c0509041a042a0f0806010308120702030c070f0519031214070b0403080603060a0218012d0305060a050f030d180312050405120115170a051614150a03200307020607 74
    0x529603032060320940c8c0792400d0100400b50b0409100b10040948440011741c1c00c904140180e0781481240ba000f1440c0070360681c4012114082c1d240c041007207082014402c1c200c21300502003031441c1400c50301c4e1081421200c2c0282d0041080c00b1210780c0800160354190b58100d68003000c1d031801401d090500500c0081c0560304036101e40610400b082090f515072007100c18009031800c0c9004c1c400c0c100401954449071f5040d40940c010402a5500080c00c00a900002110b070252000281411700e031040c0326102040703400c080e0003203144006050060b43c0016015640100e80d14215004c0c54241882840c0d510007a80028000004407414480740b50b0018080c0083d0342d0183c0d17050300a0341180b0400c50a96260040710395404040900c1403042d40d4001c0380002ca070031095001c850384800e0940d2858505280983c001c50b041c0b1850105000214009001041b0741504030fa00c1c2c00c0404402c0403c1c28580b290706808003d0603602e040074454040d00c2070203604400d0402c880542c0340e01d0101c40180d110b440840300000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 390285413 1250 390284163 390284189
    0xc210106050607050a0303050709030b040b1501180909031b14060f071e211a030307021503090c060a0c03030608010c0f0c110402070f0c0509041a042a 66
    0x1c1d590400394295848507402000500307900049032810350060001401c0385080011229000c4045450840c03860700882c400c401c46142031400382d03070000d88903805070215030410651202811002c1041c4420078141c520700380c0c5c0000c9071500c6141c1507403503031908455040c030b8007010855601484001003000155800400076181070f651034010394060b41004590f5400802c0d01803560440028a9000702109012281030500c0d443c4c070300c0341000d003a00c04084181c1820360303150b980398040d401c100e10000f944441c0036001903081c8505a80060054180b0305030314860920007100041c0d0100c2d0802508001c00800b90110303030303503202d911401440301c101d0080c160f003c0390038003030700142c3c8a0052280182c1244c1560341c007000d2801001080340e804000038070541c2c0404504da1011080c1c0d50354030040050b10f1042c0c400518042c054035052000c00d000341e00c210f200740040d8003000b010800281c0d0b1300b108581520603100d82d82d0303500d282680741c0e0410031105030301e01036485e00740036800521000d003034003070700c0042e11408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 390286663 1250 390285413 390285419
    0x6180c0b040e0a06050d14120309160806070806240d05180708030f0a09050a0f05100206010b0a0f030f050103150e0a1e0f051501090b0319030f020c210106 68
    0x90b00ea16200d8140c200d01502841b0011076204010308050460700400c1c0c1d0040d031032080c1410380d5504291141081307a0072443c8a141000ca030003450200400da0720000e043d1514000801400080c0001e001078000c1c806074044151800d64954000c10319083e185081d603c5c2c400c1031000d03000800c41202c1000008c1c0130241060076402c00000e00700f0450300800b009516085c0c7d103605440c10b03500184a050240040e5000118040c0c0e20700c61004003502c44000c40380d1000f46400100300d08041031560400540d0004c43c014082407003400e04554001e1940d0403c0c101e0352000340002c8000303105861003035003503618080012041010039110b4a404209602d0103024180304041119161010750100410103a440000c20100d0204074038000072880c09002c180118528517111541400c0883c1c10001c1820b03102d100502010841e44148601e6590a80081c07691202010310551040c12503440941840480811085914070810100111101c09410649146025071980034a004602c4224031300f07508009000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 390287769 1106 390286663 390286681
    0x1e100f0e150304060b09150105030c0403080d0914150103020438041506121e020a02100c02010c050d05070306031a0601020601081906180c0b040e 64
    0x21942c1e440d080c0303824412254190310b080e216000200030720081d5003100c800491307017500130300740b1554945960700d92003081d004940c0300810500f8006049400c17002190800701425104604903142c8440b5002d40301d4a41502410428103010040010409440d00d90440c4a405141d41d50418070301074841d00c104220144104032030082c1c1c8203403131000c2d81801e00380f00b2141000521940900310500700080144007002c4e440c0a01001501c5001c2252490143c121a010741d00b6480c408550301d2180c050080d480740c0702a60346604c00346c80c18141d00400d07130060041c0c2c05800350f960340301403a010f52004010000c0c071014129001309a034aa501000091002c02c0100d0b90380b8110b0200555468072500092034010160820142c1d9001040051317221404140750010f0b031a8421004039007101642e60000380b5240032140030b0001100c5000025000c54400014810340d0f841d41054400b0356140425 = true := by decide +kernel

theorem cover : BRFrame.Cov 390107913 390287769 := by
  have h0 := BRFrame.cov_init 390107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 390107913 ≤ n) (h2 : n < 390287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
