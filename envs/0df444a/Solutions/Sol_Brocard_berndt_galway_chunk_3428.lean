-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:56.383474+00:00
-- url     : https://prove2.me/submissions/2abff959-5ae6-43e4-b964-3b7832ecb87f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616366906 ≤ n < 616546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616368156 1250 616366906 616366939
    0x307170405092a07080d05131b03020102280c061e020601030503041205031204050606040b010302031608060616061b021b010e12010c17160806130908040609090f0c0e 73
    0x100c079040007008009007c40d00780101e4640710000c1003242180c0d065240702c02c400514920300030740002c807601640280005003100944155460000c4483c40030750411001040c08101c10b5648030f00245810303903071541c44602d405011000760301003d4120301150000c0b00100007007400042510f0075524150300c09003502002d4940645144110308140402d8894075081100b031010100b00d8a12418040d6014048a104c540044040748411100800c020406281030050680b0403648036510042c06400c841c03416518041c22014155401001c0b10042d4507000c0118000c1100e0f201043d500700e59000500d800c6010f4250329803480e07548030b030348c03410060b1004502980d03913100c84020500c43d4410000300111640203400a12080d01d10b10001c1040c1000030105946540d140315440c00c58289130b171002e8040e1103510030001040f140001d801070030790700d030700c01d403000b081950340208010305041d190594605d00d800c4c124002d603003061030107603413041c608084488141e0700b01143c140001021551440811484034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616369406 1250 616368156 616368173
    0x50415020c12010b0a06260403051c0209030d02160605030c19080f070e1e0d080a022103041a060111030a0504090e0f03070f050307170405092a07 64
    0x1c0e03031011040c1118000e801040d4403801c21300c8400d4a1034541203446460580746d070310385669040300700320200314000c818000c031800d866000340c440d16013145000c1020b41c9003442d07241890079201080b41c4c001038010813460b0400402020303d0041c00607142800b080b41c04004034040f43c1c8034031000d003c00040000e109800074011504070404d48880070501c1010407600414142c3c0407907081500e0040e00020030a0f0301d000f41e03c4100c00300740090406028000d0800c020140b1220900d1660b0421400c15090f000948050064442480d140d0700514404e02c8441c4061800b00c9101002d0700550010014003000c02c10007812541100e210340e444d0f003011748034040101c5096885458030019400b0200d000c291003644200100101d60b04101c0c1404070b14a000380064481c00d03612803940c1d07290f004010200c0001d911f030b030700d002100e4051015207007021099250442000803410301e440e2940c60006051180e894a500016000041c544140340f41c200103860800050191b180802048000824803404000145 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616370656 1250 616369406 616369423
    0x212030a150303050c0d021204090e19080901120912081503120406090807180b010c05030a080f0f06030d0e0301020d0f0c02010b0306100b030a020415020a0203070603060605041502 79
    0x90007240e450302d0366401c0c02003030740c1c10541000206008900300c41c0d008620000b180d03240850228240b034a031503c2e007202c180007400c0e04c188810035405038204402a948644918449807030007038180913520315481c0001070004442000f154400f500d003031010408616940b0b02c598801040e820b09a10584917100721040d0300e0424598242d1610031034000c42055a1100c01401c22030702d090310f590020301d45480d821503d43e9128042c129640401c098000d00550064002c252511410b0405600c1c4010944a140c04e5034820448680440d14101c14008440440000b05a20648500102896052082c002901c45180f1030f09007003003200c5201d03070518a94082d811501d41d61800d007000c0041c1d494440006c4094074a9941810165203409a405118200410755510500c0e003001400380007810302980c913030303240c1010786510072481c0d09100c04601d110380101e880902e040c045d0000c0c00f54100d940304040ca085c3c4550007a100701810180b0800c99907070000140c07401c1d502c2035500e2800e0b8103800758040b032824200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616371906 1250 616370656 616370681
    0xe040203040c05040f20040b03041115041e05010516020112021308010506090a0905030409020706090614150a0b040302090901152d0b0403110d02030d17010f05010212030a 75
    0x14075590805c3e0a00d103500084104000020440017584146020001c038051441400c1a15108000103000940c40c070307a0074002c2d910000c200d11540102080488016085a044801c0e0030004560900d03c40d002e5000303e400411091918a107001004c0b100c011620003054002070520692003d10380003281c40b41c040c0c4e1020342003034440030001aa59482c0501904043c0d41c114000d0000c02c0206008c400d0900a010510340c02c48015032074a4906824040254003029042e0b5004e035031125001c0005610740540e65100a28030074100c51420800040c4c10040110803d2034414110318004020010251301a10101d9404840194180c2d842e072032410302400744c04e00035820090b9414004100040d071050030f040c60a0300035000c030039044041d620484403505140507050381c8038002c1c0700c02c0000411340740e038951480c40050400041101c8a9022038a0000c0d800aa64080f403c90201da1661100c000421801800c010001c0c0c0240742c50100080d480d0700b0100703268011004008000b501100701500620b203400342 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616373156 1250 616371906 616371911
    0x603030711100309240509061303230a11100c0f03021b0a0c0e0f010617181501091103130f080c0604080d05062718100603031e0e040203040c0504 64
    0x258202501040e065013140c03d40c45600d000c010070380407e000101140b16501d072903900401c148041d10280e076000090300d40351a1940724140c4600a0301c1441c2c015040b40302407038883c048108080560b8605055204800c04d844600c0d001180000a501c1580100805442d040041c8d0700c0214107414007500300c3e10400704d5500e11600b443c0d4820170503050200011102501203190b203640f1803040990103203100b0b104400004000804400e41900e45001d40c1c1c0e0401102c001005006116541250400820600c0450f008010500400c0300219a01410101e0300043c0e40003455407810b000380d1501c0560601018080d1203070244141704201e410803c48000c42c0141c0c00301c88543c0780c1847c14288603400031810904d6182000041200790402c0300d040f0a40401c43c814028210091000491103010010000491206194401d1160304030910421840c2090302001284e90f03070950501811065103460b907004040d1041101042c1d0950002003c03c031020216005a80c03600d40b41850364020340107400040d406031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616374406 1250 616373156 616373183
    0x6100b030703150e09150f06061803010513030e01020102040602152a031510021f060f0e010306050f060d0f020409080318070b040602030d0527030705060603030711100309 75
    0x110340150b45442500b1002c1103500306c4840105655080c20103541c034012507020103003c141c140c0b43c00c5010b0302c400d007010413100355440440d400003425a48191140521210360780d03810410705d54065044124007a0030b0000394585868110025a00d91245841a85003018030000c9a4100c6c0f6aa07040000c150041884640301f07240005001416841640e08010040341030a6030143e90809441c001682d400f140c01500c4a0f009804403400b92866100c1c0c080c140564806011030b89026030507610003e08041c900460341c0e5070441c41d0840c21503401800c0c6c40b6041c49038004120f40c642e2180d070300781c0310b0b503600c040518480c83c4a8400304002d020804801024181c000c03040044000c0b840481c0c101095820049410f501d90341e214100c41c0348110b02907000180c10070441200d40d540c10303410041e0480103030750004038080c002540c111510000080e403064160030000d081c1c010b001003049070f1038100408502551400c1c9080c0d40f40030000141c54015400342c0045401d44c40d540e03019078040c4d600719401c40180010308 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616375656 1250 616374406 616374419
    0x302060c07080d0c0c03120903060501080708010e010b09011e030b0f22020108060118030b0703020304050d0e0d120e15090411070206030103060b0d06092306100b03070315 75
    0x5044501520301540b280b2032502180a12480c0c03881d0381c0031741083d81055440c0c00c43e12020680e40c8103a200106100c3d907040000002052481a14020300e03403600909103403414204041d00307540c1002a00642c581c100705804141c0d640356412581116111905549141582d0340300c0310001180303030300140c0120165010424420400c2680c2840360f4110b4500039005100b03005648c0b1308103000e60b4040d0002d42c240d00061015401215a1000384504210321900700d65681e0b14105151001c480d607100082d000720610080000410040741c0d81040c0381000304d4a00d0b52030000c00c080344a5000040c00500240300103561150250400700000c14020b000442000300000c84400d0607440302814501907840d1a1500b42c0c80280b000c1581c204a90090040f480d691071608d42c600949a146074081d88038241072642c10014135540f081e855114400c100c160075400289072194580d0900c00d1500e10650030204c200004000c55400c8170064891108001e9120745841c2d404400403d2a2400200303201030b2034001140300e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616376906 1250 616375656 616375663
    0x10c1509051e0c120616030506060c071e0e09150a140717090c0a03060c032309010515030a0f0c0b0a0519020a050a030f0c170c010f02131403070302060c 67
    0x42d80c40941300c0410b10703551912610f80d40c000481c2d41514001c43c1481a1030614426007145800c40d00c024a4681001e580c408618242961a03014001e0a034014044004141c1ca00022360001c0041c07801e4003030b5900c0c10940068450505a07410301c03240c0c0c21040000c0c5480c06544c03211401c088105000c070320914181070058201e000b000041c400d1030a4400014504507000603840c000800e01422170b4281e54995a41c100c040c01042807490185625401c034001c916087c8001d8400704444001c2545481c10801251400c40390007034084585141c0d00b103c03801440d18002101d1100b01d900c400901e842c0398190408000c90012a080340302c01d441d0014072014840c0e03000c406403210181a17562101400c0c424601a680e407040103800a04541000420707001090061052030444046403c0518080000b556a101500b074101000b142510001c541c0820011092258608502501004603e081c801e040c40e4100300d4070b0341c8142644c65800c441030305841e07182480004011075000d05a03d4441c0c040c119a01c0c0c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616378156 1250 616376906 616376923
    0xe060108090105070c140a0602122e1806081b0a0905041707081612031404230f12030f09070e0109020c3405010c1509051e 54
    0xa40c0c88000308a1903041881468060f50040d11091486021a61000081000b241040c01d0701d000e580760b00004520180020420400b000c034140e0600e1900c065016852180304440032802c15046c68284660540c4840400a40e04001402d00b0b044140e01107030009040c43d44c02110107409000c0c043d01d685040d0075040d10a001c012250040f160742c5801c0743d80200c400031180501030810b001c8007900020300c400000c00c456401141110324241c958400c0d600740300040e440c129904100d860604443c25490b110700442c03940d0036441244281072540702d0030b020049211844010046030600e816039000108944c5c98402409416149084440c002c1088150822030b1924040410701000801081007c1100c20070345850b000c00c2c1c07419900340400c2000030740014034006030358130070380c22450b1800100c541b00030001201c14800001000c04c841c1d03a601d00300c203654401d605000c0c5152240000840f640446604404480070004403902e1700d0070700518240b94600c8554000d021050b0b80e607007400001c540f510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616379406 1250 616378156 616378159
    0x3101706011401030506031627140103082a030301030b09030a0903060c12061211102a1a0405010f020711060d060e040b01060801151d0a050312030a0f060302090109090201180e06 78
    0x20a03818149040b0050b1078440d01c4c40c0344ad0030b01c3c4500600000e590140501280b0342c0703805105651011039100b04018140c01d07414140d25500c0030004004200d011142140e10030b601c02c01450811207140300140800943d40801032202e5214001e03138100714811507040c808115200400d203d4241e13036030001d45403000d40d203a0640d01c1a4404004003030340c2c203244260400801103070b40e40c1c000c401030801d0700c42c8501000c0d884410002903854244400b240e110100795861000c82901c0c1c035041e04140c90502d084940c05440c5916003401400300f44c1c0482e40550030701c0b1a10700242e40f0107580b018060030000041c41d44e6003140d0000c1003040300340801c0c00301e0f0b014000e042ea0300c6911003241c181d898100e00c0b4000d00d01a00c00000060203640101e28400c984011080007100180207010b0240c1c03110000303410640300322454143d110000c01005405882400b0744005450340c0039040041505540108001c0309050040000880e1140000d40841e40700700d40c0c202d030900442e8020f10b40b01e9101d5800c540c40e01c3c420755503203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616380656 1250 616379406 616379459
    0x18070e120115091b02060112061b080a050604050c090103021308030f0c0c190b1602061602090112020631090911041109010c060b0402031017060114010305060316 71
    0x180781d5080700c1000316954413010b40060015038646140440030280040e0212813080d20340540b84400110f83d003104050401c00d0711031400520300f00b00c00804a90000303041a100702d040ca024031540d0f0301a2822250602c000307190241c1d40c3c1034402c10040e8011550b078801c210622000440740410740c0c4020162480c091480c0542e041829036004008120702002c4c21100b00076100b440800c108940500100325020303134008500b014094a0300003804e41c0d0054102540d100e81710203208002c6241482c042da01404030078104414100090f00807038054007803407a14400c80c05992050205101000300b072008948604c402c6c1184061300c4000501c0a04401c807011184107500101c00c0f069813505000c2d2280ea0b030101d211090a05000f4801128121000c00c402c1e11102c0c0c1d603010911041d11540002c42c0300352900c6001381d02c200e16040e503d00203245100000c890f580c2048006111204580c0c3c581032548034246000f01701500e4450001e8207004000711580c0880000443c00035841d250460069000300345c1846a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616381906 1250 616380656 616380671
    0x221502030721140a0e090a0f14090307080a0c080c030a12021c020d02090603091b030f030901180905041b0603020a120c09050901080304031118070e12011509 69
    0x36001500901c207040818080400d142e140000e03c07000e4404001c0a1410709044815072000c200d96090607611040a96280c0305d0072600c04c0f0641c05103138107518003003038000e809182045007561207001e5041e00400d04000040c0300c090350f40c072540d1190446600912101d9450001c100d81560301c1d0301402c4160b021407000300340d09000c42c503036100340d40e51303600411381103e900c0b002189400000c0d0b00c1044c98004207a8244401e86881c0c031200d01942c071845400d4018240c5101c858a440c4440a84a504901c20b47c0580d0210501503804401c0e2541000d007800e05010040a10044c840f405665401c0704084900d031208100900c0350301051040350720102c10780c103d03045031208021000e030b106282031107001c122880c2d01c2001d059600e9001c684220014034003651400d8440001480072102039021050951012405005000c44080e0b820a00c04d400c9481010741c500040241a41d40b400505544c10302502c0c8400b0200341d100d1001e821445603041008016a60b441c014401041a00340214100b1500e82400b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616383156 1250 616381906 616381943
    0x27040507051f080405011b050403020a080c060d0203060120010c030606080108150907080a1208060405130818210610030c150c060203010f060e10052215020307 70
    0x3551070700c440b68100c080c1c2101c01150503691128007400c00c403a40c0d9610039050021074108040c1c0c01e103140e11942c40a030740d02d10310300401c4090103260708142c529803c4401442240e85e26181228500030860b480540c030b036500c0d000141c0361124190614160841050f0403001c0da61019030180f0403100654a0400c201501c66070106c400310024060040d4a034440300303111020242c0e0300e54565100b0481c000b1210840d0b1a044840d040003e0350100300c9841442d800440d2038030750008000e40c1d1110007660204810300d010031a00e01e400b4000300340640718000000302525100412010091080c0000d01401940c1021108205c0d0400040103086114050701020501c0707031300c04070b000b00c00b200c1d040055803400c0ca0801501c0071402154920308030500415800c003000083c5e1030300240d4001d1014003c640d00061601c04060402c1c1d084c01d9070640b04641114003c14030641080c192441d02e244030060f040ea0f1075450340601d000b612150400f02d2031010202c19502c503035500000070b02c00140726402082c407a110700315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616384406 1250 616383156 616383169
    0x403060f14010513090c1802041503090206041203020a02120709180807030e1f090e090f06160c0503040e0a18050a1209151211070302070b0304022704050705 69
    0x1800d6102e00d0342d0851101342e03c620303004401c190703000b8965620502d40e55200d50f080c0301c45500c12251140c2c0c000c5810440e8000303000d4404c9003012541818000b514050303001410394402c3d801420b00754114050984289482040880d010f10703070140129126418004145070349010b644a840c6034641821440c03550a801000a032070001d03482080507050010301c0c0d80c16184540b00701c0e0b081d50403400c2c16282541c0140740100c8140022040d8485010030303810300502d0350785108020141d8000c0ea00407451144103000000e0010f502480e03040d19926003a5660b00c040f204015051005003c074400404c01080550b0300c5804680180f002d40001c0040007035221340298507044065000e40a030b041486a0701c0829000d100c1244a00c0440c5130400100307860b28162040140718040c9400010850144244044071034821510248000201a420208255070083d039034803040c080d80c00103140100200b000c5484001001422004965030b054207e2180100990041c0d03007194181e4041c070075040006810304144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616385656 1250 616384406 616384409
    0x1407060e010e1c050d03060e010b0f0a0f020c0402040b0d060f080d08090c100c0309090203190b120307050615040b060301061d0307151205010b090d05030c01020403060f1401 76
    0x103840b0740002c00c40781002c11189050030700c040340e02d807101c054030b240c0080d0050190140d030358800d80b00090560b0411007285c81100c0160480180340d841046100700e012558402d90341c0c0c0c40b480d4500303000f0031400310304100e08200701c03000c200d038019001080100f0b00081d000c02500b521009082d00300941940c40301905040351480c480c800c8150801000c2e0501c40b403280c014168440440340c100e505502c03c0401040d000c11600f0750030030000710350501c40010158806a100001d1035a040d0950560030b09101d0b46640c66411650000030b00e6aa181c00c41464031491805070080940030181c03a00c0b200582451500e0700e40454611a62003411483e000c0076140c54465a43c4c0460003410302400c50b0300f0300d032060712072805550b0340081c4103c000d04031180c20340d000c100010107850480200468801044e0300034040380d845c1403100080b00e040400510034184101c0a494410b0401c4500d180150081e0608908503c1408296103065000103408403d03c0340c943c000c0c881c241001c01042200f840e40d06030070440a2400e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616386906 1250 616385656 616385659
    0xb06040f03080c0c3c09011202031c0e0a0f0e0f060409140d0f050c0a020f013e010506091b270906030d0c02040f020d0203041407060e 59
    0x1000305001084084014180c43c420100c1280c5003201800002200f5085681c1c95000c00344800284807104404141100e0922a0072000000c9401d001300016561410500944442e07001c001e040c0c40940da010814251110401c86000107e81007003903000b01401490041e460141034010400100400d003a207585045586805044100341c0b40d400d0b1584481e075020742025401a00c5109900100c0d6210002c038610380200e1f0010710a10031003040103042402e8000d040420710106101c2c0e0100804045055040c1c264111200401007400d0310050f100000710382c81e5480111402000e01550880307015440c0444411550130120080d0a54421030036a031044805640007505440411251000e40d0b65650200147c50203140c05d1402c2201c00003200384240d010312050004070401c0e41d019081000019030800c1056028020380d40704580c01400f45180940000d0040355510a9858861010742c103846ca0507200e490255640d090500f0f003640c00090f100d603c0403c0b03010782000050a580030307108e055a2000f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616388156 1250 616386906 616386929
    0xf070803030708190e1006050f06071401240602070b0f0915041208120105040902030312070c020901180c110a030c02060c030a171b070602130b1c0b0604 67
    0x129240210380c001800f414084051483c04131a201e41096405060036481021000b4514641c040c03080205460544d800b07240203000070f086400c09500c2e40c90407101000e821030110416036480712112070040000d030b4960351081030940c00311119201c4e484040c004584880d42202c220540b6808010540d20130040610310142e0b04010121031810001250307080340c80300b201214242a5590028244524541401ca404070360004403811030300c91a048903409041d0540e01000140b02c25804256240300d09600880d481d0940c40c00038030520b10503ca10a00c45501814070801c65a440382c2c00c0d0201102d040c044d2124508121000c0b10b6584140b810a514241e4070f001000c401216403005c0c0d0b50026580d10503a0040d00c1001004080d4100b00018010b14801d51b4030030505419400d41e000b00c002c000341c009021107004500318640710140d141510141500000010303a07030724125130200c3c459401540407200c840e10100341d4950303042c0c008054090f0103c0324102442201e86400170071005102e0f60103003110080c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616389406 1250 616388156 616388161
    0xc03030f0215070f020726061e01060c0821090c04090b130501090804140a0801050106050a08060319060c02010e01060e01090519020309011a030c240702060c0c01020f07080303 77
    0x44c4600d400c4c02507070340a03005071649140c8a0011000c41c0d000b81078003a404420104421420680400a0700d03030088007111038a0407180750900a61440206108150412178610085000d10480b8402c0350308001d403522a0040c01c1c9880e80000c50103071801c85015401d17005d242d12000782801d00b8020300e0f5101c0e500c412021b809030755912189015900e160800c0d00d09640e02c1c0041c400140c00c60b001000a080344d0b03243d21980820000800036402d034150044071480c0d0602004005903900007054030b49151980c24086001d54511010078604200358070804204460015a00e041c0010341d8001c0c0f810f000035900a201042e282c12020b42a1150f51003450480d8043e8070040000e4201a44041d8200d80d804e40d070300801c500e0040203c026138205480a40c040e9565007510300b0010181c1345e0b0f840750b494043c0c02809500c055003000804070080d500401c0704020240c0c01300d4100384010340882c0c03080c035401010252a0251001a0f559a4801154160140c441c807601c0601c0705c3d10002c1c0c1c520272640080002d6265a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616390656 1250 616389406 616389421
    0x60304020f04050702010f060e010f170c090705192309180703090f08040e011410140f0f03040c1a0a0f091a0307230d05041506030c03030f0215 63
    0x814009004e0411556941c7e04916900f03d00e000c3c0b10018006001c6003507180d41400c600b18900155644100031001d9400d500141c0100c000c070701c040300e00b0307012590074005a0311401e003a01c00c0e02c546c120104802200032460b42d113031500710340c80003109004660164403184000c40b0426880c03085207203842c1d200b20107c42034480c110140120030b84c81142440c0100d00c0c5000c45d80c91201d0140e4085046411200120f0b09220126031141000d00500001062502e0502c410700070981c60925803a10740100301c8050f0f40400709455440803a10007565549a0f82d81d200c0ca0740c200307040c19030410b8408032a80788042c10002070b005094480e1130000c06040801030318040382d0120a03191450f1015a00d424002c182c2070028414214410007441516024081c69aa01d0451300043c801d940860200a036060b02046501c00120300f102039840c2003214110014040e1a242061810405501c00450440d41840008001c00035840005003c99110342c842e01c0e001d03902e000c1c05903201c41714100e045000c001c01c500010050f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616391906 1250 616390656 616390661
    0x10207140d17040f030302010c05030f150109170309040e0c220608070909030816080106030903031b170106050306060d0c030219050c150f0408131205011a060304020f04 74
    0x218800c001c90a21400d080d4181241e0f6080366102407100e40b400c0004006140c0c0a00911b42400c41510b071071459403800e006241c520f600701074100f540e5007004140d40d414503405490754201404404440d02403c041502a950b6603a0003240c050380901d08145291204140000b0780410b9400c000f00f510010030342c0080c00d4020b00131043c0711003034066290400024000001d1006601030092100c0c00b0540308903a003409460404c02410b82064501c042a05080040e808140306056880398900801e030202241003c0300504009404001320402c0c0b0f0952500007074100b1301e01d00e4178003013070748000303009aa0f40c400c240c880c7e020880c1c44d50341200c0c0402000c1200c00d1694400710741200c00c2c0c1401410310401c0820003c80040c078140440100b900040c00d40c11040c0100450044084074201e60251485e0051401050303800182004081ca82c0104140c8500405106290040c103804103008030428040c3c205035010702040d0383c40c1c0211b54481d120b41c075094202082203a102e01d4011b013040600c0034100040c00300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616393156 1250 616391906 616391929
    0x33080303070521190501080c0a090b13060b0705061e0402041e0f0b0301050615090d0303180302010609050c03011d07090b040e0a0b01030e07150507020a0902031501020714 75
    0x828502008030f1045a91865910500030180f00b20700782248490a9204022500183c00410441e88884800031496035100745403c01d45038001804a50303031a000c000310f00d10307402c120748c10288207003800d1011511203401d0005c2c20244d809081110041d48522401c2e16442c8034042100303181104501c0000c0142c140794000c6038100161040c100d90f0302035407003c44002c5608070000200060b4039000c15032014682401307800e4111000700c80c0c0c41c04207240c40408040c1842180340d0180608400305c280014580a40c1c0040701b4a0140c0d0491403c41c80d452800900a010a000380d0007070625201c0840d4000113103105480c16a50418818012901c0c030150742c244c5200b006082c0340c01c2040e1110003003090601c0a01400050807101d030031054074180100001e041c0c4010002040c10549001e950b179580e03c80025007901110060f090300802054a03900440ba24170034103002a42180007080001602401940150b100b1081c0ca15010055040c540049131584024802d83c5804801100c2466507450940b40081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616394406 1250 616393156 616393177
    0x30d050a0213030f0f140d0207090b01021b0409300905060a03020c070801020d09210905060705010f02030412110619020a0306150201020406020d110a0b040f06330803030705 76
    0x10508072490b601c449840c0d031005000c04041d00100c0d030081f41c0b40d0b01000a21b001e0300b0f140030140030080710217000130341d900d032100d00310520302448094540c41c580304e0f9408441d500e500280c0a400c0c4050325944440710205401030001d048079032a031500e4805100d00140c105441c0000c118902c0c0601c3d0000481c00382d0054058000c1e64012000b0000344d89031709200030000d580f0604004944661942898840030442e03000d0184d2450700e03da0340440069102003184182d400c105c0c0c40c540c85e0f0402c0c0c00c160b401084000340b650603c0e403001051105102040c0b482c06c070051007a5454224558020340742c0e980724103041c0d071f007000c10900e00c400303807039a0f1041600030b0314004c40036290000c2e4096581c640059446c1d0302032038070300240c3d5000505100c050303030520040c00400d000c2d0034001e0f2440c540d0308000d5900c48590a010303203052034203001300d02044001c928814a00f80c0080c02442003460116000000c41d0010040e6001c0161040c0040d1004108041030000c955200001e5401d5503901c401c2618190721684004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616395656 1250 616394406 616394423
    0x20010c1206060e0f18250e030c04110403060218040f0c020a03030b04140c0307140f04050d020d142a06040509041a040305030105040b1507030c15020c030d050a0213030f 74
    0xa0308249500c6460601c210302c4400e03110001d0303004914040c1b800600d03200c45020000f900801d80142c0d20005840d070551142564000740e0346280341c0594080d80901c0e00020b1034140002004510f41c811005480410340d8200c41c04c100101d118007003070f021034113000010b1001d80c0014440d0000719001e83d012046e2a10040d1011034102d00c034504021b2140c404a8034400300040200a0150300c0d544020710704c804146040f0b00e940b814000701622441800f13184150351141e10803000b468119211038454429095102074400e0844088104450311403548039031103c0d141a00201000d92250b49000c0701e604080301a0215103468280028040b440000400c280e4014004440054103220b035607041510481c041e5845548a504000c104400c2e191a0918580b007102003041413840c111031102240e08680c0e15040c944021445031500c0046c1c9a80c040c0c05c0e424040c40415400f00c1403030044024011540498001c0103240e0340d044900c4100d0050a102c0110407601080500c0090800d0000300d00075409003294 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616396906 1250 616395656 616395679
    0xc030e0f0f130e060a14040b09010609060b1b070605120c0c0d0504030c0f0f0b1b0f01091703090307140f0601150f0804080906070320010c1206060e0f 66
    0xc07410500d203190082c21060f0342e0350902c03c0021801e121041d0009503401c1d0a10001d4400901071010300780c003920103018100d901010410480007580141c00a00d070b20b80f0140403d560354180c0302e0f40c64201c1d03903c420007901c007d05483c0340389a011a10009850850700c0e0341d810310758090000445130b0b000910360b511819040100c0800c006040100da40c00d40740307507516a45d8403419450500002412544401c40b121481a02401a109180741c03000a07a4005071403640c03100f0b9081807211600402024883c041e004d01c54000c3c42c195419000500220b0081c40502d002c801c1d0190842d51622080342c11560701e401c1031140800065095507581c0c000e4200804540342c00c4030035402c69041034402e074031402c443c034001c066040c2c620303800c001211240c8880c0d0501c03102a1520740c94407450f61040328401c03072281000242034420580510607a03181c030205c0028440c090b00b0160280c034001c02c0801c51010215030942034502d4a44194028042038030581e036608581030465400344040c0c86442c1645961103c41c1401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616398156 1250 616396906 616396909
    0x80906060a061b0b2a0f030c0c0c0d061505220905070f1203030501050d11150c0a11041508150c090909070513020703091205011d0115060c030e0f0f 65
    0x1041c017842d00d052400a03c0541d0419243c403240d0500c0711041034400038001c0110429186040d20b0340600311041c00c03030b680c140c062001806d04240f481810340c010159481241848003a9014400e0150184802c0c02040d440710f04000f0034005120324003e5540c044500c1c80072a206c0c980080d62001d201e001203444054541e031520540c8085500401000d103d1010b07a2410715605004050040405031007403600c50b40c07662a05040401949107007030262039450fa11460303042c054400c45a10841c92801c0c0e901000c064076060341c02034800901c45204034108480d50300c920b40b0f01c2e003c100450f54940003c1003109244001103000c11801401c111000c0c1047c0031b828a203448a8150320310400c50302010300b160350300b070001b04106c6030440100d00b20306920500070240081d4101e0b04102c02c3d80c02d038042510050b040c40c901603000d0000200d13440c0220140190341e1004080c15000403201a8000c12000a00350711903500301c0d01d00005c5000074000072010038104147d410014a0001584809802941242d90010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616399406 1250 616398156 616398173
    0x8040b0d06170c03010b100e0f060c1015060e0102062e1206060902160816050109050a030e01030c050901120609050727081c02030d0c0906080906060a061b 68
    0x12042469045240403d0b211314081c41494060030303003192500d0015521030401002043d4451440b0b0140c1808080004a81e61700029035000202d00702c00c50b01001c400126010142c0000c8100d003044900000e80440d140d8054014218118010381c028200d5a440d80d0400284036485c050945081142145610f0f00c80e1100c0c0c41c0e4000351144000126030300100b40342003801c90300b42e9404990700314418003525000079580450450950f82010003291500c07080d8a0410141c6c0411038000c2c015840c028054041100c00300c0c0c1101c406000ba00c0715250307003d8610042d03050b0340400001300300040042240c40c0300c0c0d40c0625000304c600c45080c1400203501c8e445481510440c0d009445410100301017a606000402400e160b082c41d13115106040c03029075103000d00c0160350311058a001c1382c40c0046060300c4c24009208100b62609651745050502815011500143c07103a6028040c11000402d0040041c135643c0001504500484010745880302c440d16040048420600f240d001254100c00090060302090310034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616400656 1250 616399406 616399439
    0xb092e06050d120e030115091a040501080607120216200d030e0a05040207020a060e060c010510051c1205030a02040b040b18011803030c06020d020c010518010908040b0d06 75
    0x3041600000c40300d05101a0440310501c000394130a071f0404c041e65400c0e00c042d03a4070504581d0b0343d210210340c4003500410410807148030220641c10501c1c2a0000401c10310010307034140260702e59220220300c803001a0783e22041e031283c00100703010f20950682c080001054513005240c91180001001c400194210000711214040351080d40050307009890f8240b5032400f0700c807410042204076400c61501e01141d01040165101d8401c00c0240b281920045c2119100c20b03080f511117501c41c0b0300811891078498540c503180074560180c103000b00c132210b00070310014090041c038407101500100403014101c11010102c0c1d40d60710007006c41128940910001803071365030010140000d00303507050510351100d44070040c1805009030b41400c2d83c100807540f0305c0c00c00c40100075404801560f406103400d642e5159103044ca600680314400f000d1828601c009041c105500341940710a0190100c2c50b0030481c0c4085080c141e90a0b5408a00c015204030800c000400505e00440000c1200d40030508010919070707621100c1000b05d001e00b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616401906 1250 616400656 616400663
    0xf0213050106020c061606020904111b010c080609040b0403200c270c0c07030b2806181d06180d02030a0e04020703020c100306030b092e06050d 63
    0xc0e400180040c5406005200e94120140c03262820080d60f4154009031416088002c0d044690000c0c20144a4450f6080003650314a0400c41e07599800519007007260500358044265031310352030b08040c00d014901c281c1e0003a014a0b8014040c00494076079031500030203640080d104400b0700010078020902010000d20119440300c111010340556820038050103102c004810441003151041c50a50301d00c00503c0c00204e4204609160300d035200c0e12114886444d04203184c01c06026201c0d08001c1010a495450751103118403a00c0d24203507daa0500a442c00590381503000340141080b503444490020486a0701040b0b0b040b5120b803248001400d410030344c600300030301500c0581d1401103210050282100400c0981c2c8ad01c0750b9480210f142c1004020010700210700b186040303100c0e580014505d01450b00c20003412019220081007810350f4410080058001e040078801100c64185100000b081c1000c0811031700c1030301c50303401c02201c040c0010072081d41d41b801c450705150441c1a510000402d05440b580a41d40c001c511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616403156 1250 616401906 616401911
    0x703140115140306070f02150a0c1e080a090611030f07200d0f0302190f020f1b0603040807060f0209010921021003060e1312020604030503040f0f0213 66
    0x40550070519a425541c008003641c0e82450100d50300b64038001055a4811502d00d4a4120500d984104a051906800e00b03d08403107444814400c0d038030102c3c0d1000e20b90300016202d090103100c0ca200710f03003080e100049609022840a00003d81d01c8510b03508641b0b412441800c0000c0e02113120040003210707400036544494504028400c004000b80c21003003200f0200c0001c260390110b00c40c030a0307080c0e545041480c8a80108980d50b0f6114034041d01030f40680b01b01b540c4501c58a00380f0200300350003d00420314260b50100503c550100b03074482d800c0c0410448600401100076080c1c144c8c0b08400e004450340003820031900c0700c2c1c0070000d0f03102003041403040078803005a90300d015a036121100001403010480d5009075054003514100a800b8482d200b040800c0c4560644001820034803496058000b8082e550200c18142c1080d020428020b4100070180240b0b481090100103944080208a917220002c0380c004010070820404200415901100c49603e2841220316104240c400e5021a41d02d81c0032041c40b160301c40c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616404406 1250 616403156 616403171
    0x1050708060d0f0609030509030a031d0103020c070e040507050a0f0603050f060303160c150207080708191b0b18100f0e01050d060f080a060b060301050a030206030907031401 76
    0x164045035840c1c00c00d50844889010705095101d520440300d40e002d00030300d500d03611022482018080c4059859425008083c1c03840000d280c100a00300c40d01503c3c140c803441038000c20042080d03000e0b20996070280ba0304002003070f0305401d007032a06900b440054001d40c2e0343c1c4070300e8100007030035034440d0f0320080980000c62400c07860301d25045e03000e01683d20140c0b00c2520150000d0030481e09490000990b580003aa45044c112820701e60300b001c140151460704104100c07044814420840c8d5000035482c022500725608480c0483e030703100b0701e2546501300d0a00b0120314a44686421022440b020700204803100103038102840159114000065540319510300e1403180084189000285400844241c191180e82491a11544050401005102a8080241481070100d4130142d80c0d80d0940c80b80c0c010b0b050310000d0144031382e140c000e29640c0b401006401c41741d403402d0500601042c24418103a0b41291009840c100c8000d05583c00c000140d000141160710b240b103030401c00408921408542c95003851410000034225 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616405656 1250 616404406 616404421
    0x8070905060d080304030c030311030703140c040e040b07090806100503010c090612090507051806030706020a021807020f070312020d1803020909030f0c07060807020d021e030706020403050105 84
    0x98a008201c0ca1007020940899408510340d04200e0f98000d61524000c0c4400c90149015001400c440c06c10149911000c41000302e00c0d031301948207010800c2440c094a21569650b10007005d580b1450003039400032501035002c030340040d10009000750003000c50300700680c2481d210181103140410446801d0090110744004100605080c840c40241801503c0d140c207000f400c140000e42185184030040701c1c0c0a90b6424407000780041408110042c25009268903001105031100300c0c0e0010003079502030720900640c000001c10b00d000059101000d41c0c041d0a00088415400e0719840980300103100d201035000b6031301c3d4040000000d00211010310312070000e40400c185600303402840c00a0300c88400c0b091184604d6031030a003042c40354811007125070480d2280d28584c7c4840141d8114001e805a881003103901044100141402190300000d0b070341160703552070300ca96a00500b280c6d00d0449800c0400540c10003801c425100e0401403140ba403440e1400c00f05d030b00d42504c1d0303a00e0004a81c001c0d401a182655a10140040c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616406906 1250 616405656 616405661
    0x181d130605090a0c060f1d0f04050a140117120304021f0809010606030204060203030a022d0c15011401120b030a0b0f010f051e010e0a030809040e011a010315050a080709 74
    0x68072151820781c1c15a441036030301030647c80a0400200a40710480401c0c002d9543c0c118500200c0c000c0a4018041802c0061340d07840a001c03005203900c0d002000b0400410052441d5854024190510303005080040e043c1c44c0840300381d0b0021304181d070801410868803040c207243c15090305103842e1075680c0540519110603007c1c2120758980022040500400c820031035140c0c000180c07a000381000100580c4d0701c03141407c990800d416443c40040e4060861200c9803550b10b4070002e04020140c000a0325202d600007210294103190074001d022082e035111502c0340165114002120b8240c40d00940002e01c00b6281001910740080444121008001c0408200e250000f1800e400e004010b940440003680d41000c0c001051405130304121043c501e13030f4600801442e841040c03540030708080902490b04170b6440741440740d15a070041c00180e009908041c254480e0700c034148100034030100b01c802466050120b20b00110003510303119030074100b480c0302c0f502d0101c2d00f59900d02e29000100101002005010f140c0b071354500a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616408156 1250 616406906 616406909
    0x403030c020303160503060607060e0604140a0210050c210d06050306040503070b07050904050c040302030d02070f1809021305010303200a1103010f0903020d181d130605090a0c 77
    0x4641040c0700780801000b0b020304000070f0f0700304ca041164a80d44c8070000705110740181d0601030003ca00342104195100b10119596019500902203504c811401119403592128803041c0250030415840240c060107200300e020f008000380d44802e40346a94010705000030200280c040c4c66090340c40008808013500c1c40c511681c8000c04040e005003035540307080e8580c42e0316405840e0018264285070800a07008a20510846001c0b81c40248100000c0c00c0c0b10340d0849003074000e40402c0b406032044800c0b40f061103000107011000c94002043c00d040c0c3d54201100682801180c80a1480c0980c40702c0c0c1200040e5540111000e80ca1483c0e2000910341d851820000c0401900c540d00c03e00c80f124480f1b0185460601003205850300d900100200c058281c0b0201203801010420911401d4910f400360303110415a003c5411210b07164507581d4040343c40040900c580d01da410302e214140e248914000006829034018a50583c00b1440541000107410307991218000d6039030032101249180c10503a03051007000401c203a07000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616409406 1250 616408156 616408181
    0x504050718060510050a090324060b0c1c030e01050f0417030103080702191e18060506180301021b0a02010813021818030d0203190209060703080c13060503040303 71
    0x319081ca010f0109001880e051500001c2000021360b0404c03040c042e0880100555016140e400d04100203444070141c0074004035800a4a0304141c0f0000b11114180b080d0b6207450035440182c60040b04084181c40d2a034481c100b07003018141c0b9003002104001d800e04c50745104102c0d031040c0c154075240903c1d050511400d03070040001e42c24030500051011600000680f00006d0341540c10032500c1058200d43d0881110340c0e8000c9042d0480880c051402140003003c40c8110780720480040000060f00604a059500d42d0182c503420607002c5c444100403c1141800c8600c90b20040c00041c80c2c0700c65106030000d04640080004520790108a0030011541e1180c00240c0c8120000c04092040400d40e0004203001c001d03120381e0007054040300200e520805030001000d541d211a0044940d520040102c5501030b40080328064161081c0061039000c0605074000c40344090f200038401484d00d20241d500b556402000f4200b01d21044040c080c5104500340c0109040191185032176598a9241030302e0f00a06444021007002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616410656 1250 616409406 616409411
    0xf0806210f0d080903070b060409171224240408150c120f3103020f03090303040e150a0b0301050f0409020306060111010b03060115110d12050c07060504050718 70
    0x80002e441c0030041c0c1b401d4a034010200c200c1915000001409458405806042c40f8050340104000402290060104050801214400343d0350001e0140603810140c0008540820702220300c800751800b001002504003520529a0310610750203210310160704681c00c03030f15103540f00344528440000300c060559844100d85652614042c0ca4880e03000301c0d0382024041c03c5509452001140c98581681090010318052504120380d004030407560a4809050070401c1d0054006c010100b260020084100d4641060141c019468a440c001200d850824010610000200c00c11402c8803503664540c0c1b40c1c40100354042045403254181420850050b8461419501c220703d850501c40040e2804281c550b03201c40b090a010020182d1b250344c55015194151065506000c0e140000c02c800d12403042038400184540c1d608650640301d00115551034400b107039900301045c180d0b040f0180407140c640000354498a600111424015240c0d00c0310165107094400300c1740c581080100740700d81412100c0007001300010f000305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616411906 1250 616410656 616410661
    0x2240609090106080a02012105040c050f0a031109220305120a2a0e0d0b070e030d02030421050604060507020124030807061103010305060a0b040b010f0806210f0d08 72
    0x4030740e5060b204000a062103410440c2940244140d00100503400f2341d0a800c2c0a249000d2800c01468003a5004051080524000e1240c1505241c0c100da029280c1c44441084c48030003823010070a868100401180b00c184081d8500511440f64801041525209858554842c0309440c10403859440060001d81041d20b0807109005640001001e1180000c0b114480c0001c907d01c03182c2155081d00f101c9809810100100007101000000d290691068209541d004419400e1008064407006102ca003000164010700007400128035021800b00342ca0b07807031445102074000d0b654440d4188281120b0954049036600100003005d902801030380d05050581001c070b10000c6002607a00c0656200c2d02001d4116680403a07010100640b5511114038148000c00954480d80d403460070f036664030780071155144c80c04d003808075042c3e82d41410f004118a24505844080400801900480340084014951a8800f215a1160790320740340c690852100040450050400301d03802155407454410544440c00030025400d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616413156 1250 616411906 616411919
    0x3030c03120115081f0801060311090601090b030a1104150302031e10031401060902070c0f120807061a040c0e0f060c060705160b100608061509060a02240609090106 72
    0x104c158405490003d9035140302040213940e1259a16400c0701c100e56280c0500481031103008000c59407040b034100d900700d516559540044403250181e105052480d801440440d04c92500398100050700040a010305051a64a4001000c500c54421800e000311b6800000d02480c000d00401803842d0501d020060310407803d000070130040750f04152002600d850303484044249510400c1d007050000304580d59055440385014180a82030101501c030741100d207408103100141204e2032143c0104500c0d00b15206609050040d140d0b04094020741d4240010b082c2c2c2c402170f0b503805a8541c23282e14200b50556880380e00b6802c40c031052000803808000c159110740f0040c000d003400c0003030010321940e00c99103e15109444102007100d0014803a0b0303600b0010050541102000380d40c03e44801030070300310f503038035a28404251220360a100c0794458168250000440070840d0100a081c5100100044c0940b481100c202d8001e40207180c480e900c425201100000c0e6180611481d8501316040070b80258904000f004128600340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616414406 1250 616413156 616413167
    0x4021f0816021603080301060f080105011205070c0611040503010f02030c0301120201020f0703151d0d0f090f0b091002030a02150a140a0c0f05040b160f0203030c03120115 75
    0x1414000c00d0781640018003800c038428009446404030300c000311503003d6124074042d031040e0024041c800000e1140c2100c030301070391701c41c0e030b910b0f0704891041c1c4a4070303003d002004494015040041031042841104068200000c82a100342944000713031490080d20f0340c1c20601003500f525103440e1101c1c4a54014018842c000c200503003143e0445501c84a40080d00d415480103038180000e000c2d90308040d000c2d03003030000144004002c992104100107a400c0201d05410703407113038000f49100c8543c0610b1340e21182c1c1810311540106038010890b045401d0210303425968400d85152100f0704d0700700400c9454007190306d0003035080520700201c0e5034010707001540c205807030103000030340c1c0f202e4020460075421b0262012400d049a01e511403c01800980745841c0149031000c5000042c010400c000170001c1c00e50650800c1e0785d0320420545042c3c0e24020341c82031400c0e042c0c1c40200402068904181d49140c020880d000041e80c1c00c2000303006007a0650045c2d0f8a50284c08905d103805e240c142e021003440074060002c1c900d0a075100703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616415656 1250 616414406 616414411
    0x709060501232d0d0506060412140304090c031a0105070209042004050702011d06070e01050702041113090f1122030203060903122511030708040e04021f08 68
    0x2d498a038403022a41000510b41ca0b119100c04020100005100b103941d060000420a80142c140140aa07484800c14010f40f03204506c56401500d0b1040c4000000440c0c400781d01c07258281d844110b80c01c0a8841c041c440031500d1403070401020aa40d04801044030440c3d1000040002003420818103000040d0085440303038000420051008090850309540c40002000f1560b0540e0090303c100031600d4818030203402002114102000c44016030328180301c10030000344aa11603002a80d82054801c8894015107181d00040c0c8200d90150300c609003100c0e0514420060300109160383c08550460785000e840380e08441e441d040d4418040d0521f40650b01459001c02154504070b9100b40840d85584d140aa1b004074100c41d400080d0b050256000340075001720000003034015150380707001c00e2074242c507503d0013610a5a01c0a188d03031540460096103a00d030384d0081d260f001c01600c440096a04e0700039039540340c41043d0300c980c0104003040d132404140300540c1080440600039420f8800d01c11540c0800c850701400b6a60300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616416906 1250 616415656 616415717
    0x40e100c1124070207031a0117010c05092101020c030a0801240f180f2111091018090c090b0310050915090318010206070516031e020709060501 63
    0x2c072400b1034482d0748200b0407500119001406000d0b00742d054090309081d61800c0c030454508800200d80da03808000d06108a16020780309480f114030380028107040c00000c1d601c08800d0b2000301c402d201801c010200038001000e0b211081e4000c0d6603a541c8a0341c0160200e4010f8100d9400040c0c000a05001c2c040301c030621000c100780d24100480316a8051408407440300402e100c0c0094814107400014580040340190001e41e5025007a105c82c00349091640200347c078208801924800030180500c45a06000c02c8803500018546881220640c03145e02800b944181c00c480300c030801c0d80e51343c2c80d0001e000c0c1d0300000501400c01680c0a001248010300000c1e669609090a0000710341e9071801302d40e20100401c440c520203000c03082c0e00560f516142c40b00d1500c1e40c000b41c40c07505240e05814031108a075071001c07450700c0c480c207090f8a401d402d01d084a11115003804520301c0840038040e103844400c1c69401302c64030143c3c10041542c01403585d0380c00c2800800955075980d0110703050142502c04c2903040c146030700781640001034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616418156 1250 616416906 616416973
    0x1703070b0118090609060903020d0311040308030c0f0a0207030c0e0405030a11030c0703030824030a120909141e01050d02010c050c0a03140105130201080a0b040e100c11 74
    0x244162090002e1881120091140b4a842110f10820031b6a030000c40005000f502a5101444104420350035580414800401003800f00418000940310318055500310150070449820000c0c03c1860101030b91000000d1009a03209502c100208400c01403404064002d100000013581040d560725550ba01a0499030000e000013440785c9600c1c07180800986402102c4042140c500503581d00300644a1401034800e40c90542c1c0b8041c20403102804980e9600109001030000d01c0d007440c20742c0741c0034005807228015008119041100080c510b0150184440000054402d24042d08208420b038461040300824032490308400c200411103a500d80c85108080c40c0c080c01c20301c80c0e0a120b458030301d00306880f01000c568000c00b186000710501a44c0701c561210800c00200811654076600004034002d41c00000080c002040140003c03080c58942d0000d1000360342c06400821642c0048100c00c2c1050030300301c4a030750165994000000c100750702c2240a0b0321085400040c02c0b400ca540e0500b111031000c8184130040024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616419406 1250 616418156 616418189
    0x120b010b13090537050a02072a091104090c11120d1e020a2006180f060a0c09050406050f0103021b01022701020d0804022b0b011703070b01 61
    0x1801000000310b0303018960404c0058400100140e40300b104101040441245440002404484284215001d40703801001c0d00d0390401c4e00142d03d180b102141030f0386404c004031030500007030b03600a40c0c012022440b1980703860617252800c0c181820f00f01c544814600301001054200c0940b40740001c42c241c1e50768a070a40b4116036800c251030041016045030040c0454804904031031210700f1840340d001e0f1260684503602c4600070000c4520702076110300006030b003041580082000c543c504407a200300001003c14a8195001c0c024400e10321418080c0486207010b0454544108000c51640001c881c000740400b01c0302042903504001c0400c181d604404509814141e000910110180000c4811280e10711510700955864074001070100304425240d140c400d106501c003040c60b03504e42c00418907052501c00740d580d01031156a55020040030007025a203111b81a040e210b05220750710b41405611000c580102c80d02031113540341048001c1100c0812001802a40050115034001000741c0150342c112006100d00360541e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616420656 1250 616419406 616419421
    0x6070b061c020307090603051e03030f1503030c0730080a020316051c03180f24021216021906060e0703051803040f06050d0b0901120b010b130905 64
    0x2801940c000ba51520594034006502c2c8020b0300703e40292441a01507502c04569506019102c0c030a0752000324640c0c00a00000f0003d0003810001a8802001d1980740d900d8031101010a08690143c0311801c0e140c0c1126209206080d510343c03124554514114004040d4480c4142d8842d0400c90355900a02540000580310a42c03817080081c2c686048190441c403036944858500966115000500d0f82002c49900d5850314000f400703881011100b0071041d030a01d880c51031642e112602c07080940c00444101c000c281840c07040400d80303803140000c10b01342c250050348e88440d5200041400d030b00611032340d0a214070b100d04400380b1b940840e203115040031001844100082900e0f041000e42580d0300615002c9030b10300c2c04c004615515400c024001c8400744041d00800000da0040c0c1e889101d030b8012101c003e40407031010080c09128400901c040c030301240c4001090001d179400115201c4080e48048055400c00075a001446540b200700e50040800d5000f00c0e1401d40011400c221600c0248a00003059981d0300009040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616421906 1250 616420656 616420699
    0x30318060606020303010812120c07020a0902040b0702010201060b07030e061b060708041a06090711010e030705010213060302040e16020a050604050609011a3d020d0e06070b06 77
    0x10aa84440280103075902d408000f5603a40003407007907200600c00c1040c0c1400d049030000c1150b03410481d1b118204800d98072050644095400180c040307800c80541000066007800c1c5c3c0c409071010300079501280ea620b203000e0000900b074581c590800008030008002640001c0e822405064800f00155907890321107100b0510308104800d504641e040600558003089841035008184500c52440340c041c43c0e042c071652114464130814100c802c10f070046024130200b4080c0303000d00da8000301c8048900000c15a08203200c122400c0da04016000c442a03034010885100c55400c5104500c06031070545400c504180c940340e03451031600c1000d4003120340c2e01d4220002c0020903100707005046040303410070102c46060916190066443c0c204603034464141d440c081e11009400744202281d078110a0080c00c9402012140613200d50694949079802801c1c0203804e10809a101c0310b9840304103038201038001c0c05841c615000041d014180c01c0302e88600c214410040c160018034603d00e51a008041070381c5441049c0c0c098a4003811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616423156 1250 616421906 616421951
    0x10090507050c0307120809030901020d20070f05101d0402090a0302030d080103020f0103090807121106040f0b10050102190611040801050108070503011401090506060d021c2004030303 80
    0x28074000003800e003041c403031040e00d80045d1070901e941c0c41031a5911001810303100d0080c0e020303041c0142c200240950795140320300c01c0322580c601040c0710001c0c801c2c20484043e2030002281d00029901491500c200000d2400c010094a4254107081c009c0003c1c8001000c420085107806c20310344103603800300c0e41e45800d484040c0360001466010702140c24011040764058040c0070240b00403841000c4201140585500c03c0c0510180036038804451401e04220355140e05e5a00720320200c3d2410060003104140c03465004100003402a401088004070001590030700d040c3e12403004002d119011103903401003201e81d0b40000d85201349003030055111034a400310300e8060007600c0002050007013000081001319101c581948418100d800a40403603ca003a0f031507046c0350a8a0800c03450280340c0001400410080070715410a603801400142482e10704135686024000f240c008071451449140d44007405558806641728003050507818451080d58036122009503805403107540401000c06444a55945821450603d50304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616424406 1250 616423156 616423177
    0x105180a1104080c040c0f170c0f0406080a0c020705150c0c0901060905090604051e04050c09040b0411010903080f0c030c030a020102030f0a0216060b0607020310061d1009050705 78
    0x70b5446598183d00d566406000340d019100d2885c1076a0001818019403d24400140ca6100e8003200303102c05201287d2510020300c041100f00f81046030304507000d0700000030000303030465884001203403c2c01c101030801c4603500607109040d50f0140d802400b2781c0c0c2e0390308100750307034003c941c0a9141c1d03600c109031219007001e0126024036088840440080b0b00750760090065030607580240c88100e00c41d5914420001598016155604050020007a040c01c0c40d9500803400d902038021011904c0d103000450204e03c03c108100c405036828089070041c0400c010703a0a0b04048003131000d2900500d0705003503490300d012500c40c074440031026680c00550b8418400302482a107450754581025252150803a010180c080d41c002c59801301010345901c0024524800d038400c0d24683d16804131b41d60b114204c55583d08d801013071204d465907406041071020707500581e003c1040d00c0c0c48030301c40003000c24400e19020700000c880c1c11041002d00712440b2403003009040d8100981d00030480d1820900401c1c1ca032100c01e01611035204015800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616425656 1250 616424406 616424441
    0x11401050d1406180c070807080c0a03031d011a090604060e010e1b3a0f0b030709290a170c130608030a0c080412050f0d0203030105180a 60
    0x80c0c0480010481511900f01590301d050880b1452082c4e4035414401c030707844045101d0074417120b404070340780c240034020130740c07240c0c0303500c0d2400340b021682501c1d02101e104100d0010703071203010600c03403070b00e0005401600420050007442840198114102259841c1074010700032414000018840d580b55007006006140700083c020480d41c68550211200404403198110a9100084548080e40741d178201c5100211122003400318400740d010900c01407152002e000c000049410b1403a07840d08640c480c403031400d1240c3c0b030300049070125a03051600306a000d901180c48146041d41e00c501c07108182e51495004100000160440728415000410251054006104080224032404402c0e01e0000300803030b03010002c8501400c80b40d0001082025110f1502518080360414090160181e01030712040220300e00c1815041c2c1410b460307000c018051506610291a640c0c01948890642038081c0040e014183c524030103186075606241c08140306588015444034100000703800501c4c0c0314441e0784000401550040c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616426906 1250 616425656 616425671
    0x130f0f0504050c030610030f1a0c0c150c0d02070606171b0d020105070809010c0503180112051003081c05010303030902033009030307082b06060503011401050d 70
    0x8890040c00100c6084070a4481d610700003100b481e0004401c1e1082c00384000d10811182155182c0510219042c3c040325407284800c80d0007468062100391034482c02070001c100d80c84665a8001c646000c0c42c40a04c04c01c2540d00c0e4003400b2288000308201d410101210502503034401032072030054000c0225500c4050303094120300740c821880c3d60200e07020510048940c6d0191544650104000c0400c03150f4030000d0105004004c554001868900030303125161050411500c001c03240d40b5102c0c203561015415940c0140304d0b0002801c5507811181c010403a40300c06c20100081d01c1c1029904100d0885408060542080450303001e82c5c0d901e51400b0180c00300000102031100d544c2d60300c0d000c0c3c054a00794008a129005d03401c1c1507140c55503101707004042c0c803810890900b02c120101c100038035140c4c059010075816000802c64040400c041c0c40051120007500c001801004000c440c107603081103400074079511282e04185007044034035032220035241514181e011070f0278a07580000044e141e40c03180c4040c1c106002e0a0185 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616428156 1250 616426906 616426931
    0xc08030307051c0227041d010c03060f03051002160c1203090504020a08010509070522091515050f091206070f020f1b01020304171c0905030c130f 64
    0x241100648050b0400c5290b0f8a000c0144164010707001d0107014070300810404081320300036506042d008034000d03000142e00b820b109070900c2107000c0c0310701d0b040c100c3c1c0d1100600c03104c0590503c0369000401402520b1044039055076121501c1d41030300d5980030b03481c64012400300060156000c04140d001e038809004080d495680107188070400b01204250301088840300c001445040038001c0b28910308142c2c1e9100e60580c203107000c214410300050402010044140551441c110b42c0303034808003440c200c5c01c50301070b0040d00d01100a070649240c40c00145800c5110ba0003041207484214402881000070b0403c552a10300500b211002c81c050000e400e540081c00c090413a088000209003135001d8100755a0b8000c144954110a82c2c2d504900300c0d010345035910000000800ca480880030340e4001d801403050700d00e01030740c6250f41d8018140c81d06806d00f49400980600220030588004115450340c241400e0500390f2130100080c1c3c44a0218802501840c802c00c04003c0313aa003581e02505900b0369610007041000326100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616429406 1250 616428156 616428167
    0xf0c0a0306021b070315181113022106040e1c0f0c0c030f060b01140d0506031009030206070801050301140105040203090f100b010801080a05071a07050d08040b0a0605010504050d0c08030307 83
    0x51b41d5100d030307441e1050b0990b01c1c60303059101d00201c3d40c001c030720341100b0404101407111141401d20990382c41c2e5070034050403018410710320118080844840c072102850030160304000071941d131002c103140250b100442040030800300c9001a2180308141c01e008400c40c0007108207980040180d0300042c60683c90500100410005455040303c240c020101040a072090200568007003c1502360000e00700c006100e40010841c2941100d43d02c40742c0075082da001d042c0d4243d4954255007005804601582000003001070642c0c1c4900d0017801018120000d1280300180718120040c5a010700489000f1900080066140b142c10070101c1c90045981c0203c421081d0841c4007900201000c04185000071510400001d49500004a651800350404081e10083d8070300000080708260041e000d40c00c031a8144540d101083c0184000d143d209c09903140c0c6c0440340390510300b000b912072000349141e0b003581c82c1c11005d0140b6644407040d10700350350741902d0700168000e0306e003029071018101d54840281e40c170002042000d00c1e503004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616430656 1250 616429406 616429433
    0x3020910031509020f0f060d02070b0f07031a091f03060f0b061c0504030903120c0b06060705060705160b180c03031602010507110409050a050f0c0a0306021b0703 71
    0x401d40a02c44152001211058543c85440030b540540c07074041d031080510f005030032400c0c00c401c0209980e291000c1c90b400c0106907049410160391940b008820490700300c040c0722007203620a405180401054040240da074505408007505607018008282c009182100981c03841c500d820f100c008510b1a0b6079032807a20f10060641160806a50760078100f01c2241030a000d402d860f102c00c0b100b0801d0048008000c020402014010015400c0200c40803000000c030750211200049100e240d80e030082c654200d03040150f41d9260240c0168010182041450044ac1010440c00d40095031850441e82e643d0903145103c400c0650b011020700b0040034901442420654200860082481c2e0000c5c0c038080d00040c410103440e8010700e1402c5208121218865005620410003009014402c031210801e12004c0ca0200e0121400e0080460303955004881a00901c041002125006c0745200020074400c0038050115000d07554901c40145055000325036881c40c2a01030380301c44101c088100848a0b2681c1d01c1c02c0001c0b00300c80c2d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616431906 1250 616430656 616430663
    0x1a0702120c1f02030304060c021606030b190e27030a03092a091806060303021b0303090127030209040305070308010b09101115151905010c02100201060302091003 71
    0x14a1508103420842d01e40e4403800c0d41c2c0d10380203982103a46507210366001c0c04070307101e568046002e4202d01c03441c0041e0441c4003801402c1640d0380020301211100034088155135100c028401003004039410044200039210842c3d0101039540f50108660b6807189448850442035aa0f81d014000800c1080025900d0390100c24528040e0f0847d000040d1000d4003814a542c0d144011017032041c4a400500070300b1890740201034801940c00000d109003c06403264030448426420031001a003047c1410101d040d100784c820b03407240e4802c902a5241c00044400078121400c00b1084000c5881d0070401610414101c80c4400002c58014080d03041600e06490001d00c180e0001400300d0216241c80008100e00b5404020f036201001d02070720750140041011410355035520300d2079040f0b9540c8101d034001120041e654404a01503040d082c0d06400c01e1312501c1c20040314002c04c0145190104650360108100d03a0b000c0900c0e2100368058400b038121074a801c00480c05410250006500b18202c030307042c00140703510f80c4440400c5900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616433156 1250 616431906 616431919
    0xc010209010206060d03020d0c14011a13060f1a0412061d150103030e120d050a0f08090a0b060d0f05030a09090b010206060907030e1c02060717011a0702120c 69
    0x64200400071707940700c00640680160301003000c0c00b01761401000c90340701d090300a40114400c130001200c09030948034100c950301200e2250f15042c51844c104426810003c24804405114840c18204480038005181c0b04048254014052100300ca01d00c0d8000ca03005851103c000c1c0c0c1c0402d070b45081880c0641000ca4500000c680c0e225883e4600f13120108103100500300c080d0711100c13144d185407000c0341d161100400703180e840241004e026030000d80400400500d41c405845803a10390300306800c0940f20314000000541030140c0841080802d140c041000f10070194003484032201c5840340c0001c11003d0007104001002400a8a454070a21038000050240e44c0d01c0307030765030340310150302d03620005c054403004000d450243e4045004100c085c41c01000301a4013183c94500010f008031952041c62030000040280061b902d01015070140803581406000d9102d003290801c01881c9000b40741c51236081e5014428442c1c440c3d440c0c03000600d0010150101e4141075001414014402004248141c82d500080542c0c1c0c030951 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616434406 1250 616433156 616433161
    0x2040f0e100b0415031b020d020c0d0308130321020306040506040e0d2007140a0f0501050f09030c0d060515040b01020d0302090a05030d0c0605010b070f1113020c010209010206 77
    0x10703402092001034858400c40301c0c1c100391030400100448882d000b000c0d01031540790703c100b0700030400003849076070040380c680d00920301c03000781001c0a810803c90000312400354496a1403400402d0f0030410064120311040000c1c20383d42d015007001c03100e1811014400205559040c00c84480142503000382d401600f04980800494030740c00304206c01c982a0340b402400d150400620481c00a00894074612103244090542040e80030b1040700c00e080c610350b50401e800c8030f0f0044042e0a41ca040420b4400050304081154030591030406001034610300a0130003034811182c000900802a840a019401c10307650085c010703141d281d00c140781c00009003004039000844800b100c1e00b030003810700c0c040c000c102d000748060700502140c80a1150440c0a035100007101c5400c001c00c3c43c0005a10f40301000003005071401c03656644071051591070840c06030740042c0c0c003d4280c48401e2200d000170401c4c03880c4601103030b94410780288a84403040f01041240c0c1411000142152000c96058110356041d0028031001d0350990a03580c003507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616435656 1250 616434406 616434421
    0x712090e090706080105091302030709090b0f15090a0609050a1b03051501050c12030a05090d09060e0d030e0901060906090602070e06042003040f0309120302060c1b0102040f0e 77
    0x2080a40303e00b00010b8450320040003d8140380e10007640003140780708100d103286655000300c1d2502c1c08039071101d2000c6641d89089000c0c005c40c6c80c034054100410203480c7c0c01b2410300e19401500103400c81c0040384180e0f441804584403100f1540080000c1400703a0b01401186040f5100d070009010541e0030700c0e0311012038a4044c1c4050320a2044d01c0c420301070041c1044c420300c003280044a15422440100546100c0c0505c0c0e005d540344a0000380d40308420050010405141001e0700605100105000c02d0a218115100f40b00c690b03000302546113441070544c2c21000042a0782800c48040c1100c24010f508150361308004140243e001b12140151483d60f00e8044c281503899100b2a034074016841910039108154000c188645080d801c6803500c1408101030040543c2d90403110411070344180e4044401c0c00f070600902c4c0070141c021040000818041c0640009429691000b9440d00c5008020304440070300024180301400c425441d05a254024000031511582c03140c0c00b03520411002c2c080d04030086180300015480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616436906 1250 616435656 616435663
    0x8060f031f0e01020d0e07050a0b03010f0e0a090f0c080f070b04050d030311280503010e07030507020f07030515130f0b0603011d06040209070f0f140712090e09 70
    0x600c0911560081114400c1c030054010b1544003098009950200700500e065105030051003419882580a000c1382031601040040c80d01856000b00d680c50310500041105421345140c02e4115a410761300010103070b031910390890041030300d450300500c0c6000c8901c100c82071101d12500c0304190380950045a07810400c0c80701c030580e80d1b6006c1c0301c1c0e2010071504110a10040c1822418041c01d64804c0c01d01080d810132036001030780150000408a14080303c7c460181000260040c400d88102c3c00c070b810150300e15410826049089800100b40b102410b4a52000c2480d8910030050ba802c1b00c0d0f01c90b004d80c1c58041e283e20b045900c8800b0b43c0c3d0b2104021000300e000c07404100301205a542400d13401034640005404994810000724001000b07603a0655071480c0804130030000d0301079040c02000d21000b900d003074a0213104101000c40060061010400e0310614802c640790002d41031601c4c1d10883c00c00e0102c0038a450b145c07100301d2207004c00003000010004842c91410350082c99241c1529903680c0d0441465641c0304200f9907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616438156 1250 616436906 616436923
    0x6050d11011128060e0613150207170919060c15061401140d15210804090902040209030f030406080106020d02030d0c2f1e07090e0a05070608060f03 65
    0xf00c070110705590a03500c50341c45071424a600d01c070781c40105428843c100744604040c41114a154011040c0c82c6c45410400682080e0040d180d40c0c680460503d0603a4403201c0c0c600c141110f004019400c001950303001591741081c05c0958401300f80f81c0712038107900d4500c01098088030120464400815240c0c0644d40d0700680120010b807070ba030541c194942400440119600c2c0080841c03040030304c00402943c1841030990082d910903a600c41d07400101c05242c0004118503010880d000340c1104045940040000d202404a83c101e56200c040450300784914000640240b08001c00c440c1e151103400c0c00454015004400380003128038507103030080d0b00e0b1380e5040c00341c1e124070b9011070100060300100300020010b15242d000109903022850960700c6901e000c0c010f600307080c140c1d000da5449554002200040c0610801030355400049510b040040c2280f10907005564a1385402411040364650400f0a51803030b01304541700301d2a0b00b0804840e241c6546681c0680070407019642d0501a0340fa0402c02100d07410700146541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616439406 1250 616438156 616438183
    0x902090325080a03020c01120b090105150903190b0105060307050a0318080c01240f030803070201180b060301050f06010c0b0c0c07060e04061413020d06050d110111 72
    0x30404030003101c01d50740d418881198144808600001c142441e00700440c2c080c0511a030014020b1491100c00034080668200e096818035082c0800e40d09141c541d0030145046800942d030111500b80301d0b81c3e820105000d0401c0d86601842646044103000307441200030716a0a009408403001c030390701c81d000e214507488119110f401240040201059291203540880c00a080c030040403c4a0103c03562600c0c4284c3c001080503400c0da45070030074011131701c0782082028856070b40200c05110b0540b0304540840007244501c009407980c0404000a03403150700039008041e06449014281180c404580340890010340262071030b0740650302c2d21000490003120410341c41e01412050b110110346c0301855969036a200401800035404a00600088580746000c000300000b0784559280c0e1850340380000207000c11114139034001503414030703c01006503581e00d0354079080360f00c007a08c514090794801c00009480003626081c0d02240d04002c202d0b415005001003c0d507800310b0300ca0241c0c1c0e01d0202d02110154140d4620b00c500d842d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616440656 1250 616439406 616439413
    0x1611040c0c0809060d021c0c0201060503070e041a040c1a1c0e0c060f070302010e06010509181c0504030302010f0515010309050c130603031e02031c1d07090609020903 73
    0x7101144510380a0700e50708500401c1149000040c0c1641c2c400e98004044a2000214442d40c02d406041c442c0150440a49103100030852a86030500099642c54684240b1544400150201301840f40d4002c50583c1c080c02911155032034141464082044c456502c070743c86000d64860710a00c0c0740014101180c14503060b04080812103400003804200400c0c0f0f008201080e0311131418200700340d45814020740302204059100700d4503040b0605010342943c03800b011040306a0015401032003075540d41d42c01203401005102011301c00c4000714840710b06d8101410011820f2110710118500050b920000420503684268000d000441415030003400b034400c1070300c58100325801c0c5940000c2c0c0354840e91003101e07a43d0240301225071601703404010405044030b19240c40282612198107000341504150900350703040d08000650010042d6440c005d480b070040c2c0801c60903a0210011100280e209a00084003010000c08440400c400145049644000c4c0344503019045003000000540e00c1e00f00d00c00e03240100d1014000d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616441906 1250 616440656 616440677
    0x1103040e07031a0306011e050406080d030e0f19030905010503071e09030c0810050c0307050301030f0f0203010e0f01111806070303060320040f2309030408031611040c 73
    0xd03000f5103101010410100060400b051080e9070400c02240244083e41c2c0b4540003503211a480d01d840b2895400c400c0c0078070308004040043c00c82c001459807507a440e80c41c002071b902c8860442c590402882440a01c410320800e2101d002c02d010b46010603403024820f494010016995a0064980340011524440460341000b0a034844104050079020180700901c0c080300c1182c3c50b0340c2c40c41d02040783c3c0c4e0481841390f442591641c144101074450550400320010026055240c0380000600601c414040141010102080002084000d1100003c86035008000303001200400754115582c41c0300d204c84041079800c020000345500c3e9540101d4a0000f01200c00030700d0141e01c00d081c0507869118800403004c01d950f808000021030f14200e01410902c84207408901401481010401070b2080a480001e25901d4160b90b1840d15580c9000d071f1112442d80f0705c80f0038441c6c1e01e8620807421802903500a11a078000021629525440041c4102c85144108240696001a0824002200d58a0a00d0310119080e0f480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616443156 1250 616441906 616441921
    0x318030f1103130b0c0c0604050904060f181b0e0601020a08031512151b070b06010311031503060f010e060607060b0d061a190b18031c1103040e 63
    0x100080c00080c1d6004503840c00f030310991020498819a80a1003410350041000d14001200b407008520740141140c2840c142814503000800c0814050002064203a40301a0013074070030b800741c01c52510302c1d072810000400e084090a010214180008219044103079070200415a0110200018000c41040e0300420f520305090b0780e001c015a101a09030080b90003007410034207071034cd60b881016210f03200c280050311060a80040c60080114050407500010b608100c1d0740c400b027410841079075070b4940c00007140741903500d40200580040035126601d01c2845400420090042c00c07401c10b610b10f029090342110b240b607598200d25030b0a0300e001c1c09618100c05000d404945640f600700081c1c815503000b20300004030390401d900010311404a610003150b9032603c0f1051110304410324180619009403d480d0815150400d05586064074424061b503007800c2800300303082c68407051141c03140c1c51030b074805400c40d0f0140d40b155035030a0780594166034040001d00c9803012180c2080d808019141210850b524000583c2c40d11038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616444406 1250 616443156 616443167
    0x606031d011b0e010c0210020715020c030d08070c1506050f0d0515180f01060509090f060c0a030f18062f0d0f2a051303290f070318030f 60
    0x44500d0401081c2d500070005030386d6620410300e40f038045800070034402d071a0a09401c41140c040c4490001e54120cc1008030072030700d020590000c50b80c0140b50451440e91580f009841e0020111805840400100c903200314021450740701c0c1050790411600002d1a001001c10418180c0c15950003c007650004519a1a4010f2034810302da003000300c400448007052a21820140f820320003459807100c503074444900304401c0c00c00030040380c0c10500ca18050700c421000104243d9450501502c0040c9036280010001c540d588030390300032554411300807414040d06000050041a003029070740140c1da12072514606032001891758900041d80403004030107501c2c055600d03082503560f4100b030b141005d800d030700c40c4d444c01c6400c03000b0300c81d042018072045030013680400700740c815103180c00101c480142441800c210701082c0f00380d84400c403012654403150702115482e00c052002d4500c81141a140c00903000705060040382c100407100d091160450307942c1040454000e0b0f001c60042c0c3c4072a42c003c0c0100c0c95004400214a1003427 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616445656 1250 616444406 616444427
    0x60403120302040b0705010204260d210e0601030501050708040f030807122309031e0f0c061317091807030e060c070309091406061b010606031d011b 65
    0x207040050400341d90792001000c9501246086509940c0001c2c14089203542c51400d62100e48800c42014190070380403116544c54005484080074020096a07010740110480400240c4064440d0180b101400240c0c1141ea10030003804111030329420300b000035001901c01c44105228941191660f290075038a91820340300d48002070003002c00c001030f0540c0414500239078018000c0d50703064900302d08d0100000301403840680304048c260f030280360010444603d403580c46403880581100000a41c0d942e44007482e00300c0c21144908100b503805e0b4001c0301c04000300e041e1810240c150b01e40c05000140c1e00080060301142207442140f451740e9004c4440300b120400e01d50000f204d035520600c1c9060018201c035003807456034038094040340e105903184400642038007050341c043c41c190300800c0c6610341413042c144090000c1c1001040245040c1c0251008038559160f1a00c80c40b4580c00c0d101e809008200560b00c40e071004010f00310740078105000034000c00640702c14500500c980b00c2c014080c02010341426038145411141c00218 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616446906 1250 616445656 616445693
    0x30e0604030e060c1515100206060f1c0b0414060c0c03040b0307050c1218121b01090906090b0f01110a021908030f030a061a040b0a140c010f060b09060403 68
    0x50101c040e280748031708000517018188080d04160049104d00420825a06064044007150801018829680c856042c00c0444440489600141016407a03003403901c980441c001a0005403036105100c2030106040300c00826582c0c2d40284d81c8680c2d0707900c008000b1845000301c034900356803003004204480800d0001450f081200c1e880c1840c5800b148400d000d146c41c1c4a540700c0c0614135400a000115442400802003030720109448000704800390310308182e00e03009101110103d1001841003c0c0d42603204032100e6000d010084010031000d0f860380f49c2a8000c100c0c54003490700941c02c0d9002c018244d805004410501c410b040000e08a643c0c565007800841c5100400c03c001000609602080c3c0160600141c290000a070303074066220300e4545500010b941b40c50340014101c9001d061400d5404401c80c00b22810f8440c030094580d41d81d04010350481d030300502003078616520800895000b4180206410000e0b06140148040c0100c6445294041c1c841c8144420664801c01c20002040052855070040c0641c030721 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616448156 1250 616446906 616446913
    0x30f0d020409271211030a18051c0f02030a0b010e090706080f060409110d060f060e070903080f0d05010e0405010c0801060f030e0f010c11010e0303011a03100302060a03020703030e0604030e060c 85
    0x2907546010b1447e003240101d0404210580f400341d8400340200c0354007004210407078481c0390390240b0b880c0da140110032108002c3c1c040710b003180c43e40c0107646040150703008280e8440c060208641c4d507030303001c06d910380c005540342500c0b4000c00c03d001031202d1044860501941c40000e00c542c1d1a15a84100002414200401c4400b100c08030302419031995145211200746e40500e0000c5034500c44c224007081114159005940550420801c1c8041250b00c2042a000d0300e501082043d9114500741d54580035006405107544014140b9001151500e001603131180038611610090148059009d415685190300740290030014a8901540000030310a420801c00711603c0030541e4440e011201c3c3d40303401d60310441341c02004031302c6205034811100401d01c182d0400171030501c01766080d941020503241d07075240d848002088113400480030a400d0b400d0001b4000055a008250311390354080d00030041c002e5042028141c0220b0f2501c00d44041004001c55010b1040358160b88581e00c1000050400204c1c2c0c02810390944140b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616449406 1250 616448156 616448177
    0x9110708190e060f12181515041a010e0d020102060601050a1e0206190b1c020402091201150812030103081e0a030f05070509090612030f0d0204092712 66
    0xca48800800d00e20701134001d0785940b0ba01840004580401c013a0500400002c01300d821540e83d1004910000105011340301c4580d00c1e26900c48140c0d4081c0d2008032107034000c0c41d1114100c810424441304101145007a2128250003145104000352044540e10190141e00300710005221503104000814802e10706050a090000104418170590f542d0002841d01503804901440310000320855401e01c808002e58050200c0c036110000b1410302031003100848006912021464119a9643c0545a40300d4014008030201400d07806040d020b008140481505080f103120b000c5141c0002207250000c80d0380050780d980c55a441e59580c100c1d15484045a29080c0c030704024810044018100180b03054880c90f600032a4058002e034180c0d00302c5001402510034007000b00300c131001e90744441005690140088400c075040640b03500801e0b0640c80f0700003072500341110012381c00c4208074490380a0015100158010801e11900c00d00e000900e184558500d8041c0100a1401001896108032406d156016117000660103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616450656 1250 616449406 616449409
    0x5091003060f1806060e0112030f0309021807080a0e030a05041820130906080606040e160b070b06010804021f140301290a1b0203071e09110708190e 65
    0x41d84203140450744e00384c84410401030606c0300c0300440c2c09030815a40070340c0d0f40801542d000e0a11021840c142d020b05450b2050481559039980041480e0890000300e4503071460400c00c0240034076802c0f00c8098446280007035505251038000286d402004003512500d15041c00d0003000ca0260780480100d0304c0729911484507210030346400303c40440d403075000001d09444500d120044040c0742415046450500e103448010015250000380c06a00603405441c0059020407040040c0c3c01c09201c2d07980b10b01501e0954030002040030081c1c00400b880c6000c0e803009140da81b21180111000b600035200030f94450070440c05004614441a50002500a5801c050031030660011461010303400c241d10400c0d48800702c0c034003009400b104c0080a1240302c242c50b0360929060b04c0d000301401c010300c000310340203142006030541021900c08101da403024000044014a1140426011144d400d5044c029800f5440c00c0000351110080c141046d07401c410342c40802d0900307089403101c00c1564106205580400c200300849070350120b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616451906 1250 616450656 616450691
    0x2060405040c020303070e09041106031f0b0405210a17040e0112051e0319140301091b020c0d02060304291602060906040b180f031305091003060f 64
    0x107088260050340d1170b403800c4075000e0540c412003903107940100c45001c2003100241c5014000c900c2000122400380c0ca9484038840c2d0000d107200c41004414130440c07010041504031142c8060421a24202c0300e0b091511809103000880c0d0445681d00343c0560301403d021f000140c0c00c192a0312414002e500d14608250b6142c092111901083e0b00c0740112070b80710f10194051010505c0309000811180c04852485a80f6010303c1d5580c0c441e9501d11185049000454003a044c0b2840c02c1e0501e40010250050b242c0d610340109070300a00c01e02107100080c4050782d9a00b60040d00110704490b100714014241440505681c0920050380d00c0107108481c42d002ca1042d0681400c0b00b40b05003624034a41c140c034040e10745411409000080c04a81a0030b040d58086400c00400810001b20300754840d900030030142d401c0d02c1d1071216418011070007054041500030150613117007204c0000b02a102d000d402040b90312282e0750710001d204600d4001d690300580c40200f080c0030310115201d40c11170b09200c0940c00002505e00130241600c5003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616453156 1250 616451906 616451921
    0x6211b180f07081501090e09070503060903211302040f0605131a010203041a130b072907120b01020309040e0304030204050108060f010909050309090f1b0412030305040206040504 78
    0x29003940c1d00c1c080c000c00a83c02591507600010f00302003400009280d074000b8040308130501c00c0160501880d40010455075051142c5c0c00149809000c40f03440f403e0264002d80c0720340090803085a40c8800c282517400f5410880d801c2c0740500000030380319095080a400340400b52010148189013280c45890015403516040544070045103030b00c00c000341d080e030301240c2d00c006c0280c0c00010604540c0144410301c08085000c0d40344000407004c802055031010060780058a01c070883e40204c0040202003442010300a2542a0354641c2d59203101c51000d180ea180309040311003100342c2d111340c0010043c2c102031a02107440c2d800079402500500440c1d050991080015003036801c40d800c05041c41e04040340420071030816018190250501c000607000603d0052080e0030900014400d0a88251f20b801d800c1d02032090074401c40e608650040d054690700e00d0560380c1d03194420000e80300c400c201c03110340c40f00c1800c404c1940e00369400e8a00600c0b110b1001800341e00c0450181c01b018000b6680306500700000990b5984a119590 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616454406 1250 616453156 616453171
    0xa061103120f09070f0f172b0305130c030615080709020a11070302010c1e0f0305180307030c1401050c0703030c0b0708060303030a0f091a06211b18 65
    0x542c03481e100741464103001072580132545291002d0300910007441001483d505449588100064070007046100da854000d01516681520210f40400042d481e2110b2650b041d1b000952401d004a490301d011104190341b007080b010303001022810080c00012881d8214a01c020314500c031499401d40c03540315107803c01c150f9a0018051507030018003203440b01c3d0000b04000c450240d203800703403113036520707540000c0c02c10051448010000080007802008000d6100380145000d60020381ca500c200809142c00350070f6502805144503201d5503100c0050041c900083d891041d01ea012104000c01c62074444251511380d800b6141c00d050020030310036401840760801c003000056000395542c000001542c2000c100703031540508050200b0004008000164030300004503a04040900b41c002050203141d00190004c14032690002e00000044034140340c080001c40300140102401c540546030414600d0800300755018403040d542080c0c008080450030088031002801f08048064141003e143c2107508809102d2005c44080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616455656 1250 616454406 616454431
    0xa0e120f01110414240706021b0102030402030d111e011407260604020403080c01090302010b01050a080a0504141c0905010302090f0d110d06060e0f04020a06110312 72
    0x1103460039000d0142c200c1001580d8040c07407800e800c111100e902060200c0d40c3c00d004020803c0401c0d00c0c86103078000d801c042588800590780300c0710030703183c440041d45c00f03403034010390580d90726400010455041c400c6034025540140141503a411040b01a6000b90054100001c0d6006008400d00082c2c2ca8032401011900d8141c0000394120101c1c12000315084080d001c58200804900c00ca282c1a4401e84841100e018841c18103c2c1917607620001806441541c0004003a014003049400c0c4044054210082c064440d80081c07140c0040c2c2e000449240c01120113020008447c5008200f14900a0307011a411a01890704144540001140107151500748011445100760114031308580680c0711040714003900c0240381c01c1d46001207030f800180d800c10350011124490101c80c10103600b0040403c66010245002404429500b07456050001c0181114880c0c4c0030080801e00000d1101d10080c20000d10a03030303005003031100050500d10200d806108008540401f84801c0100c010490040c0c1c0d105d611034107104016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616456906 1250 616455656 616455673
    0x815150a0b090907030b06030703020d02042d0e130b0405101121040f0b060d05070f1a040f120305251217070309020310023105090601050a0e12 63
    0x5001d14550b0051418081501d0448050a07e0383c8490480343c00c440185805a10f03040c000032054020300c91707548401c3e4841000e2080c500d80d20004140342c0400440200203403581079a40b4880c450b03036101140c40c00b1342c2c50808007200c000508000121500b25000c1c6040b610f044003254000001c58085075803407911000c003c100c03001c07400051111022401e000c40c540c03544a08250743c0d0006c1c075044041c4014076402170a40029030b180c980100020103c3c1d000000c03200c450759586800b40c40042240150303c001880f00e400d510145035088200d5013151000f03540f04114170319010603961080e401400031401c1000c10800c1ca40c4844002c42e1031092042001d101c00407611040c0780c5001c040500700410340030f2007034a0070b40d0600725481e00ca016601008034280480c0e620218400030307041001c1100e0380e2400c58030101d8620280314140541483c502000a07054010390b482e070305c0d281040d180d0b41c8201c0381d02010035000607929510800c09029040c01c542007a500036200d20380051f8400d01050f213085090361201c0034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616458156 1250 616456906 616456909
    0x61c0c0b0f0405031c0210020901020a24060519060e030703060608070e01091406101814030d051602010c06110307020607120b09041214030c0a02160815150a0b09 71
    0x80c0f10450441c1510322545d03084401006503c400da0020203920b0203501080c00314503030340280000c54030140d0001c0e05004800f501e161011001c0c1030700c1600700400e45040303404281130410340b1114661807800b98150406a00d405c2c41103560246071000140c040c014030030000b0004509009a0018102e900040c0c40c1190508400c00e02c0e01c1e10583c00311580350b040c140b9001e4085030f1485003a1f00890142c03001003055480c07020949480400c940c04419801103014002120b08010b40000c605981c110266040c03580c030400c04841c3c9005804468124040c00f540c4400158001c01c4024255449000d0109614000300e0b800b9065800c22240000542c2040e0200030310b56078001603000c5405c0010318101300b0b000410003c1002e105004000401c01e48488100450640c001e160628490350158a0a035480c684072405440c550070089651026100351146854903004a060706c00680c1c80c10340051030038030318040c00f01d012080050520040c032400c2d94440e006a855035607200d009407450724480d03681c6602080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616459406 1250 616458156 616458163
    0x1d060309010213120b0c030402240405060a02011a09010303080114040908070f03030c11030405060f0d0e0d0e061c02070303060e28270501020d14060414061c0c0b0f040503 75
    0x204000161b6404008002c0143ea410004400c60044003c14100d15800c0070070792001c912890300540c0d800000400c54680540d8150401640c0901e4424080d80720101141072000e035000030f00008010440f1400184080120300403490030f0380388010000316402500c0d8807070b1000d5603c418070035640d41010310690814550507014142000d030903441c0088403c1002c0c07260701d407a801980110780c8a00c2d00002c0f880300301d032520010740b201110201010802c01106200d00e07507441f2000421203020078420004030005261000a50303c03401078086522081c1d02d10a01c01000a601405044090650710038000c6440d00780056030b14071842c0d05062002907000032060781400100c0d401101203002d410500441411021840880ca4148003c000302c07402006600d049030180c000c43c01c440f0f568a140510840c89039159205241c029030003510104032164000c4801141d11000321042078102c034021031140070190703e818100a0032405000c0c0d40c04000d48811229a065212181c003882d09400072900380121314050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 616460656 1250 616459406 616459411
    0x109051e01030c090e070e1008150402010c0605040302030c0114100b070c0302060322080901110a0b040809010c05060112030f090608130c0306020307110601061d060309010213120b 79
    0x891034045290300d103958500e9100c40c1c13409001400380d10b588090403000701c00c1061201070308506140c00c5107460110481403d0000f10300c16194640b1540021882c80000300d00c280740940e4044c0d41d51881004162140380180c50003031700490031807208003d825551704007031194100010300104403034920b0414040000c01d4017441c1d08a0301011204200c01d0001030145108401260742c180c4680b503c81c0d881202d610b0701211050500101003800801401c03c220f070180090a03104802d803200003d0700d000003400d40d0366907941c09000702591001400701d80403520007809840c84000514003040344406560b140da00b00382d021b0388076203d004035806d00d4408144e00305403003030109401890240c60781351500d00010610440034111800085002000505004a9243c001d01035500039605650b03e062030b03030307004007101c01218040204e4054000080b640e02e200f8403981127401c03c5640325180150a8104121490b4005008828030759070800c803c80380d0442000c81400148a03549591442101d1418411001c1000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 616461906 1250 616460656 616460701
    0x70906030506061c0b2403070305010b0c06060409020f0409030207050901050402071502070305040522151d1306052a0a080a0b04090b240a030b04080a0c0b010905 71
    0x180400400c10814550130500f06060321000301d29003a580c4085900c9000f601c03100306808603414522440420703c5401103000f41000c1e6010481603a80d18010600342c010000c55828940000c0003056661404e40c01400c2040d0004008000040214001400f215070000342140907800030322041000f49021f0b0340003801481705950543c40e1110a90f50000030200703071070880000e19070124980042c14411019100034090240683c042c444907002d410928015108018215a0400c2203101e00d00e00028500c500b158a40314800c50240c2d002d01d6030080d00d05c0024020460507003088442c00200d041800703042c1c0100350911107100e000000c060540407840c10040300030a0751740c0c10044e054460b50701607103c0b82e10034442d000014500b6400700c00a805445d40c2c01010300554003913424000d13040101c07450100c0002c10004030030206c003074000a000b0061614031015001000a50004010840103c001c041c402c0b04c03441c18450145280c0c0d50780c000a48280c00c488240366444081080401c1340301030721640200d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 616463156 1250 616461906 616461919
    0x618010605010504291c0f090b180f010f021803070b0405040b0f031c020f010b0306040b04030c0510051614071e1410050906091015230a0e04031409010e0306070906030506 75
    0x2c031510703001e201038800350094216801aa20b51100c00c40d082c448006d0180d0101c009010711f840c004082006500561907080c10400d034003f0000161400045401c00c40355500e11880c00e06245c5002c0200500043c54056041000da00700d03030020341c1c0c00f0301484c0b101d5900000c401a013012148802842c0401780307000542d01c0da14100350090950340028001d80c2c000c1c1e10032074884003640c882c0342c00c8440e400d0030840100141700d0710754800041c02e01d94001a1251041c0d5802c02c13041e4a0aa500b01c51802c980c15441100e203004101c1100400d1010b6503000f00641d03009401403030180b66980386906c0d249e400c0f00c1c04000ea0400480c2c0101c600c00f0b800380396000010a00204400c0c20601c1a4030303281c6200000107100103541d040c3c0a10005040c40c2c0c0e15000384000114030386029400c20340421043d69450f201c03481180d0401010400211a0300d41902854042d6110b104005030054208001d0b482003003d1030601460b402c543c6c02ca55420332040b840b80d2010760f11410085d00e4500e0180070b8941c05040a8030070f54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 616464406 1250 616463156 616463171
    0xc05060c100b01110a0309050108070c211704050105042303030604051008070f0510090b07140703020a060323070509090a0e0f0618010605010504291c0f 67
    0x20000a031401041012070710004582c9142c40058414003645002c2e0304442c040c0040010602d40c0000f45801103940a8840c0e44045d41d900b00c0841c0d6045104000520329614100c0014020740708a104118640c0310742014036000c004182100042031040300c0854071691528200700030003581100c100e10080314590f5009144041e40c51035503d90000401343c5008650301c0d0000b40d408001c0d040c0081c000c1c01040e0070b6071680c0d915072070b40040803d0340f070040e40c0c0500d0a04299200c218465114001165130045042c0d042075800c0e074540d0313242c089615403d211480b401c540400540e40d000100001030940b03490000f4605030081c0824100301c0401101c41e02135207513404005035290007404880b45e0000c215582441070759504001e5005295840442c00c1a2040129a00c84140d000440500800740d802d01500c2a041e51200c141c26101d89c1d01889c0c3c001201400200500d848180350402218083c03408411903901d00f4807516429002842400001070044800d84c0020000d84190301c0300c000b10b044c0038024403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 616465656 1250 616464406 616464427
    0x4020a05041503060e180f03030721060e070305220c090917030a02031f14011d03010c051c151509030f030302040311060703080403050d02160f0c0506 66
    0xd0080740b05048841400a0700b075844148a540101c01400124008403a9030400c103200184041c000e165030200313489031240484842c078000040e03074441c04003981c42070040300020840c840010990401e80c2d03020b0b912004e01069408150700c00703500c40d42d00341c0d4001556150510b2603a04070402ca131001000040c02e0500217010500311016502520381c003c10208228046d4a800800d01c80403008a02544c0e0010041c400401403c0e00198010f030900b445101c80140940020307a0104064800d100c0301d60301072199114154010203441c40360b0608a05503155602107140803d09603004007603148009440059020010751407e0010881c20440780d6080010b4644190700c0c0c2d40c0410140144129602d9103005808034a20401c010805954054200302611780549070190207504240411942e01c081d0164240c06400c1c82ca01b5a90301a0701662414283c0d1a00d880584240c0e01402008464913020400b85004440600d400101948520049000ca885606151009030b10542005104080411840c7c446 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 616466906 1250 616465656 616465667
    0x12010624051e16080c10060b041401031e140106080711030d09020402070804180609020705060a0f0e1204090c020c0a030305090102070f090c080903030618060a03080c0f0c04020a 78
    0xd2802281c0c0c0143e8030046080500c008820200b40108003080c0042c8140400c2c40c045401503255002c01800d202e440d8440c42681c1950040c1d028406007004d0f441c0c06585035601c650040b0750b04400313080d01600c030b07569480240c6060300d65614180c4d0092859800402240380d102840c95131204640c6030060f034181c2c01400b0b007a181d02c03c0303144803c50302d521511500155983c030350448100b950301c8043c0320b1340d440d41c4170222101c9038030b0303000f6000949181110024060b141c0b8000c4030800d550140c0504407964030940420020540424042800ca5803040304203928501005443c641307071000380a881d00c0c3c2d13180500700001e84540c2202d002c11900020021401500d030001640192a49401c1003900e070300c42c1400403490031410350701501e01041083d20008103000c81e5404200045425a01d0003e15130b0b40842065592105481e0a500900c01c820150294010200d0340b6401c0b810041008031941e40d02e8851410350380010304000c09640200141c2222110300300304074520040c0a85e019400d14540440c0070b804c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 616468156 1250 616466906 616466947
    0x90501021207210c030906030908030601030e0106030c08010212060d0512180a1701180b15011209030801051216060e01110a11010e040203040803010506091201062405 73
    0x680400c507030b41003002042c0c03848020310904044680060240300003d0101901e084c098000c80c0d122000030504521a018001c4c401d82c00c0151030346135071101c10044009201841a6a003e9541c4120200000b4280743c102c500070300119002680f1182000000040610007411451041c1c1c2001d540a00007403011403003c404880043c405a19002e12260380b141810307007100e0f01540f01030310810201d00d0a00a00309030803021402002003066400a8102030703004040a45d002d440014603500044815600f070125808844040c0340c002c1c00c01850150010039100070000840104111600611050070003a115002c4039400d04020708801c0100701e05420b00310598081c03603040201c0c503035101c0541d9000300495814480400e084480007006801e103c0281c0c0501403c10340010040890803089241038020350340584d8000101c2440e50b40303840b0400c00c003030348240d180a8000b240d81c0022108003c0a1244100500d400e1103050443c4004440ca407910000c0a00403006110b810f00010360749954544003180c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 616469406 1250 616468156 616468183
    0x512031e0306010912150e0102090130090f020f03120f03060f03150a060602070501350901140f040f0609050304050a0803192a0f060c05031609050102 66
    0x5981e80c8031030004a80000e01600a582459003800b506070810011000000b40c0c128112001c00c503030f103001d5204501340d21135600400e0000f075a605440d651450040741c5007102c0700004011401d1890b00702201c8082c1c4041d600192207412030342c030700d030742c19400e0050240716410700c02c40c00b801c1241c8406040740d100c0d0140903204581680e010000a0598682d40385003160000020101c8a0294080704d2010480741c084608840c900d007011000205540009039440c10745a051311460340c0440d103640715981003646000b01c24180c10302134409005085104032018040e01415001050928074808100d40c640c40241402d039011520300100004034492211029607664424000b09280c0c4150601503c2d60155030015a84041c0e0004001085180007000b4014045219034034550007d524405495070001b030f01c14016a250350304400046100c4441800560900c101c0002c04110020f4690400715143e189800000c58800410300090600818554074001d049191441c1178906160000752100d800c0d14204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 616470656 1250 616469406 616469467
    0x1110090306180b040503070c0906060e19171615050d050402040902041e110c0a14031c020301080105060d02060a03110928090203040c17010b040501080304051203 71
    0x603651481c40303402c803181c0039400200030041c0c1c0c20300e0f051131600e0754080c80c021210b030315146400248800d803a0203101c0440f0303841d4564800d41001c800c20f06c02450314010701005400b48040011407140852200d070551260741c00d0081c00014000740f211810705078140c20a0941c21122000464119407000c2250314a9244100100307c6464910118002c1c1022002c0258032904003559002d81040d4410711a03580070744008140802c040300c068060240c4140b1010311210f07000b940c80030021440700c5a842c42d01c13a250713000300e03494413100d01c1e40c0c0e04004628050b02c08401d6000001000b0032080bd0207503540089044501c400c09a001c3d500080c558450120983d041c1074030703800300900200c521001d07a01c0a18000c2c224a02124948041c124942d03070308000312581c44184100854407000d5442030b241310325440510011004d040c8078543c4550100b03461714805541d20307007101c00c015407224001e9900030481240255112828242000f00c48103080d090115964020b00c440060340b80061508a0501d5010025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 616471906 1250 616470656 616470671
    0xd230c0714130507030506240702010e180403080f070f20010204030c030f0b0f0705121305031201050f0402070c0530030421032f010f0203041110090306 67
    0x1140c100c4440c800d401151516203c10050340075019080f20303204001c11103118201c81c8030074032040d00008840c00010695801071040d8001940144806490300703800510702000710f006551000c200d003004450440c0007802c40c00604c000c1441d0f04034081d4102c5d072181803841231100403010041131701182c88000080308150003040900f008080d4102d81c06950808041541c8544030300b444a84010f181c40c0032a1030590090004e41074048442c900c1d40240c00c1035407118070f401030404902d140d8040150407203080a4003c102100010700030401041d080c2009440e21f035556161808001800010b400b01901613070041107101c0000d0f400c0440202038038421141d2a01c1c1001c000c4141e0f40740c00282c4179071002c15080e2006583c8108002020300100d550080008600100760002090005c1445200070302061040059020046d45100c09401d009400a10300c03082003c199400e0f030940700b4001108141541c00400c1c403042c0319041442c1c0741350881c29641c0056940d00da0340c00901d003203041e10015064903941c0c004d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 616473156 1250 616471906 616471909
    0xd06120b040b071107260d140c010b1f020d02121c09050729040f0e04150501060c1103070f0e0406090c060906080f0403120e0f0d230c0714 61
    0x31082c06420041007282c00b01707501c44040e004604581c4a801c0c0c00101c01c03522a80412000050700701c90004140e8540d508580c41c008050303c2504606050000341d520350001c03880a8450325510305562002c0340c507188801c611040064200804003000408542014102d0304a40340c483c0b080f2119103e820002c06c14000418074000c00403d5003040040c05401030200c0081d0401e20b0085032284031b500c0c845940c1c980070300c80c1090707100c51190303204803410241c42c840d08000c00550350408a511174011a80140401f4150702268200c0304242c11100c04a98402076500a010204020b000d030b40030164002c2000d50304003c5000000c0e2203d119a07a5100e00f140e00041c2000070303079003044040c141d028001a9070340380c46010140844080d8081d94002444480004c0e0041450344000d601480c3c26460320040910051008e10190100e01c500c044a80304404058954980812051501070440d5030340d00e045d090740d07500241174468981078140c00c0b504140310812003a080401c0240458036115007c04907100c0590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 616474406 1250 616473156 616473167
    0xc110d0c03081b12040f09090f151b020309031c17040b16020102091e010c020d060209010e0a0e0112140d030f0c03020f0d09021c05030d06120b040b07 66
    0x708014080000481d0018203100824256606455540d0642d001a604502c4010103805076100f828801c000020040083c1781d05640005d40c00360184180030300410250701e48026540105803c03051690340c030700401c0040a46248481d0341580c04c1c2c80510310b09000900025680d900441c519000341494460b82a2454040c8962101c0034684244c500707403610706800c1c1091108412203034400c010b00885d00d0104e00b14818400c80740940801032811010245d40303081c000b0038460300d41d5040e05009070b1400400244e951a9a0206101d20070300016070740b041280001045c43c9041c00300310340104001c00301400124080600d1030305407440d58032850740300b801074100121490384611000c4080d000e0104100c00c401c1d4160809035034105001c03018001c0255044040f0100d108444040002d9030090107000180c3c00c0d01c0d0044030101c0d0000301881442d00780c2c1e40c2a0303403c41648801c01c566a070f10009030025804640d00031600245207a03600358221071800d4035840c2400c00001c200801040001000450490064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 616475656 1250 616474406 616474409
    0x15030a1505130603021014070b10080109051c050405102102070b04050625030b030106150206011d010302010c0b1314070306060b0c0c0d051c0509040c0c110d0c 70
    0x102505040c401c000c0c00b0703000030010741c001a40100307130306201e1034507440c00ba45200301d490664166180ca03140081d181d00c000220050040d180755800180c00140001003402005460f0f40144040c1050001d946030f103008004240018405010040c401044103907075000c0c4c1043c120b1441e0070304400c6141c401c8000280807901c0034521a0380352020601800b446048000180b0517442081211540c1d201c1400e40c202c448050740d00d6aa00855000034500110320a070801d41c0c2d000e40180020401c1c5848100d0801d103581e2214610005910900c0100000ea400000c807100c0c0070001441d08016504540000f0520105038901412900300e80021440a0318074004045c1c03182e8018003030004645d8603030500c030f8a41e202480151025401c4c0701011400310f42400c102c41000d0078580040038824a14000e0000c1c0c80e10942d01a6494007908081d040043e041e0007031814062980e03500c6540e6145e40c007042004480d0b10f00b080004101007180352500003101c144500340030440031a24807800c021145811124820039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 616476906 1250 616475656 616475659
    0x201020715030f050f0f060409020616020a0302040603050309031b030a11060705070f140603091c12050c0403120e0a05060309070b0f0d0b1c020103020f2505060615030a1505 76
    0x103080803c10117510584005001d8282c442441c16103441d4030040009407655403101a40c00041044001d440044c01c006a6200e04d00c00b601c0c1c007000a58a40000b41200c20b07a03401940d1a030000030308180c1c0c901c3c0901188280c0014604a010b80c12405004241e880070b019100500c18180420701c00581c0d580c1d076050340c80495100049500c21078a44034064000400c520440c885075040f40c14a81552401c5001e0700d204800c050003c00300c1c4440d007203080307407114012034150b007d00c500400340068440440c081c2903ca20141003d00c4d035280e1a42c42c0465088a400c196001084850381401d0255518238155908446d012141180c480c3c0b5002001410045141d020241c12040090f1107104c0d29454805400000b254010070000459841e043c00508403000b10388014454810601200542c00703039020744402310141e0071940c101184280c1c400590700e1149400e1400c8c07540b110300041004410007055511507020b0f5001e0b0385002c8008002252400041c0940f03102a403250031800c030403030910010074001d040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 616478156 1250 616476906 616476911
    0x80303151f090504060b04031109040f1e02010e0402041d040212070303031d0307170a03140c0c0f0c1c0620040e01080d0804060b03012c0709090201020715030f 70
    0x10307001c8018242d10070341e1140d24081ca0414200060000b001d0007950100e80c0c00c8254040b014402c1d800b004003501c0c006108881528201203200b01044207012403a040c4203800c002a55600b9890001514045070001100c0c4524010041440701a105200d080104245031140c21115220f070f200081c6026481c03102b01d083d5100d480360000905505400c00135640308e508c500034551100d6044007035103130700c18224081c2140c43e0707422101c2c030380b910110000c209a17074071407400040300d202003801c1d9003031032a050f03509221001010820503c110b0051200c0000544100700810708103d680001c1072075003400b140408209032005800c001400b1854100034501080804214000400f011a4070384030f4015008072280000c0a41c00460141ca000800d008140e82c1500d851300d280e40d0f550307102c80180084481c4d20303816540b1100394101212219110303403140080f03e802016030b0310040401038a08086c2da44400c1c03d030f6090408890160360003103148000e41ea461100c0f210801791210045d0050045404124246071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 616479406 1250 616478156 616478209
    0x1005010f0806011e031e0b0c0d0f18171c0603030806010314070f05040e0903030106110703020d06020708091002031b07150513150302070308070e0f240c0a060c05030108030315 77
    0xc1d0205c01002600440c51041100034440080c503021900744429155540842f80d403040082414070042d00c00c8811402e081c9880c00d9110191646100d00c1d01542200c8513464907820f02c02c041c2c0203d40c041c2d005000303107800c000c810404200f0400007400a0b007120b092010070003074411902d02c19011980542a4452400d4160802040007507890b4000d00c1118001600c0280401d1281008180881180d03001000c0507082e0840342c403524000d6000c120219007402c41000503d465455040b45a1041c40558000e50303100c0344020b80541000079003a00007021a045004188145003290782d21045000d8240381985d11142040c00d00081850385401c10314144074118074080340540e154004001b15842540c8030358913501d80c1c3d501501c100c003103040c01700c0c2d2200344188802c0144c2000d2840405040c00b003a19548080840c0030110f406038001c1c1030002103900300340aa501809498051442c2041107480c00c0d62440d07240040481d281d02014000302c0303800544041e24107503540c400c1502503c51450a0f200241719 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 616480656 1250 616479406 616479421
    0x20609010c1b0e060604081b040b2d0d0206030103060c022a1e0d39050901080616050d0b090109090528060e1005010f0806011e031e0b 59
    0x8070300ba03100e03a510259011000070841e0502100f510100d0f1040710041c0383c5160660410007178001d441d4029504655500c5820029540b040342d03095044000f02e002194040201c180e030109540481d50060007a82c01c03130030403c01071325100d04503030440f50010300000b84080c1e03c00c000c038100094440c40d207080c200402191040080e40414483c1000340859015050328695007051049692070989142d100340640a194041401004e21514010901c0c42d9841d80042c40d0b602d010620002d12802a6001c0818005002c1c5062000419000d46402c0f00102500c1c607229020748a0005d002c1419010400081101c00300116950822080c062000300a0388480d0707140c0a5070001040780030425205031040522100020b10b04c1d04c20401c0480b2003034100c81069035140ca50101a1041081d00c00e000d01ca0075003010300d001520b01c52309019203045403101c8240c51038480341c146000c0f41070700041c1150840c0b5200c48140790070f007424401144e078045444c1e904110713103520f001e1058820325405051003040e0400c0000c031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 616481906 1250 616480656 616480703
    0x1031806050a0b19212307090e0d11010501030c0303121104030b06130507020601051e0303070302030a0f020c060d1e110316021c1107030f120311030f0103020609010c 73
    0x54400103c1c4c80450220700d05480c03c0e2101000c030014008540e180141c120240600d007002d01d1403843c580c00c1f03411460ba21800f45040314103104007048280c112006c0120410fa00c010a01c0c40a41c085000384015419906c580c0650100341c84000c0600c11303d44401c07413010101d600841c00201818580588869036800c240d00452001c56029124980c10391035900c568442c0e01c9090302414190b030080103030343e00300000c0c0b007244103000c2c2c5024503006006440000c1980c080000b00760f0140300e5800303141c80700740015001e0805908500204150340140001d01c40645803002a1000030070007030f8000c50b0118840c090011031560741000410114141000707011081d100c84011070040303000ca0301e50300055070b464108070b840310041c44200d03106011004103151500c0c0705101844417014002d082c1c1e503141d039803559050210100302d0340855008424804602100c1d41600c603401c1c1c1c51202d151481c0c5180f501002da10140601400300034411080890b01d640311340d00c0741d20004100d41c0d1181280b41c801501d00d036410b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 616483156 1250 616481906 616481909
    0x2131415042d0b03040c170a030e090603010b0d0f0303110a0e041e090303050402031c0e090709150207090b040603030509120111040e010e0903090306041e0812090c01031806050a0b19 80
    0x896080000001101f800e0024543e862940c02d540c4803401c008409080111041c0041d00c950f0b4150b48a401c199032560340c400e10080c01c188656601d08000c5010701c1c019081c1c3d40040e41034203d02c0800e101460b4800c0d0400114956004121000100b214110201001001030b01e80743c400b2140c07600025408154041e4041d60266000724200c2d00029045a2030880c0080d00040800008482c5410424207080045200307800c03100a0609040d500e407a40d00b41c0a41040706042000142e01c000010040b200e00352091140c9050180ea09201c040d003152805403451103050340143c06104503030100d22840c1400c0d40010300001070020600c0e9641e0b55001c104082c65404e01402c56606080004104100400002c50f0022031005d00508102d66950320341b00718002d01070700180e2210f081d840309513002550f070a0051030783e80304144d0124506d04280340482d180404468030075040c036107090b013010840c3c6d848400b0350202540c004000310f1150307240c100c07400160000310b5640c0c0c0c22400c5181c04100080c1a140c04c0d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 616484406 1250 616483156 616483169
    0xc100203091b060406050a0c02030a050303070c060c0201090c0329070e030609030909011203030e030d0608060906010506180d12030e0d032702010302131415042d0b03040c 75
    0x2e2240016508200301d41c030442c89000e010a004014928060b030080084101e000d00080c203844004409403280d605542c0304030b4080e00052220300c602400c01c02d0700d1040400c00500f51008100f00402e40d40c1d2003108100314003019201c0506100b103002c401120b0340401131440302ca54120031003402e282d01c01400c0d44c140b0081c803034428004c840004000c25400016248800c4000f011030000e03904e0405c80102143d540241602055161000380c6000c050400040244070b80041c1c00291640c0b402c25614180040a400c1d2515a00414010450340d9a154203803085d103551164500301003101200001c044101056004005c0003400c2400d0745515055440440b05900d001d05882030011010402c604480c0c0304a84410b010b42000d605400b140400807940c7d4060384181001803074221840c600800004483e0300c0084214549035115045040c40440781c20400103020142c1e06103410075081c1802c2d40745002c0c41c0040b452200042d4034215082c2c0a0010050002c514203d59900b031074100a92050014024107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 616485656 1250 616484406 616484443
    0x40315050903190806131503080f0c160302040b1008071d09090607110a08120601032c0c0102030c210909042001091419080d08090607030e0d050c10020309 68
    0x1106c141a20700602840300c000249100103542903135140401d03600708100d12400c010003484a041c11010410000150f10750b81c81060960518520400c801c1e51b0010800071302a04030800c2c500300e050742200142d03401494a082503020000031000c40303400714008404140d4040c0b0701c1018825001d01c0814954041c4105503280001150302c0782540c3e0781e50703142500040507040b04000b03144a088060125a41102052501080301c5402881003034011118100d110030b102c0c2080c02201c200e040070031100884010a00255050109201440d6241d0065480300301c24001d40005550102448004641100e10000c0ca40f000c1c1d811702d41450700744480003208155400d642c0c0781c01c0041940c00740d42c44500321007880b04c80200340602c24042c80f4400c83c006100c0300c0780c402d44003030210300b0a03c20302c41c20359130110715030b9541c101e880c1105c0040d19118014000009040c5403001c18103800b40046191440c8403000d0612958a01c186009140303880300c03003000d25602601c04818400300040100d8103902d240420b480c031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 616486906 1250 616485656 616485679
    0xc151b010b0a091a0a03080703030c090f08100605010f1d270403080c0403020603010315152d030f080307020f0114090f0d08060f1305040606031403040315050903190806 74
    0x11720034035084034000942000300900282e00020f00c03d8000c02c84221041c541600040d50713480140848107401d411081c100c1e08980b8981c10540c502e4414200100404d10b00303032180020302c040c0980101c0514610f403581c07030f50104c05407011f07440d0301640b8401c22481580c1005c07030107040d418061220350181c03000c80c0040d60304e1002c500c0088030741054500703482d001071007285035910b140d440e006501e1004800c000034030f843e01001c0c60790f01e1207410840d005200c4003d0801203003440e00b40c60111020000c41780140300c42d4859090000c20009008400c0341640628100e940342c4a0482c168a4112003103821025982000d0b20a000c407807502c00e045005004100440c0c5504c184c0c0445941c40e070184464020004281d40002411840c0c0700500d00d1a1030005000c905890503480b0303200c420350f03a0484040d9411510f40308100108201c20a1880415241c1c401650600782196694401e40f0346544031049010f0326000070441c000018421114441505504855041045d480c0a07014075401c90380944a242905c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 616488156 1250 616486906 616486909
    0x130c08010e060f0901200301090f06232101060e091c3507080c0c070e0c0c0307030201060e060406050a1502030f04060c050c151b010b0a091a 62
    0x1407154640c03080390107001d850740c400141d2150000c0051400405640f64015100e0000080032509001103a60401756569130515074400c041d0b0b0901000d401c034192078908100011130903a02e0244884103d0b1203651818031400c00040c0185507041659001703000c900c0c51508298005601c180103c0c1d628045601a65907024081611010300d0100d280b401d2016001051003103101321500d10340041c2040c1e0760902d56540c4142d158500e010040c1c05610703440d01d4010300c103400360090b00c0141e11800301c00810b458000e00d40182e6445d005a84100001440c0702c1c2e0118402001001c1a110003141c5041180e481d28601d0400a019140c548544c58020701980d010840700c0c28107004207000d80308045c00c43c00300e203454400600003c0d070000b541241140000d02c0040064450207004200500071982c8158400055040407400c2c002012407440c41784168404840354020100e05950002180076031364a115429640c606001d00b0a03200d02036400095000301094101310b43d0300c014509410a03405082c4000c0110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 616489406 1250 616488156 616488161
    0x1514070207150e0105072d0507030c0806010302150a0302040909150501051203040b09041d0d0207060201051b070c050a121a07020703020d0c0317040914070e010f0201020f03130c0801 80
    0x1243c250005400308400004500c44100c040c401200d510160001860400f0046580c00300400040303815404c101e0b020801d01008001a5000c0c00107400580a954510ba000900c994481c0303c41c60004e41001c101c0030407080c02541543d00812800074180309420184c600190310002c1c056007e40c01510b80b00c0041100d06120f41044d80f204001c0c001903141c2400c00e60080010740101840d1613216845414241c450f803c5160b405040344800750041c0700c84806071a0103818840150405021681f4120130400000303000000c0706e038441c520040c0d443d501d14141c10312151300340b890b40049800071114640012142c0d0320814550707040340510544205500d60085074041c804041e650000103078050b01d018405880e100c0d01843d41c0c0c0d0b1040d955142129542c1c0d84540c0d05030640b215080c0300341c001007401c108014050042c9440c40c1609071040d82d840c60501c201034110b4000f101d0040c10010b200f420030101500035130403600f001180341030781c60302e0780303000080801c90050b04007048500c041e0450300000e40e43d4050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 616490656 1250 616489406 616489427
    0x2180a0e0c031f060306021603020601060302070c05090408120f061509090c03070c0c0f18020915130b2a030301030f0b040f150b0910050a03151407020715 68
    0x80140031000540c0300001c80d040140007100f030710155204000000141e0301d10090080030b410400160707503440c0d1810083d0a02005030700000506004100c10000500102c5c185c100350340048664903c50348072818241c030b56000b0001400000103528041c00072005080032424401e01c2e04540c00d980100c1001c03044035050058154080d004100000450030084015000c0d41d0720410510340340004404a44440014407c154444414006203030403d1081030300a645070510a1383c0400258900500c240101c2c014581c00000ea0040200c0410610320b10301480528400801c5200e68081d01d5420b8006d86000002682c5e1681b011030350b1910442411100103c1501d040360b801c00c3d1441ca42001548901c15400401807003102c4410040a04c01d00182c00d1032801c100c888001580026140640e100f4450701050181c60a155541c842c1410042030382e4028111050707907440907080341e902019408040c060115502c0481401d104e036020007027015400540c8031301310b400c00d0045030601d40c80320303c0640700100c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 616491906 1250 616490656 616490659
    0x703030b19030c090203090c10050310050a050f2b050123041e0c0b0a08040b09011104031104020d0c0c030201050705040b030c1803010f0f060e1303110a02180a0e0c 72
    0x29103010002502141d01a6a0083c2071f803090741d0051107007a0000c0c4402640102d0310700403500110034040c0105818a098019100c141c580007011070912000900e00301e5400300b098403904080e480686454000560400c3d050352246c0440c0c171a6860307260881c040c1c88807800031008034a1a0100545c1c01c80b19644040c001c5400c00701416013450101522200d00c420028291407410030740344000789442d004e0000380340c81d0806a0f5507590504141c90306148001003d0b00814090b03060600401c1c80f00c441100320b404403544a0001ca0f0700042160100300030b03014034649456001d00d07104005030102d03081801240110f00c0303503000708a40d942e80b0350159124055802032071541c2406000041c0c880300b11034020051041103c48150f00c1003213000010b805d60b00e0441081c1519503c1d015081d814035018080c03d40907102d501035442c03680c80c2c00003084114060003c0040c0c00c00400c00d902008159083c000e8501b1150041d01c08482c08004501e01c001a0b0401d54a981070b00b85800407044a84501003200c00c0b69140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 616493156 1250 616491906 616491923
    0x30a12110403140a08181002150a0c0c060501060c0212010c0804030c020d0507060207050a050a18020714030403120f080f180115140909150105060d060305030703030b1903 75
    0x2c646442d100b02041c0659070740700d84190803114002c07a01d040d002e82001e9404500405035403016005125029041101103410b55004622461940c0e000700341c550360010481307400054040541404581d40d01b0100c8001c0c01131031500d40045030066001c5544074140d07000340d90610000c0c400c00aa070742201c010310a5840010640300106001a2080c96203240c00b90008041f1040202e5545031a420543c199000c0000341c0c0c0700040801c01c03410040f0042004100803500e4541c0c0610b0100e41e508482040710304002c0c5580d0006151080214018210030a04c214030100ca86954992800070561107140d1052030104003044c5900b00010320541e2580c0c41442d142910f1540c43c0c43c2c05005000450107407500c1c030140e549519000350680d03c100c02c650014140f0907182007112115000b401a000c1c0c014041184940044100054007018001c101d0f044480548405544602a40c04000244141c0c3c00003170180c0400075100c0d040c140d040e00051340c10b101c00c9514aa4409244182402c0340d0006d2000034000070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 616494406 1250 616493156 616493159
    0x110c01201204060513050303070206070230070804080703080a03060e01030201021c030609091a01330203120c090301050c19050c0f150a0e01200327030a121104 70
    0x240306030421500175543e01e01440100c0c8007580c51600f0f5400440341c040060744180200542c2580c10800d0900c11380e00040c03804410400054815001d601080000384007080000b80c4000b002583c07000c441c024059041910718407a180c0c648100706501809102e0006807d16501040c0c42d8103021203141202d905800411a003a02c80c00b146ca80d020200d15540c081c585d45240000b40380989006803e41035102e0800003507000020080d900e154041031300714007080d8170140550302c46152038154800200085045d90485400d10320402c91940c03203a1021744451030800c0c03082c40707011100d4101038104081c01314001d204654402105054500a403245940c01c06400c275030340851113014800408558210794165076100c00d410424030b141400700310345182810409020064a0207461060440c0d1822a40081c0404801d41151f0841c085106103840551803000000c0b9544203102c00340e0030429840c29400e64050304502c824030f43ca03034202403c0100812407110f003940c0360614074171940f00c1d1056000081d6042a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 616495656 1250 616494406 616494413
    0x60f0702151f0b13030303150303080601050d090606060905030f0604030509010324120312050603030301090218030105010b04210213050408120f01140f09070e0103110c01201204 78
    0x40000329003040301100100c00810b00030300843c010714a504d00d40c003c042c046455440c009084814650407440e03000300d40e16045c0002540702106a42083d800d10301103464110032300b013210062018400013042d0070b2520000080c1903821600b140d0846038101c007035030a00034041140700d440d00e01c101c40040001d04100485504e0350300030f80c80595600401e040c1e50b4031384180e8042242030000c1c65005042001d0820007070008041c0d00c002054812490118240268145440800c1d44ca02041c00b81e81c20359a00450f0100d0f00251404100c040b15900030024841941c0d50728800b80907500038010415203405a1103412041558420002c10540d40a4000815111000f0f0360300c000f02009002100e03a0481000381c45000c6147d040e040f400383d20259460340aa51400341c0d0f088a0310707002c1420b1400b6801140c4e507a9132a5813020400c0764404198100411059002c400490080007507480030003034403001007044040c8510542c042010384040c006803002c0d03418840034040250007221030407007098038001e0005002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 616496906 1250 616495656 616495681
    0x12030c020606060c19050309040b030d08010603020f070b1503060709060c0624030809030c04050702060f040201270e060a080307060c03021c021e0310030b06030a06060602060f070215 80
    0x41600c402503512141d255030345c40044085c981c0003034a041e8404034002c001807500b0b101c5c1303442d2110200c004003030903c208000540700c1c24052203008217265000c180702003607a1091040782c01c00c0342c1c0115207411914040c12850341000c1c044d002030340a440b5640004000318069914441035031620745a1a0708140750355206c101412070b20303003100040040400c0d44411007002402e0100039620a4140940341e2500384289464001418030701031103142001c091107102d5801164113600400c9500342c004055440c0d0006803002610507240900008050704000c002c42441c070704600649001d5540000c1d00d4440c0e030104810b00005001d9514180c00401003500060510b60090501b140a424050704080110401d20022549018a134940980010b400c02000e07c80040005503115440e4815041d8148200000c80840b0517000c000e040e03000340070128800366420400c001c0441d42c805030502c0010745901c002502d484058a21080da50b01f0fa04c0800c11050020035225022210541d1010647c1d4815015004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 616498156 1250 616496906 616496917
    0xd0e0103060f180e01020406021f060f090213180b010813053313140105010605090409080f030702010e1b030d0e01030b040c0206011e12020103111b0a12030c02060606 73
    0x440303a6135505104503c04081c0080c10003413189801520802c400e01c0c180c00080890304130b100c00c44038035108061102001d0b401d010000d84280390700050320394400d43d0821103004a280c1045e6101e500c149865220030b07010360401160076100380c0c0e81d070700030380c4035012003030411501c0103002070080e00001e01452441c8800e01c2030002941085101e00b25218a00300e0310740c94518151800e40389401e48040060601a4a0300340c001020700000c02040558540203006069008000f5210b100e5038450420405100d250410303504400c90391112541e8a0800000c064003c00c030303200407805140070380000c0308000c100314441c400b00d5000150141c0b90396001d4660072030310b00402c003012605155451003880300580300e921850a83e801c00b80c00810895040804c08400044c041003502007804c20a04d040c030035500c03200c40c140707126542030030003150315070780d208519000b0b008207002d03404066000c00111031000800104c546841d40110b8202800100f1500e081b002e071002c8007442c0015902c43e001140381420810300405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 616499406 1250 616498156 616498199
    0x8010510030308060a12230d1e1205010e0115080421090b030711011d0c0d0201090e0c041410050711360618070c0303021204050d0e0103060f 62
    0x14280d403104d240407071b280320340501039481c0001d40c070141a10303402d5aa160820802944001c101d481031590340101402c0d140440c0c0030000120700310905006014803484001401c02e01e009100940e100d070300c0380c408450244a0031420f98500c0d160341441c10300800c02c441c0501c0d0840500c1809031070b280e112101304010340030150308100794a40001414260400a03500400340c0b030ba1801c0703c2d441c0c4458440c3c00d542d242030580d22019014810785008a50000b450214400c00303a42009004000740010380b05005980d10a070080010f01d000c100c0112503c4000f8030507145810460030051302214184084044a000841c002c0340040042c0c1011514410000d411140018051451544003501c100782140540b135104014a0b82581185c003003c1c01d00b252031380d011605035142c480058844184022090380a00034a00348840d0070300c224107062083e0107c5040b0700d4500c556241a041610300566200e83c40c8443c00000707151120720740304540c440e004032030032165500c14001d42a8102a81c12450300c61403d1001e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 616500656 1250 616499406 616499419
    0xb04030b04110a0323060702070b0a0305101a04150903023d0c020906104d0d03200901020a05070e0f0a140a050910050108010606090801051003030806 66
    0x51445e50841d000310490b1007015020800705010540b80c56400b610040035908146020312030049400295035281240b444c01055584070551901d03146040c941058450b4091b400240c120314071014014800c43c2c80d02c05140d00c0c0080c158404444590060100030740c014100400c081e2031940364812110346210341c450402459078260413451714440740442c40c8001c00c00b50f903030f40e80c01e61605126441d4000400c4e10715000c0b020703003008000e101c00000414030450040031040c0100d20601440800c0030710928010003000c03060105089040d4100c00480f070511032144c001240300d40780c40b9024955412305510070050801c51415a0400c481d0800300345541188100d16610010440c2044420b00410309620000e1280c24150401840c01d20700034110030b48a8108006002e0308070440e58038960040c5120700000d160f881c0c0c2140705060011100c21503284a040c10004601c22506601030b204544140c0c072103450b81c5903903104250036281d0071a036141c00c96661b01c50420109024070b02031640701da0000c202 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 616501906 1250 616500656 616500659
    0x24090d0f050c06150406050a1508070c05030a0504171603030509180a0b04060506070c050405041502070b0f07030b03031804020c07030609050c0f031b27100b04030b04110a 75
    0x81030b1801c441200d083c03004100051a00151703041c28450200980425180e14070582d040c007100348103085404079004200101d410001e80068440c100390500203032301c48103503a920342602c1303030051140d0040d0090581e160a10043d0384142800020415050003081e07000000d00303851620103640940020f0303d420b070043d00b0300b219104500707100200584140c10403400010500807000505c011280c8030780055001d408100249004624103071040000c4440071140451242c1d220700d0620413680030480c040c3c183c9400030804804005065032901d106002008a0410039030b540c0000b14143c8045c0e0b100f49130140c00c1001800395804010030700e00003400c8003600c09403030f010920240900e045038583c000c2c0d07085a56956240d003044418003000104800484582001003002000603031541c100100b4a5101055001240c9460b01d17202030480094100c0c401c00781c050b440c0701140c01c60350b450480b4292100000c1d0800410920307040c109840070340b5081031702160203581d943d891140450640342c000c3d03800042281d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 616503156 1250 616501906 616501927
    0xc050408100e16031e0c030f030f02010c0e06040e060604030203070b0304061109060d0203090f160612110318070e04080703030f1103240a0824090d0f05 67
    0x20000c5440c1c1001501040b014101818543c02440654828084400c20004108109180810740c0340b20100d40068a980703150041c074010241d44000c3c00c0600c01c0c4283c0d4141034010142c020070003c5900288110101c1c00300480d081d00340a448241c4c841000d00090081002c080051035000d280030300300a00c1e141d02d0b9000240350800e154005a0031040000400c02000320074001c083c0c901403540308041c2403d4003240000c600d40500241000007650201c001000e06204028040301c41c82007205035a80850032500141c900c6141c0e01800340030801c00b52440403403a8140c41500318034906d00f0f5801d4110303124481e500202d00c00c69110040c4034419100003041000d40071140c036005a1080343d901d640c0f910140f030090b00350b800702803240301a1458100740105910718202142e40c402c89086800b4415502c48803101d80030364189030100d4120036001c1000c9410701e40042c080382003120880313400e07660741c480003081c16401a04944c44602904007850044040c0d01689048540c052141000d60411140c1e05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 616504406 1250 616503156 616503163
    0x90f0115120b0d0c170a02060d0f1e02041a0f16051f0501051e03060114042301030201020f0d0f0f12050a0b270f060406030c0b0c0601050a1202040c050408 68
    0x84d6032028000008109070810417207188030580c20760015011400641d0001a841d014940d000c0710b0340ba0b154841e00c0c0072110107511408155030714001a6016140c01e0b03103100001e42040c018110f1034103903581412402281501a200403281002c0010f203407082028030008030030303820300c01101c1d1840384d848007206e4807094001012154195840014903585031004001c3c00b1080904510020301d0850100c00e00358402150b01419032300d126488800d4441c110022900504100c0d0f154000d0700d06040c140e1094001b0101250304a0b4001d900300c808103440041e40c1600d035407202600c50042100c1c1010b03580281c0c010307903000c0305214203400c0151846100c03180d40302c10b4600031900c0d0418281e4072201241d0500d0070f103d040349880502c0d8448110b07442c070603203620825500138000d212940e2100c0001000365031396030002405075a202320940e83c0680e603150036060580003940c5611550145800100c0c1605011101c0f0040f11981d0301025402100d54091000800302e0003100b1040040030400801c40b044100b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 616505656 1250 616504406 616504429
    0x40807080903030c0f0115050915120a0c03020301060501110303040609030309021011060108030c071403241911040e040204090209070512091b10110d030b090f0115120b 74
    0x207202400e200d05140300034a0840b02e0b4200e81c00c8208441f10014492a1621008650310441903c6140145c12800001440e40d1041030f080030300c01e2048640d084104140c02c0c91520450b4406d9000303204003a1610010743351404071030f0f40c2a161307500900004011404c82e411100020740682000a802c01a980100f4114000c86461002084203001c0000e61200b00b040360900400b0020302450420f034884500316291112882402244024031007100484e0307034140030071406040c0090203080c0354840e0709005000c10749c080300c52004640c9810011845596a8016401207244910603640341a04244161030007400240003a80c000703540c0c450150041e100c11200c0d07405a1070135151141c84140f54102e022541e0030040901c0b01c10340001f22803015142c01c4085004002c04210741d03424254804601c219140c8414044100c481e204400b40e0070304030354160340b110b001c88005840c001082e0341d40700303d90740c4041c2c028070a07100103d0307010405644140c401c0801200100f540c20b804245051400c00266001c6002e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 616506906 1250 616505656 616505677
    0x31009020f0403110d050303070c02120d11070f050906100e040504060519020c060412050c010216020109121a100302032a090115050304110613030201091d04080708090303 75
    0x42c148103001c00c0705460f618520701200c2078041958142c4d02c0b2901d80c04040c02880901c070800102000b103640305032020800780300c5441200c0600e10100c4004026070354200d60b0921b0360107200404607c00c89260900c1042c2c1b9809842210700e5102c1c0818070a902c410b6105040c06c0118031004205030356114016a805907010f088003140300c2c24024113601c2001e1643e54034444403841040340c540c00003030105440d80d000d50040c24000c002802d940c010741b01441036440e508599440000c4a519890300708140701002070007039079401d101540340d84202034101a40b070b10141c1510544140c0144068610002d143d00501c2205807002d00c1e0768030313404285005aa000e4100d85883d0005900706000c154541181480008079480402545010708a982c800c28101145040190010000b824400c203001459800a0302a0004e43d1f6503e000103071000701c8840340403c82c0012158074001401c04030b00c1d81c0d4440e4150a4500a4001da1143d42c0d400343c1070340c020502201c0c141000d011043c0142e50500141501d400f2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 616508156 1250 616506906 616506937
    0x705070509060d260c03071a100b030a05100b0d05011d07080705130e040b251d0f1507051903050a0e04060305100903020c030604050d0503100902 64
    0x5140c20010045401403070680940b22001410003c18600401c03da603c0d5500044080003142c888004112072080a07074070315503440001880300400c40210068900582d080d811902e841d02e0f6840300400f03c08440c860400d824005001203030440b00c091340240c2c2c0001580715010450703035941c544110150403d082c208100c80d03840004210b4850424940c01e80d5000d4100d021000346420030700904804c5020700104c0400c80702041c1071501c80205403107517011340105c0910740e499181620f03100c00820b82c100e401c01e070340110310000c000c80368007100008041148140c41e91200381c03400c1007207118101c2070b8440155022740d5200c80f0105546400d609500e00105000d505656000c141c10b01628207280010101c840c960021921404a42d10000766000c6011510b4030304100500b034000100945041c4c0c0004e4624050381103101050303051580100750f454400d0302900d03a0071040c40308041d2100700403240508207070810380341c004500303110b6001154000702030900d080c074141e00d48190303008070381181114660545 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 616509406 1250 616508156 616508159
    0x31506053c041b091a04060f090308030c0c1b0a0501120f0203271b01080901140901020a032706050c0f04030303140f190f0f150312020d021b040e03070507 68
    0x3036204e107140014001040785c00d03c061504070015030580c4158132070b0f60300700488040d00b0f801982c482c241e042c00960300511540e40383e0070045490f1807039a209814181c0d80307208280e401048110700341ca41c280a0f203001010f40c0109490500150780f08044080308000143d904c0641c50f45480e82d5202950054180100c00081c80044480807a80a03981102049007544032083e030341d03078a091950146134031020a180c0100706454104c150b03070240280e628240f038000055401c021602c0700540c040c1041d0751590f5000e02984d0420040400d54034000300c082c0c6416115101c010001c5401900600c1d088801c0c21318880c50200810341c140c081d904aa00201c000a8964a001d24070440051000b90811001c0340c41e4055410000050607266803042d814105c5c00c0c0c0c56444c890584021035100c58484505400c0074419100641d0ba000060702d407a00085980c5500d108006014034070000321401400010740081040000d901e0141e07440400c00c011465225444040200981c0002d002408405100d40010442c8a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 616510656 1250 616509406 616509461
    0xe0906090910020d091109010b090409110409030c020f0604060915090806010303080613020a05031303090b042603120406020304111305100e0601090909080d06031506053c04 76
    0x481c171030300e684a411f1020051003401c034aa4103c9204410071100003802004925120080d10140c000c8240c0c052f28000900080c1031b00000b00610040c401c5910103d001c0e00b88080025034051401660b00007030f00d00c0d505000a00c01800c41d921101910b00304407026039500d4415901d06a000d810031000525030b101403146600340704080d101440c601042c02e40c107284140100610500004004881001e9018031080500d8000c00100c0090003816400540d1035841310104410482d6560316507842c4003480c68000c10340c4a0202c150742480d41944092402c2d41ca841e16400b000e034101a1094540940140c845003407135442c030140700400c61251001180ca0b281c02000305464a0030703035004001c00282c080401031280c3e804503500050390f0341e0300d200040c0038000c0d0612180390b010b00b28100104030f00d000d80c04401d0029482450529100400c41070204980345c2d02403142c1c0c100714807055840340b907101e210032001407600241c05c0c0110203400c4145072034401c034000060581c2c4d082040d28007032901848107000c0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 616511906 1250 616510656 616510673
    0x32f280f02010506100e040e030a020c0a0f1514090607030c02190303050301060c03030605060714121e180d030e15041206150b0c0d0801060e0906090910020d09 70
    0x100040c0001c03c0700d440c3c448003040034450799010500821841138000850390740c4d1940400700d425250b804990300c130300743d800020355501f040d07151403449010301110008104895001420544a4224500c01c1907200d407241500c05c42515074050040e00320034403403904c45444050260208078003d5442c980c0900950050004050014251888a9415540030310210b5045402c07241103607590326280c4601a00750404800600007900031a500c1440010150184085082002d0051a03920300780c1d10210210840944103100e050950100490380400000840e00008007030410492001402107103144808001045810106c80443c0421516210400542440ca0321040c82c103800c40141864607080201001c00101e51000003000f42d03850700d2408000c1280d6003842001000c0e1174100b142c81c0c0704000f81130340e1904402c0911800040f980000064828840c41041c0c40d0900094a00b8482c1d4885405010101400525074a840d1195141c1544441014801840030503008800000d01c8003840c41d00c400d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 616513156 1250 616511906 616511927
    0x8120406050117060c09010201060f0b071205040810090c15110609150612150f01030302060705040506070f02030102091c0507090b060415140403050d0f032f28 70
    0x8032030740d520300502900000180e003900040c120343c485d41c0303d0066400403409850310360882c040000d503a8038000352070702e410001fa162032032180c0b544008410110340102c07418041c0c0d2240405941c4541c80c83ca0392060280d000102190140e001416825198440a10007041e00c0d8080f1001800c215014801003c0511400350841c130100050f240b50b28010080c07050045c4080c140354802c075030f40c2c0c01d0300c01c51950070005031100c6007a68131240d2403071030440d80181440ba001d02c010fa000d80600c4000800c1c3d07500ca141141c00382c80b0002c0c080790a0101c5501c2e04588818443c00c101d030103643c02c12202280e40d5900004409500790307504141c0f414a29850312608281e0070394808003103175003080f10b0106c040d502c50302139809989001c0c004400c2102903a10440341c00185250f0a08920000500030080c001c0119540440a04a4481010f02d06080e181101213035500c110044c0c1507d14108a5040900c034bc900125110080351003203800c0084041c07541c030301d56024030750850100403d046101d0007aa0007450703290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 616514406 1250 616513156 616513169
    0x91b0a0e0705130b0c120d0e01061502160b070b090708120d06120c0b0708090d0b0115020d090b16080c010b180421031e1d1f18081204060501 62
    0x500304076280f13840d2a03a9540e00004d0081b840b4000c03c501071030303d44907807102c007003a9203d900a201584d41c0d400e400064495004114006001e80242489196944c079000002c4400241e6580c0c54010030340c4405990003000782a004260080b1100040d42c042d04110f00e280c200c0d040d40e5902e94074546c00036040c0454509a000398242500501d0b5036001c0b5911034038603070031940c64600690f503030801843c1c1800c0d5840f5582005610a1021034280140094600c80701e05861041c0000f0750241080142640d482c4044c084007c00a02545c000b480080b81660180201100b101c414481090303050b925580e0b2608152499081c1c0da6481d8503140440c640344a00e02070700c3c1d82d4a0000515410300751642280c000c1c3d0801031030034143c0e1061200340b0b058802c0d400044800d8141c00005052030031030b120032010f48881c00d1550f0380328242000c801400f880c04160710b00c441d5001d810182c8401070003507914016044105084089100c1807101c100418902e030700030003425040c2800b03617481c4d2900b0b10b0304c00d0464206803c0076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 616515656 1250 616514406 616514429
    0x30606020f0a14030f04060801090e0a050d050a021905010f0501060c150b01051605010c1e0509240a030507020613050a0f110315011409091b0a0e070513 67
    0x155825500441c1e0b1811079500140c2903c0440c0340744004515622500441d07806944000a000031581e5000008505a980c44034092005000b100b81031603461401c48800f40850b00b1900b000d00c86c0340c0c02070006119815180c0192240c81c0d244d41084ea86106d0b0160301513403584d45540324041181c002d4454640540070301e05080001c0c0d103d0b41c941081082104851030345460348c6420042c450780c0030b101aa1000b481d91640141c0030340351458614040c3c25413258610106020b480760701441c91511889404400c0c0d40c0e92850b09012210080020f80b032401c4107084401c6182040740c0182955071002071050300d1807600d02090324103060b2802480c064000701551079000e8102c20752000100007080c03c0354080d4219480920340e00860405030f0031405007210382e07603041c450740c2106a038012409040c01d04950f040307541d250311184501c050009483d821546100d054101241c0700889000501201c0c00c200c41c0038147c1c112a980b02c48403401028002c1e245000801d02c0803808500791035a80840300060a40400322 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 616516906 1250 616515656 616515673
    0x211e041407170c0409081e2b0b0402090607020906060c0a052109060a180801020c15060d020303040e04060e0d0332010b0d0b0907090f0f05090411010c0b011503060602 73
    0x40b0b030100d00604404055048100f00301050b00000d40302551000308d042081c0c7e040c00c181c4082031080d02c50300d0458000c0200d0810032900811703d4103209a400d0305c6070242040c5e14080729503080054200c0c00410726948540140601c00308070804006d0980c2407486413004046170950346600200110840c8490900110200708030101903d4260035140c1000c030a007080117a0740000120340060594541205171198404544101011030004a200d8003103880d0304a80c207552140802e01c560310b20382c120041d4060b441040200030700f80800380d0141d4064090440094101c2420507014100590302001c540000c0c3c03600500f10fa1001c0c1411024084070f24001405520790303e95003503515142c014811550070050214040000c0140384d040003c0a1800505c20b820b1407900010240c0300c83c0180c094001c40b00e00d007203000f0840c0000620718600f600e1008000154039911544d4201505c601034400c241040305206040c0c0c0055000c01c0418060419202c54001121801038003d04488882d4004021588003044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 616518156 1250 616516906 616516913
    0x3030e1201061a09030a020d05061801021e0c03041a0406110f06040b060a1d090601211b0b0c010b010206070f080f07030e030a05211e041407170c0409 66
    0x540f10444602110710b03100d0321003800003414004069400380d0083c50f2111003404228000c0340483c800c04800c1070705810503501850250807030040c5403860000c1c480544004800d142d40d030300981060007102044034a040c2c0c0307072a0071100c5291051100c032014800410107001e01030300710a902000e2004003006000c40ca801c440035030f545a40140c4080c0a00d40c2c410046a003036182c06a00901a0a0036006101074513140356400302d642004079a80087e50290000104050628038031b50361810b100440b90062091464907100c00140b080300c160b4200303032008480000c0f03080500010b400c8070100d8100003c7c00c0d4452000285c2403042c0104150100300c23031080d820b1700d069001903803603410410690424040d0303500d592081d80102941d41a01e0001e00c00820001a032683c060001c041c004000b28040113100305280b401106040152545d1412460b4010010000c42407910312070b90041c0590f030300740d034a0b46c0142c1c4010700b000d80769001304c60007103041d0110b901c2100c000c0200c0035180d501034404005143c0c8549 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 616519406 1250 616518156 616518179
    0x305040504050109020a20011d0a020f09330423070302030903040b0c0c04090f0314040f170a060606050a090e0f060d0c0305010c121b020c220603030e120106 69
    0xa420240f0036922803801c2d1f1200003d610800c0c90b164040141d150784405480c05958075546644105d1040415560417852402c0061015003c2c40250207000030940031114582c48203001034110081141c00041c80c04015034440c0a8400345114440340c1c440c20121ba240c0480340440010708d0041031500400500c15001c00000032101250102c41d0341d580c0320641d211240d03040122412003070b540b041c01d219001060024880c2c0618809100e9110f4040c901d40103034114030a0701036813240c4810003d42e49010044104000034a8000d80d0120007135443c900480e60381d00c0304460303154008200103a8040b940101650b0001c625a01030603442700401c1d01850b00007454903100800420315030241021195000402c00c0c440100c2001d564050000e010011645600515101c2241080202e407410940c541025001c1101170441c124001d501900f00e403628441403001c0b1103c0b03006048070203034014000072918a0b0921524002e14442c0c2e40310b0b800c1c000008100320111100c0f00008105900d040d4080043c4203105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 616520656 1250 616519406 616519427
    0x306020c0c0a14061e040b04062c0114090d0507051519031e09060902010806040e0d260a060609050303030c070201030f02270118050f0613120305040504050109020a 72
    0x80b1a4195103041c002c480c4a000881c002212440a80208011403160787d000301903c03d55801d0350301e42080300c141d5540500110407000014003608807012694450703512400081c41090400a030003887d02c1c14480104074581c2040c80b007914560407090050016181c100d8440e020144c4d1202810304100c072000c07004109804180b6040f05060b5111000850354024034641501e40031f01e046c0400c0080c00c00d041c5280600b40003101280000c89007000601d26140a20441d14640308040040015400001056a0001e0f2155a52441203002007503030b105c0e02c03000946070b440f4011228012401718605600649980020703084240319410910400250380100d8040d074021640902e004a0075001c2480350344000c7c49482c4900b2182c0c40e010714a100c00381c2608035094100c41007a80c1d00902c0c90f01d8031030984020280c1c0c6c0201540410031181c0f44a81d458050050405804a10200b890720343d03540f401d90171682e102c0f18003103010840210301004207141611440e401403171000400c0d49001e000709001040610300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 616521906 1250 616520656 616520659
    0x5030304081513020a0609030203060a090503031305030f071b0f081c05250309090e030405060d0f0c02211305130f02041403010f0c020c1e03070306020c0c0a14 70
    0x7000015031004890f00c4407082c040d40203010030300c5194550710010035103015400305900038800c4001040102c030551281303c0c1c6094002c000345003541ca0302da803104201c402043c001d840c18030080c450082041000b1006003000c5200b800c25002c0c0f1080300014200c041c08550000f4107002c01e06904010030b94000c220b10910a08488101e064a0024101618035014a2032400840c01010840305800d0040640a00307000740030341c0301c85c000d25603582240019078003450168846908184002c200d241010800350490402c0741002080100608000b40200c598a0043c0001070340080303040701801e8000001600252182d50341c035071030003d0001120a4a00c0a40b00b0280240b100e0080402114443d911213400d201c055481956210360741c030f1b4910400010000202d1095280070300042000c100c03403064000c40c0c00ca81d00903100b072040641c1000851840c60320802c6901e090300085003440c0c0e400344110381c081d62003260016103d151030400c240c90210625400c40c0608144501070004034108800b1000c940c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 616523156 1250 616521906 616521943
    0xa0504110a080c0c070f08010b0f0102030f0a11190b130201020a0f0f0c06030608010b030c1507170a1715180703020f07050f0c0a18020a0c150f060503030408 69
    0x140c5043c41c00341c42c41038414140780d500070140c002c16072160001d419402c032079110009100d140781e020100140c412244080a016900400410800c40b00b00000340c030002c080350528100c1444068255420302040d004090421b40720310203010208030350b00c400030740c105003141c941e400640e8550f80040d559040300e0324050804048600d0740c100304540300300f040920550002c1d440000c00d0751000090046e00072409403400039404c110b184403050900050884422034001c01d0803100c040c1502d414003465000010566240005808990350240750704000d045800c003690761150403181942c1615081d840c094141441c0d40c1120380541000e559002a030581005000041d0101d5181c400041e002071041c0b000b55441000302160b1802400780200313008401928801c2942d0700e01422a08108000c8080d003c0c66030802680440310705401e5907a8050070342940a03081490f40c5050076141d803601d440501c4c41414580f901c802c12080c1505c0ba50007144002c010540c01107082508000e0b0054a600588c255001c0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 616524406 1250 616523156 616523161
    0xe0129090d0213020d0c09050301021c0c0c08040f051305071e0905030d0c06050c030112060902010228021003051302062a03070308131e03020106030b0c090a0504110a08 74
    0x1038514500303140f505503030710045540d07400d0181202d001d40004e0381b144d4040f5103c2c40f400540345c00c040c0210345038144000c400840052071040144014158078003004c04009241140900081100c0c0c0104003a00c001c1c07030294900c91500040290003030a4030340580703800b4103102c18000450703081000c6c0b001508014102090125503d0b400b02d5142100790f2140360300d03100700784c0d0803403420303401c6103c1c81c0750940200001d00c02643e803240c68071000c5c0300c00e1090805203803603062140d010404550191040034414030588200120454a4059102c1104851129800c000c084c0200718a0000e01d0300395141081c0c2418401880c4c1201100345901111001900411002901148101d0b990007c1d56441c3c6a0001e02210000d40c200407562303039041620200c0106041101241e2088240071407424540e51019404031440540c01b5032414004407400110195902d950020001030070140803d4420b4603200385186d19501d090041021091031036218034051480c114104208844c207034201c0c0c03071041c1e090414500c1b98 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 616525656 1250 616524406 616524409
    0xa0327051e01121d010b0603043311032d0114060906041e0603180303020d0e3f09060a0504080d0206060901060e010c12180e0129090d02 60
    0x10b0301c00503d0314001c601e410103068003501c3e20f004600d003002c0c40000030420444100c0a21080b0720083e134010b40f0a220100c00001c04100b09031802c901304481d05003147c10024000800c0050b40e4403c20303051503103030000c01003045452840b00520b20410005042743c60001011201ea084003030103020b214403034020466198a1038030b4010072501200406402c440c1d0311640d92031404072300702440440502c04081d03100d0001d0114401d0250b2201144440e000c1e200001066030140c000350b101590500c0981c1d21405980a0364005000e11003811601145041164042c4084142c001c038160941910f07040e412000240d002c0690410751b03194107004e03101c0c2c59071060035000554140c092940a0180345c46449002d141c6994007043c064007c9009840000180e43c0b034000598a0004065002d40055103200810740070448490310701800c1c0d070720307420b00d1806c1120105406880c1c0e50f10740c000851542281d0010000351901310140c10300c40c00c1844800112401204002003c0d2080d6042c0c54402e03801070b619503056 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 616526906 1250 616525656 616525667
    0x30411010e0a120606030308090307170304020a030f05070609090606091202150307110d030b030d0f090b043f1502040f08060601031410060305040809030a0327051e01 73
    0x151044101c940010740c1103280010117002180030840006100d50042269584004159018168088111310000d408001003407110b070401002a64000380380d00001022071414104088503602a9000d48451030802801a0a080b050b0f480484034602d800802c10001e58802044019540f82a2000c109034a090001940c016800c1c0c2842c0240000003040c4501c017904a41c602044c1c041500944007104808841502180d55604041c0d8142e0001c00c0940081072148452080d0040142004110141c6404500810781c000390008804900b52034110401c00c00514090100c80d0181c00c007280b41101d1090542c0c000c034004450050103104c00d080000d21411a64050781d0180400340364040e8400c0d9a640501d641ea00c0c10303200e203404030345041c3c0c0016100e404140c0d131500c5000341004c16214685001c00c1100100360061007501c01450501a80002d81d40c14002040024004d944032440e28105041c1c2e1128140f0306031001d00800e0490000f08066128400380901300441414180c21031400701005896 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 616528156 1250 616526906 616526909
    0x10c0209090a05030a0f030f0204050913060e1b0a0e04080403260f0a0f02070b0306150f0703080711070608040b090c13050a0606030b0604092003012603030411010e0a 73
    0x1c0c0c4c040403418540c0c175588502451032403183c6036004d10507440e80003d80b400324451409501d400c50304200000d0300f0155418103541d110340c4103500001d0a0500780c00c0f42c82c2009003034007142141318a0444040111b2034070344008000391a00b80702c1140c080c101592004450710440c8001044140741d404000e15000c102d00c5a54032506459944076540c0700005001ca665a000c00d107481c000c500c04040e403000961001540c1000d84503a03030303003080c5581c90306420005040307080030740c1c000346400400050154440301c401030801544281c0724080141030414024284469088003070742c803030740003d45c2008165848207005030400d40040c0250040d480302c1c804c4030704168525950b140c0000f000b20900300c0403003213603000f180b150800744420482240c07511000c40544001025195000906000904c15403c160340181e0081240f170614600010851b280d000180d0000d82c00a80190403184660341c0d4a40d20f400350b8250000f00001031841d62419a49500c15103034540764090410400707407102c3c40c054444481020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 616529406 1250 616528156 616528163
    0x902060c06070804020a08010213031b090f0501031208071202160b090a0b0603070506120a0b150304020f0105070f03030c0513030b061f0f03110d1a03011a010c0209090a 74
    0x20540d10b84044003505941d07081c0d4040f40111060100024144410f2007543c1c0038510005c0141d404500c1c2d0780319030b0315120007020f10b1103209030070003000900702026102ea800240f4200c81c002c04d4070740c51800c1c2030410113240350301e420511600408008800e0351055660f098240038040c010789819240d054000540d4412000401c940d5801080c0288250000344803a00b8511610740c16100341d40300380a26807034031300500c83c1c0e0390091f07410b200c551600b075280d0501c035038441e01d20180080c000480c0c0000500e40c03a08168000f8452000105020070f5007480140550b40e03180070f0800c2854007031180e0395100c2c1036001210140406940d540c02c0c1700d459105400715547c0301d0101c0002655951a400c050900c140240c40c42445500c1c07495150501d0f035001e94010101129a0b203030a420b01d04901002e030083c010550303203810b0b102420042e40802e0400d5100e60103841901c0300403482d04c0200c4100b45421a0280c08201d4140d51940c040200305a074001c0e84000800d80c10341d107422203502d4042ca60f6261940c49030004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 616530656 1250 616529406 616529413
    0x5071a010909051615030e010f051312090e06040506011101110a020708060f0c0c0f0a06140a0506030c0d02030109120c030207091506030207110a08013201090902060c 73
    0x4040c181504007521a034001d030140ca00507410410754814211451040320217a0f05400c1da10100c450281d8401303040c7c01039071000401c04a0121a600d41104d104403025030783c40c1040101c450030310008607040302c0c00b40f409080849040d400d01c00d107060f00300002044988100c0d02c0e000096245e0348998a2100d0b101c84a400030b12106003800d140d16080d4205094950040c40341100003c1d0129001400601529201c061035450351142d42045559070701c10f03031846130303248145040c00e00110420025902c2c514003070701e0002900003040c54004602003000e0088483c2c141890240001030b40c01007401c48407040f046424200512640c8040f902410103884c000c0c0104442d50036851000d5080491003040d103220380d0942c1d12594039034006008503910884280390600100d0002d02c100c500035030082c07501038085c1c003480783c504024000090503c841500021200d0351940521100c1440071306071441650003103000802e0100c0c100d0605079110005100d42e00c003280c2c903545058103640740c62080b031f98a004140d09a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 616531906 1250 616530656 616530659
    0x30406111603050418091a040c0308030f010609080a021f030b06040806100501050c06060d030c0609140106050103020a020c040213030c060c0b060603070e150d02040f1a0909040305071a01 82
    0xf81c00c94002d44a0511004440c5004921010f218440c11281c0d0340d11040d4650020018160034120510040046900030f0b99240d010020030308007006144504000400c501d110340c1171501c02000c90f903007688905640d6015800510050b41d0ba1007000039003444488240c17151254120080b0050161100b1107a0450300001303000c40c40c410082012446003040c0c1424030a025500c0700111005c0c8642c42d407150840e0042c0010804607d401c0c02d05608060003031a08045111454480004941410000722402c820450a0203402c00c002e016110082101b42800c40c140140114003a442d0302c0300320140c1e4415540060104c8190b020303408418040d50704102e400f46850703200e050141518507544d00588030400c0040c009825031500a044903c9010b540c1c0e1050307980356480301440f95070401851040030700e40c000d2003551035050091014000a000415001110901d0042c0f030805114811208400c0307448200941505070f11a5052107401c2079051601310b03692038940c180b541c103400b00c406128140326202d000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 616533156 1250 616531906 616531913
    0x11060408070806150901090b0f150c011a180a0e120d051f06050711040c02010b0108131e0f06060311130b030706030c05071202030406091a0304061116 66
    0x107038401610040021681c082c0c44110002c018010f943c0031682e407000c040c1006011000ca65000080b40e40406003525002c1001c1c0000034415a400350780f03044107100702091542000d0380034011514992f01817603140d428100e49001242185d208444050f0004d080030020039500c100580c41180284086003d85060000c1011070041d254860201c1400b00d5040802041e5411941403102ca10340c21110314482c84113103444004c3c1c41a030003548040c3d0701d00036980d4424825071074a000b010002c0509a00001c0e4215181c00090104840640703010041103000b0342c00300001c0d01c1c1d00000940941505007103041d50125240950204c050703070340002e0500341840000020041c15005010306034001702c2d0500044500d50f9203020440d4458241075601d940440010099203000394490000054185072440c540105131715400619120070703400c0310043c0c0c17001808001d4680c1c803810020140c410024820003902207002d1406550001400160203c2d41c5d070014050000c089174205c92555648845a0b91401118113 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 616534406 1250 616533156 616533163
    0x50d0b010c050a12140406020a0f020301020d1d10020c06060f030f010207200612070f050904050c120c04080d05030709030b090601061202090102060406090501020903150403021c1b11060408 83
    0x30800c2000c10000c0d914802d611709088150340586980354010980e2600548845100d8041400141c0c0c00d0355003000800403502d0640180d41c0c3c80b56180300100f02c3c2c500811a001d1600c550100710003480c92042c060003100d80030201f00540c214104440c0380bc855220381c1c0000b400d004442c0d40304a07042d8800904e50302048150300301445125a488000481410404240901c41c41224007404c01c840c890030018150501940c2031448900040c68240d08102d078900118013180e1301071707604131100100481e04540e502d40b0196050741c0305920300c110b14101443c16064598609820b108038081c0302c00440020341d801d1080c88000c004680240c0e4512281c2402030301c1603101c140030701441e40041e0300c07284030042000407402200d44019040e801030400356100d40b100030007040c841c00100c6d450f54082082c0c143c0c0e59030412001402101c03188003840c00c0d090614010745009958007005640d012644c000f8191142c002c0e1920b60200185030b0411040749441c03401d040010044010030380c0c4001d010034041000c04001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 616535656 1250 616534406 616534433
    0x100306150e0901050a0324021312020405131a0a020702040c030516110d081305060103051e0a02060d0f0b1c1b050a050d030e0d0f021807050d0b010c050a 67
    0x15a00040380f6601d03101800b803002d82c540000b50801341e401c1680f04402c0c1b0064041d800390030036010010309144e11800c01c064003100d00d5000c010604001d401c0a020b40c0b41602c10179400202000422940f09030315600c0b00d03002c881c094030451201682d1000a0942c284d00d4040704d80c143da00406c10044070a0700d103000390080500340d4009609200e100e0352a0003c90007140705c501030101072001404141902c0e01c0840309940010200c0c0240b8498000345000038004010050185101d040036064030200104040b0080500e800c41145982c4040b55000258907160222039030540b1100b4045030646109014101904126a8860300130207404160085460344080018059100e105082c61070070758a13040711240049801942d0380404000b504029600c1c0090280142d0f034482c0c24548000c1142b10005041490751240995460038002203803011071510001c14102c9203010b211031540c03420000b000030f00710301030824500301041c2d13980102c42450f801040c8801d11079038003804440d04460340d46060091011807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 616536906 1250 616535656 616535659
    0x31e0c150d05070e012015010303050c060903040e0118140c0307020c0d110d0f081810030510090515030106081c170a0f060b0a090303020d021b100306150e 68
    0x2c10700401c0d1100d1050b01c11030303041c140596074003522115145d080c0d00000310503080c9425620525080521840d024601980254000d4489548a400c400c0c1c40e181003039001065040150401c00043c00304140c4285103506507180c1020044c0030281d2152101c00411484d42c10b00c01400321002041403001351440118030403c3e0503421784641c002c00e02d0500220311040a4020100211401c1007461401c01010005805000e00070a241d1031406e5120041240d21160143c0342c9507422100812050900c90395101d007041c07107841d0030020340c0b400b16031185100300c40d8040e400d00c081c0c4540105030b610030311700103041001e90001d000304070386542c8407600396569403440310b894421503648640b012058095030451440c07071550940a48103541b41c1110b5001040544404644103030b50304800b10705403811901621092105844100005042d810701920b00021030514004651102d01c1c1600d901d07445811200a40e00180e42002c0740c20005030059000d05425000804400d00001d003506c043e50744115401c400180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 616538156 1250 616536906 616536911
    0x15120b04030f0c02060313021512011401050c060619080115090614060406030b01090e040b07110105060a092708120a11030c090a0f06180e06031e0c150d 67
    0x1010841514928002d041c01303580940d061001480c8401034205060300d0503c01005c0000920b41c00c82c40d0f4160341c210a407141a044481e00060008110384444040c0e4160309084c1079040801101d401a0b80b004014220340c0107130a0200b401c0004034400302100702030700d0002c0082c40b01280300c12081d120303051984a0255040c1c10b01c40d0001c0c181021600c1180d005d000900b660b443c09080c150706034007826900190a0400c8920200081c154144200140c02140301d144c0e92921405c041381e00500b400c4180b079034a82c490b4076142c1408001d80d109018903089800411012865041c5e10b014a00365404205410764221303c954240810001d1800040140c5500c10b000d45c1d04946440390706074111000198400c88d00c0c0c5080010074241509440500f004400042c02e107a54203440300c2005e82c9440c01a409440440c1c4030b0311820a81100159524001e8400202c15000c6031a1180000e035070b07041501c0c060302002040fa944658100c0303041c0560b0003072100107810070f0301c0440001d201540980c05620003111161 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 616539406 1250 616538156 616538177
    0x1b0f0d0209160905270c040806010b18030c0a060e010c060f0b031204050307050418140f1b0307030201080912040b0a17101509180905151915120b0403 66
    0x98003d0b103951020540741180c5c1001072400b004070b544504040e0111241500c04d0000180000081002134040c1c849082c40a07100c0c0d01d24180c081c001c9480141c0503200ba00420200303486900c449000300216405460400c7d07242da110070058038603070001407024091900f042040d884808098000140c1640c0c254112400c4889040c05032180d0f00941c041c045e8113070082101040685030541152000c00380d80038503400300036150740da203030082c3c5580a442002c5411204040e00524030610002d07008802c0060814508031000000940f00d800d103000c0241802000404956034840400100e82d0f07a4111000b0700b5541c40d02c40d100c4400035040020544002140c005800720030804040ba100e000d011541074190320f590400d01503021300002184081c042150503900011724500101502c0381c1d8244003540014810514280309003058040d42280014541c1c0b0424440c5450704102c0806c51007000c01d000003641d050f800441403038150075600c040c10b000d0000e896503090010b42e028407401141b09072a00b43c1c80c01c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616540656 1250 616539406 616539409
    0x51504030e10140a0302040902030a2a09030b04050705030f07091b0c02010e0301151404060e1b0304030207030c0801023a0e0307170d0e1b0f0d0209160905 68
    0x30210329042c0000070703102a10800389202d40b601a1800b61400d0801609050312940490200d801c1141d14046860700c0310340c0691b0700b0300d100000311000c0d4240041503003441e14440b000340c105415440000d20644003a80014113002040c40803a019000040c1513401c80340191418a6840110303008003130f501e619280798a03504070064144510191b5407502e580303414140c1d40e001074908220020f1411f03015503d80040c66500300c080108000a003d0500320304040d0820726050000f1641c054000d015012100418030646000404d4003c65450a10210a41c1d075602ea1070b00300c1c00c003030495200030488211001c1c04030f48a50190090802c5400318000f1000c59042101181e82c03001000400e01c0004036404140c00c040780e0030b9080760b0758246040049929114042d0b9410f21908400c10b03016444107c081160400c00546d40105d014072100400100301500d49008808540c82542c0301c058403a20400c030240b81113868101400981a0b00213040364414070f0715180100c01c040113000101d0020308084000300f5113 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616541906 1250 616540656 616540669
    0x10050307120807080f0a110a0b0112060e06100303020705030304050303072306040803041a04080301180b062a0114061c05010504030306050a06080c1b0709090c030213140c0306040207051504030e 85
    0xc12741c10150b04034080c0d213022610801c1d014000026540b02c1c0c0c0310700d40500203003810000c0d22300402a000c6018031031851401c1c000e003452401e40010340b1a40080004004541d4000299001f0980085200317800015080c00440980e0b444810341c801c0c0e0091400300030a102400b00950301c194051345100e110080030390070542803480201e0300102003682c248014002002311410100365254107460016910000c0d4000070043c1d0010102d1980e81e0030070b075054191100020907000304a00c0f40d0780c028031500f40c000c8070b18240054000c0809004480492202c0d03a003514141d1812600c0b0381241c0200710702e04003410004c014081900409010301e2520000089041c407039101e040c802d8041041042c104142c0710151555540040003c0500d84101e04000c6a104c1980c49582c00c450b128000854600d40745206100c0c0c0c181e100c1820f64801d80c545001c0104a5503034101460740448000003840d80da6882d440020000d0080303210180c9144a040218141c404405204a002d10301a0311180000c540b0601003140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616543156 1250 616541906 616541923
    0x6020d05090604150f0b1206010302040c050a0c020105130308070c1e061706030c09070c052a040902012f1009021c031e080f10050307120807080f0a11 66
    0x131207081c01c650141302030700c107034008458810310076030100d0001100e00000341d070300461600c003c0321504000010070071850140700e00380e41d02400d810300310b04000c1c1740c0501a040d050000b0019040c07100004442801d40346806010740074640c4001000d032120b000d420454004c1d005400342c07012031810719402c0b003e144c02c0c0c18948000c94420750b03500203220f0301c10070750022040000b400f5550076100c0c00240d03003400e9540b004031500c501000c2c1d44140082e00103081951a10314240002034208d0614003c0d01801c1c60441b40800710050240e030080740861403480100e440411200001c100c0d00204101048a282400704180000c21804112040b00c2e507940c1c034500c11a006501c00035031004510001400d43d520003034401b0f0601e40641800e42c104490b070110007418240718069036000640c00d00030403c0d001c104c0f903070464000d01c80c0e001a560a41c10000070075601d29241c002c1c600c114002445034070810145008880c2ca1507842151952591580c08041320a0340040b42c0c04800301d502c104c440042254002140d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616544406 1250 616543156 616543163
    0xc090109082a0307080601081605041109040e0c0a090f06090b010e1905090703090506070e1027060302030403120b09070e0402070f0b090c040203040803180312010306020d05090604 79
    0x142c20100b0301d02180a451800300215090700070720900040545080c04090300808060003d40801c0e01208003003080985107401c43e40c0300d180307010001c64075984440c2c181c60410b801034030b0002c2c00d940424101703860036412003005540121a42c60101e442031160b0090480e07008540d41c10700209031035402d0b003401c1d80c2550a4250004404817034544051508075000f0b0480225542012a4552203402065100f017040302c04e04003182e00c03030020303204010f010482151300c0840d034581031000f03011038800200e08402c1c514201c020071501107000f20f074862205401d00c00700300220030b4101855a036500d000c0c0c041d42003200c00744c02003102020a4010f05445014200c50b05000070941d1020360345070f100c10307240d84e030840d400c050300541d0074884a00000e4209080c5c2940c140920380b29595072a201007007914050a4654590083d4014030030700c40062115400e5a411a03050524895210941e020180c40d500030409c044c081902c14500000600c0f0f00d030307401003c091a405005104554400482503619481580c008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616545656 1250 616544406 616544443
    0x1091220030f090a080604081806071104020c01151d0106050c03071b0b120406050c0702010818150c0c060a02120f060105191d0a1505030a060902030c09010908 70
    0xb01e456000b0005220020034140c1a103032540324035450036108403401c5039a610002145046807501c1c501c60411104119140c620740300c041d40e41c038510034148803041030040d81c000c100174000e40002e411000903440a101e0a070480755460000144220f10358600e401c5001c500300010030302e07500c07a6041303c42410005d4011480d00c9002d9444101306841c01411301c002e501e0040c07001c100c00f14518010100c8407100c0f403400301c46050a003414412600007400302c65218034100030047c0180d800c020100c1d40402100c8080701c48940004906060104100102030f00031006010004440c000038081c1168440040c112181c6503642e40c00c2500724410046d8180401c40782d48001007401c0c410441c1c042d441032040c50a142000000315154000040d24540400400e6468210142c6810f1200c40170303540035421104041c0b80e5107480c0007a4904000000707060304100c00000050404a8180c019400404614a00b10f549103803a4400415903040b48071b00768000746130b51800040301c2c0d1000030744590840a00008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616546762 1106 616545656 616545667
    0x120d030e0c0a090504020402120403080109060816211e1104090b0601050705030c06010e061314130c12030207061704050703030c11030109122003 64
    0x40009500c00310702074140355aa41400030884044040005154555001045c040e02c20782400c00d91091540c070904c4201070307210424904072216a00104007181d01c07507901c15142c2028200e07406614115580503c0b801da03111000240345c15840c0e0045800000e03d5850800f1480d1449071a600c0f4988064a00d092046411003224054811202001840180d99407582030580140102d13040020100b0841f04100007082241e4150162004031030039582d4a550a16001400315030303403030003520f581026546084c41ca001e1310554000b041d50662503030b82ca84c202d0f00714031402641d041c3c5024034403a00008091094601d01c0390070354000d134041e0141604107080a01121495100100741d00e09480400c8003045002c50203006496040c5004544980e06080100f14450500d012591552800c914a81000741d2611424843c4000f1388605030030302445034101907034081c480132001042c1c204002 = true := by decide +kernel

theorem cover : BRFrame.Cov 616366906 616546762 := by
  have h0 := BRFrame.cov_init 616366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616366906 ≤ n) (h2 : n < 616546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
