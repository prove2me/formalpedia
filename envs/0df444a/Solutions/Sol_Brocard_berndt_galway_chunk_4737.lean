-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4737
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:34:25.820911+00:00
-- url     : https://prove2.me/submissions/e7611b94-dc6a-44d8-82f3-45759a10d198

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851798561 ≤ n < 851978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851799811 1250 851798561 851798579
    0x20a1e170a260a030203040b070806010215040f150b12060112030e0406050d0b0f01080a0b1618140910050d0f111003240807180204030501020409090b010603050103020a 74
    0x60341200d408400d6502480c407080b101e442000300400102a1001038507800c0030b04040c42078102c010010400d000d106404d11059070f80029010301500a0542444640d58451030021440700750000024140c2844a581c102a0101900040001b40c0700340e40c01c110440c200ca05046e580c0000b8460040071201a40e05480030a01c80e218990944902520129100740d8903400b2034200c541c1000c0c2034590308200b500703101414944002090040814800400250f0442d88071801505006004da0001100e280240c1880718061100384000381c0000e0301e441c611503a58442041456160b00d5118030402c2100006040039200108003010303079202902110b40100c495491981c03800700c0c1c038821ba601e45214144034209964889401020103110f690104451110a01c10840100074000402040e034014405109131100050204d040350516190307500240710604006c0001c1c41640c20140265000180c08120044207804c10080c0318410044460315a80e250300840440c0c2c0c0a020095022000c0c440030803148130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851801061 1250 851799811 851799833
    0x30f092a0d0203010222051503060913060e16090c2d02100908090f06030402030a110a0b0c070e0601081e06151308060106030207021f020307020a1e170a 67
    0x101c0a00018940103202006d00700084440c0308a161010f0841420b01150401d240103078800310b110030815055040c22000200801c000030300b45580004441704040a2140d030781c111a40b03002841003601d20f505607021410400d404c050143d0311031241012160040544a081d410641000c60106451050000700d0b905c540000414010021480350407031581c508130f1588140d50000e40308006140d80d6080300e800340050707240448000f500c206401e10410026880115a900110b41d2244403400210f6600000840d0002c05420072180302001055603141044001100400e0310320303004008405c4c0c1d99440045501c2401182c0e07108800e91000c159006c0007086000c95a0400ea0040003440c101241180b2040d4941224489006501c064002000301c0d0909110b001d0241c52149000d52401202d50048ac2d620f00301d550308060a005023044c010040c44c0309005840f000c80d0300070b01c207000c042e968907003028101901025034800c0f1000c4403400030307050031401d46440b05828070102030702e6034524075142c00080701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851802311 1250 851801061 851801063
    0x30b100f0b0c01021c0507021b09130c08070801051005090103030f050703121a090a020f07080c1c020303041a1003060b190f061803210c0206030f092a0d 67
    0x143d000d001e0a0300080142801510400c5d60f04000181840d10000092405603817030044000150610000d2096485121400340e01c00c0d078a5541c00005030b420701e8076800841032580941e0a90158a0001c030b498201074000740e015070040da0350304e40996250020050b10010030711000340429071701034610340100d00170303c081e0950600a0928800d981c0d140c0d21000251251809125103080009021a03814501204859000901c0c03520442c203090440c074000505100f5440702801003400031909000b08002081490740303028000042c024007031106400a5a603400035542100d24050591031a01c01404220103180b1482d02c0882c84007c461854480800410b039200941e50031009040c8000d480da1090300030400101011720100082c24680138000b00b2803100103c003c09500c0380c0c050701b003000ca400c440c0032141d2981e001d03034500071031381e40d441c029580d017a442d640094001c8400302c01c00194012501c5100d204101c900107403000c84561803c030282441d40c2075441e03108407041600d4542c590600d003050300c20b42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851803561 1250 851802311 851802313
    0x6010513200a031a011d060f1809090a0312051509040803070306080705150a0c06060e0114030102030717062805030c12030d050a0b04020c07030b100f0b0c 68
    0x6918564007181c160031911144121440300040a0245583c540710341d50a641d0450201c1500300f5010340001c25907401c1c8002d0700c0054420088017100d564440049650312002c4042107039580c0c00d46120846101c06840e4414410001040003030115000460900d400681c1590b89011654851043c10020040a071055400d09035480d04540c8580350418403c0c02903002c2c01d925510b07403071b001000405940b01500510b085410514080103981c03101c003d202c0c0380c0a88002a55194850614111b80c03843c0041400380c0b14900701300c000103201b84484849810384000f20001e2a07090224014135090b40300c00c0d9803880c0040c4410041104e84c840564406400c24002440c54080d82c1101c0f00c207481c10744800301c290a9002e41c0e44810880c6107400c02a8000201d0180c80044011003155050364480c0100300d445459141c403000020302c608015400035080f000000c01c00c5482d1100e02d2415035850009010844880c8000401315070b5000e210340548048800d841d8080718014200341d00740101d508243e00340225 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851804811 1250 851803561 851803571
    0xc0112060b0a0c050d0c03140714071202040507090311041a03030a02010501080106060207030b0a05070203040b18010806012f100612110907050f0c0f0f0109020a090e06010513 77
    0x81020040000c10000703100c1d03514502c1c40c02044c00c10500b000b80e203101600501016148010000303402c58224480e00081e03061654882a06040042c01d4040603880c050060081e12008500648140920181140280c40410003551440b41c01c2d030f4190200d0101a0a03045c800308c00b1071043c41d00340c110980a4071032409007544071f0340d00c4011a1541c0c00c29045000544d44900060101e51001d1084000406442c07000b4034450340741d0740f50f00b485080c000c2c0551540c5511900010110303030080048400800d80f00000550f200050501080c041e5441d0b84e01c03e00280403800400c0803036100e20030308640c014a48920113240002012900040015403481c180d45004464410441c2420f910800d0001c003c19100719030451254507000015401415005120340004401d0200040e8043c050768950400300d1a003039511421040b5061511310300309403482c03051113456200c0c0038441e810742100d820301d4400c4d030b40c40341c0031a100c1014505441042880e140c90760710100040020341382640030b031481014800f000040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851806061 1250 851804811 851804819
    0x30302010f1a0d051002130905102601060e011d0f04030522090e07030213020f040603050705090406091d030702100503070903050a0b1b03060114092d010e060a020c011206 75
    0x806d0f030300f20108000311151650b81c10011043c0354010389600c01c000c2d5550080d0305040c140083c444015580c4007c21002e1000c5400000100940c040000782c00b5524088402d503a5070414224000801c01d680751180a1a00c04030f40000002c45400303010710740c10f484440c107100d070265a04442c55110000b003c51002c5060001540606900c1220030f41a0701201800c015400c50060000307040310340710784001c00c510400071503041d50449003e44041d07504030325003c9400e48844500b00d4050081801310382c0d2191800000041402c050b501621044035003180c48510346224000c1e41f9201c0c042c150010b50440c0600004c04140703031042c0001c41d80311150f8203003500301c84d8407a12510301d003c080302c0c4203d41e01d0341000240a03800c10b150701352201d0190704001e628503501c0c02c06c0000b003a802104132002141107021440c03460303980c0c0f04c00f0399003030080d00404904148042015107000c11510203001c02d02044c8201030307040301418403804aa11800c002d400030962804a140111540101190301006056840364003003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851807311 1250 851806061 851806093
    0xf0a1202150a06050f101e090e150405010f1208300907050a03051b060904020d06030b0f0433020a080f250302130e040309030302010f1a0d05 62
    0x1406120480b2002860f1800c00703052051452001c40c81a204034034014241c038031070350f0050381e56a1941c028000384129841d00e040a4400104a40105004260500030082ea10551000ea181241001c80e400d00041c1d0341c40102c012041c01d00d0007200200351342035034120b012903071510050410558800354508100040d4581c410039180140310302600c0c50910040c0902400100a01c5000d440d00715a5074180c50b1031650390541d60892580303026850900a105001c00c1e645200c1611540200a0004c3d943c44030716070441d000402d030034001222031070b01e45000b0400844004d01818441c0754440320a0800c000445003102d1881035401019814035118400200c906540c0e00140c44c4500580c1c417841414200800403807a107000080460401c1950024045140103e50340031022610044c100142e40382600d0a5003c10900240c100208659940c400e100405034040480030880b8040c0e8002c100c42c91142005009440b50044410f240520f0346030502407600c0c107108082d030b00c1803240040f541c40086081307401d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851808561 1250 851807311 851807353
    0x20d0203090d0e18100305070f0807091505100905120312310c090609020307080a140c1803010204060807021006230102031b06010501030b0301110d02090d0816140f0a1202 75
    0x241c40018001c0c1080ac810401008824080c2c030b40305405103c100003040c400038659000340300d1548649a1a40c00011440c0204036100c0548809021401c41c5c0b00071480142d039a500c441c02598244640d0000079052100041d0201403821450603100060519171705260801c030392018090701e40c02010840052084002d10540c00101aa100096201e2800d0040a0813010008241c0c4800e0341c140803442403214202440d165000102e1056242c840f4580c0081048039006104420f80540c400200071503680c2e0000e4206100b030701a0380c201d80056501426074020795203188914030108c1d40e6404211007420743c04e10b003201c1413801881240c1c00d1610175000340c000244100d80e000140d4000500500165030b05000e0304c5034103030058000f4842c1c80d441100303071200b0303103d014441520940c1c040781102c026950341c640e10007403941280102d603c840fa100e6003031b90710703001240f0201d0b603562400004100c00c600216404401940201c040d0900032280d840c4c01303100038a40e424100850040e180c8811284403401c0300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851809811 1250 851808561 851808569
    0x913060b130903020c010e010206100b160c0905010306240311040f0203160e010c051e030405060c0102031e0c0a03090302010b1008100816120312020d0203090d0e1810030507 76
    0x17001d09010300d400140220342410041c41c11508090104030402103074103860f104035046000c545654080305014482c101c82c2488006140120303120f800103160446400490589028100412200341488070200e40b0300f03180d44110341d00c10030a10041002c50210841084101ca01420101c2d0703420304100100c08981c400c8030100383c943c80c40d2041c0d21480b44e2291681c00040704c01e080c102904c0c80750b1384a0607070b00d00140541c1d00d8100c400741a060506142441038034010070000d403d6903240d88103003207440c1c040d4100300c0d0722180c1204600a0b04685412030650302d0b00508025090710b20f008055281113014101e010020380a5640b10080d43c42180c955a102d04441801e0b65500d0700e850812000c1200141d55643c080481a0710981c5102440c0b212800d0303000442d00000a40c50651742d4914082c2d0f20a02102503001900344048bc1d8200194402d800652084100505030780320140e5050003a40c1c8042c00075400c6401400c0b0400d24400707500344060b920382086d0a0108054190740c0da80d5840d14201c06500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851811061 1250 851809811 851809813
    0x302090a0e0c0a03050603030a0516110607030801080d03150501051803032a0c0a05121f02180907020d120921080a14040204020a12110a09050913060b13090302 70
    0xa5244442d5130b15206450700031204a018601d03100d034080c0000c1c03090240c050301d01c1035003ca0661440c2040602c009541d00024041d02a170f4a4003841d041c09807480200741328484050040c20390706c80109219200702c100002d0340c01072070f00d401d50600e001144c854010440702c0e81e5020b110965410196800c00140140d03600580a28400302c843c02990f4600100c00c090b0711110364030090301420b05550785440c0d0000e03034905881400c0d00c076410881562906820103c1c51000f21403201c2d0b201c1c0f442d4684d4000b0f0000907084043c0d0204404c100341070000b505002c40d00b000041c1c106d03010580d030041c444c0034520b203007101e000c0d03010640c3d81040c4c035900503409032081008507440b41000940e41d1240c100d1003007a0311504c0400d0403c90140445ea0070f2018039001800240700ea43d00080401480c3d01032180b202440c121840301b0048007080940d0081694041d00300d8101041e140140001c1506e0140e010b144110324805001198203403c0d501c01d005808440700036688041c03091013900d48402c0d548209141580aa4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851812311 1250 851811061 851811067
    0x1e040218090a051b030d030e060103112701031a0906070513050a0b031f1a070606120c0e092806020f030a051b0a0804110a1a0c010c0e100302090a0e0c 66
    0x140406162014001c0101b007814104505901e25160215410b0704403034202010b01c118015890000d0b100142442c50998104040c10304140303e43c8251500c0c5059034072540443d1101c009511040b000c11104640d44001607101c2000a0380710340c0b2030000f82c40346010744110b03a191180c503031300010309030035442d040b050300040044204030740003c06407400c0001c514450b0029640324140942d02c84041c11120800814140c001110b6040050036404200140441600803080c0d5038a40703401d401c60030703403485039005075201c21000c281094400316a51001c1d800d44c82c218042c11030511030010411200781c0301550355560038442c640c0328503202401584a03404035007002500d071814018410075115964081c45140c2c03004c2c0a400111500203400c260000e8014410b159640741220004980101e5900703d2095403d1072981d69844c09051000b8062401442c4001e000703200711550211480e02000c0340709980719070410700301c2d040d060180e0300900300c2c1c03c400340c0504141c42c3c807880500706004041e0744c900d296000c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851813561 1250 851812311 851812363
    0x30c0703150b0d1a062b150506030c1221041502030406170603010e0f030901120c08071d192102010509060c100507081e040218090a05 59
    0x1480303076198045084a0303403e111030468507000255180502c0d95a0741c1c15882000c905e25590b102007400304081011800c1c01561101d02c080c49054580c4441101c902e00608040340362800d075400340607c10300f40a0000c00c080039000382008120701a65440c85014040c0001001d0680e20484407507540504c50480e480d176603482d02c2440048040480d83d40b01c1150420301080c40403d43c07102081680b454130900b49910b54942c80d000900501f00701000a000b0f02c1035240d40445040044081e080c040d209880d6101149104202d4a0070744038006060030010703560030002909140500c603240380042e84120b10000700002e04011902c00010140d2080200680d160304108031010880c0d207203170768400c840c0014038201c11a030000c0c00500030361131614425240415001c3c2c03a01001c200080345005442c03c10f1003107080010380544494000d0700d01900b215900a41c80f019500344024480c040c55011700040c0c1005030840780c5290402c1e0180081c0c2c000e004854018011490804c0f1a05c0c0303803007c12489860310195 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851814811 1250 851813561 851813603
    0xf14070309062705090a0212010335161a01060e10030c0f0f140706020405040c091a1b0610090b010e0f060a02241e0c03070f02030c0703 60
    0x50220a024a8040f00081a1030452400740f20b0003140c0003550140c8994840154500182c021610b06100642d0440e0000052000d00310004800c50403070302c001d0300d048040b022400700040c01182c41000d00798041180d01810544001c1540b5941d0146107406005400f417400300c80760b440d013a40300d4800550140c001c40502c0c58202c4c040701c6e501e41c550070104105400c0785005042c000c007480ea04018000e100c2160042036004200c4201444002144141d07654034030302e1300b040207401c00d0207082d001d00d10745801100c00600403d115030a0300c0410846e06080c486070454004594440105184109048403181c1003464003041943d0045030b0301c059a181c940d084c14107403000c03180315910043c100203005c0c64900300ca490790411004407041c1603034110740d10300d0348a42c103a1900b2410002c00303415842660010103031480c04184c0f1030040c048044010701c13090707501550440904e4241d41ca42d021000402c04550b42501900520201c8141c82c01542c0c14040c1840070341c1e0900b041c55200f6030f6841c0500d03003a4100a16 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851816061 1250 851814811 851814827
    0x507020603310506040f0c08070e04051b06030a0207061803020d02010e0606010f03050c120403020304081908030a0b030a0204110405012d0f030e0d171005100f1407030906 75
    0x1000800b41400d800341521001d035074800c05003010340064028400f10041c0714840508030003601c4a03d04071a001a55416448006a41124140c80900034428084a11850b00a06c030488103c02800982140c403194200c400075031004400300c4175640c3c1c44c0b14600b1407122401100c0c14850194002d03166503400d0361006801d6445020031003041f5005402000748076a00700d010340440324007502d070000300c40d0f603280c103030048a120301104240c3c03c00c03c5c0c1040000301507000006000f80c0c0e0f09030060340d480d281c049481c0d1000f0800c000000301086410700001e400341c115a40310086010b802805c0b641d411006d900450120380401d08024a0007000260030300c01941c00205480c41e5034907003050400941100150041c0c2e40101004050800000900e40ca824521982000b0381d20040c58081c2d40c1030015162010749415a69401c600b04140d070a0300180b82e010b03100b04440d0440d000900390081065100d48100d5408000b002c0420900102d444080e1a8500c543c000d82412031294649054035070500c6000740c103500b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851817311 1250 851816061 851816131
    0x3210f09180a14100b0d0e01060b04170304080703060b030c0406030b06120705060304021c120302030a0c0e0102120d0207060614031c021005070c0503180a1d0609070507020603 77
    0x1803007030f410303c05105901c00fa02c204840d03150480a407144115004040a0420798000340c0da50340c00d00b07001141000800c00203000b21058030403070b0094003001c41d81d103945a00907032089000907000003000b04046900c9400411549000506480e09210214005000c8510981098951602c240304001e80ba081c85420340c0382c0c0050680080c68090b14002c00101940701c0200000d004180c22810684120350a0034400006075110b144682181c41a2100600039001101c180d4011400c07d0030045820340180c48181d401307039069020342060700350036508108070740c00728001005250342080312401241c01c9101c1c00340502940b0905852180d440070815145c060603100d83c0c440d1191021040802c00e8000903400151a050304000c070740750307880402c203031100c2c9801c410107407450200088690100e01e004d11f604d1a06881264250100c540787c440f01c103045a00300d041d41a00d00424400315802d483d0003082d441c3d0042c003510b400d920301416035011a07015001a15008030b00c04410011408020501c10410068 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851818561 1250 851817311 851817341
    0x90e0106080703060f110f031009060e060405100807121101030204050d140703150e280b0a060b0403030819150510120e070305070503210f09180a 64
    0x782080c1546440e80814031009021a039210400c0c07000c28040d40140150b904580c04103501d0310b855a515589a520031a6441903244c00c00c5400301c6c51079914803424040c0c51800304804103a03a1507c0c288002000c000d0b001d03c051810300c000001e00d4100400c00d11014211111100d5404880c41c5070000c031120091082ea818140140014040d6440e00100c079030b11541c0088200071161094104ac82c10001a038002610380d2610080045103441c00b41c204c460f66039640e0b400c90320036003003040f1128424600c180c03c0ca441807000c1c0300c4183c0400c1c40d00203240c1c1c001c1194240010000d40e600035400a561082c0d0040700800e0f01e0704200b04080c081401c03030240d640c42548040c07021030300701c41020500c0d0401c1e000345403203141c0030070607a182c4a114242c030803c40485503000700032a022100845680368814032040303655110300c000100d06400c0200c3d800e03591600094003601515a410b10840e03007900940011035983c0403d000303000c0650303208491012005d126080300d000170304020300f0b8442510307040082a071030b07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851819811 1250 851818561 851818571
    0x60908150112150204050904030908060f152b060e071202010504150e0909031c0212180a0f030e0f011d010f0c0501140f09161e0306020d06090e01 64
    0x12028442c0c11489101e98441910090082c00c20b81ca60020f000780d800903a042a1413000300420180c000c01404192801d840440d0613545d03901d8414410040c2c00c641c00d0710380b900c0d00044c403d80341c207001d00d540906200b940c507201440c20303410050030302030039a270403060322405e8840c035010b00380400501641010701a440d442e041c43c406150000b170a43e10071b600c01c403504140320f050000e600034801c00200005030401001d0394001c1c1007080f1007940e00c2d08400c0501940b80e0100900d140070740a10300c00c0314043c1c0f00c08a2100c4050381d41c0d880b84030707012030b82040c6000c95004003120b1600103415240c0b6012198440e40341d46400c45405000d001001c1100343ca12030620800c995000303002c1340c40241003c3d40740700918204050003443c910448007504070f410001c20942c01d103607004900500710f00e0314603c1030074400e0b8070385210360322101e1981e554004280610406403000c001408600b00c1e0081209100d4080607100312141e94940d91171041368801070f003040c1495a00c1d8001c2c022a1264001d4114902000000f804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 851821061 1250 851819811 851819819
    0xd08091b130b0622140a0506071707080403030f090e0f0c04080703080c0d0e06040b0309010b0607110a4401050f1911040e130b010609081501 62
    0x560000d9042030600c207120800000000c94100d03008040c0c542400780c140c0d0744500b0305032540309404051091601c80e484d0503000104000300c81d400d4280285d10300400d2110303a240351009101c9541d02910307043d40d81c941038418284c1031421810050021500ca00102590b403455030800401c0c651480d81484100030010808202d00400c0b800803a400030001c44800740c503034a800d800e00110303218a9200d50392074007424100205000a00002c3c20600789014150745420900d681c00311041c50a000c0c00d103902070014081032111002c6000550340c040b10340d40001500035846d03000201203802409003200e040025843d500c02234100008814001e01c020f00f0100500741e592000006041c0004601010f0004217a2980c052914201c01e00c204134210a00200311a08219404801d800002c50b4030440f000c45207002c400c80c0d00c6251103049640b43c1c9500f00c0b01d04143c109002090209006800701c14003100101c01c00d00821080b0701c082e03000700170580f113400c6524a010203607070801c0424076410b4803070512040104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 851822311 1250 851821061 851821093
    0x302060319090b090f070503010e0a1b2301030b0301050405030901030b2808070f08060103030807170a1b020a050a12111f0b03010207050a02061804020c0d0809 70
    0x94000d0000711500800c1c1c0d04124240d0014070740320002800c110058818081d54242c0811001070300d490070741c250341e481d41d00d0f0424507080c0c0f15003009008455116200d5100401c14520414841a5081c0c520441c40d07561000044a44241e204489521010300101c000181da0944034003000c0c000c090b00280704074a402e8440c983c40b405042d21060505840e45600e001e1569698001101e020001e9407007140380030307070784c202450076803c90240c0059032283c0b10020482241c50302c0300c1002c682e920b40003002c20b41c3c02c66408a4004901819000034000c41030b0410150040c0301d0465032092515540015500c0405040801036034402d1500000390340014007030002152011800040a40e0002046d068032000c20070b0407200c8518190702c8200e42d0140c0782d1004a0031601400c03c003040441c8490900000c680d00303003014200d2088100051055018011000040c14680c018008600600000320074006401e03010030283c2e8807a04081156400414013059441d800c2146070382c0058103c4020325141c0c020300821 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 851823561 1250 851822311 851822317
    0x90f0402040209010302091804050d05040807140a080319030c03091707231b2b020103060b0c010504021206041e110a03050c030601150e0f2b0c0609030206 68
    0x640515000070f842c2045902039011200303c802c0140404601e0f01c03c110403401c520304203540883e0507001741c59010102074412000c2e00c0694401801a00d07450746040b5030032110011034800650800b105420014886030180301410f25068030301240d40008844290060480345a8501002454540760000d00481c2c40d0300c0013841c0e0000f2440700c1c0daa40d00820b041c00003003042119181d00c0011000e200124a4480c04500c24440040c84000c0c1d0000c1d4500408200111540c400e0030028542c500c80399060880d11281f0001101d80181400111540c6030030301014a640011502e046580d10b0b1030034002181840360b81c6440002c00080502103d007401d90381e103400d09030000681a06020001040343c01e00c00741044104804200810b1001d083d40d4074600310b030304c1c0e00707804452a11034041c007400054000d105040910241a2030356500d44055601010000340c0b98900c0d080c150460300040e0100344c412407401e030510018441c42041e0340b006982d468040092481c1e0b4210b28100070783c54400300016203482044d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 851824811 1250 851823561 851823563
    0x20f040b0c0c0913030305130308042a0f1404022b0b030706080a05130302060105221d0f1c0509220203090f010603050618031201060f0e090f04 63
    0x165680c450101e4022031400c03a90381c459640c0060070a0502807a22040080f0588081c800d0300c081c01942e59003880c07401030740c000c5980500466a2900081d00040c145000701c196034040c500703480041e02940802143d03071404c981051401401509051002940070b04840034048000c03501903103011f25150703009012504201012615100c0e050307007201e41e401160011108400c0140c101c03100d42e65102c0b80145107000540d10b445009107080e001c60010451442013101d0160190014905a480c0509100f165502d03030041c804600d5258600c1003044200e03003d550420b010014150642440c0c07804182c3c181130550000700081d42c4181d0002c0d030310300c280c00c8080241e0038060a11700d4440640c0b40100d400e11100c00a01c401410300c1d0004801941a154003542c02a60168122500d001c0c00140d110300300c2d41103010280140c0d01c0312001a442c01c2e1100c0a171076511100d842540d05100c84403c050032408001e07081000814010740e407034041960b100c001050807140c200c41c100c4250404908020a2000141c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 851826061 1250 851824811 851824829
    0x1b060706050726010509071d061602180f0c031509040201030f0903020106030c09060b0409022101140112050f07030f1803080a1d0613020d1208070909020f04 69
    0x1000031035050144050490f00c2c4580d510401d0418034100321114001024000c035031083e0303044008244510b00c644441e407180c00000290b82c450f55403039801c120a54000a8103009940c81d040d1a40e001a1902082810f91101c610620a1141850f001112186200030860031030100c0038001c100c140d0709849030622400c1d009503410011070326603000403406400c1402c00040081d0a103501c020806074150320080440b030040200146582d203448258099860350311820003803500074031092100504070760042031300c940315025040000780c645c40e42102184090340b2890800c04640396003101ca58010605081d5203030142d5080201d4a01b000000d1034410700030340010100350380c3e03a0700c101802a20360b00080c072000103c103044400588a29008021075400c0315451045e0303007008090f480c0790000d803500481c1403818001803c403542d500301000346440d28402c0180d0740b04002c0312910001c5440030070761200224503075840c070442c0d02d0086e42c041c14142c2d0039800103007a144100401500201800300b52820358a0000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 851827311 1250 851826061 851826071
    0x18220b0103032a050610090b030d0518210105070c0209010612060b0d02041d0c0306121006140f030703030e0d081b031306020a11040e1c0905031b060706 67
    0x104035545032016490040081c40c5031483e941040c080e00040c190310510240c4041d0082544520075041a200200b259039095800342d140c071050030340100c003d44140802c440300c4c04038140380d18002400d095010034094444d900c5070701007015515020702400390b200300305062213660507080e0b5010514242e414421a81001481d40000301d10740040d8100c1002042d020101a0325803801c013000c00000d6006218600042c1100f48401100e101d05000040c1b02e4004a652541550386130030a00c41ba1510850301c50b6681d020b500181c1541410711301c2100003500f030b00100700595508074428400c00c1b004410341c8500c030b41c4c095002080020b40c070070f1500c40001002c2d2400e0040587e1454108014001c104000b0000c842c0081e50a4070000d00101600f4081c1101110101c01d40d0750380d2060f030b2240d581e100701900040c0481021041410183c01c1020413003c0398088820982100501038440d20111116100003510450100720b01d1804101c03003011044a03050100c61074400000140c410b1207940001801140c846d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 851828561 1250 851827311 851827337
    0x609121407030c050a050105010e06031510050f01050f0c16080f062202030a08030405070e01180209010509040216050105010f0819110a0f180203091504060b18220b010303 75
    0x24014101c515071b02000074842e65841e94044034150f04210f40d0030703019105500750b41d448200d241802c0c0d805a0320030385c030000405081406022041c50004622418400d04003c9006c481c0d00100040000d41003540140c6181c01103015640c05000582c1e01c0b03003500d58454000342c805a5400708205400c0443c026501d8901464504010308580f8000c8001e941805942d02003c140b03c0048015480b17a845841030340e00251319001c1090341d0070002c0c00344000903e03814000b400145215801440c51000504100342841d22950000701030b07038840c040206800103e0610320007000000d000d120701501941050030b241a0074002c5a41c1e41342d0740103000c585040d50030145c40090041035004034560401c05031400d0b05464440541541c500344038400c1c15890400d00d038400385441554420749004031310352006040c03210000c4403403603103900003d4810707640c2a540d0320981c025640e80040000420560000d00c44051510b500c2123041c00804142244521040c1c034400c60005008440c0350b030540c0d5242c02d110040f2550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 851829811 1250 851828561 851828563
    0x4091b0f0315170303090d0221070204021b030d06060905240f0406020a050c01020d171015030c110604020604180905010f1a1f1d06070609121407030c05 67
    0x56500c114211800c4002480c810743c8080011841102c0c0002182c0000020382d00481e41c400002503910783c01240480b0b00e0701d0300e180c118024040a070004001508002d0f503240306600554448001401d50344c800541d4002c040450b0040f07400070000c03810300c0d15070b01e460807000c1055030107641842c1c00c0303081c100303032100815a150300181c58a0801c6050030f5525561184c42c0a541c982c1d41e03010688980c0315000e000302c841d610015800c0d458141c1e5075035203045992108800000c00001030180c4c0e010800c400400b060501c0d0500d146189000556404a40c10301c4003100030300714022007903032546160001c0341008007503280c0100310350491700c0254031041141c1504103401c00414955074010025402d0519013200449180c00981c070310702140740c400400341c41100030404070a244103129a03058440b8518203049074043ca4402c69111031301c020500c2114600000140c0c0c0d54400203040310413a07034032400481801035a41d4030a03050b0480381031080d40344403c40c42a40c0b050259601c0142040940d00c000010810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 851831061 1250 851829811 851829851
    0x2030a030b0303130603020a0801140a150c0615170f06012606070504030210031406090a0e0304081005010608010f050603070306030816031d0d021908060702010204091b0f03 76
    0x1d5800b4401c13519a0302c0741c0c00240654020103801c2d0000f40590008030b20004012031200301101c00411b405005441c00c90f8003030750030100003441e200788030007001c2400114005020709219407400310699299141481811524041c00d01f180070b641d42c1c0f000e04c140380c40410000c0d16a040d1910980e00c001c40d0000440302408440b8040007840c264000c00090010182d04600648181c2c1e01c2200d9101052006040440480e181032440c0200e4150507c04205181020307001140c03c4022100d000c2407500c041900703207140d0f60041d8070003090780d4854041100d6110261182c41d0241015141a420315407500194504122840c00b881e841650004081401c00b4041d030b114200130b5902c11001d0340c881c420b2000c2c000108003001c1054000c596004010703040c112401d10f010360911001404200c120300c0720f800340040101d20750b0300d201000311301100c00b05043d142004040d00c0741c01942d002503511400c03c95054181d41c205031035600d01d6031100158020054100c000d0380c480c03400e41d190020340c3e02088400500d07525 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 851832311 1250 851831061 851831077
    0xa170603030c0d030c090e0717040c080d0e10020105060619120504050a0302010e060714090f120d021b09070806150d020d050c0403110d15060e0f061002030a030b0303 73
    0x300c58000b482ca802074041e0080c1d5203d003100c5d2601c41603180d5072007040914100488c0c0f4840050b00008046001000d107031805038015000e01301c0c448440c0e071110b11151510030071808072004294208112286c42c03410740da151069032994402885103042500c04920103018211403242400002d80080f40785502c00c19200d107030f00603140300074019070a0a0502c16141c41603440103800550074502045108000040c1c2c00b80900300c1c039500d01d603061780d0b40e1722080b003d43c12000b041d07680500c01c841c04a1090351054081460760344440b0292038503500100c0041d01e0030500e0f55040540320000340507100c290b0f0360ba001d5070b0384c40041070a216815aa40b88005000e0a1405000017071500002c46c08410098140d4050962407150780e41c10403440d151301c0b81189890003988802410440004114901c81c01c0040700c034901c040c03258801c4102b000010910a060780c0c050b40128581c0c0014a0402003180b1500702c2c49901f103c070546280075140c441e01c600a40324450f0808d10014140c4034003165503d520104116a040b03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 851833561 1250 851832311 851832313
    0x806060a030b0d0c0518090d030f0b04020406171506160203011e2301080304090221160f050c06010e070c0b090303060108180d030f18030905040c02030a170603030c 72
    0x124845184c5a070a840281c01924096010804481c04100100b030082c0e0060000a00401140300c010b10101d014203a94051880959203ca20000040c3c03180d0003c1c2c80549541d446400d40c540400e03d40d8400010010b01840c1c84203008580a0510f0720340317008480390500c185075200c841f0005030000ca0f000d000d100740c1450402000504c89c01e908070310b99104100c44808001d0b49903000544c884e105100f5803080c054040b5a8101300f10400c4200c20960007424021402900196802c0075200054011402240e80502900088007448501070b804280400e544c000c070300b4400d00340000900056628175050150480f003013600004119128010195110f05560120340080e0500d00400d0603900c0350005c0d1006804602e568000c00d5000214045000c0b52140c00c000500086180c4942100a0411142d080342a203945004183e0119901000c00c0320070303030094940d00d48041c5000140400c980b03c2600790421500107010030704840368021030000c200c610a445801c026111840003d085100c0c0c0d4a400c510317 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 851834811 1250 851833561 851833579
    0x604050d0506060f0a08060117010b090c040e061c12140d0603140613061119020309030601090608030d091a090d1b031b170307030b0a12030806060a030b 67
    0x810500051051003240143c40c1150802d01ca0b50074000040705c1801130190a4016000502012103c400c0d003401054036400042504100100490b50301e5006880000030354000203014041d41c80c905032036540000c0183ca05040d140c101402c0b038048803100c068020040c441d11030116021510400c204250020707001c1d00f55585034580040d12000f0101e42c40100c80f411a842c003805c00511000c00d4051050005026101d01c0d90380c50f64904d002044181c105200c0c2c00c9040c4451512204687d8424410100680086684448c0da03002c042c5032020580c40507a8aa040c000c0911074458040140d032a142c40521003c81d00f140c4a140c205801e03d056560b061800c41500704202140200265040d40d540044e120b2100c0308a401c000c0081c03008a015018001c1440c004079003442040300f052184101e40182d001301750000786203500c00309035842a294103000940740c68101c16107140048500d0700812a0000818014030140d03000b07000e03800e00408191044102042c0850b48a01940010f000443d00401c0386c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 851836061 1250 851834811 851834813
    0x60e0609180f010501060c06051509070810180501060813030e0409020307050d0b0f01061e0804140a060f060f0e061c060920060a0827010f020901110a0b060108060604050d 75
    0xc4688040d60b4148e800070f04000c0407402c070134010b003d108040040074024020360707070300d4220940d0b4407403000e0206400071412480000e80c0c4264128040e0341c2c041903410129555141c101700904c413000c050080c0100c6038818400500107a0842d0388466000d0058501041c000c20702c3c00000e007400150b81c001c50b00720f854000c9171410006000c2416103c3d00b0402c0d2065190390700c1c3c1004071100b1010100c0d00180080074451440e40301d01078032016500074883d030694004640104081ca0030110b885030112001030300c4002d500c00300003050189001400d500c0022483c2031b0b00c1d1682070901c181d0b0141129000e03090790810610148410703400840300310303080700382800304444910708501511090345081c0410705501d8211101c518040080317914200d02d6030303900180c540380c02400c8003a860107003410b0b410345140031400e031002803802c0c010ba090902180000503100c034501d800140901d070b80401484480e030010300e00d0400141107502203039040701c028a00045c660340e40758007280081c4110340026a1104071600c0c014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 851837311 1250 851836061 851836067
    0x80a06090e0d0219080909060a03060c0201051501050901050d0f0207120f030c0318110f0d110f09190e07320405010501020705040509030d110a03060e0609180f01050106 74
    0x40840b401c0d0742c01c80340b400c440301010b001800c03250040103150078401c01541115103800568507411101c02000310410743d43c1c1c0c0e5103072030869051019039005030351a281044501c0b0702041d0000c0342c015080c2450b40c40c00c02d82100007895071141004000203155a1105180e40c02846e9043d503c00e140d0000345100312178082d0300c010301142e110303090380c0e80000e08041030703000220f1081c010b6207004401280207815040b500c8c0d89520007548410b8001d908145040c10000c1c09980324242d80920034003a0103140600c0ca0041c0502c0101010740141a01928003041031012610809180035520004060f001504040080320700c0d04119156114904001000c41d00740c0720300072405202007011546038220150000802c0a01080e59402d20415025820002082200d82400c2c1c1141d9400700e11341d01501d181a00041400781140c0f00300e0881094a00702240d96a00e194040c420103001d8090780061940500c0e11500080c000e60000f824444d81300700c4c000208000b40003c0000c0c60305401c00794001d01040d80c541d0313402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 851838561 1250 851837311 851837323
    0x120b100503071d01080d09030308130b1303030f021201120c0f0e0603010e0c03060c1b07080607110a050c06071a09100f05010308040311150c1e01150501080a06090e 72
    0xe02c03040c00c54800002058680007a15074140e1b0f0441c1c660f030341110b20356107042c2c40503400100002e01c40000e6110f060000386040e012513125110950050342c3c02c40302ca040007021212003454154040d481003103211004810042c00b035044420344000c00508041601c1c20484502c00d030f511401e44000c8508000c50300802035aa0144205c00c1a0020095407100c10780c065a542101c4090b15015000100411110120320000300031041d441daa42c10081b8a44810301780c5400084d5200c4007a81d0010030a0102c1d50350721002e001d1448140c1c2c401041c0307860440d2a069110034903189041d20400c8000364103000c004040c20001480e00ca0502281c4803171a062441c2500d404180b8104544140341c40343c02c0b441f681007403249038180ca400c414802d06142c210341d03c0f4420740344448102a80000c0626400c0300303940d64040204168440c20000d081c030121020041049500c2c06450081d16034100b101c4c104034900d05942441c1116400d10b01f8071650344485080178010190b942140e0310303460a000000c2d14540c0c0005003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 851839811 1250 851838561 851838599
    0xd050405031e03041211071701020403050d140301090b2e110102070515060f060f0405010824130219111203070f0e0f060a2106120b10050307 62
    0x207030401c0c031545003420700c0d0540f1046400400b03a4042c0384240138038034031989005c5c044408050443d05640d807580d555840c3e141c00c188965025a400180c148100030003807042108a519500b0040100c8404101020311030205000f0152102d40e00c0c09103048668480c0000503040202c00c805000201468942e0b07003280400c030641501245021381c860b08460741c1482100c10b0180c1000c0034040400502c0f41032000c1c45030103400c207540503076404990f520654400008184a079110311a030b5070768074502130014102e8a00100741c2c02c00c2c480030f0005880c3d102002180302c040ca9008542d0440c1c1107620241031802800f0703d044502240140c54801d141c510b811001c1300c000018484102c60308101101000c9a5902c4129002e0000641d006000701009024103042c1d030000380c00822162550b0842000306010750410350713095001910103d44800b0307640414800c000e201040f07a41c03c0c01032a080c0103007071024a42881c002005429a000090b051040d59409580500402402e07640c100760384011000001c444022 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 851841061 1250 851839811 851839837
    0x120603121902010509160501180e090f010c0228020a0e070201090302011104060e010c06020c0303190b0904030e0607080403020a09150807180c0314180c06030c0d050402060d05040503 80
    0xb01c0c0c1c00940004244090081406c0e103998111300b880011201203403d02c6504800310340ca05404541c0001e2000c1241c443d403200c01c01010f0316201010304038203580c0503504400c19500318109003440340c40b040404204042c801710142c41c000e0514408180003401603402042055203e8040c82482641134002000c3d85009500902c00ea00c00030190a0362803050f0f01c80d01d000b14100800e145560350041202c09138040c040c08005080c01010b00740203003198021240b407442209904088400304103180f003001d12040d401d5071004010715142e58054003188444c122207101c0d202c0403403a00200014101207401030f5901030003c00005940d100a4400b82c407124489054050050308003140403580001e20208940f020701443c0c5100c2d2107088080c0050105d403002c0d1041548403841044141e12510003e03005040c0900d1103c100a080c0180508181d0349120641c81203400f00180015440c0307a00658100d885c4420300010503407281d20005006208510300c1c2210039007801c040006010011014110f00e8450b48 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 851842311 1250 851841061 851841071
    0x150405151213030c0f0501090c1e051c1a15104e0509010c080105132322020d06050703150305012003060612060312190201 54
    0xc00050080c0142000690640e00300030014207018115601418064020f0814040076400c03902c0f0700b00e540200103026102691561000c030b003000605000d00b8010008031009140c1040c03003034081100903040d44280751251010141e086100c41c080c0360a508010350040207501030149440f030b40b401914048030540c000d10041070062140d07007440c207050607201100c0d40c0c0d00e642074110480d000740054913814982404400d5001d00000030380030441c40c459080c0c0a8000c60b490164140180380c16100300524480e034990501c001020003e8020403400c0c1955001c4803040c80340b81c41110307a5070081002c004287c031054000040400c3c00b9044969150255002401441d064054545190280782c0c018030020740000c460030520010403c00d034040c036004401e42ca004541520313035044220004070f858005075085d03552000700c11694a00c403a4283d01d1a260900e40c0c0c4d00b507240480c00036a0074017030f6041d0200e401c02d90000086c603da5003802000e011011484416071a0b0101c407454009500005103a000958030341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 851843561 1250 851842311 851842339
    0x2031902070e15030304090f0b04020d02220807050d06020d06170d02030a092105100b01020f011802060d0b06211b09060903030c030f0a0f0801060c20150405 69
    0xe4644110f110400b50003189080d142070070060040108001c0001090340e150740881444d0b640d03000510b12013070381c00c02c00358640c0f00303a2002d072092210300d05070a00040d45904040120744004200d40341190b00840f0403100c0040241481c0b00a4401c140480391040d20300100401d141450b00e603030451060248007100c043d00c810000503641c0b441170490003400301d11200401c2100300014081d801c2240021181101207102da9070380d95160059400003d40d030b00740c80e03404180003960304000100211000388002e018a203484032805420340031504000e030151000158100031201950810501d4442c05064141d0355411a0301564817000c0c141c41c12498030315000b020a0981a81d55000d0361080c00c0461b80b0f03840c118043c003c00095a000d95800c0d074142c0414408030340807800603c040d008420750100165614844544014010204210318400b846001c60040c04400d50001d080384159500841c12121386030041c00400c40107020b444103590011101d000c02c0110142400030344102c600a0715026510b00d51 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 851844811 1250 851843561 851843581
    0x61903051006051215040b150901121803050705070e01150f170610110312090d02150a020a0c0516090b01020f1203040309030b040803040b13020306041202031902070e 73
    0x602d0b08904901c07455840800d8404010005d00c130b01c0c04600a00000c1c03424a0000447c0c0d45140500d80b034070031900040b40603800d0703503081502070100c421503400400000d21400711a40030155078003030183c2044000f04004041040401941001c4d007100044101b45695580107880f180503c8100c031000542c842c2e4000c074205001d200314844480c00f5014034489940c0303840500a40502e9138400408105d10b01d61701d965040400c0c4018100c6240140d0603ca0300d191404c40b06240000910107001194056008014409950b1a074190011603012015a54000c1d040e002c4a0441c10140041c1130b900800d0320f9611200c800501c4070040f90982c200600c001d100703a100698550749044110069038001c004c00e01750490140008503880303413103814407076016506c949540000a90881e412101c11100109105c1032103042ca0030280d104d401804801c0140781c980e070202c0e4445401a10041030a09056164183d941c000c0c02520843c040c0300d10110310310074020a0080da500303020f2194041c0070780c1c928045007138404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 851846061 1250 851844811 851844817
    0xb0c01150e04030e130c020c040e0d0c1e081b15010609062f0714030601050a03150609050a06030201110c030a12180f033e06190305100605 61
    0x240740380d1026440d42e61501c0c01d4541e010b2020403940d00c07041002811000001ca807049980d001c21075801000c804140c1c8050000702d0b00c2c81011280c26610110620140a6110702c040c1c041991140d00314000c0e0308000c1030000b01d04e00050005094010204100100c08a145000d00e4068040760032100440c0180442c40d01200b000e001d0b00340001d08045042c8400d5009030101c0d86c014002014507031405d140100c00e42071503050400c0054880c3c100d0b00741004600c0840a09009000003203000e04013079494040068080911444024000716842c2401e03041907071035905c460020200c1042c1030080340342c000d14032002000a800128085840d48030035400303400d4009030100e0107d4002e0000d1207000600d0322100c034842070400c140070400801c118906000d402000c1240024036000903280c2c155801c40ca030020303414290f143c040d0325841e03241404d60b04d01083d02500040724100504105050714890001c1841e61103a80b0300766801d0007000e5503d111156240d40450f204400080011000c607407200c40444140c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 851847311 1250 851846061 851846069
    0x706090f03081f1418010b03040506180309010c1e03030b04060609150e0312040b0a09060203031006050f07020a030c06090602030f0307080606090904030305101a04030f0311070b0c0115 81
    0x3d00c101205200c000d02c2c449000e20000c00044c4020070001d107101ca010920740c026041240b102101205110400c074007000895005a0702c8480c560b50100c2d10500195280228040c40b41002128480c4200384005480b00038104405900b40070728000c0c140c00e0180141c202e140401d805a031a101c0c4c00142d1034070134075035441550786024880425460b501e0080b5441c003c0030b026543c0c076008d20032180256003507000081c03005080310000a80c6072101500040c250030580e41c004825900108100f118003418034854000f0703581030341041d5446100749a15200740d801b0395403009401c107040b00e40104c1442480701d101000c07034605540e05281d04d511176800303c0c0c9a000d031440c0f40603056018404260028080c45079164450406009a030074140280c001568641d01910181c02203580d130400d000e20007004004d084003a002051000352500c8401e4004546c510452202a104036403c192420400d072082030707914031064060045a00c1603845038840340d0140c0c440100c0048561900b10a1046501c101003410211 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 851848561 1250 851847311 851847361
    0x622270b0406021e120412090b0717041703120c1201030b071e05090906030d0c060213120803011e030c0b07031106130212060906070f050706090f0308 66
    0x10340c8030780c0d8034000a500300d40400f0030071040300c00e1030f4004c021400e00503256031203032a43c0200c802e040c18200082d032100400d030741d8401c00c0200c0006000d00d8206008580001d64452800300d2050000011403003503005a4008080707410140e801c00c100302400001401102d4001d020aa20303d440d070341103854a503c50034203002c076450f007113900400202d41d034170903507d901c81c0103810481d140c3c3e2220a044000b440701d852403400403950101d40c2600303038100200d5056012509800130030030b00390300320701c040c01820811100502440e0000f03a0185841d03408610700000708591105d10358081d209142640941c0c20074061402c00906441303154a10203000c2544104880d003100e0158405800e0250410080e4000002503003440322020020100200c20001d41d445010b0540d2480801000b42c0704201503c1c072030310088d4166900001c14041c01040120310306801c1441070401011a05400c10107460f0f40c00381d1100074105510b070249036428070601c0550031510b24404d60340d91220f661424015043d401d0340203001424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 851849811 1250 851848561 851848583
    0xb04050c070b01080613030c05010605090a020414090403021b2106012d051003022a0f28051f060905090d080106080a0609020414190e0c03062227 64
    0x803d01448c0c030401e81500803c0081ba4803915000410003814040e5540e560071907000408101c10b9042510450303e842c81103e0000e80c81c1003030b0710025612410986054000011828501140d170380700d10400900c10645030030150700559101d0b20a0301d0b2182446a43d4241100503094004003840d441d102c00108040004081e0040c201410300a0407581c440e004070038540d0030005000701030000d02c60002031140d040845190400c022050904042c0d041280d004a175200b0240300e12640c040003902078092810203100a1000281e003001d030304d40341d9900845032030b1a0411000712020b00d0940c02440c180c540700001400396031901e01074550b56440011090001603031400c010f1008a00c40c680954001501c0d0302c0104500c0d48401051049a00c903501c403948528a40c4004001d40c02c2806c0d40c113909a00f1a10010300030783c58812a8242848000d00c90840c0000010010700150785a500d40072904100380c600c0411003d1490300c05004080c0010552241e4001480c200146220510400d00f0254032201c4040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 851851061 1250 851849811 851849813
    0x6130819122102130801051f050a030f0f030507140105150604051e0f1005180402120a0c0c08031e0c042601060b1603231b010b04050c070b01080613 65
    0x40250002c0244200c07250200d01c0c000f130060403d0160340e00230365011030107109180000740180c24081e4941c0c42240521101c0100304041b410b440942500c0541214505602211a1408495510400c04018070810310840030f00600300c4154071651141c4001860071600c40c101c01e003048a10300481c070643e603200541c8213480c02480d41d0f0310b1000d41d00d0f01c00600070000d20010b0000103110141280303403402c0021804108442c40400d82c1181074000d09042d00c0840c90081c0217130660207003010041c9080c85042e240c00d00030410501c6000c4e2540c000341c010440a4990600341d46003a04079002c044c00910390016071000c00c070b034030841c1021038084818041450700c04225002c092001050750101800707807950303180303000251240341c04014000c041060080400705101494043c00d9505c48440c80403112844d600381100d5441c00200b04c1e07010b0780030b803184485411300d50702d00da038054050a01c042d904203040a062000c0404444040d00c8028440c0070031000f1030381c03100c0c1c402d540c40f0006c5910035002884850240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 851852311 1250 851851061 851851127
    0x10311010203070b0a1d0d021501090501031214070602070b01080618030a032307021e010207032c030a050606130203221b080c01030612020f0613081912 67
    0x103000000b103a03c0d8500c0001b8a100300e41018010509174015070440c01144100903500f10341075001d0a00d0207000c004039411030b01c801044c5110a8a24001d04c088070001048107800001038840a41d8000c20a40d40e40d000c1c4e10388260802802e12509030306201384c0c004284407984100b0070360100c40b1824020b5003405412841213018003400010316902c007440b10320b400307103c440180e41a44600000d4004110070809050f035405c0c414040322048210b0b034414010f000002c1d1b8059603203c1c1000741c5010303250962884080300141003043c024955494401c4480300402c1003070211740c0c28403a450403540e00c90821201c00060083c2e2104070b5901e1880381424183d003c071002c1d10000c441c2c503580200b10900e51403112501c1c984c11031803160000e0702540e000c2c4041c104190303414040c1c4801b070314102c845840c06484560100d03044101c0090024420900030890032221142501030700b00400340c0714121052030b4505000c030980440e4a4600b6103070a0145000d02c083d890140e003d186c40c01d11681480c41081444541070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 851853561 1250 851852311 851852321
    0x60306090c1d060f0706021210060c030807110a060e011112060d032001060e0c2b02191d0301200901020a060e1c0e0303070809190608010311010203070b0a 68
    0x9035003da01030284004000f040e5000e818503500c11640103940f5070307000071041c000507401000007825841180e0b05109140e48140e9400105505044c0010a912011000e645000850450510038407508054500380308070781e041400840f05850080201600a072140c0c1e00e10f214009014181f40605004a0382504020241e948050b0107481c20081001c9800c07510090300c041405180f5907a07446440030301c000e03c1c007000e80c20340042c0d140d41d0040c603140041d0f090090000303401d020840030f042c80045202c010140c4c1d0301110300342070001d07948042c90103645801078103d0b0b03a0b45e116201d021001203140e07285030805120f01035645441d0701d81d5048148500d0050091603208840040c114091841050001100c1e070284040c1040040c01810a60f609184140038000c40f080c002010040f0740c050900e410345000c0210740c541608803c2c0300c0e95a070394400120302c40303004001c95000400002d20000480d50b03030000c05103040c0d80c411284204401c01c02c000480e070b07a00480c400035000d540e0007404503c0090141e0b001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 851854811 1250 851853561 851853617
    0xb090d090905160c0f06020301080604030e030316060e0a0209010b04061e020a0f03030f0204060c1104051611010618091403040b03191409010b010306080105091509031201060207060306090c 83
    0x8003c4001101b83d4a4106a803c00c0e40600d15a41c00741080c4410103410003130b048050f1409030000c5090254000400d80801b101c15805003d01e41e50348046941060180040c2d51150f0300640303806442c1d41e40c0c5280c44090f0348240324040008040028000c02608294480343c00603a040d4024003044146481380074000403409030072001d041e40c038171880995a0850000d00000d1907180c640326944091400e0404019030300d10442803107240b034801080908030204402c100c10b00098070301122142004020300d40102425040902c82140c0c2d035100f001900e03250341203a10101d20420f101c6440d411b0905030140d886c01540601404030000384002807400d480a0400d10703007984a503001040c40829000c0c0140d42000550310140d1b07694440d101031b105541c2500a50340102840002045240380004007e511000b03070710070280800103c900403d50a1804000b81d40c15007940324503100c0107513036403070020b980c6a50511566001c03e092900004060903107200e488020200e544600c0003e450441c50746200e0b6819400c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 851856061 1250 851854811 851854823
    0x31409150c13090207030f030e0a0303050601261012054606060506090102060109050403050915030703061409070c0203120d0b090108010c02100213030b090d090905160c 74
    0x2250000741410000c0c5840201582c2c0401030b5509400d00307005020381a040210401c8c5810301090480424001a0719281c8036058a00003900307454200040311000764501141843d5191002d041f081d07600000109406044699420001036944406801c1024115200a0401c2d0014942c1103503004e4515030030f000304c0200301442070200e00c411007452607010b5400f5481c618050200703009410042d2a00c1880080d103400c0703924609025507180001c2d030750003050144600c541c3d103601c082001c240c095400c0c2d45d00c0503c01011a42010045061030466420403100000082c0c117000b000241c4030044001d80f01201c50144c41e003865540d400209a849000f40c1c602283c061281262110b0320304001806481102d00610380854280916420441c00444c1070300900c10f80d0b45013403030513541c980c0c002404591010344010050b031501c400c00c0d0003462600440d030000c2c088100300d030100030358900d01103215902c1c0c0041703403140301c2480d888000610441f5001c550f007c1c5a82c1c046800815094002c82c405218103200d19 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 851857311 1250 851856061 851856067
    0x41502070513050601080703020c07092304080705060c07020f010e01180603090512040e040224071437140102040308131d040f03020f1c031409150c 65
    0x80b03032081084461000c1501d07524000d00c0303415079220003142e800500518065080111015039161502e03010320a450303c039691036131000c060032002c009444148902000a6956103030508049085611102d030884003400f07400001100028408140c07a0f10a4000e0f2a5282c4501031340c1c01502c50b0b2a1040070b1a06100f1101106803c00984d004001c015007460364020442e1400c2d40341240c0303170000030b4060040c1004244402d000c3c161000e011240c1c040d404a9880301d162502900d030701d034903250004a2469440001400d0402d110150405405203000e1608440d0100c82d4a903c4030035406401c620b000102450b1150403030f0f0071000441307040e041d50003030341c0c40060840c94015650032039202da44211031940001c5006418405607011800052192814031698600c1c085e030203c3d159580248000d2205440381503100070b062081190b0505c1003210421a10000c50304034140f1a80c559500180000900300038506a91403203080d041e2b8001c0305a10020441800400c3c0d003454040001880c0301c0150b0814 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 851858561 1250 851857311 851857319
    0x11e020c071a09091e1609060908060727030507180b01120c02190c0501110610030303090c0e0f180106081b010c02060706050f07050711011101060504230f0c04150207 73
    0x960a00d0040803900c0034242c032000e075410047d040031200d034024003d11a2011042010580110b06203a1102252511200180c00140801c0100001700a10344c0d114680c94400b00070058009a0f200c1a01c003914602032400c40818015010f60302c640f0080c0b400a004450700070410911508010150401c90050301e40700706903440100c45c030390f990003401d4a014500b00700c10001541c125000014102082000d040a440c0403081c0c0c4010746010310009003055916040c5a06002c481110803020b05189640d08045007070038452221910010354030300c1c0d440c008100c1c1d03038003402e041445a08110f80b034103405050452501c1c600000c070244d0a4600c207042c80710f042e11240040e901c04000380620b900c24000083c0e507041010424111382001002a01400020041c03240825043e00084180318030910b401610440008020b90241c00345034042c4e508281840c044080817208040d00c404c10042401030501c02e0f40d295003541640010650b412414030008200521101407c100f8004c2485450b00498940641d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 851859811 1250 851858561 851858611
    0x1b0b040602101b21090f0623011a0409060902091003150b250311070f050f090403090902030c1e130b0a051920150117011e020c071a0909 60
    0x8600c04079006d551814603002041340310322171911154543c00c041e80d001410600161615a8180105002c02000c1454400d004100d88101d401500f000641404900d0792100c0c00c901a4002500c480c0c0701c0c074254028021068401d1050141c030011511156070040c0c68403c9231a5180d000d81084810421701a40c130440c1120010340d01c10000d0712075070f15002e240701111006801e00d810354005010154440004100300c1d41e8040420351041001c640c0040c2da5110740c502503403490080e0b848014400d0012040102da940102d0107010700740500300101140389401d240800389072003107030020b50a0090345131052110008030340181996880500b003e03841d12004490808940904400300c000151401c00c0d11024104c5441c21030b03c8444d5410020705030740c2040000300c80500c20500540b103901000050f14510441c09400c100caa0355007119080c03082c00d1814100c0006544a0f29144010388185103000071a10b034400190103a240c1c20a20107410b068264040140c1c41d0310150400301c03803c1888501d0103030564 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 851861061 1250 851859811 851859821
    0x70606030c03081e040b07030503070201020714070f060318120c05060f010504061212260c040f05060a0c0f171305090c070f06091b0b040602101b21 65
    0x10180040f03a484002ca03a107a0380380900c0464882c0c40150081c00f04110409018080d82c40340c650504040e40c0380d40d54110100d00a00030f4480c0503202400c00d41e034860000c0c00c0841c1d0003050b01e410544840c0d044d6201d940036800c1d60f941d204400c4098082d410b6540c04510590300b015455401032500040207803a03920350500e8400c094800b0324031940ca0500405c0f02e0703e01440f0701e0b130060403a00824035261070203454102c01e540a001c12070701440030041513010f060802800107000e02aa0211010207800d000072941c6640d00940162406150801d20114951034090195081e20203160b6038003115015654440d244107950720700c2151510352411000307c4e4402c188028225802080c2c00d0045060319100400221101c040d000189100b01040181c0c0410280b01c41d031103021741c0061011555400501c1c041d800510440385004d842c038450840030500c4c031080341c02401103404035400c8400c0440d4075114102150300c00c480c1c0d807103600300c9200302d008120f0194000e120011064600700000014440d414801c1e60 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 851862311 1250 851861061 851861063
    0x130509042301021804060605090405270606130603020307150504210209070305070e0f0d17041502070e0106121d030c011802060a1209061b20070506070606030c03 71
    0x6500450010404082c2003000c0c101365a0444003440303c0351900101500300c0c030803072140501440d1210001050400300c0707442030804036203034240d0100c04510005050340307a54040e641d8a10507203a40e000d0a49a5010340142c0c82074a4004014080d80d5180c0b0b8001c00d03260306090240f80a0002c10f000002c1d001005056440f06481d0302540124200f500c3d104224115200601d40803e15180000340540c1507840740c07100244040a540e1107000c0050600010030442600e0002010030524000800d4021041000341045480c01c690070b40100181c25000d98666000d80140075030001071a004110a03407142d80c1400d50017140e103400007101151281400d03080040b007105804d095000240a4060410074800c018840c3c1110ba03200303d0501c4a0b9000031003500c00c01500e1400c101284d80c1d03801560f02c00d070388502549544140104515041c1d4241c6907680d40c11a107998010407180031803052117019000b42c0c2440301080da0b0240542038100f100300721a0340c0041d14142d803210f644000101c002400b42c00d05d14091 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 851863561 1250 851862311 851862313
    0x603181c09030b0f0f060402161205040305101802133b010b1003110d0504051b0103140f10030c09050906070504060207331e0201021305090423 63
    0x2075080d41402c41c154032001d00700c101031090110400c0102c2c0300301c2d031610781c0240b01102d0159071384052000624840b618194007074210801e00f801540040d401000a1007141c0c450029100840341c012228800c0303030012941d0503080740380c0d100c134140145040421000c0c0c982003031600143c80b1035840c00c0e03d030344070000f903039400100e9000f01c6c0020303464a0129041045c01d0043d0000744403030101c1101086600851000c510241a10b0752500c281310300910003a6015091866820401441e25060965448204894890803640101c903144515403180c05500780c0d0b48840c200868464071414050810700350014801d0000c1c0c3d09542e801710000d8065801a00180744005002c0707441c0c10700e01441406c0003c003603c2e1605000d410001000b00c3c680100710a800c8642008201c46c2004100c0742ca0b00d1034070340c81c00c0041448a1000300440704250004070b52440b00d83d0000103c400d94154900a900704d00c103000d404116040684001c000b6032070084240b681c031a2040078940c411420b030000d40c1c13400040c60085c008035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 851864811 1250 851863561 851863577
    0x30601030f0f1b09171f060512070e0703061d0705040b07031805030610140102012d0c0509130e0c040212150a0e0a18020303030108010c09050607020603181c 69
    0x7182c0e44210104040c5c01d48401c0c045400010168056a0302e807240244e1915071020180074400f000a94010300003010083c2c82c1031410845924000c4e140c007210300803030303596000b42030104000038401d20a82007516a00311848000700c80080c2c0503410381d580101000201314081101240311000305010b0044a0b22980760008001e103184181e02c06526107800450103a4001020814490380e01040352044400840c040140510513000407030240030400640a008200c0c40344403d10100d86500178603840b030300c0c80020864100c1d00c88040364039100c0d5070a400e5100c28080782200800c44194010324003064020115220400d0040204040c2d80224208410701203e400c05c01404403045000c0300e1054004480c208100d0741400646185a42d001d013101030126911840c51500403036454507091000c1d0000d0440b6100e40e56444002e019206602d0350303c0010b22443c600041504000069808483e0300502082c00c60f80d81812600d0b01c842c0140543d0b03010b11510075140c2900540040070b601504c035943c1c1d003c0d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 851866061 1250 851864811 851864861
    0x3030e0f07090b0901081c0804031e0f020d08040201050d0f0204090e0f0d050c06070c0f170306042a08072715080403090308090103110f0307030606020d0203030601030f0f 75
    0x13445505a00045e100d4000070a20915084121090030200b080d500301060301c0d84a0f0b09040792200000c0c0300d0b040210820260710709c0c100e9000702401e82e00301480e6088500304800d00d441150b82900c01d0f05c3c024040343c800c1c884003c2d0810359800420080c0d4403403000506007a40e400c0c04a06a6000a824451a400070304403001181c1c01403054071404072050400e04d03e0110b4200710b056541500500c07184c1003180c462017240802c4100444c240c1015005030030103a1000e03451520b51307066801515401e1180f803401e844005802c940c0a0002401c10540182d0078058002041c10340d6402c0703005202c1c01c200400f043e100104422a0300e01c08100d001440703084001d0a0500038941803948204c8200741c2405011000c20000a60084088003565400b000494841c81a20b005038040d040c0d005c2030854102c3c0210b04124801051005544150440d540605c41141d8842c0103980718003034180d107000113030010000200301d540240c02ca0b04060510700000100640c01400100c00c4a09902e03007a40141c600400c840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 851867311 1250 851866061 851866069
    0x5120d050f090402040b07021507111306030204090b010503071706150102030412080c0c0a0b030a0b030313080a020310110d110d0203010303031a120304120206122d070c03030e0f07090b 81
    0x108806c4240344070182b40c0712107515001001034155594911403240b10110030511046030700b01c40011580070704148001201341c545482251001d01400f0301a2045060015070f80c150102103104140390400501500d459400c00c80e07034400b0314449800e05501c0100030006550490008440305240101081d940b01c1e01c02c1445c0504182d01d200e481c40c85101000307001e11051114800716034010144610010300090300c2d0021034114002d00032400d82040e0034a034005000c000104000318035610860a4464140c0142c040e42c040b01c3c418030140400d440c013808000c90f441410b91150b24120303c0309090f035090618640000060380d00981084000139160345a110703080d900b103541c0e2a54502c0440c1d41e0703c400305034086000d036680154494101040030030000d2200355200c8400700e170a203980c8074203418101c0c170f0800ca184210305a26030903440c0083c0d0141c1e03040100c448000000d40109129501c0040d52032050320118003a0554820694941c06440c1e0144880802084540c004101811001c00c06541070301c100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 851868561 1250 851867311 851867329
    0xf0901060b0405010912060f0509070302121914030d091a15130c03090812071d0315180607030b01090f050a052701030b040c05120d050f090402040b0702 67
    0x25030907010140414410303a80c2100b100703000ea821308203480c2e01c8800c40e0f0403d080a0710310902c0070304202d0b00d01000d000706034401050071000c1e68026911004034180000710a07076103900f400e80000076811505940c3e4000f0741d50302910000007030528112070600c52082c015104440c910b003000c0b2803552140010600710000c0e00011580040c07450410103d00e04103038040b508044101641c00e045035682c02010108500960003102c82a03080100a0384070301c042c22911080e407030281c80c42000710b5010040200040700c2d0120040030340a014018084d8400400244200c5001c0035218040d400d20400030994500c1e4100401403080b60180c1d8081500b051940000d0050380e103d4108a00b03c034038200c0705100c517803940d08800b0115402911082ea003180d2024184012200c0410002c2d4900d00481c0008280714030004050301450041d241d10320340366901d804002d54011000542001c98000101e91401980950060f21503d8072480c2607615117141c83d4002403c9038056000300c143c0b02404908001035040c80740c40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 851869811 1250 851868561 851868569
    0x8160606060c031d01051317070e161b022701050303040b040b030a0e0604030c03031b021c030b10230301081207170d02030402040b030c13090c0e0f090106 68
    0x442520704441d910010b10000090002e100e140702c4130468680b20383d205004a801c00400000d168020640303449000301403070b000030600d22442c82a00404102002405c00a9000310b940e200321441d11040078401350750640701c00700c811201803030645001002d42c0b117800700780203200d50074000f0440c81214154481c0340690181c11481c0680e006000c00d010018118049074280c802c01017800340c0703d41d201080c440141111008008141c007400050004054009020100c2c1c903110740c80601000c3c031000800d10703401d90710180c01001a07210800d512100c3c051740303458003c14000e6140200b00c03091240c012881030072044010000140b14580020207040241034018030707000c2e41050480c550b526145030243e44490407846101800c0e8005440001c00c503034604802c0b04c8220000440741c8070151102d440000b5007080764140d02035400d04212200514004c00c00c00c4c611a0020200c281e9035066504080c02403044080c22140c2c0b5180e10b00220304d0000c0901c2e000d214000b0040030b0300b06850300000340b9082d0b42413548 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 851871061 1250 851869811 851869817
    0x12180e0601030c18140d2405090c060d09020a080f0a0213050103050a170c07182a0318060203010311130902060a0f200309030c0d111c0816060606 64
    0x1980c40280744e0a0404c0341d050309030b0000c00480c214001000d6003a1481c00034080d00c1e4079000030040d05407204200c01c218260360420131040e03640805042c0c03030b5001e08104036803040c42001001a01c0900da40f1841480c0c0c000b401162070381d520380c03001c41d14010742800c90b52a40e9000092220440c030348401c05081c84129107500380f000d03500d5503550702d5840f0440b0100a007500445005580e41d14507140658000e5050602121140780e9540d1b84003100c920004203000840b82459404010300f0107508856400301a2410300ca08012030701881180206101041141000c1c0180010303c0031891900285010b580510304c0341460b80b0074201088628400034207181002814003080c1c901590380c1c0c1042c0c52801c004e504019400448141e01102e981c0f091040f030542041c5011041d8169040010240151140a504540521544d0b03000c0144131a0f11800003424268001c0c043c4000f420001984940c0d6400601050407025466869102070703000542c4100440f004c800c010030074002c41d40218802054582 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 851872311 1250 851871061 851871077
    0x1110151a0708070f142d010509060f22350403110111011a040510050a180e031b010b06090d030f0e060d050a050f070c12180e0601030c 59
    0x255030401140103240010784030040b24130b25041804130466421903000b00c21816100004036500c44014080340a205564003801d4034006018154814403c66000b540820000c01050307036a10191640c0980051601c6403080400c00d2480c107039140e522040710f54902c6200001394103c00044105180040e009600f01c04040816049141182d0a412176054a80080034a06180c00b0440140c0d003008500912020b00e600e84802d01088480707003140010f010401720760034055a250000d00c040c0f030038031a000d00f69101c1030300b00301042100c11070190480d4a50000401040c000c1400403070f00d0858004040c0440c58075aa1925004018001c5c8640014620216101c0c0d0230a01c2030b0000c1800f825a03d08004d081c420801101c2c190389004202c0c2d02c00c0c1074002403100d5581d811410181c4003400060f901044514100f2005c1640c8409410080e849808944c0d070b122303100300f01900d49081c03140710b11425805101074901d2040461000c40c0324007016241e40c5c500c00c0ca01d418a2400101150004242502000410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 851873561 1250 851872311 851872313
    0x30108100c14130e0c090405060402041a1b0312090d0305040b060613050604121a071403100504050703060501110c15070528020306010608090a031110151a07 69
    0xc41c0d00d003a010008000355a84070507418508a84210581c0c019030f40040144c010403070001c01580040624520a4034240001e8480d0301c1840160b0066015034820704c11694135100d00f03401440042d000c1c442500351460344034214951410f09640c400101c036081c10000380c0c00c120003140e00700705040048045143c104194501030708c03207010408001e80780300d00c150000120000d00203010b9a824001e0580181045c3d030b01d0783e403007030000b0300a221180c040712011000305640310461840168144501c156454828804c0710981c0130403104e0740020620100d80301040000f00e0261a1440f8041c031815540c1c90002d032081c24400007501203c070310007050803654469503a82200b615901c007500700c814009503039151941d00b24a000c40c213008003052200070401c00d03000c84c0c0380081d210645009042b4029815a01d20b40d81712101200d590100301d81d816a640c0c48030b413240e8000383c0305000c51418200c5010568140e000720801a0040c0c480c15180d02407840e032202400e105d110804278500c0000c940a1108914086007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 851874811 1250 851873561 851873567
    0x51803030103080414190902031014030703030c051005072c010c02012010020d0b0109080a0b1503100501090510081203090102041a0a1d0906042c0102030108100c 71
    0x2079800754001c000344290203072445840f109241c2c041406c018100c0841240c031020090001e42040b50360295134914000700040190041482480c41d03074018020b40511429501c0948045e60645012161449504d60302001c0307150398822540250466075628090000e903806518070b07108078115591420510050080c096a0131131902c011250303081c280300800040307455401e0310140b1918246c1d4440d01441d1940d4100f150340da80241030384480102e04000c5c00921000455011a55000b0850700b903020030b0391040071404c84020396902a070411903234100700040c480400d0919440a50020829442d01c005000c0b8030788900074140c0c420880005070001304c0c60540e4450351560081c812161983d4004042100c0130300179011200909a03894100b4907150311106007002d2076006800410005400079003c1c03c141001003995481650000c1081500b6210706081100034045080038050b16038903412201c101c507089407240e41422101900052b10b03907150020460400c22400c4c202090180303048042000c140d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 851876061 1250 851874811 851874817
    0x110f2a0108070e0103061d1e270c04020406050720030c0d0c050907020a0b06030c0904020402030a0e060a1409161e18091115040627030605180303010308 67
    0x2e03180f03000c403d40461000103030010709403034000400382c0e042841040c1001c00e0608995000780c080d0010101030303000e4165003030043c2d0001d48841d450500700301050041c090701c0061003100d10705944183e5504200c1d55000900300d9000d64000ba02040d004140d8100744016034071215003454820518820314075240c40040e480d80c02c808403280c0b003401c04c440d601081c40b403441c081c0030103800080c00100340350414901c041d40e41c04500108681c440c06240004402d402c0205090000742e030084c1080d134140d1642c0c1d0810000e5000140080312055445c0b00d84a000e6a00300106d501804d06030400250035003440e4440c2d1100800100203c003d07134441400c2050b2030004041d200c0481e0291103003002040039020f041c0c0d40440903a440488235107812020148c5504140d840700448600c1040c80e1028683c610040c44071343c605000c00440c4805c8144010055203004400d0740289a80e15002600d51075030f0b01c450b10030882c0f1980c000b691000da444040015540c00882d110301c19480c0d010085042d0340c5542c1e64508944 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 851877311 1250 851876061 851876071
    0x112110d030e0114041d06030d0f0f0309081201170c1203031f030f080a03060e06030a082b1a0612151305090609120906030f07110f2a0108 61
    0x40780c0c0203c80701e070540c0501d0a40b005411892046c4500b414001c00c210400a000c0e1689480b0f0b0040400540309240104910700c074005140d2144100286a17503010741c024207844100784c071900307402c00a410b101001743c401c0602070140e1900c0501c00c8000100c005140c21281a4024016810f0201e010800400002a6030380540341c04040e821041c90324007000146d20481e80014a0410740394116420000e0300ca001e800306000c1a81c2c1042074070340c0c1708014040c265042d111250150020000f41011170300080040804404000101421b92000740b0740084c5040e0326441c014031581c0d0b50600300d8040000000303001c2c02880c1296514180601c000c40306e1200d0b5006880043c0030950b2024008141d00c0e148520b868040d010300d010482850f0000216450301c0c3c0403528000140140030655911030079010640320600006482c05080d0b560300c0d0507200002401821000500445512010004a0400180907018840310140c001412844035250101040710a280c0011140d603c04141e03590348202415840 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 851878561 1250 851877311 851877317
    0x30b0402120703120807030b060901121107150606020601182304030305040309080616052802030408010f060b0f22091a0a030320030f030112110d030e01 67
    0x1544803480000c1d034105104964401074061414000305004804082d03041d4148035803905801ca03611007108500b203800d000007140d0701400a01900e0125440365070b060845000c850070001e000c42c0024440b2459400c2101c007103e0175004003e0031200179519008600090016000030310455043c20400340c200758075210540b9040d40d0700c1f281c01c40190700740018a00b001c0c0400003440d00600f047e050080142c07c3c1180c055001c1005001c00084610f03002810380c0c81500707408148440e008814804131103a0b81f14008031140607424200410103415889504402c3d080716800465440b480c0100090035501d41442904e4210f00e044000c00545002d1000c40d20b40c51036403640141d035604822045a0300140602c0c0034049005008404941d199a6a00403c07a007800400c1c000c130344205d11810400f41c1c013407074003008000a460b403a241e0500805210140248404641924280b0b50952020f8007581c2090b40401c0485405604417000e001d61402c0500140324151110310340001c1e6602c000d068003034402c03419410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 851879811 1250 851878561 851878583
    0x203041e05090c0403060e1209042409060e070509011e051218070905040c0501260c0d0608150f07090509190b03030a1b0204090b18071e03 61
    0x310110190180d0103000d00608059141c14a001d020b01c0981090100b100c000e498280a0540c1c1d00000a41d40c4100200200592408400c0300510000e8080c1c00c40e03d20082900f00103c81c0e10031380c440e4104c0301401c88203a00040c01880d050146650390b402419420510170f040022aa640c1d0b4070040d40d0010402210035290300543c80e0300103c0300c6128011410720800030280900c50300c000410102d41c46120b01504030340c1c1d81600d40119400f1103400f9074004100601d8540c0c10405075021744102800e00341d860b50b6a40a19940d1940150120421a50420f89680005441800094130310425028000e260005d010360800000c440c03c4c410f0010707081c910107071003220009103000d22800f07265018101c040c02e01051824043e100b015441c80d4162038140301820908102060704001041d03c615400c0c96031040303442d40c0c0300b41c5103e020427501c0c5402d03038202c0c1c4c440060401045250081c070b8018401203110160006401c003e8a040c40129080b6200b0040700040040700780c04d1407540031054a40040519039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 851881061 1250 851879811 851879849
    0x170f01030314040509040c0303020106050a0b120717040305090a0608070c20031506030606040917031306020403120206071128140d1d0d110a0911090a15020304 70
    0x1c150180ea4004c651260120040108222076040480e088a2007030b0001c1c400e240d06c400030003184807002c0c00703904000101403001c811424200c10881ea0000c0860802040030159501c80c1c07800742104607800c0e80800c800140d0f104c005c1c00c2c80b8a44100411003454284a503003480340d0700170714070f501c0d040700038043c00702e038900000800108003001e58018000404940c0300c0003505181c0010f5480c1101c0d210710900802000400b81d00301802050515a84403444114141d1411001d041d980c101a0640c10302c01c2080190030300003100b600c0240003035400b4141c18401020304110007460300000a00040070000340b02840c801019002600c1c00811050641d400c96008200280c2d82e1301107446070020380401040740c84e40d0142c10000c1034070f40780c80e950f654545100c10311390f0b5400c40101c2060240103030840001c20920010420445000b840e82400400c00205039640c1c03002003060b2038031001c0c000a0a500012900e49500d042c0044c0402840d0800c014080c00328580760184d181e0040d44a03200203500014004030f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 851882311 1250 851881061 851881097
    0x30305060f091003063210050d1a060301110910140d050718031e03120614010327030e01140a020102092e050f04210201170f010303 58
    0x4845009890a9400c0c64400e90091070340f5201e10050f211240350081607240e0319005a0503100c010003088200c2c1c640c80c440804d80303d14102c020301c00340c0441c0d0401804039a9568001c0c030782d01982e0261054240d41317500c002140340c0030000a02014420b0703140007180d040310701a840c2550b62142d012118401c6c81c43c6149010748036940c50f503079000c00c600d50000f0604110b12465002c140150302c540e0b075030003c18120141d40c40c64007207140009060b80a2281900c1041603d04c0741c040f400c64840c0c0f9001034201080329485003a24035135001a08880f030300803450b48065a051007075100066615010106a0043c22890746140800d001c015081181113014a4034990080c0102c0c103c0100204881765901c420301c500034000c0d000307007510511a4601c138489204820310f200c49020303888809250310401c0c1a10000a8540340c0c04241c500d400031a0030301c00050350080072804145581481602d4a61004c1c1a200041ca189580c2e021030154107588000e000780403021405041c10740e0ba060074640b284141c0c2e09200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 851883561 1250 851882311 851882329
    0x302040e0c04170f03030c0d0207290c09090f04030311040906030b07111f0b030706031a04020a082206090302031b060c1e0717041406030c030403030506 67
    0x40c8400d0012002403002482454005000f103c44040c4103803200c032070a40c00c141d2030308a82070070b0459641c0280701040e0101d074420014004c489030180010320700700207996260b1003818042a481c4c181c50403802e40c562011001c0d0503440c3c1c0202220480d6145c00410380028441c0d0304081c280700c0c11000518001010580264824503c241f00c5c4001c0c640c840396140101d2026015500046984003d030401048440d0301440c880012910124090100d09199814640c06c075a0090841485182ca550041210741c900740140c1c8081c00e0034ad03902003180d603142d50f5052414043d0515a41c0264030400505c4000b552100015402800608a100ca40c180c0503455075281c883c8041c024014030324250242c4201500000103010040000c4007110500c80d14040058841d0021919013050390360400103103044c41044141c40cbd00704c070410411a410100161a603560b441076566181e848018005020710000c1c00400000d0703c040000c460071450b41c0391110b490460b600000e400141810348500109445075240640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 851884811 1250 851883561 851883569
    0xf080409060b07061119032a0e030c060702010807081b16021305010501020c12030d020d0524030c0108040503070f0b060103060e06060403030f140406030f2904020a030204 75
    0x3489140d89400880c0b4481e480400101c903002d241041c1a644007400d84103580b101c0c40840f11165012210b1402540030f001c0038040b5080c0c43c88182c2600d00007410481d28156007020650701e2607e19604a03050601d460812414a0f100750303018001d4a00503a404280035620004a2030078066039115580313520444500310381801105100482d00902104401400c0201c1038000ca500501c01500108420200c507801c0c05114016003104082c940746060042c00201005100e004a9190100390b00240c81281c00000c02d00181503120700501040210004410206054101c20740e42c84d6903003080060755502d01000d0940c1803004a9000a003809000d106641100d0b800c2140d108400c00700c0d19010b02c03003400c1150f1690120346003c0c000301d401200404281e20401016050030302d000e007148c40c161128001c000c00c8000b0008084a030300c80442c000d801030002030a00741c60100d8080b659a00700c2c82615140484c0003440307151543d0011100e00c1c0460070100408060720010ba4410384500c04401034444c2c0c1e00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 851886061 1250 851884811 851884829
    0x4031b15020307020a0b0909010b0a0215090c030606031219030f05040615090911120c03120d05181f0e01090c03050c0904020d062f0c1c0c0f0804 64
    0x61042150350040003c007801c0d80308550700750010342c42e20204104d900071208030503000b0060100600c22501450b00903c2c000300140110350740c1040c4410100b01a24085400300041c5d0040101d0550fa42003c001b100d0300820301314040e24a076030404901c0d1045005e082400c00090141c1640e0b410001e000c0c0e4000540511080d00501c8a0726050a104020300400619090440102c400020702510113115150700d0307035070080380da14403032401c0350421200700e110003190140b07400349003980f65140c0d42c1000604000d1030b280c55069207433894040124100c0d880245140c00c1540801c4010503c003002003500c032103001d002e40001010010804511000380700c10244c15105610304604a004d118081e90002c044030710032400c845143c1c00a800344903c1c0d10707041d20025003104041100200040e44c41d005030341484412072491050b4040d501c1200b80300301601c080c2054800002406088824007401001c0103041c01001c0b0620386c05065138010200681c0c0100605600791000c2098100303d2043d046030010407000d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 851887311 1250 851886061 851886089
    0xf1e060c0201050f070203091c291f05011b03090e070c15060b0a080405120d0219030b0604180b03031b0d02010605090a0f0e0d0203090a0509090304031b 67
    0x300301a000f400152411040303082060005034041c3c0c130010441d00e61100141c4401302404102448200d208101c400031500050300030780b841031520400c04003841c580d11000700340d0090b0600c0302e6401042007901c0601c6100721000e07181030215981040b0807040c40b403d0366200c1246c17001141411907040c5581d42050a114070f282c0f0030301040540c4800c1c44a039a034003e030f04261480c210001c440c0c1c110340340c920600550f850b052045c0542103001e5085294018054820b450342c500710a006401c650740300d091000100c0b40d02040d04905a15440c0c00080d14a071a801c0c10040803514000255003406148903013001c1451310701020068106941280b0712019003e011651200200e000c4c01140c50320200d820401486611440741c91148140141000c6130000b40542c9150340b56041c2e50170183c07081c003501780d44003500c581140c201d00900b0003001c544c0e400164051030b11100346500700039040e40540d0203148a00754150034000d564101200f1241102e07030040c210070b00c4041c444a503032089000e03540407514402000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 851888561 1250 851887311 851887331
    0xd090212010605010f1706120a0605091f0b0102060a0510090e0d081f140a0b0d060510030b060f1e0c0109051005091902220e010c020a0f1e06 62
    0x541101c400c3d50300c241c881c10140f80000804403010f010898452079007821780e0b400700c2c12070b0400040710303402c801c1e554080e01c40c03c0c007040e158a407d0300d0f01a1219881a446060504000412508003030144c0031406414004200840d0000b5640c1c40c0c0902242406035603007001c500100c0c48081c1000050841c03201c140410340d0058820b039107480c4820510400726040c0c0c0d0000e031040d80005000702202004580103e041410403038641500c07000144583d070407445034440414080d440d6006403006c5000c1c00e4022911904010030f000031002103440c1d0b10241130a2030594503a599800c400d480300703c110b98600316103500e00a1088600080c0c1c0c908a0205150000344180d94080190001d00c07a05001d50202c40344400001d007654102c2c1c0d002c0b21204426040024903401ca280070700c41c560780311ba00080507000d1045441d440d503495407402d0301e189910250b41e4418003019000a0003180301c0100a0b0018201c0f852181c2c490801280700320800420000c911143c410300c0d20340c00910140a2500710310204446508 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 851889811 1250 851888561 851888563
    0xf0617010203040209090a17030402060708041206060801020a0c0f21021c020a0f06020307031b0306080c04020906120a0204240818100f02070602120105011706090c0d090212 76
    0x7030358181d0040c1c01c440d00040c903d00001071f0344c0035466408000036200354a6105291041e40001e882241d0010b001c00070303507012690b04000b030300180ca22581086c80c0002c241c0f400700300b280c00d9075010040c1c030b900603c01d4004141c2c01002024103030360042510780c0505607a1404026064a9002c87e041807204d00c4a01071481d80d000909081812014190002600107104107036581c0c81214002407200491218007000100340e50043c0d03802500d070742400310b40302d4088a22412151001515100060b940710810001d000040296400640b4161740c114500141a00403404ad8450a07580c0d04070310443ca004901e104010390304031001072070b00e0403000780742c03070b41500110101000e61b000a0000910400100b0710350010342c140c001794001d00000810100011800e014043d101c1c40d1404200c4650a024000c00319466000501c088000308022403410343c14000090060101c1c106116035003046003081002c61380b1a1005a80c09c142031500b01c0791640400081c21001d02040c000081d0800b0101c03c444101c284 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 851891061 1250 851889811 851889817
    0x90a080706110a0825121e0e0603011a040f060513060f080a0e12160302010e0303150d2d0b15030a02100903050d050c01050106170a0f06170102 63
    0x2941d00d0100c0002400354040d81c4000059001d44644e404110b890f480b06a00d07442c11083c10304600c40780c8901103070754841450320034032207100201181c6828010007101b002d5480d004420481170600c0d820046480d008180da034081401381d4500c00b90880d444212401284007a20020b02c040c042289080d40ca900c0c00038031642101000300345042c1c43da400816900d004038010091007400d5942d699140d528100c1001c050101101d01c101c46004d40c064111415058000800c1384c4120210820f103209603500c0e0090844444800d80b202c513400a000740100540307582c4846460101c01c94441040760420305120301c0c010703280c0440c02c500300410f07403943d502c40035090718410f600b90003001c09501d81d60320700c00090031241803074060942c9500848000030043c5003000c160380310300c2094a040c1800b0740d01c1b9940c2c14544051104c000021410105030031010f09130074052640902030178500180c041d406004aa000c005001d042540d0160f2541c0b22004085825400030008200703405007210701e0718100c262507000f94 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 851892311 1250 851891061 851891069
    0x90c13061d0904111306120602090f030d0f080702331605070813031b1406040302100e011e0c0b1b030f150405460f02090a0807 56
    0x4034000201e00c51a01c2c080105900c91070300407070a401e4030159036080080d9544100780720f100c07550ba04c000204140d9182403070514910701c18240142c1d1034581b002040111000d942c01e4a2080d44900340c22010290300081d0a5120b501604020b00d180e100d400081e4140044a4a000122102c01da80d680c2002803055048030481d914811568540e164424114001c1d03001c8a20800440c03000c0008100081070302004180b03603041c02417403801f010b44944d64104442407202c0b08140800310960300f0302411028905860000b40e0840c2c3c060b2502d455980800d81b00c01303004c903a41052106060380c85040740d0040d0300161058911000b208500300b5510030250540300000c07415614040321900048500a652440d03540e0910302d48006810b643d12410181c2007458010034170140c080302c84003000116100c901683e40a80581c10b2001c0800a02c410300c20071b03c0c004000c030078400c26110030085481c454840810a032001d601030307010501c641442030310703806440f0354400c694000d20101800103418001048500c252 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 851893561 1250 851892311 851892347
    0x9130210020c271620120307080405071202101b050703060f0b0102060603120f21070e0906010807270b0c011104080706080a060e07080108010b0d03020705090c1306 72
    0x42c0c5800d840001071300104c69950f000705000c091204010109081d21700c0c260b0100104a517200d4410b14240c0440360400d40d10200420b03240300500081203410300011014104400c140c40790031400d0f400003500c00d03800106030414000b0b14444078550850764414880f20642050889014590303074540301c0000d00c103442600b1203440c80c0c01000c038225031002c01c00502405009004020b4218584400b0485602c226600c20b000034041107403030302642070307644100400511081c110320640780c41c1c403026000e4100500e80601c00e00101c8100002607070400d0520748c01c4103040c506843d04414148881080b000034003164041022803c03000141a04d031400103149580c00c3c50b0080c4208044644860041e005a000381d54081e00040c4061241d180300c1e4203d5580100c1d07010000c2031069481881c9488540c040c0c032600001010031006000b403910034010f000e0200c409072a202964005510002e45a0849009407807140c08404d021902010105c4103a456070314030403111840c1582d550380088d08080c240360641640d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 851894811 1250 851893561 851893639
    0x409030e09060a3209010603060608100303050315040605041d070b130e0c1902100c140a050f12101d1b0a03110c1b09130210020c 57
    0x200d08107144103008503a03086107130800c00c1c80c0143c400e0080207004641081001d1940c00d0321200d50f030380c04040500902c0355031400181c0d1824058001c04400c0020804480d4901c5201e0800c0060760203401c9903400101c0700c0c0441e0308071250f48001406408603512042d846420080400c402c00e0960a4501001c4031800c100d40c0d1066842c441040540103412001d000c501004004201d5800961060307640001c075284918601141d8084100c20031010f8004c3c440140e010304183c02072800c0354403d02e0600415400e01081d5800d100c0c103039000034819040c00c03808103d800718a4038841c15000080c2c039030040414103143e1203032408840441c0800e03030350f2252102100750400480d00c060200c4003503d0140303100d4026401803203001104085141c2c8a810388030b003056034503501c0f4840c425407035000c1c12016000c1d8002d04903a00d1000100c03e18541e1043c643c030f204415500c1807041c443c0058141c103c80d203a054814407903181500006034103140c0c0b420411500800301c0f2000c0301803210082038003080000792803070171a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 851896061 1250 851894811 851894821
    0xc1f02040806010510020d05070f02030d0503090c030c100309110a0e2e1211040c020105010602121207031107120e090c0a020c0f0607051b0f031506010507110409030e09 74
    0x5448902c040f80c17007015802c45941000c174140719900810440d0f00603a00c0815400807603010030710301644004404009a404414033403130f24800d0010807420b4400300e0041c44900e02d01d90002d106604443c0251090684c0c800c0102d003003000400300f158440300e001300352624403a90b40d1003800609808440c6601ca010341c602801c40130030b443c0b030000001284000e01c43c001050401007440c00321100e000c0151030200412502179525a114010100380d8405540045410352500350040c0c0303000d01c145000b5080c1d490520401d00940c1c1000c2c0a00c0c0c2c040500e2801080041401104401622588101070040f09041c8541095207400c031840d18802c050580385c9260b65034800300214914005d0b9020040160864245544246403d05000c0e0040070003d203294176011203a900c0ca4034180d40b030943c900038100700c152040f0140c645003c8a001c4a0026805804d012165030322500f200300d40140703054140403011501c0c0d000d0206904000c0c540791400745c01080f142d0041e0601800340008500c100b0720806403800051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 851897311 1250 851896061 851896069
    0x2091602460b0c0a0c1217090106140607150513050d0f0e0603040203060601030b01020f1006032a0b210901150b09030a03120f0504150e01200c1f020408060105 70
    0x2989114266940c01c40a05c8240d03260000c04c0c141e5220307602040b01d058400c10184000200c480d009403855000024981c4c074003294200c400482c0c2603920b2041c1400c0c0016404284110418462441402c0000500750b5a82002a00407002c070500130b011b034882d03080841d01541e004444204203070141d481c0d83e038042050004016a80c882100e0007034040d0031030404549c5a5001e60004403c610050040d109112010300030179203412424002e9110158540108000748541d0f45031a52502c1d95001a610300001d8500c4114118070081c420aa81c00c80001800c00302401d80d003a1076960450103040e44009400d00070602e6010b008000300503650b080d00e6142c00501011f001c4100c03070307600b04041e02034154001a500d042d5880312080340c4000c01d060f114104039010070780a06c11188603d01c514408101d0514140150040310110000c1001580c5020440c940d9040324940b00e40408004250103686e404502c80f230a410488018038801007403845403280091118030b6000341c0107444c0e03200304454041e81c0c0c4600300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 851898561 1250 851897311 851897317
    0x1609050906010e060309070b0c161403060f04050a051209120106030309180e0d020a031214011412070b0406030b0307030213051e0403020a02091602460b0c 68
    0x41e404111105150382d01403e00f07001540d8010000c00c1a81c80b00e40da01d14007200f00350300c89900000d003a000382e01400034021000031a8005482d503180c40c1c003903200401011070f03554030000e4104041c00b0032040010b4100241003021144540c0d0141c1510410150204141459003000c4902c61142555021001c611881482034400b2290155104400503191139650b00541c0b1031942e1100c041d42d1504044092501c04204c85d043c0c1e014103034002c101c110114103004241c2110500024842030401c0d01c05110401654031550545041600c00c0c80071100c0c88000808050182d014520540100c00000031042a401c0150044402940303040c030414030ac0350101602c030321682c000250703c07016038030945941c8042a030201e540480082c5840b10707109440341c0b654400f524101c1e4200c00691120f48040e04500f001d6140e281c215295603076800c0c84a00c061741c0039440304880201260b000d03e2000c402c03407120209900c50706060903001c0040d40d42d0460384c1c0700d82170705580c1c1e800c0540c0d40b0380814001c581c17807000007021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851899811 1250 851898561 851898571
    0x801030c15020d0338010e180105062a0106050123030109051005030a0b01030219120204092604030b1e01060509060d2c03180103050a060b0316090509 66
    0x94000c5090204083e0700500303d141c01c0c8580751a04054603030740380055020082c0b130307813a603900b076a850645c504000401c808074a0389240c1c042d200e01c9007400034410840c803819055039801c8890303507240e4038580500001c1c1d00d90180c5810756107039a50151143c84d0030640c071174402c1d10b10aa8503564882d41e82d00c0709044c03210003a0720714a400d5a00300010480b5801c1640310a810442091440c28101e58400000f032a10241400980e89501c40700010000c500c0d00b00c003c0c90503980700d40c003d41106440e101c00b030046500003d0020340100c0d1aa141380041104a00c101440481c28080300c0000c40c007014400309054001340001c80c1c86840601c00301c0e003129004691642c030803019644036070b100da007055800c0701c03503030042c0c1c03020341e00414240040100c06010b8002e8403000a503400000c9084204034640c403144401000c40e01e03055400c1006000c60f00384000b4005d034001c4100313007804211380e11100b240d200100000e40c4080c6140b1800302c02d0140d0003641c00d280810004055540300506d40c0c81d901000300015058403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851901061 1250 851899811 851899813
    0xc01020f032b02030907140a030305041e090f0c120605030d0f0201110d091104140c071703011205100507051204030302090a03030e03071d0c030919030801030c1502 72
    0x2d00004042c0404503008080c030100c8070245910b044088043c1c3c0c00a603a9980c070368011b02c4007404a100300c51000d05018108590b1001c0c09031454601800ba44034900402d41c0d0018098a980d007a101c10f000f20748000c000d486070801c07500d140e04e090040180002e0700034000148070621030751401c8201c0e014980c19205c00a015200b02d0001340401c3d2000155103401d8001c0d5500c030341a241c1c2e06d18142010b44500036518030045000300c0e05d403604151442d00801650b11807843e18201640c00031914001c01e03031140300009040c0c2d075100181020f00e4089120005180c45490000010500000003600e1008040c4039004440005029003500c000380c9100315a81c100041090200194240d07440c090700c3d4100d4024100149055a190080790000546802c00e6000c500108400b02d290b0404000440080120b000c4542000340007414a45550102503d03141c2c00001c044080b40305c1280511000d1142800c191b002d241d208030038500940464024403040d5058502e1100004103071100504aa00030701c0568 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851902311 1250 851901061 851901067
    0x609100207051e062b06060810050409030e060a02010e1f060b0f030403030c2f1608120a031e09020301050a05070203070f21030e012406050a02010b1c02030c01020f03 73
    0x41d80c4109005000d403407101480e00003e100c040340025031b110707000107400d041c1d480d20b09500d070485608441218a034400d40c005c61510910101080c1d1288d001c2c48071400469256540b047c00b100e040f405001151a1803405004d40703c000704685d50f11f00d807070710704203802c03030b801400700e01d07070f10030206c0740502401640304941c8008000080001c0c0c0b10f0340c000002100030381800d8804244158a01106552590226400d40d680f41150049a4410020303101103492200030070480c24100300201392500c91458400406080100b550402d0707034041d402c446c0301c40c0c91120603100c10740e11440c00c1802500c403040069000c1c2d446c1c600401e0401c00c450080358800d002640066140010a0707440840600034007105a0366030084902403c000d00103080c07805100115507a0200c2c19203840c0c41c80350308580d407071000913800e4640380080c0400da0146118100c12035259040841e201d20081005070301406001c8141a40091042c60030a0305280300200d80b808c1c28002c1e4111240c00014900580e0b0310b80e040868041c441d1720034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851903561 1250 851902311 851902327
    0xf071809030912020a0f0314011d0c1306080d091a04060806060309010b04060b09040506040b01091205031c090515070504051207030f060603030206070207060c0803060609100207051e06 81
    0x803010740d140d044e2000e406800070b03a0340e810318031404058035007084482056420020031111001d0181d000310840340741e60743d500b000121098956883d80c5804107800343c00801c0040880c44c00c00c0d03001600901000046d00e00100074042c00402d0310703095000c0d1041052010120401c8100030700300b514141c907456143c43c40661580c00c20007c540d04010865807066403074641c50401030f2914054a0001c0070f014209a0720b07004060100000d40d00700405082c021031800c0c0400d0030b00c0c0e034000030070701c1191610021141d80c000c45061403801c41c82000100f201c80000101c2c400070401f2030f944a10f43d0580140f041d1824a040d0391b8600b85c2da06026a00400016001e1006001038500164040b840100c00d01c200c5002507500d03651090301079480314055641e25620300c0108103040d0140f02459105543d48041e12109061502c06006031a410744054403181000c8000303041034540504440340000c000703051341102d20040074001e588100d58011240600412110321480d0f65174214481d2a110004125505010324 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851904811 1250 851903561 851903579
    0x1b021c0311070c030c050a050306060d030f091d0a23180312011e0510051903090515100801021804020a0207050a030c060f051c0903110f0718090309 65
    0xd40c07000700181e060300300008000102c40b6000c42c4000c520803410840880d25201c1003085004880e81b00034000d42002d0b08005580e5900c4a9444e5040d5050414907040421041d00b1200802a50425224804034044500c07000d180000c00b039120350036001040c09200581c0440c5110fa0300742020840c1d111400c0000301c0d2880300100d42224501243c00220303420b2100c44442e002840c40281e001580025a216030509070007044801540034110a40e0501c0c003485012000130b00318420b211002018003130740001558500d2003500031945040d040b1044940c1c0f60100421400e80b01010794850018000c22100019a41018000c2d1021180991300d81b54aa080392010720000e50701010510046019018020560ba642e90b41d20304041c1d409100521004c0d420004054052126101b15805201090040309201c5404880c5401d01000003980424084030a19007039448041d90003400c03201d809480a0404122000600c1c0c50840f4040c501042201013503000f14800c450241d60040e000800240081c003004c1e174 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851906061 1250 851904811 851904821
    0x31209150c0624080708030405030601031b0e0106050310061b0b0405010204120f26070f02030a080a03270f08031306020406110c0405101202040b030706031b021c03 72
    0x40a01c40204001050010306140c0c00240f2490700c2c6940c9852009100d04041002410043c00c0500c000f0b500c0c150608000940e602030501c4010004100300d103458540008044a4000501c40b0300e84055580d611071034003504d982c000300c640d10440c030000b080000f0385c43e200c1d0503e200032524064500c0a14207058036103d1132060300501c113a4182d902040000784049480d481500784070b0103000e41c0c2c2070001840c90003a0740802c46a5103203141c4850a00381c003820b070990104492a82c0d50008510740c00c260705101080c204008404040c00d1580041812000c1a82540001c144441c1c07160101900348200340804148225540f000341c41d039080e60010000084550700110f820009018060031440080c4d600c0800313903071261300404005001c0249240d51800b00308a12050800120b405000901e08a281c40c2165040c0b8403480c0c000c0c0031140c2150b02035483e10f6204240d1128081e007952503ea44070080503000d04035129410207081e6500c00d9100e451840496010400341820f031310820080100313002100940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851907311 1250 851906061 851906063
    0x11b05250c0501020706021f02090d020301240f1a130e160e030d171b07060209120a0c42020d02030a05070b07180602010204031209150c 60
    0x1140d151400c01040100c40303150045215104103401181840002410a4101e510076402e41d844000c50800301c1c06100c1031903003441c41c9002c0050b203a5041d0b00014000d02c18a09002c2c0d019460880351202d841920000d80301108a0100c01f56000b6541c0e04048032146c005206088009d15041c080410000c5004010a11203641044e80101c0303031744410704451050000e464503503850386d000d59440e925940000d0040b0040c01304070094054a04c140c1d0018264403440d90010100b41000000580c2e01d0034071110031320030400c499031943d40341c00c00361034003600941c00840b10380c3c0304101d10701603011807040000b40e41c02032691003031044144030f15000b208104000e600364510388807446001c884e030b804200c18450417070f0201c0710035481032410400c0d20040e00b002015100201190070070003e060420b0b070080111010355038001000c51440d80c030b08104a0f81ca02800070b480807482200100003d4103a415006402524010ba051360b00e105034814060360404914810840c01181c8241c0e080eaa842c00394002c1c0c002c0c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851908561 1250 851907311 851907337
    0x309010509163b091f1a090901060f0b040509010e0c0d0c120e06070e0f03250b0f070b01050108011d13080a020106030b1003080f0a020f0a0602040512011b05 69
    0x3e2a048802071032540044680e401207620000c1d80308520102c01c48400c41c00d010700b5030104800300484440140411705809100d015032084004901e61319400d50103030006200700d01d41000e4003500c03005003103003541c040d100e0540301e44e01000c0003050881012040700e0084801d003210707610340b0350303e01c440308040d0800c07600b2801400941402e1806405160180790b51080c5a08090041450200d0001e007000440401490180c004000340d01050746000070b101d101c0d902c2018100b51140d0586800d503030241e009411151420300042440300034008010050404103108801d0b0101517a251801102c0900f003d2040401c07002d483c2ca070020f44001d09034000c42d08124240c03902c1c1e0303520f12503456030140c3d07a018a03003c400607036441008106105281a0054005d212140c0c03106c0010325540314040140103200003203009410016110044900030407590b00050030300001c1e21550309641c10050020b401c9842618011103000d501c000d2610010f03c01d254440010faa04c0800d61004040200c5654005e83d10400f41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851909811 1250 851908561 851908649
    0xa0203150906181014040203160509070c0615030303050709090e030702100210050103050606030d03110702010e01110703050606090610080714090406240c0c0605090a0902030901050916 81
    0x400c4e00390007405c0d901103c124401c80e007410b051050510301700c07400030010101b00c0080c0081c0080e0360307000510340e0000d045107003c460a1940d810000000c1182e01c1d20000c01200b030fa00c0010415400d81c001920030946602d401c2281765175002444d00342c03090109001007a030001c1041d0001032070458241c0c8031345506441107038102e1520f0400740d01180c1c002c0e082683c0d641c0c4910300b006200e103001c110004209000e841e042c80b9000005030004414064100001d05101c400055000b199100320089201c000b074410403100303451b6503810455140c02054401c41e0045009400013005424a4412901001a25550a141a43c2c0c02c20100c65400518040e050200000c00188a483da00da01803c4054802a480b010060200412009003098903203941070500442450503c0454140f540c041e0481e49181811503803141d400c0001400b2400a8102544c00c0e031000c003c1c0400d02405601240c4030f81c1c608000c031a40b0004901841604079042c0c0710354440750300c000251042d81d03d00e44245042c504107540b05044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851911061 1250 851909811 851909833
    0x105030a0f0213050906190905152815050d0f0b280501180603020d0b040612170c2e11071509080703180510020a020315090618 56
    0x60743d0107160f0312441d000052109014034504440229003000341124a0316100360707098080c02400c0d00038800c000e4150307904d500141001e0407800fa20424610020300d0388002060343d89905141d02c025034900260000c002e500443c0382800c2c41c2d03c10b080c80840f502e85e141009910940300003d07200c81c405c100d407581c0e01c0e00030700d2202d6215000e0480504d003148441d80840081c994110095503850380c8840e040214000c03a04140404035003030281600e100740b50150355000802e8030307070010340500800307590024906100040e40300c0140045540f29881202d51603000208003001900c903004150600146400c084032030000c5002201c4030034141000e4080c08100c10034070112905c12a0095000c0040c0c48d40001005010040b1001c58030810b08041c003000c0010f05402e880706101400303441c0c03008040c40410300b034140340444500c004d40002e180003803100240c0e1034086402500c0d00c00b0314804074003d201740030680c810b81c0a9a10070b00c3c810310f284030080003145d440354010060804a520074075003d0081116480d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851912311 1250 851911061 851911091
    0x614090403200d081311060f0708070b19050709051014120711030705030a08133302031302150d060b04060f0201050601020601140612131412090105030a 67
    0x4050411642c0507100c424054107000d40070380c000901140c04d92840c445c0000009841c01b8000a42c50401e90303c0907210604490380e041588104130001e0100c0d8004030b009010491042001485401242614030020800c0aa00019114161088004504501b0090005040030054a1300300b1120b13141000c155800c00b04c0d02c2d000c960141850310000f0001400f00700c0050780000001642c0301e1928001c2d4a4100b054030340603228041c407402c0700100220040450583c3c2504590040140d4000c07070a40d0f5602090410384080c00c1038059204103864943e01400666a028401e5a2180f51401e80d4105191416400c000b0031042c0051201080a02070001c18a5517000b03109020103882200c1242e070b6130b03500703100c400b4240007201740340e40d002c5a0403d400c002050368003151250440d024034100306e556082d80340005255010352000341d81c2e008884801c0040d000c034000000700320341d4000c003110302030040d00b001c441c0d8451706051103c0303121500c1000175aa10b54890001144d00211321030001400c1040c0098130 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851913561 1250 851912311 851912357
    0x507140309011d0a020102151b090120010603020316080304031104140f2a1b0106090e0615030f060c0703030605120a050d0306151209240507030614090403 68
    0x60700b00351340078600b114115601000f070004540004150315000b850400351200000c1000c07003060703880c2c10000c510080d8590084050a0352100c00328400c50010000b07070380c0c15008160f03a01c416407292099a440ca580b050454500b2401d0b1f80e110300285282a040d61100c0e403511030481d902030341096413a40f0030000c03509501000c84c0150301b070009201e00e07810090744581401048a03c444000101ca042d000380d01550f000440703484008000d0503000b582e10420b061801010168015402c5508102c800c070b841000103e40c26100ba01c2d9010810909080802071598401112250340419400600410090720380d92000d07120b01d40c413a10f40402c40076110780100d468a105860340c1c82c0d41c0c0c2d02c4281d1800030807000b88418082d209061504005040c98142d924600302046d4041e1800d10201e48182402900e150b0454403002341c22000d0583c0c07110000078410100d61240d01240b80451405003c10601e80c400e0040d202220001c0441e031001310a03003801c11201d1803000c1c0c4201d060100256004440c01600481b0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851914811 1250 851913561 851913611
    0x30d050408121b0301030308040c051003140109020901050a1206181d0c0901120311010204240e0a032307170706020718020c10060b040f09050714030901 67
    0x110700e0300c4012014151035803038000f9100759281d45403101d90700d240c0c503c0901600d04494140c5031010198442c1e08040e40c81104681149800c000142c2010203000d0b01904040040856a003075038446070b9a80c2010400c90158002d9140015010404c51300700c00d21452107503650100c450000107050f95546200002d101141d2a0365000315291000b44109000c3c00e148800e140030100301038801c9483c008001640c0032014042e1030602600200202d051502c03d80b8440b1450803000000c541d40c41e211146a064402c00a4452046418544a002440f4407034840c1d004124005031180d41124190381d110000c01007500303030111411980b282058441c450812842004240d449042c2e29111081d000143c100507143e0000300955200e00020402c0501540d43d41040340e210000040e1036481c110500c0b810240302ca208203107901c1c107243c0301107404e20b0048002d200b140e00c008030300559180c0c0c40c82038809a43d0300321403a00104251100c0c0207180c400d000700455000c02500000628800c00440244821f591a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851916061 1250 851914811 851914823
    0x130615091a0a0e06211005011e0b0705071401140a081005030d091a120103151a030d0e041e0203040b0702030301050306130302070f120b060103110417030d0504 70
    0x710038007070360421000d61400703007402121107905490103101144e00215110340140d54001504644a00c03400188140800284000c800340880d503980d29401c00f032510015915410702880800c0060010080c0040b07a0a90b9417110142c00ca0528001c0e00590b0110704c0801d4506103c0102150401c02e0f01c000d000700101070450710342155608000000c4883c0000540013a07000358820000a40c2140d00910610220b4034100400c114074203c072514803103a40918089520910202d9001000708005a07000c1c0100d5a41000104500211021000031010700244050f0f0190004110202e403544168074041e00c00310050000b08030003081001ca14032082a203400240c40d01d0307001c410721041000500c652504032a03148015800e40d4104030019031951b001418841e4440400000241054000d01c019401800c50400c511300312650352022015051035130100322404224100011100d41c00f9100780c00c24800346008003400e00f4140410b648a44aa84041190341e1200b80036a5040c095203011300740c41284298 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851917311 1250 851916061 851916101
    0x71e170d050a06051525061803030b040501030309050f0a0f0803071b03020f090901090f11011e050a12060801050907050310051b0304030516050c0f0913061509 70
    0x181640b08071060b6400051050510002e00f1465240c0c2c14140c8201c43c214034544081681d040312041040c11304204001c0c807003800c1c060302a41221312640340c49011130094400b0310141106c00c08020403244240001170108a4410007400b007814010342d40c11444101401000b6002e40391140001e8040c46984960095400000c0090402c820364011048001502e0002d00f80d0a00355030000d02d02d0050008000c2c0203000e00000210b0070f40094008214198020301d100707141030706e2401c000e80d04c2c6040d10304007804107a0b039101024400100f54035143d26800c8a5455508002102108a80c0c00e01c403074803401801d9803200c01c0803c40da2421b2250fa401442c9a5000b0700c812840d02050500b032107a400403180d00c0901e000300b0840c0307c01500c0c400c4580106540e036442e40d255034925044c4c4043c003130307046034007081d4401144101c01c001c0e0000701c2004c651320444484e400400100d082100d0510b0172121810007445104040c6c001440c41d4012260440c1916100d06402c1c3d2a01e08a800b1503504001d0810710700c06074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851918561 1250 851917311 851917321
    0x7060623040204030c061115130308090c130f14090a03030e0d050712050c03070b180109080f2d03040c0906030206160213090812010b071e170d05 64
    0x250316402401a015141075041c203141d80c0f219414850203210709424444c10311410103881c0801d0043ca80c5180a020600d0251301b001040c40031280c5400c60101d0108490300d02144003640002450103490800401045c20075840124520140c0141042421510744450f440d5000c0007062200324401d070300e184014031121905007401003e07503d0344903084074203400c4040740d401f040ba404070072034010319007103011040d29a150b5503084400c2e00c40c58504200500000c524201081001610280202d549214041002440300d0381c0b40d0898505c00f5008140031400c200c0c0d074450400060180c40402c00f952558450b880108044541c80705510038000003100740042080200402e40e504070000d01005081041114251360119002d071040c0d031200f85c803044048101a045545030200f080ea05031010710144074110140c948903002d50007420f42040142c0d8101d001050b0500c5041c103498a407030b00540d030a008952408103d04124032420400e41e00d00040c142100c1000d080e00300207102e45a600c0400140d6450310b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851919811 1250 851918561 851918609
    0x110c0d0504080a03050703121a120105060f010e040b041112070f09030803100801111b03130b070503090d080414010e01210f0e0a031403012603070606 66
    0x11101102840303400d00080c0111400083c00700074041d4541000c607603600050030309641c114a24104403060700e040056402e2003049040083c0c0110000381d0720112451065100c4ca03003aa20100d0b61f194005c0d0000252803255807040a08440304071001d040001c00034a000d0200d4140c81503103200c1e120032107001480e24030380c0340e1075010281d0040b030500e007007040d4900c1d02c24010404001484060070412011000c2000e100c1c890181100801d4150000c00c0300340220495204143c1101203032000547d00c541003a00380070310200413a0086941480c001c7e9500d410968a02250740080000b5221484140300806064480441000c0b45034001c00d12282c445241c4000b89944120701c141c018108207034a1610b00d0266003118450072110a41144481200d00514019004000e0f00d0a403080362400c01120040c080d10110308424502d00036551050840a9004850001d03c000e200c0d104c08105a07441a1005010000e151b170041602041540e14200c495183c0009950460300003e40b8280c610143d0210003113 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851921061 1250 851919811 851919823
    0x204050a03060c1803020d020d05030c061801141003020d031e03060906081c05250605010e16050a08060a0e16030614060909071e09080d110a030e13110c 67
    0x6602d182c403044039045d50302007040342480d07240007800350010b500d6103010000c2c14010307560b0320010070003100d42da46040b506940003000e105e064a0115441c100c01c5628101e0100381e40c03441a07901080010103940356500380f00481088041c05d03010400401881d060b08606100317045041003170f0342e80214a103801c020450080721460380c00410310b81d004840c0150080fa442c01c41d20a0f03501c80d41459511800c60862200c0f00072203045440108010701c9801c1070401101d5072003681607400c4003681d4001542c50007580313622031860300340e07070703801308209110798444544102c95003640607a020340304d064917a81d20390a8003242d94059580152520819654580d1281d03d84654001450000340700444a0080808280c162141083c2d040c00f03502c00c1800030b42c50901503841d0304030340c02c2d087c240704e42c46081c4060700400c1c2005a02440e540c5014005035580c0141c858102c0f424081c502c86d018007680c5040743d800780c83e540010702d1060380000c114001c3e60020301c201e00c00c00310042c0b020180b40751744030301d034162060600c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851922311 1250 851921061 851921087
    0x70b0c0d0b10020a020d0204151211030106051c1e030c06050c090a090b060702060c0304061d180601090b0a09090522020904050109050303071d0925030204050a03060c 73
    0x6400b940e907210040e8002803103034a16405460f84c038486c807513070b0000c2005043c201c041c00c10758840628001a00821403240303990080c0c06110034a0903101094101030a0b102c051003040e50000100501c0001c5800800c03c4a200354030508001100c510411400751a03212920740c00e1b80410804010382040c08524003446074406c060801c1185000720040000d6116174090042269003035941c444c89055440d540200d0f5800c5800070030389503c440c20100850f80c1c80c0c0c8140201400110403005050085002070303030000c4000001841c1e0421319009142d41c2e400b082e0010140340c1080780c002c00004150011600403e0ba418581d52920805400c15801ea82502e50162140c20044c105a00e80807800545090b400340c01c59049500c401075031601e040c0580500400d850140242c0400014040d60319000306400880c111211090503461959104000c81800f04a9207919103441c64850103e1030742080302d90700324400141c2001400c16072103a003c660a080c032030300126007841d03403410011402900414141409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851923561 1250 851922311 851922319
    0x702100825050417012901090806040803091e03071e1205031e0114010e0d0602030109090c05030f1005130c090f0b0604032f181f0302010e090903070b0c0d0b 69
    0x141b040e16480007003d9180b01d0713040c1e084040b025141110340e0701c219150340060418004540290a0504005036198401e451039100b42c803405041d01c00c0c582207541441c2074208018043d6003060300d180c0b5405c640a140c1e48901d103045960340b01980018071850001d0911000b03d90300c0644902d00410f512108841000c00c00d078102d10550010440c500803030603c1c00e02c1c44070030b20740010311001c2c0c10082010052480b000500c024008400480c003034403542d0140f0300c254040d030440488035070385c0d00605d6100d01c044202400550003100710703806031513042d4002c9600608080d4440c0c200c841c850b164400383e109079811180b407080c0c68007151703039500d12580595003041201300c8034240303041c1c0766946804448102e2a0080600c02c401c0742400c5085e1100a205208160041c00c4001580d410104800d02128120780c1d0100d1403814910700e000c2b820061420b40296581030311a01001c503084000c000310078000610090072448200003200010300c40046582c0035406202540c0e8659151b140715905840b1a40601401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851924811 1250 851923561 851923571
    0x3061807050d050307080708190201091703130236060306010e010f17030d0903080f2208070807060c0f110a0317060f1c0605010902070210082505041701 67
    0x11503c0441102d910305d91204e00303945d83d540b03d4607001000340211500c0041e0044084140f043c295010b4008001052181340004d05030710030401c3d29204c0d40000c0c4d8400984805040c609001414201e000109600000410040c05c00c0e8454150f00c200c5441051130320980400d0080c0100703070070200b110740e01411448001c01c00b00d40c1482d01d05811000d103881107035000380d050440c07101821410300440701030706041c075024044c0f801e5908000d41076220a81e80c440c1551054000103075040c640700c4818000d80c00c88120300c640030810307031070715940740c1c00060b8152000801044020002034040c030440b030348181181c441c090305500152010300b03544c6e101203010b1076541000070702200291b440a42024000e20f02c19000180b030b00d80074045070150b008008004c0c0c003c200c4c0392440d50710030400500e4012241c0704000500052780c8030201441039005a440c000d400018018001e82d40c94041c0841ca030b0301115060b040e51000d202440100c554030f500f101d0740c00c00720700001018012140c9004500441004041c02481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851926061 1250 851924811 851924813
    0x6080303040209040f0b25020c030c040f1401080114010801050708160c02120709060501030204030512070311010c0c060f05072001021b06151c020f040b03061807050d 73
    0x18803448000d000900c180201000601004860a00000001e0300900c19074140c0c40c2c0002100c02000d020480714411102003072070f9400300351001503c805840d170040c000c0c150754020102030001620101e0b00c4000d0203030321244038900502040ca01180240800c40000c0f69120034450344103500c0300180c0020000740d040408010000750480b03030098000711142150005002045e80484181341d0203c2c009500040134485a640c0005c0010008181d4404c03403001c00a265071040150128030507888002c0254210203007114484104602902100703000b41000014516506207050843d80c1d041400030100380e120a56600b4003036107102c1c140292070454010001e500744141c01400c0e200c802c1c041a4850364441c03000805040c03080d01a00e20501003800d400b4001c1000c42e80c103c0d2604d804460144034a0321602c1a89413500d0b100d6500c245600351440070720b04601160302071204c0c2186001c809504580c039600001d045440401c1028032410340620740310382c0324401609003030522a0a5104920840841d4400d00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851927311 1250 851926061 851926063
    0x8010b0703210615030b030d0f080c03090a080c01060807091e110d0f0e0f070f0e09010b06070b1e010503031c0e0d050a02160b0301061214150405010503010608 70
    0x6003003071860020240401005015002c081c180a0704000c8200a44402c01c07003107035405800100b0344084c1181a03d060b41046201225407003980324103100014a004042071005c1e41c039000031a003060f5080d09071600d403081629034580c103901504850209a640301010015440e0501c034000c040c21502d5418400440305104095a69519101c1d00c01c050780d6941004100c1080340d41200e134400c407405000c2c0900114100000020000c0046a5946001c2e15030b0300342d80c080b404528001034584041001c50843d040803a9039004690092914109650795807540b40282d0f00c070400b9103401e500c0b0f95081a05440c007980c0ba1841001c00754000810042c11000504c019034010064422140d42a0b44c40c00c1820280084035010307103010100a0380382d004043c0a0026070742c1c040000d050b054443d408032541000c106240d03681d900010320601c1d9064400380014009148560608080c207068142d01045510000c0d54600307440c0e02c242e4002e00984c10000c4407000504142c042c050041404600803c00f03646442519 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851928561 1250 851927311 851927327
    0x2060115050a12020307030b090c040608182e020304080307020d022b140406050a1d0a050609030a121808060408031b160b040201080f0403021f020904020c0d08010b0703 74
    0xc10f0380580110000e1400d911a074407408101c24010098011800c1c80071181030390307511038040c00001846400010b900e805d412421004000c0e011401054002d001e80701d0442c81180329402c804000111200c21703103a00ba034500240d030080c4d00407042640e490034003800282c03030b10803101912415500440c119000c1101d083c1050f40040507a800c5143ea100c110b03210845904983d00903040d0900d4001c1004142d155006020700283c41d10390f01c42c90101c5104c96082000a8951040e10307510400e981030520603400c05001038090703030384007170100c1e2003144180e41c1d900043c01c0c00140c0071000842c840b03000c9900d0040346080d0402440d950000e002c1c0d60400e13480e140844d1000515251041c03006080442403114950304585070702c0c52119201c580000d29240103080d02c5405e5800f0fa000a070401c01045c00110070741d00d66070245d40c0c950000e000d0141010750341078079600c5044010700341583c01e11a05500c0c0d00d9600040130351054920241c0b900c903842500c080c0c0b5042c4180c12103143c050081c4910800a50403402d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851929811 1250 851928561 851928587
    0x10f020a170307050c011401153f1427031b070f06021b0402040b180301020405042d050c073302181c0f05070308040602060115050a 58
    0x1050b03501c3e40d401c01d0568181c4208190340d05d1a600e00790388005036458000700300d03041e60900944100d1003070150500b11800039031036038441c030546c103604226100c030041e000d43c083c50780003004581d0754140e0104c640f10080318041c241802907010341318104411200d4010541110301f106a5844070094070103a00d0700e5490054191341100d000c20a00c02c520700300002c200c250020480c17421034020345500c0d150700a440d05810740d10034620103541c43e01203038207151a0098500b074660310303500d50b420514080c1d403102d40c0858407080d054244d54200720114854172240607040c1041c030301542800d451040e00c005090148503410711010082c0c0b81205000314214120121a80150480d4060030b441c09102c1d01c0c2c4980c8081c88151042c0d0509a541402e00340d0b0068025100c00c00050642c07007090003412060050380c032003041444802c00d01c10384200f000a100e1140e41030038030b4000c204850b5019240d41c0d400c81e20b5070058000c5005640a84010494004480015800c142103840d19034101240c51802514200103400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851931061 1250 851929811 851929853
    0x10e010218120c120f07060905060a0e0409050d0c05060a050105090f0a0f05070c0213090c120606091112010f140d050c040911040605031b151b010b010f020a 69
    0x44145600b8400f0441032100e140000c0c9188040b26001400d00d84c1c440b400400c51040c2d000c1c54100080e101d0103500c1180403588040e02e0701d407a06148100440707090000049195005588402d04004960100114080d004080c0ca5040101c0b00e02d081c403c2c82d1280c010007a2800030309010040c011034641e40701103504150789440307040203034450380000b0000e003d60800d4101c20f50700d00030800240c0c80d8040d243e0a002030083e80c100300054500e04510055414071a4050301c858100213042120301d141560070314001d070040c0000100261120007442c20785030a406407143c0b064021882104058541c00030500520741450400c40c00707481c0a603a5100351a504c43c0041c418101c0f540310009100c400e10040e081010010030402000382103103400c00243e03542c2502903014034501440803955085c0000c904081c034020807019211040003504200344580545412602c1641c244803115041564a40303185010070319030008500404810001801c002c1c004440ca411940581070300e1021072460507126038240141c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851932311 1250 851931061 851931079
    0x1206090302120c0c0f010f23040315020306280311010314180106060504060801140d02270c070803060f01030b03070e0a050a0e0d0305070909050c0c010e010218 70
    0xc1030076410105a032a40c070118810004010000f0725001c03c4d9413110000c01c83e400d0501e09598001110710181804034080403d4496a80c100580c0d20016403000c5004040003441c5459281d50b642840a040700390030b520701355008000e002c0d051038040020302840c441c0c002d4182405003402018010501030384800740082c03c1c0f02414020b203900c2a001603035200c0114202c0c0c58903091603190741c05044c0304400204400d500e00b2002040441c03040f0119400c0701d4071607903180e0050742400d0155100413020700529500400141c8444010b8884c640b20701010000100c81c40c2d0b20036800200d03416000d20007881503141c50001c010481c00a0035040c103881c0c010703206403140c01c041681d000041c3d004005014610741d05100e40007002588105c000e12641c800c1c0e840c10800d201d644c43d0346802d4810f0342c40088803008143c100d07411601d0214401c3d4049a845240c40c640601c0d21a511440c1c24111442624022440c002c0055000740141003401486501c00240008610346032882d504c841c4040d0014071800d2140c5c1441e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851933561 1250 851932311 851932313
    0x41e09030302040f150e04020301260f0d02070810050c1206030f01020c0c01031803080c0703020102090406171606051b1e0a0215030915060102190c08070e01120609 72
    0x2e506030390151903154020b222450300c1d24440800d407070441304000001404111058242d080c0350003900d048035482000007018005101113046003109221000d000c622613600b410840714400c21154a9500854001d051034604113000c040c20220360584402029050201f8443e111407402d048401ca50980101c1c141c1070340b10100000d04000d030b01164003a4640c00408d18017001403002c95103020301403090300d017041000205c0d080c04c00c03021500d04028001c90920000601911254001010094404d10006240500a20000301181e07c290080f819000210b884200804810050041405030964145021034604200140b080c8901080c48422811622441880820402941e0052002c01c28508444d080e83c008503a0395084065081c0d04c2050228181084211130800310b82c041d484110150899031310100500c2e5038800050901030442c0700da000e60200ca800c41042008005218001c000c000728a04a40300d8a454901e030000000904401c00400140107101c843c52445a4404e1010814400e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851934811 1250 851933561 851933567
    0x51309020c03090307090b1e090a0510030f0506011505191107030c140f09010608151828020a0e090907030b04060c08010b03060603060915060f03060906041e0903 71
    0x1d60f42c980d035003500c18907001207520480e9030070200c4690740c00d6070b81001108149003055440d9403000d4a0a03084010440032070f00c50713411a00f00c0c0381e202008c01f0510240ca80d5039a04c1040c581d03440ca5056a040d0002c0380144904048085503912413696440c0950621040003458402e07413101c0014241842180d0103a1100f213001446800002c54101174403146003070341d5104105403602d01d4019648184580f22a00e200341c5004042941621703c1c643d2011042d9a41c0d122000f00c0c4440589001d03407005140300e40101d208d0001e001980b140c8040002d03414008010081d4449055505288183e80c90050080150f4a0340c0315441210a80d01181c0e0a061900d91003007642c1081c0f12500701611903030180007008140416078104403c019055500c040c00c0d603a13106420001400251501c5510040c20030100b43c1702d02c2c0c03141072107421154546600840c043e003140002e0b441c0e44411003008081402104020151400d0243c1b80ea0280e010f4a0074000104c3e002410840c00090510340401c0565810000b800d143c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851936061 1250 851934811 851934817
    0x10020709020c0c0a060801080703080f0403020a14040c081e0c0d091a06091314070504021305011713030f0e0a03060e06130209010504020a0c08070b0115051309020c03 73
    0x8000d00e01103640d0000300041e161900e5a031450f860184001c01d00c0090414410640300c0d04035401803001d4040d8a0450751030aa4980c84040880f604030002c2c480800540d45400301e890040070801458042080150180001e9607c42d135103001c14003000078200280c41d0b54038140081c0700d600d02c0722011425550440118054003a04400c84112441d08405104025946450300840390324034aa20545036910003c0201e074400031500c20304821903030060000011740c0d096114466207218030a40d90080d4448000c14102d80191511041c607000da0f030300800c01540c0001d8903c080b031100fa580c010851078909200144040300440040400c055080c1c1c42400e0741c45450401204c610040085100580e01e007018005001d0401c000021401110042401201862482691913501030044020340e8070b07000c2008000d400203003000042c094807003031007000240204000c1034443d03c18035040174654140008056001501100078080c03250402c1140c440181801e031040855203822405660380120f1104281580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851937311 1250 851936061 851936069
    0x90b0c07032006090618072c07262716060807030612030e09130803010b0d0b1c021c05012a090b16030309051212060f0f100207 56
    0x10065051004900c03001040650007140311074111041501c412a509809039400c451304810787c0c1c03121004201c080b482c2c1026550900b090303c860080080c000700362180d848401c5843e100003c501800105401c00507280810503290b9500e0100100c2c5840c9006100300d178074618500002d43d40b2583c1505006400700305000d084814203010140f03450752000050518001030b01d401c2e0100b03040c01004a204010b800070100c140342c0507610000b502d0304d40002c0c4181072001900300490040300d541c00c03102007540f0310011402401803201c01c513503400560a00c4000c841409200c1f600c559180c05807400026070503081d10140540456484000603036178080d410723220420b03240080c91542041d14440c90310340140940403000500300c0801e0b08042010740d0407210b012050052405030a01486a0511150b0f035440641e000d034802c0c00d00180c41400d644410385010b4030b1202d10740d0708000014a59920103010341d2801c2e00540141e8448024683d15800204003100c10022607008100b01c2c49850800e40c07080014030010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851938561 1250 851937311 851937347
    0x120e0d08060f12120304050712150e0c10270303120b03030706050c070c14030a0b2a0c0d0305060a05010e040b0907090302030606091506031e0109020a03050a090b0c0703 74
    0x1407500d80d003284c0c26504200c805071201e010310a00000c8041881c030b08800156400b481400c15540d03075000e075100900c8003144580c60780c81801d201c060907854a030280c103c4603040b5100c0302d80c103480c0003240d107500c82032800c904108c01200b0304003000000c0d042642210580b45402000c1021030701c09001c030b1f1550141d444040d000500b010144007606103608010a00a40540d8143e0280c540300c641c804510405400c400b070301343d80203000540120f003580c035140f07400450314480e41005400d40960300000146000d80100d01c41c1d00000c41c010b4150003086140112a041e09080c445460000e00107a10385200d44940d81c148a950704440e5510341e200e86c40f10a03802002060100700e4180f6203001000d50400c3c0c00203d00070303c19a03020a0892030480c0e0514414124132820306000013065007442699040a89041441c031038800d200d6031300c03182d9501e07624042c012420006848603c01403000301950f401412400e411450100e444000c14118511550b00c000d0b009107180d03403200c4038031f000c032444809044c2d04001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851939811 1250 851938561 851938573
    0x210121a0f10120213090e0a0b070309020f060c01020a021b01020d0f02011d0f07050103020910180f031b0902090d06020a0917010e06060a2103030f0c120e0d08060f12 73
    0x40b80120104000540f444074001f003050000380b0890795174170851007d0203000008a03900103085940f00c0c1e000301400320720141c141c25003600381e0404542142c0100d58100c3c2281d4020034000c0100364104012000b601000381304031400e44542c0c0000c0c0d100c4000740048810440b0003a807076940c00c2c0c000d40211400e0b00075840000802481001075940712000b005c58102c2c02c1c01200d0740043c0d298841d0094900e1101c0040c4600702c941c1c20314005594141d080744002c4a0b842c240d880005480521081e580c1c02580a550152490b1000c4000881445140e4201901c0140b040c488080c3c90388079030018100003944088010307a60303140345105580c060704950280414840800e0011000c1d041034104078245d08907101120615161881004010f2166024000c0401c1e120b032900e1290300e0000d000546094040d0400013150103010403003000383c441050b680c07800725200100482080400780304001a0b180c0e694054003c0c07410080c00103111007406442540325004856221142d95140c444039000c88002c0d07011201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851941061 1250 851939811 851939827
    0x3051c0605031c1103040e0f060a080303130615031a0c0c120403051b09191d06100f06020c04150f0e04030305060d170706090210121a0f101202 63
    0x118050f41811000c0061055a600d440804001080e10251000c0c05c180511942c0d85e5060580b03000c5005040d41ea104101c0600020f4102082c0000c5000e8880c1d01521144402c0900302582501d800e292101e00d881b1080c40d0800208544030030103001c41d54513070000f071090780318400c10301c429000b0320b40e81075402e020303240e2281d055450303d1000700202d80c802c0c02510541d038070481c1845004002040c40c190071000d110000307181c0c007410f2280100003030315604001600100799402214468840d1a0100d0903501400c00d000340c2552003c0b40400404000205107000c5080540c004d44424800060038003031521000000300004002e00e200c0080e00b44803004583c10b50ba2100c017810301401c140e4041d00031918101c0498442d09184005100326500a03400c400010b10100d40b2840c0c55005400c29504550740b0007144005035204040703103481c01d80a1380c66480f441c2207500d0710700807202c05010107240440362082030006a1101519880e0454049440303d6580c98030725003d60300140e2007401e580d4000d10005801d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851942311 1250 851941061 851941093
    0x402030a080c0f0c04060b04030b13080d0b041407020706030903110a0803060907050903060c03060409120807030b010207080d0e030703060e01051909051510030204050c030402090708010303051c060503 88
    0x31400d00309440c2100c802440410501084a021f0301802c0c0688100304010301c0440c0c180044245c00110f00d4900f1200c40000c1c2d00c074000203410000341e10301003945035402103090f85441c4c0180d54959841e00035224180c00c1c0384e4406541d408040c0300b2442855160021142414040c2096007208081001a90151003040c43d2001c4258401c50b0711610902409000c00c8041f41701e075094036a090000b5000300000e0f00c800002a00d260801440c00e5071140d1a641d008001070001c44403104040c1c90750712140344500b0011806030940b402000402d0440d840a941000801d900090a0105c5031040c100981200c0001000c03d003440240c1d08007030b00c140d06050500340c030182c1c1503004502c9002c4e10a5808401442d250b088001d8031014940904142e0140d50b14800342e048005010b17410000340180140c61a07681d81c00f181c03c2d10001c0300c2005c2030076008800c0205500b061901c4036402890381c90031420560441da00a801070007036580f5801d0101048094200f00446a40854081c0c030004044840a80d0449008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851943561 1250 851942311 851942323
    0x2b050915040e10060819020c0102180a0909080409020a0c05161802121b040807090501031502090102120a0c02090c1b0c0a18060509010e0405070f1503050402030a080c 73
    0x210a82c60a500000740d500d40d10100c400e819208155103900b03464860950301c1040c03500701082007400a07800c00204410100074401841e000d00c3e261115100f40c1a014108411008e40d54007041c021405c1504000018040303604403030680e540301c200161942c3d0915411181507110b110024140d200303680703010071401c81c50952901107501d4a0800740d001d0f03003410b400c401603020380150700e60415801c1c00400c8070707509940d104603240c107080d070001030130142e84071492483c001781a8440c0800700d03075680040c003c1c0b0007413413605415005080c0f170540c9032192200000b0360f980ca804100071003039400030074160101ca2082e41294243c1307400910141c1203080001030314041c0d906c0416162249041401d010303040c84030224000070a420020301960b90741d0310388044420f0048440b0590140740e03548560214980d610301c40c011307002c0e02802c1440c0c52503180c1032504615140032500701d030f01c08200d00c00f0200141800003641e040259043d240100b80c589070341c80440c0c5405c6801c280208404004541e483c2140000141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851944811 1250 851943561 851943569
    0x15180501060b0f030f04050c030102040605090a0f0602030702060a030605060706020d0b0d0c140406091a13050f060d050309041d1501080d0f02030c061003142b05091504 74
    0x80120580d1500800000c0c03144041c1049071120510019406080d80c4c0c0f0792586c818005c1094600c0712440c2c4000a003241d21a41103900803400104090500341052460403020300211010b81c8909030401d04003a41d6809008002441031000040041e00c9070300ca604540c005000c060845038072002c0034a4420080d421011000100515101501000b0700d0507119060680f500040002541410003032910f8828014114458105888241c00a43c0450522039103008481881070f420320300206030f0412000116003000300410f0741c102400d000c443c06c0140400c6070031074000c4074540000c1000d480c2c1541540a0080c0440c0c0c801d2a00d000c800c054200380743c0b02070000540c8000c2e5070341703070200d68817600b940750080c0203100c41a44035200038004a80180c12480094041e401143d0520301c0200c02ca9103484400c681408811581034010410003401d0824904020707071038000b409900703081440c1d450031030300c4074042240034510a010b40300f0614081e02c00c9550780c0300c01500550340e200d071074040184190b11601c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851946061 1250 851944811 851944813
    0x121e03061a070b04060f09080309060601020606090114040506040f1a1c0f1707020a031202060a0219120b0604170601060905030a0303020918180610150804151805 71
    0x640d05541c0024211030200364003d1110500da1070325141e8200030328a43c100c049071555510070080108906c1d00c080c2d4441c078400c80c018845494040e000a00304072000d45481e028500d0702d00140400d0303800101e1a00951010740300024241d80c0e1100007402341c41058001001c1a1401a000801a070300e11400030201c20f040c0d417402d1003034110500d00080401ca10002800c294032030440c02002403981c8030b00401c858040e4200e141404619000540507080c00e5204644648107030803500550b603018401c141e4007803103444086060074003c248140c3d0181158403610f04000d142d01000503070803160340c44880d6000c4007410407500c1d15160040003c46241200800304d203445142c0c000241076209100714025544043e0262485144a5a0680c040d42052080310b50081c6488247d0241d0310400c40d840740702d82d929600143d4605481d680e43d070b08201d0081c10026400c2e85c40c840902290403161241400b16a982c5807560301070340c50b81000b1280801c190650b0f00c05d02d040085907001000384905001107103000380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851947311 1250 851946061 851946089
    0x1e180a0b0123041206020c0609030a080c03070c02010804060e2d0c0a120c03060c0c06051506041203090e0a060f0905040221031e0c1501030f121e0306 66
    0xb01003590754032000011012420100001c0c4030420150741c00c06030b403610a940242c28206c031221850709083c800c940b913405951012480340c40342648440416009542510000d20b50f003088400103000b4010283c006e81032104003808030741007010350b902451802154a06684603940b108101206d4911400359884016060304001a181c075004102440081001405170303030801d107021001e010300140031005690028059a000010806a00804e00351181580d10b1840d04007051400c48100d61020b07140031220b580d014210000c60325010100d40c1a5105030b591a00c00c0e14051400300c58181d004d40013000c01310589014071040040540080060300c04680403811030790340f0355407068211801140d010758402c008015034003041003d006200104490700050320b140c816050303081540400502001e290507440040c1c04424091b0038082d03501140c260780785028081d45103848450b82d2a54600b4050300e00c81405004007507482c06000250880314520052540d1203200c0309000d0028a500d1199a0500c1304c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851948561 1250 851947311 851947337
    0x9190302011517030301060807020a0501050c0310120506040201030b061615111e2503080612010902090c0a27090f1b0c15090f050f010b1e180a0b01 65
    0x14200c4007604203c0c6000850442e03190280440c0c8800c0094251410f41c0982050400801c0c070038005c0341d1080e2880c00c41147d5030b007000c09108604402c0c56100b44080440a81003400042c00400c000c2d811680919001c80c03130454000004120b0300c101c10500081c0034007200ca0604001c01b900d904c0407400300c1c0c002c081010421030030511900d8402e110307a002811000c01c80d0780700850407110190200c00804000090308034262917001c01103041003d8150041855417041101d64075005182e1807a080e0620002e000e407401c280d010072001c0740042d0051b11405c6000c8bc124141602c40c4520495102000000e40c1e90b80321000a0700030703984040c0c011250406c0c14080b0003c034014072402610740038602c032000184071400100049032403548a4600701c42107412011034264101b550f005d0002140d028a10f155090000e91920601e0491001140c982c02d0b414622410341035a42c4640401c408540d692185105081c0d082c00610f0082c200300c0420074601d1294280705200300d45901c580c130049400c5c0c0b00c010452400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851949811 1250 851948561 851948579
    0x216030e18010f0308030403050f181f120513060903080a0e120910030608101e06060e09070e092401020616050d0b0d0501020738091903020115 63
    0x900803244a03200f540c03001c00028101000840c0d00600a00d02142800c0c44941c09400c2640a0b400040d12060490460203040c64030a0140c00a0210000411072000b4143c130301034226150b001d5015690350307585000840c0e017404281403649040d4454030401c40041340340b0b8040c01030a0b05030340360340100e49804040c2120f18000129170841e0f80c85146041c0c2415403000c10046174640b082060020140c40e0100000c1208040000d010200b10b004c0f070200d0780300e51700801d5035108a00b5039054000c0383c1c100300d0100f0000c1d41103135001c905200c065411880d07942e18110b0586081030321011941d00030282c50204130301100e407208145000000d81704150045542c07240120781e00d0318141d4000d1003d002d800c0d04000d8a03070241c802040702064112001c11210601320004410001d00c1c5001e4079183d400003490820401e2100c042000641e10414400045400625030240588030000c0003088800c07900108049075420044402002e1540c906034110011501e002400b0303001c84048604402805500842e043e89 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851951061 1250 851949811 851949859
    0x3180305061303020c0d0c090f1a010c0f0b010909110303030708150d08070c0807050d110103021c021308061506030a1a1207050f040b01050d09060216030e 68
    0x2400c40000c0c034250301d80403244141c07154032031012002d40c0302e2480d0b0f0869580322001c800d0041406401a03107041840c0c5803546058444035800b0314030071032814800c52403420140c071100088040030310b48814084c09500d80342c1b40c182048180507083c0020f0100014215a403034000c5000035101e080755034400003450b070900d580e078001500d029002c50381c02e20019400d05441808a604000010490f140950a03a2100103503a0b10482c002d0b00c1d410000700040c0481c00303080240314003c02007070f118004c0c50030407615401c0c1c0c581c9210812604064000500580800111005001700604e0060442d0740d0291041c0e44801c20249106480c443d0089070700080300d400800d42441c086640c007424181c40c40d5a0320b00300100924200061360a40701c10185292469103860f20042032814819004021003800d100c104011400c040e0722a901c294144403202440d40d0340001070381c24041d030500010841c20304601d040300181c0146100031085010341c035014014558048087c1200b00c0054540c201160819400b10400030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851952311 1250 851951061 851951063
    0x306050d02010e1923030d12050907090204080c13200304150c0503010602011103042a05030d0c020f0402030c03042303070c171b130e010203090307031803 68
    0x140e51008120095401070160103040c8500403c4800d40c40c0d070224982e14030782c0103500300e02000e2042e0548104486a120780c001d4450008800811484c1c805200061480c0d80a40d440610580c8400202c1c4480300100301c542e000c4c052003030013035480d04d865103100c075a24180592500d1103a008a514045451141c1c429907020308410242c1d55085081132003080899480a8800c40780c0345000345003186032a1182c82809030744003250341c50750340d41d514059001b420343e40450001103100c03c0c20000c2c0000520401c00b00b050b04000030007840012010040c201d00c86910b2a0302c080e03010b020385904c0300d002c0d0350302c00c0d03500502030b1086075900f01101c0848180304c201d000807181000030940c20000314020404c0061400c10450f02500b43e48000308019841d85d043d5040140300716800449404144a081c0750302004400d0840c20400501501c030619200d4400c494a00c80140e0185105031a40340c05002160030002c0d44051020080d5500d003044c03000c031a0f40742d00844040d00011111150051107540c1e11140c00100d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851953561 1250 851952311 851952319
    0x6011220010f0c0213060611070e0c070f050c1917060103020a031103030d060e040314030403080a0c020a0c0e0106030b031b01050a050409090b090f0321091e030304030f030605 77
    0xc124800400e443d036102000e4240d9100300440c4100342c800c1150301584000c1c11041d5508400d019007000c00358a4009980c103d1680e084117401001502440750098807050340d00721a107043c1c031200307508140f807e241601044d80d40140880400c28000c0d400031070100100d91a041841c82d01c00c01800d041170703c884081c04000d40c0b02c01840820400b08120305500034210f0381c01020f4a10345050440140c003110055800441c0444480d810003081c107810034411840b40703061044c2c29295191950f00245030a000418020070f0a94800761160894400c00012004681c4144441c001680310019051140070034480c03000001d003403400032900e604000c01c50204000c04011144665881c60005650304d030045440c510400c0402d000014104030300340265001d06000b13003216090390030413003011030824002122540169100304600c089507a440302096000c0446548904102d0301c45021003810301c3e09008861540c40d03100030044001c0000880294051882910b5060396400460802d805035100e900c2240d41c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851954811 1250 851953561 851953577
    0x5090c0f03070e06060f19020d030b1e04050a06170102120105010c020130020a05120609061c0f08130617040b0a1d10020405090c09030304030f050c030601122001 71
    0x240c0c10510701601140e40e001c0388160600f47c0b422145001c0d07503503c1c1188001644240c2c0c143c0c81007a00b6108821121005a07800c640701420800d00300c140402000b0746c6030213641e80e040043c4201401e584044098181040e40e0381d40b0710410600c1c24084d41200039000100141c4000001c2c440d03000e2040303010074541c180c40e00c40d02080303c4d0f403004508440100414552003150000102440300c50b1004040344500b0751101901c881d04140078502001c1c00400716802001507a061000300d030b07620503145213960100e00c000061139626227030221504200c400010059100031540441482344154907800b034803055950780c053300d007145d4480e81c48014152006801c5d0030400022503012455900810f442c00070510410340c190f905110414035085040510503401036003c1000e100b9407030044003543d0032000390440c1604100c0c270600001c1d1641306d40e100040440e581d05559004020060100e81030045005003a901150382d070b843c0000d0110b103104405c403160340000403100d10140140c090600101410f17512401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851956061 1250 851954811 851954821
    0x31018141506060d060f0303080a0509010b0a1505070f080a1209020a06030e03070506040302100f0b0a15110102070b0a140f0103080d0e07090b0a0e010324060905090c0f03070e 77
    0x35003980801e444c858135a440f03d502050203110160248010341c400e580d5500b0310314211002d4002c56a001c0c0c10141c840c0d040441c0d040940da54207990308203517512a40b10003924505d0f04003e84d03240c03250b01e00045c16802800707101740500182101428000050f40ca803002d407888103900d40411a504c00300020340c49031341e460060014600c030b0b9000c840090301650880740b8000d40750b11814940b80e8100c904500503884006402d19001030f0f80180f48054102e0384060100758821000240c41030028041c803400d0006100050751260301c5402000251145a0000c564070b40d160f080a61744104102c031a981140d081c08000d41081c40c100256511400d403500080c0c41590950360b0b2040641d01507100810300c0758440060780e5407040d090042c24000c0508100003c0c0da06036000a010f00031503c1d0703029055040e0828010000300e20509000708000745000d5800c141d51030004c640400501083d0011400e8a181c1005c000e0001d070001000b00d5241411100c821000088008056542046002e000751154200021903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851957311 1250 851956061 851956069
    0x10e01031106040b1c110c12280f0e01050c0c10110d17010b03010e0a020306010c080c0a021201020315040e0c03011b0807031109060702031018141506 66
    0x414540148810300d480c2c4d0b01c050708409a0010b100346416010312020302405d1004a00c102c5541e69048501582421011541030381c54040d520b0450000c050700050059020152000c440b164594004001c0c0007900d0b503002c01003541c08035461076030105261012525981d8055001d407101500c1d104000d0200c0420302003407102c041c071804035070014058980c041c85044002408510b03407001150303860f800c104480300011060344806034458540005d08000500040b004507280561110110320013694a84400c00100c0c3c038100c0d0034501401004000c60ba030300241e040450b01500b0b0900031642d00303420403a500f024a081380b1094801f020018803006500078503040c0b43c0c0141d04508811030585a140758040082805d540340b054000020100b001424100103410880171500503d451408002900c45505600e00b14454000c0c0a44510f002194040c2155020005a0004c82d43d0440900040501c0a00780407030541e4102d0441c0c0c20b92088080d030b40902d0380040c5501c01900342001c14030716a01c1e060248 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851958561 1250 851957311 851957333
    0x1e1602040213050406120c0905040c120c05060f0a08070201111e070b040501022104020f01050c03130b030939151207120b090c0a090f180c0206010e0103 67
    0x88408203030120003e0035030745902c1a480285a05040710030700132542d140200c5101e207190442941d117480c000c203100c041104400f2090075281e01060726100120780342840c22090030198801d03a40400b0014000072000d92050140404202c56202e0246503203079503405a00ba1600c040c81a0030b0f40c0d005000c4c001320011100e0410000500d40340c48645011720702d0701c406200440880d400c0d00e5917900082c5848010480c0d00400864601c000564005802c0c030760b000032094400c84410504129020480e40002d030070910884003d0f200710342d407161003039656601188460300120b5054425010b8101078a103011110b407002030300480307810112a0209255400c41d0766802c614080240c11450f02c100d20320018030000c00a100b48102c10210b0081031402060081c400c50b00c41440621090030208020960f484001029400c030344840c0040e611100300c150210340400e0b13194400145141c090300d0024000c401507003d00041007221805000e000c94055084c2d0750b4490a104035851400740c4401000460340d0440740b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851959811 1250 851958561 851958577
    0x10b0a2c190609020c06070c050307300c0302100c2f070803070c050f030a0f021c0308041709010f0e030109240f0b010f0516050708031e16020402 64
    0x3001c814052012050000c58560b81c0007180c0b000c0d400141030b819498200410703075000542e0320302680b12201d15910300740ca0340200c4600604401507000303458038568054404200d0340c120031070341c0482034003000700081900e00400020f50240c00b90610a0a105142e03006420580119458903000408841907a1000401c9480c195010041c00aa58001d06c40107018000040000300c0003103480b48050b0070b2098401c502c0b075010318428020760254100310f880c08542c031140c00760030880349100c0300103c0c004151001e2001c00c0c0e55150508403a039550815030412030103405580a6003900b010304d909441c0b09105803294001131804500320061001d500c510540b0b034024075a43c080c0022403003901c103a4420403013202000030b00c0c0c0102000003201144072250b20400b18510505c0c4c400780010008000084c09444c500c142c40b1042000c0007500e0a540c2d00300b2418280800d5000c2c00b141d60f5240d80303108003501d1340c000c0c52001c16410354454440d400c034070000041c0e0b2010300304400c980c80403035407550800c0000e600406c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851961061 1250 851959811 851959831
    0xa05120c09160212130603200c0703110d0506011e080102190f1e121e0903090f1508091510060909180b0c040305010c02010b0a2c 57
    0x38151600380c031040400d50040ca10070700c10341c0544098410203814841c0c010103480d070400c020b01940f1700d000c594070600300c2118032604000500c8400e400000d03185911124400800ca48002400700c03030f00000146000c00c0f43c2c09603507c91858035415080100100d04250094055848407005020020040900c61074401554100741c485942d141c0c02c0500f6600508001e00a05108000b070341c02030380d04005959040046440c1098841c4003c400c0c0500000002d03807907a00300503065680d0f0030f107030015500103103450300101903c3c400380d610841c8407006401e00036070441c002082d2010005131102d42003042e00a43d448641861420490800d0494032600000d0803a180781c4104030103901898595021240190f03d02e41d04088441e080a2021304082c02c1e42d0301a605245c9403c418201441e158032200041d5a801079250003141c88503518161a80034541019289501c1c1140f101c03281601588002414001500d0104000380c0c0e6400420101c540791109100090004000d002c9105c640580c281d441240e0304 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851962311 1250 851961061 851961073
    0xb0f0a240e0315060d0506040501150605280c05060108010b0a08070303231b061b04050d080c0109150b09180c040905011e09052104060f020c130504020f0402090a0512 73
    0x14071b0305071810340b003560103941c142d640e101491582141104200c4c05411582469483e048643c07a4100c040d20040c2e28500859241c51006100903100c0c25641d070030305400ca021528296140c899080c000c000d0962001d2003900c0e020030008201d1404660803089a0305901c4481c6e4480c1d81000114031641070781c590102d429410402e81c1007554499000d8800e1700d215600400b110301c0c08204040002c24806d2658581388400e00082102c1d41c0c0307c008541e00103070312001c4a40c9401d0200941e90141040c88001000201045038001700341006a1014101c40c1d4216060300741354170360000d40c40c25031150a009070101d0b0841c0c0d240c903042d802c0c2074000c07a0819110350000160454440040c1070104a54a42200660780f6003030140d080c002e04004040151701144d445005101e03405001d41903911030347c03042c40c080c029846002c0c0b045a00902c04c404070140c015003607142031041d201d0381400426080b03030f00300e1050860150130411410180301765101300d10050000055903080c0410000052803588846550384604 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851963561 1250 851962311 851962313
    0x1b0d050f03040318152d11150702032104080a1b14030a11012c010e03030109060303180b1605010902120f070605030c0d0b0f0a240e0315060d 62
    0x3c00079100922140d4107004a00d05007200040003584c0e508603007030990400c0f81c03821580b9170056002c2446070388181094440ea0319a00c02403424a00184800c0c0300c02340c0701e60200a8560780210081c030002c400c00226107016040c04604070045002560090003e1030305020918145000392924131020a56a100d0ba0408105984079039100d1074903001c1d9251390300042050014150019052303141030400c45c00174440182200c079240c004040d18500c1580030708214070b941c03040410a6102d44203445c903010a4991300d6171182410805044c0620003107000a9011001e043c42c5c5480c1404081078800d00406541303800b131424600c01c05032503003080964407556a00c01d010010f075919500d05402d811040007402d200342141c0038007400d0540650085c010b0040c00c0042101116056084500d081070796400028007260040200d00c1c6580c2180c542ca0f002074205c5070101c0c030180450f80382c12100c00c03001122018506034950880c0d020f0304840010b501548030414070110201c001d8205c0d40d104101510050a40b00e403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851964811 1250 851963561 851963597
    0x15040911090403020102130e0f04171b07260604080a020124030501060509040b040615080312040b15011407080f1801081302030d0305190c03021b0d050f030403 70
    0x20ba81c12005070b980017940c4841f940394001000010401c0308140400c52401c0c55001004001c000c00003070480350050f810b24160039540054482d03403c0441a54442001040a000da4a1045020f031940090800c001041c07402c030401e03e04c0c0c1039031810b1400fa040c2030711583c1d00c940c1503030080307094101555215843c110002034141030301000c0012010a0700380301460350034030608651b490b411a03800f80810718100b0002c030715803481040d0003035488a00010781c01031401044184100e41e80080304540000030f6208203686400d41150300803405452010b5154840090000b9103154160103d40424000c0d0b000c1c0a00701440c00142c4205030103100c10328544820700c1c40040c62039000166400c244022000700c1076495a000e000313654805070110381032114884540010b03642d50701c0c1701d001c44c0030143c613640000c3c0401001d07501c0b580201031449052001641007a40035020750490343d02a40c3c18a031505886044020020b40c0d0941010103450343e0345400e50298009459610040003274051115121180802d400303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851966061 1250 851964811 851964829
    0x1b031e03030610050301050a0e150901060f02060a150504110909070c12030b010806040e01111305041506050703050d02070503040905150f0a0b160c0602150702030315040911 76
    0x910246540745407a10410540d000038140c6071042010600041c05a03032615080207080e50610580e0010550300e0013040024a218000007640006240c00000342e5142c000d00301218400481d0250f892555804090004030307074920030a40484030303619108000c07508280c4c0c4607444016107203000c18a8a000d000116080301c1c000d42c1c0300000144190702e0300003805072400100000c01b0b158941400214403002c00201007001c003030b10701403045030f440c26803d80c0b42d4002d501201c40103e4000c084c0381c94025001130580a4200340c031901e4000c1342001d03012501504007204190980340c942d2a00e5040155075201160030f41c0091804500d0b15508018400105004102400080940f00c001054610b07144101c5e07210350440040346401a060f004481d041552044e40c40001d40b424461030076219512002682c02c424182c85016191069145001c5000c4d5400b20700c886400007004452007140d100c14004a035a1300c4203c44c410007030181f100e207080191405402c40354851b030048420724210b4a807980020134910b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851967311 1250 851966061 851966113
    0x1b0206040201110607081b1606050109181205071a010b0301240e040209030102040911181504150903050102120601111605041113090b0312030106021b03 67
    0x1a00060400003107603400031401c003102e01e01e000039000600701101d02600c02e00000d001034012001203802e902c1c441820000382d83d40701c83c0c503100c1c07041a0841c07400c3c02c13401441c081c001d000041d0f0800c0c404e40d20507159422094040c42c0d00c80c6020242d00d204c1e200403540703a008154102c441c110441100903444c0a1000468060940c0031481c03990b9500d000c00c0b8100108000781c0403c44020280807a540c02500040388c1060b9050580c1e02603921140380300024028403440d000000c00c6403501008005561040003d41206040e5400d4a104078103c40104481200ea040b407400d0385c2c62023000309201d188020010380e010280503040c04100c9548035618582640c00400f105440b00c90a202004a10369201a5002c0b250b40b000c07010f00030708140c00c1601810f02000f0b019032800345886080101c1002d01450446002103000d0707500b940d40940351200540901a481001c0384070380b080025080c0b00342403020850741240c0c015001011224a415004011207000b1500035600d070003600c002c10030340c6c2c026661000d220 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851968561 1250 851967311 851967313
    0x1b06090f0c0405060105030402010c110d030c2009010909020102031215010f0504120b1308041527030b0619171c0f050c0c041505120a050c04020d1b02 66
    0x1400e03211050720309040303595401e01ca02d003800e003841901e036041000c59800540a2030800c0400c00c030b42c2042001000c3c104455504940c61000f814141540844007103400762182000c2c1e030101c6030340c02080c10f03d2000c811a940d40134949100421900c0f038a6405401020f01c10b00560341081001c0e10030100108044810390781b1540942c002002d95a8031507a8481c0141003402d245090909142041c4c121003a0a00010501b0350b640d0041100384803400b4800301000d500c40b41c4507903216100c203c14814107640c4101a404620b2148895103440c400e40c000d110720820a455a0203c6440c540b910000d03401c0c00360446400000d81d00710000c2c21a0200002d001512408003d40b0500168000301440c140c04e0000d617400b00c032004400004140da001000300000c0f0298a4851749440a0140140c18070a0801003690f000740f42005031412070504101805c01c4440c100c413000c0e580c0c07920812140d2100d00300c100c01000b0342c101071502c031801d240613400b501c4600d001d020300240a03404a20030030360880d000030005000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851969811 1250 851968561 851968573
    0x141501050f0a14040b0109031b06090609080a030c0204143d030b0403110102040f09060b0c070501080a0905070f080613050606090406090506240a0b030a021b0609 71
    0x6103007005030103801e1100c01507400e40301c581d140401d000c0c880c50301103011034403d6448080e02a4070707038419603d55019640280401100c40810030f40705100c004c0c1846468003054082d0400500540501d05030300440ea0841c1c05021801c4007075070103c070042034200f8220380c455507640800b204c1d01c04071040248100140408006040200301116003031102d1402091003c8000307140f066185c08540500b8000c6a5000301d80c003d0544607848c0540d22480c4004a076156584045000559245981d1810044640c00c9508000c1c3c0d40e200da1a00d01c481c880c0582107030199104001c108004d501c41c02559501140101c00041d0b91025641c5060903c11698488903981c61196001e00c20743c10140035054020002e10045441c0444580e2081d4450b1002400d0030b200c2c0301c0980c000382c240450b5410841d525940300c0c050f00d08a182214940c0c203100032308022903540394100c4d500e070f802d00e00340b420f1b030031050740c188010481c1035030398100d43d620195010090b441181103c080310368800d60000c1103030034002c4c03c2c01006860 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851971061 1250 851969811 851969819
    0x203090c03060c090f061e0d0603020f180711010e0708030c0105010b040e04030c0f0c08010e0c040c09090506060403020402070507030303110711093c1021141501 71
    0x407030444003034407540741c02c2070411600c0700b1903550100d82d21007100d042c0d074055110300070280840c0a150891f1040500b0000005032040401101d600100c1580d20841b501d00100e0400f005010100d00060074100030440454003040b903060003454910a090103505c00401c0c1e140d8901205828064240c0c0569040e910110305844c0000e001e0042e5405050510456400e245c60010301c500c0c9244060405014004d000385940e042c0003651014100068111313070320104241d40d03190480d00174852903600141d00e020308a074401507407826006103258060a90754281c44c443c1442c0086004020142c05664071050400c00000142c6031030010f030003118082c10150414030701d542800b03016920602040d90b4000720400c4144006810402d541c02c11110554030b802a59581e003020020f00c1d64030312404d0308507420190300038041c1410558186c910464150850302c2a496410001003144068001c410b55031921000421600290103101d0751401d001c0c3c561640548426044a420309503520050f4040381030fa180180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851972311 1250 851971061 851971063
    0x141606080a112d1b10050705031b07021005030105030d1e0c06090f080903011505180615180f03030304020306180c0405010e04061815020a050d0203090c03 68
    0x5903008003161401e100c004401d40c0d030300d0503500c10140410240c03800b488200c0401c0c28040c103400f0031079215000c40c9985030501080b5032254110b05400d442d862080340c0d031300300341c85916006450042c00982c42c0d150542e140ca8030501885044020b003004030503c00e0014402594440ca81c00c1940c12168552994030750401c01494200050a00c803001844003403e481e103652038580007000d11012061801003030300c42040c03030284040e11044502038000301c441010720050080420003004280d604400800c000c04881d11148809100780c419107034040141d044c0406952482064585d00050041c00d20b248070b044800440328507048141d58458230003407214040041d0500340400001c100d402c50003141145826800655105001003520701c1d000c00c0f0000315907035070f00c08100201c070500b40244140719540e190f40c1d5810069204440688803c3c0c00c0602c03040c1d4a448180c83c0b140c000d074001103202002003010349544083c1d40034121701c0701002010070402010981c0c510181d4003640c00c0d00042c4c0030100d6110101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851973561 1250 851972311 851972327
    0xe0f0f01170a06420c020402071a06010908030301050f030c130605030613080910090801180204050c091513050a06020d200709090c080a0b010f0806070f0309141606 72
    0x240e4982001c078803241302d01d0701483d851070680c85009041c01a500b1424202103810000090000f90810300205600c0108141e2000e241c5058411801c51039031940e481004641162040c4540c20700b0f500104018000c6042203e98000c0c01c450190455102c0c4400202141c6165440741d902c2c2c614030381c3d409080c00030746801e006094216200c3c150740364600c42d164030750786d07485d10400c00c0e1940b090a94a03040c2c8545400b511074280140009002001511a0740808002906a01c007040317200d50301c0c0100280202d8114001e49a0542c0e01810341485c0303100b40c0c2480001c81d403040c44d11001d02c1e404a00001500e0351402682c1001c0e050a0340030344000d403c45600545030858000b08601d903408041d103a45002940060800110b039424000415045404d04209800c4c04003508041c54500a403c015424855016000d5040b11503500100c640148d58050307141d1a288241c4001c0001040804882c0005110782c110b40000741c01840192000c090480005203003103109105010009802c01c000c118141c0c0101c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851974811 1250 851973561 851973599
    0x3033e0d1d0d032f2a100e04020708073e120708010905070902040e0126060106031a04060b0406051e04090f0c0e0f0f01170a06 56
    0x44038402041d004011640e2402141580584800c81c03015042c903105019030340c0c0603041e4800c41180c03542c8070050300c22445055400707080b86100e84413190280000c00e14008072103800508600307040c1103c8000300803884c58450342c10420010407a040c0c52403030b80d840c8014110b0034030401b8001e6844002c1d241810180a0b02c4000f6074945e10307035100c0e0403501c07480e2680c0c94a140b00780040100408061400090003419145940c2201c2d2040300310100f080b500540c440000d490141d001c480034940c2d01d034074031030691003680144185200340400400030310041007400007148980001130012254803803400c0b803400324260b00c030000080d201c1c817802d019015240c407003040c1c0300d0054405003c1c0a040c91400c81e001d1103288034960410100250542841040c0b508000c44c0310384601d405950f0701d40e05c01c03000c03024103c2035503030341801407521044810175401454528a0044080c2403084480e40031010440d1502e000c0d10b005060290825100110f4800b128415108451440c0000380050509491281c1c0b0611498 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851976061 1250 851974811 851974817
    0x60e010504050c0909060907030213091d060103110d080c151009060308041a1e09090a020903061906081204030606050102120304150603020604090c030c0e0a03033e0d 73
    0x107213200b521103000e044e40c01002940d030b001e0719480d4403d084000307109000070320404036000c1602080020240c1c02808040c0c0d4000340c2100d900c1500703981c03076032201820b200080a5152a0000f121741d03040c200c0f4040000c6009007080d90612690307e600e94141000c4c0f07000b40c54181c00c0c00302000303054203071013003e0005425106000c000c85030644e0b81d101403e1055008641d0340c3c810600301c1c501c4010f1910308513124007030043cac140c4204981c408220500b5401a1100b507104295000002c1e694081501c06e0f500d122000500038007250b220f0388518071806040b010314640031519004040f030311400822894443c0880c40c0540340d0b480746103082c10380c22502c00341c01203811504900300f254000700b519010f41360055041101840102d1341e022004c001403000c0c0d4002504201e01003000200c040803a8010107090340b072900c06000d1800000c500b00c031414005138075290300a180070030900200e44250380011200440c42541407105080282c50f0a90350241c2c5031542a40c031012184c6c00019900344003e03514003407942 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851977311 1250 851976061 851976067
    0x15100e0421020f15060402070606060c0b0708270703080307020723010801030206030a09020a060f23041e09020f071217010509071205040311071415130801060e010504050c 75
    0x14030f4030388030810345002c100c8803040c14010500030ba031aa41298122035000d9800c2182c1d980d0b0310409070854000080c21f0352404c0700040040c1072076015080321885076032a49a0344442800b04190048040400340907a030035441126000300000300248003c50040c07910b500205100f0b46400740d5111041e80388094404178001f020503039030a698003c80c80e141500c0e4111a071a80340e61312118080c00819072401e01940c040c03002000014101e40014020b200800b16903a010290303405403054001c10341105186040400d02000b04204032112010818007000c088142c0c11800c0340d95804c2081070342c0000025441c420f40000d0583e0802c0711800400c0304502d20b030b0400c4d44504801e0000701c00100c405106050150590303500080b080342c806d44826800c120100340811160519050003010580e902007504141c1c440e0340e1300825101d8900108143c050310042c00010050300000300c020454104568403030281d1048080400c68500a0050700b010b001c444805030302e01c0d072400c0c0401059540103481100000010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851978417 1106 851977311 851977333
    0x12070b04051305190b040e01111308070602060402100311180915130213170102071506151d1806040f0506010215100e042102 55
    0x259241c6540c00c032400d100004550064131101440c001c8062100c00c680150740043d005400080c0c00842c072440c0451900b030a4511a5900080b0fa0402040d070f0205818080d4500009103182e0b0010603605107000c1e070213902d80c1c41c0980b0190066100d0120400001c0c020380148005040711111290341d040320354000034910461448162280140c00041203050905680030700310301000034100c404460342d010100300294454051240c2c0d1081c59240082c07010800c943c03d003014560480090303940e1101e49014004501e4800e0320580c80d6140c4a02403000380120903003c4000d60150030f02e04400003402c410001c1c86140741d104c00780d0052000c0d04d15004840c0307550103140170b1401a2400c1c01030760304001d00403056610840e08940164001101d0710284445001c20940045110b00c207507014640f141d95070840710008031401d4403e0301d0b2980e81d5010600154240d1480b00d0801e01c0036000381e07d81 = true := by decide +kernel

theorem cover : BRFrame.Cov 851798561 851978417 := by
  have h0 := BRFrame.cov_init 851798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851798561 ≤ n) (h2 : n < 851978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
