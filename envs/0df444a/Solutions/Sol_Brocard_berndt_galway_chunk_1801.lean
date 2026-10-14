-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1801
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:37.198969+00:00
-- url     : https://prove2.me/submissions/c227f657-d848-4b95-b138-d9fab1c9160f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323741007 ≤ n < 323920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323742257 1250 323741007 323741027
    0x702070f1d01030215070b0109090b0a05040308060f0d05030f270102190318080c2107050904020102100606021b03010b0d060f020d0905030c0d300608011503020a06 72
    0x72054800c0c0d080d0703002c00c48045e05510b501c0c041100c0402c200c40000f5a1002c1081c02056842c070700140c0030201c0c0c1000d42e10088010081c40420703240204000000f5003040301d82c0d40004045e561040403100c00404a40d4441c0d00d000c020f000b912010034030309815030700c0c00000d100c64401c0c041d03056080d864401102c0c20121109490b540540c10102110280705540a010340702c0340e001c0e240c144640c1100d85071031708030b420540c0c001c4021074102509004003420315011100c4400022050385d02c81100c00e040140e120f800e28001c0394071950f100c40101302917a00c00c110403550000040000c0001ea0f6030390102a580e03c90400900310002d81c0510102c1c05483e0601c506144040c02900c4801000c0c00303650380030000c240304005407203110307400d10017649039030503c0c41210091489480115030b1910b80000382844e1081c40c142d0801004440226041142800070380d6040303841c9080c1100b80d2990040311114090038040e00085d415610701190b01a41040b6000300d04222402566440c001c5911908201c0b0049a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323743507 1250 323742257 323742299
    0x605150901091d24280b03061513020904020c060a05040b010605070f030324080303010306050f0408120a020706020c16060311041e050a060819140c03100302090702070f 74
    0x6608200008034101420321a03001040d010500c95118400d1140c00380c5e031500b00c60600a040d81d401c03c9102600f02000b420f03402c460503000c80c81c0340c1c00701040041d0b22007440301210742619801062454450711181c056902c01560541a10b20600d02182c0550081c0400c5409407a040200c0d40002020781c0078104590900c0d411422a03140f00b045038900b6405004c0c5103440b51158044582c080c815800c1c640ba900c009000164044c6a4a51541c2048801d540000d8400d04041226030203210001d815501200c0755000c07403c60185090f030741e0403c3d0500034018000c015140f140001040740756020301050107171904d2072040181c048243c4440c003c90840c1c490548280b4052402c01090100740340c880d1080118803806140714801640740d80104080c0742c1d440d0b100c1408942c0b10b1302804004d030010f02540020007140d0108000d40303e407800c080241c525015124078140e80e80003021400c0840254074402c050740d000780205030780b400c0035a0008e5030782d012071050382c080324080000400d0743c502810980c401904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323744757 1250 323743507 323743543
    0xf1902030c121b1903110a0e010c0c0506030c0a2c1c080f0307020709090302100b0d0501110309102901020a140d030b1801030605150901091d 62
    0x30540301c01d401c2d01c0400341c10743c0703010006002051072024104000b000c00100e00c03a1800c600c606128409026a400c0944580902030107101a10070a50302c412500c1c1003160901c2e04210760b4540307041c65080254542c010f039030030240000810444d8a0200000c6c0884001c41da0f600807034001045408280703c481e10882d084d00d04d0b8109800002e40b0f0203505210844c0104402601451705030b0b075541d04168410a07083d580c000d00401003080c02c54050041000a022100d41484a0f01007564002d40b5070342e010a148081c0307540c0707040d20815600c0d0103404c0030720203a11100802800144800300c0300960412141c0d4007151180c071418902c488220300071210b80c04210075281c4030280d0503031032040320700095102c040e04601ca2084a000803803080c409415141014401611030304411407002010b5882e03180045008194210854203038980064400341144d030005c000054170345802045081034049010841d611142001c00030481022035408103514005a24001050505000329662101340804000c440c01c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323746007 1250 323744757 323744767
    0x5030604320609010b0f010c03090e090c0d0501051602030f0f0a0504031505090c04060308030408070f0803011d18100c020705040c12150303020307080a030b0a06020a050706030b030a0818090f1902030c 88
    0x170bc01d8554550704012840192012100c0040c081050610307180070a0301c2c143e445000b0301c041108551400941402e19102035854460b40303403480c41e01803054041004c40160001480341c0c21510880c02c2e00c0c0651740c17000a021409400c800000090001075400c01e2050051440c0c82015241c00d02c1083c1c116070380500c2c4142036075240d445011554010510649502100d60314040c000f0b4060380085010f00300503003e0712010015110b00c1603040314002d040c00d0306000064010202841d00280c04903025181c03034004280c406115108a04046084e803101e40c01c5400d02400844a80d0000301045041e101c03800b04101700e65030494001401e120300c1c48080c0c0960405c1000b48042144a001032007000f6a608011071400d45510225400d10a00d601c50030040e0000c482000c204001401108002c0c0841e1405010314105000060b072212000c2a0040a5000001e6801170301855030149e064059001020034810f0f25041d6012800c079103040304c002c1065400b042d010409002c05200303580c0506101e9070114281 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323747257 1250 323746007 323746019
    0x30b09010207151e2016050105060d0b04020907090b18031b0a03020108040c050604181805060612011413050f0303040807060f0e0f010c0905030604320609010b0f010c0309 75
    0x400c5040040740c801600d14941705400c40741e5800809040400001407864282c1c541041421600050003ca2051021450b118041a828410780c0c0d0000d404a03840f40407034650180c1540d910401c1d521410000b0400b20f202d400044082d540c82e1035040c4250240c0702d890034001002841100d0042d015940003590842c14400755201d040481d5116108a40460384140c40b00c0008230fa54002d58491400c0c4414015040c07460040c40c068031020395507040e030341c1520648555905448140082119000e5822650303001d808070000d4002043c20b01a6450369130050519030800308411080c018141d407103204500740382030044c10001c11030741310340d03006204203041c01d445d40e03a4007018000c000f034428819a00c4402a200400007400159904000140005680103401101030300480e6264415840b0b604100304000108040320700c41030304400150403000d80020180c411130542c4200402c0ca1100d8400c1008110039404158040944102d04469290f04046443c2c011614506481001000a030b0191010000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323748507 1250 323747257 323747261
    0x506071a0709080316060c170f13061d06010e070e130204030b1e01050409080f070501091a010608010f181a0301021810090b160507030b09010207151e 66
    0x300c2074629221024035503c1221914640020682000c0800360094910402c01030703202d03100ca6a03a140c201a0507140801c1182041503030f000f030800076000e8800001480f010b0403003840c060000e80c0080c040003559031504600c5d114810340e6140940520034200042584079518480a100d4145651860b803006a40d40034801e850f041d500c4400342c41c940a00000c0005074002d542984902140d91000340c3d444e0084114080d146010b070b00c894010b501e052442000b00340f540080302d0714030b2488119680d55540900c0c149004040c2c0714400740c05000040078002c8401602e83c1310074100d070f640c0c0c1d40b552220f0b41c90702500325a0084c40d1149244080c81d00c0382d00084082a9007120031900c0301d2210100c036481444010071300ba64420001a1259034603e000003140e49049802080c10500c0351400d1041359081c88034100c814800e00c0c420001e030024a40030700d410081d0400c0007401456004200c1810b45c200064100e001c2c3d0480c00302101c2031100e201a041c0c00c80d10a101d02105c00311000c008403076004400c009100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323749757 1250 323748507 323748511
    0x106030903090e0a0203060405070527240417070608070809010939060203030c030a020405031e15090304051e030703120f0507020d020f03010f050703020a090506071a 73
    0x7081c411030b448002030040c0070810f101d104002c02200507a8030700d4045d081104603100200117405224082c46881211842d01d41c1d4898400f140108002004000100080e140c002007025007010b140980b40741100040c203000070f0710440b001d00c0301804540c2e920091041d19002c141c021403000610550000f006a481030401c590880011f000008030511141c4400074645054242442c5a200051084465142a002100b00000b66540a2600d5030810b14029142c2c80090601542c40e8408004900d412042d641120020900141261080e00c0501c031030319803001100d514100f1a0140c0000e000d00360300750040440c41414007401440c50541000c0030002081698807500d020507848000b101440c2d1002c01403900610300494030746c1c6005008400040001107201540d00c10864180701e41401038030740d03520803074020703074103c42d84400c1c01c4101c00402c0c0107002d2121450311b0f03a810001442180c541550040c100d9542503994010000c0d01c90040c40741340d200d500002001c0f00105082410400c2d45940055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323751007 1250 323749757 323749763
    0xb090f071707020f070812040e0c25150903121104030501060311030601060912020d170a0c020306010b0405150c0a1b06020610030201050711190305011d01050f01060309 74
    0x6114080000a904480c0c00101c0707010001d0303131003040c0c21240d803801006500010605080240300703aa094115084045c0110b104d83c0c600c01800002040445a424058403400e0b074020103002250500d00010014001c85072005075042c50095000c00484a40c80c05060601ca42548a80c858645030044803030040c03c00219146420302d007404040005003082c018103001b14010b4400c01113004841302094200034040c0d01003028401c03a03400800440b080424600700e000e8046600140860369814400c8040d0118050900b5074640040c230309140c00c0d0083d100621190080c3c3c1115801e07a02c0340140c144910450151681c07001d08200c820009800c400010041058001e0a60b0160f45907a5075400580d034031414100c2500f1621001400040e90400005a02100c8003501f40c101034555000a4050310a9200150011000000d1005592070301c000c0451801d180301c040d0b1b4112552070401c3c2d0300800303030401c101d00c150070030540d0082107607014091180104035285016181341d180c903c080e4000d1010032000c0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323752257 1250 323751007 323751017
    0xc010b210d0806150703120b04050108060408030406060e0112061109010212030c0705070303050a11011b08040c0f0902210105091f0b030c07110a24090801020c0f0d030b090f07 77
    0xd0004c5207a03001505440e4402d842c0c1e52401071802c4010300586030300e800002c1c019840c0a00400450800180440d00503410040482c0c0d661031f6400d002c005001d013901300e000094200c6000140d03d07041c5ea01c1d01c60905004040400030005030b4118a07030030b4403d07280902c0c0107034440c0a000e0104900c1200a68104000100c22841c0080b00d660b0242011925481a0040f03400400c3c441d010380d0304515503c80c0590243c0003004017562a03d1a41612107600a820041040ca440014200040319921074080e20740c0014901c08141e0b01c1900c10007a602816641c0c445080e045002d11482c548080354505031b460060000c019607849000701070000f18045451504150440d42c0041d0130703412500290b014240c1400000e903124a03c0c10b0003412201c07182c044c180a06004441003068000c8800742c480c074404030400308420103201d40c10032182d13100c154025490325440052103041900002400c40b0200b43c0510660b4180801c4a405500301c0d90f07100d404a0704045c414000440c2e00c52901c6420364405968200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323753507 1250 323752257 323752279
    0x1030c0207050a092f0d09021903080903010c0302031308070f0812040c08190204020309070f080f1c090303030209040f050a09111e0d0c05060c010b210d0806 69
    0x2031110560f9502c0311110541d90209040c9060420340c12000400c00c200094000d840e8500f0440f000307205d2070340e0810b4819560b002510841d510801e14061011000d0701c0180341d6500c07801c10404541c0542e0b1624402d602e00030a0700c407424028000e580c4101522910044c0845060720f94034a00ea0007520200c03004080c65042e0400a0b2008010707011000301d6102b01c10451503e842e2403122050540c0004030315a10104030801200040c0030a0340c0c4a90741a103001d83c503a02e40042e02454480640c01001000480c2c01d40895403640000b0b032044c2800c4504110b4404612961a030501c08018021000010b40003000074004640290010810484098400201e0042c5076800004540c020703641700b00c500d91100c14a0041c03200700254891484c0c07003102c0304100d2200d00c0000c00000e0950210240c020462029600700380180c00d26140003c12010b051b041c0d0b100c1c0c071a0b5050380203060356241076100740540074407440c020041503402d00601c44403c0003000c3c0845943d1040e14044801001075500184c0303146 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323754757 1250 323753507 323753509
    0x1203060812070201020705041b18151701091803051e0706090c0b0a1d0a09050c1201140612091f02121509070807020a08182d01030c020705 61
    0x4a29510107008003900c0e81c5588851000900f07200c00b96001a01c901c5c10f062a07103103c00484500000b03860341905215521620446001c088220302c0c6d8807003981c543ca082e4000c411103030400390300117072041d50120102181c0e032260700010880710349851100d5032840350642d010000b4003a0009180403103035601e640c03142c0754000d9544025944911011146103850340c80c4d600402c40e400400d080606141e038011804c12144590050252121900c0c80315801e081138a02101511407071088005400600070621462422001051242c1d000901074141405a00000034642c0721400a0550400c4000d01040c40c14088020f24615400041d03c66507260164250614051642d201d07480d000030382900016031180c6140074404c90200c3c0081107241030400e40207007407030b640d42e070100300540c803240604001c526511114001ca203040000f860082401c0400192001e580c1440b4100c000100d20848000c902c44c4c00b10059000b91a01e614402c18402c03804494011596010fa04403020b2040b03c0c1c030440f00c810765110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323756007 1250 323754757 323754763
    0x307081309050403110d02070803031f0b0d02091008040f300801080717030d0e031201080c1e0d0303110c030423060a0e060f040b0a02100c021912030608 67
    0x28804802051080d59080b107201020b02840c2c01b075250b1800585400c030b25080d003071074403071000408852460480241134a40d0008041d5840064045040c18684441c0802c2000c4000e611456969105462001c00340d40e4440c0301d444050300c81c0754000e01c1c2542030b80507580c881280f5060140440c4250460007d1107000303400d03002d450f1605001c00c1d900e07240d49501d428041c608080840d0041e4849181040001c4041040001214071240c6005000915080c40ca0360240c11805101d0804054000131310000030707030503000a10f408070244120340d048070b000a11070342e00c0c0020b0240d044241d0003144400e50207010901039407050032819401100c17103180414800c14541141e2154028440c8034049050020800d1081004542981001e41d1641d1802c001100090940b080d012030851080f00000340c024041c100c880e06647c001d01034076584589403140302c44040e490707800d0902ca10610b2407600c0d0341c1d65007140c8001041104030402010361140851652107907000d50088000c00c00074503403a801c0c0003e000d8010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323757257 1250 323756007 323756011
    0xa0f0c0309020109081207150213060201060905070518150d09031d0a0f090e01060b0a030c02121305010509030f160f050a0b160c030510090b1008030708130905 70
    0x180d800281c14040c6100140c031240c0d207604444a140e001070350566a00c14940d00301c2c0c80554004500000349107aa461040180c811811102c032110000e40c2e00207107644d0150090b00554103480c0c0d0a12490b9a50076040f0381b80e00a032901c048403820706240715012401d207100c0144600450207a6986041301c050346130015100d24600c1180011004506550314400c07030f0884180c04002250190f0030b541c608080c03100021028015540490366501c0c040d90903440c01d501220040201c669442d80f13801e5140e1001c3d008004807503104025004621038130000ca07000c20101c0d04540380e1582c60444040c2000011103c40d000058419018402d410800ca0044010400076180081c20103030b17202003500b864001c1c01e50081035840700b801800513040c00d100c408845020395201d9003014031a0310340700c06c03182414500e86109070300103412400303a0040440302604071741115000e00e024102001c0783e41c0301c03c4a41c00103681d6074410030685410038131103440060788401c010100c4994400003080c95544802031300c8112102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323758507 1250 323757257 323757281
    0x9060b0c0c03060c070b0a090209070c1104111c02090901080d120212040b04030c02090906060123030c030408040b0316030509010b0a0506030c0f0c0303090f0a1104050a0f 75
    0x204401811440c100441c0c84828000e8014240a09049000703804034054010003c000c1d402d40d00014141070441d0740561000394008000c0002420a8000a001d8000342c1d04181c6444401030145c3c00d141c20030b4080c400c0c0100c441c00525150030712000d1000c4192040300540c000c2c1d103808001492056580d44005806000d4081c060240c08607524805001c824095000c1403006e4010b102a10044010000c0701c1d0703000c0e821101d0b130b005950715403804550f07959002400960080d902d0b0207003c202a00010894070411081c2c0780c4070309810b4000044400d407030795614101c2c040070007000010300d010440c202443d0803910030317100b2a04103502d4030a4420150021613a554610f10410740106d1055418003e00713402c0b00c05c7ca00204060032150012645481d5140101405240c000002c1160b030785c000400c640d050183e8410f02c0d80c541d0b010304522600d03a44261560f0392030b84152a88505260804030320039403c00e0748a42021030105800080c4000b4010041a0a8034655a080160151401805482d42c0440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323759757 1250 323758507 323758529
    0xc04060b0414180402060d0905060a06090c0e030616090503030403080a020601091e1d030706060503101103131106030f180318010e061e03040624140301060906 70
    0x802c0c9070210000241040e0321500c11086002c00460100100100b1078205030141c1d54207540d42c1c444401f80019160400006201d40300300c40800580310300903440300c1c00f5a420510180500f108011040700c203038072600c41080c0c0c1a0000303404511082039040d46102a01903c0c180812155907600020341140c000758800c2e11540000601c01c2c0c101d0b581801014094050740c2c000300007611f00c0c501c8404000d4000385188000326a1013850141d8400400000326041c00e002040f40d54500c030303d10b04040a8a4188240d42c024480c0c80d00e00c1d00381e0b108034000c02076008c03e40200c4500f141d40e2084203240101400c030040d06c49c450740c001865540d88852004601c1454485503094050038080c224401ca8122561504005e80050140708514030507003550f618030700800d1a004115080300c10010301c540c40b81e103a880840120b4004500803070743c107200c080d51146000b1101004010580d11032201076402c00780045150301c0c40007000384010000c609050501d0b440103800011096100d941c0c1c0d004a03503964000b00d042407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323761007 1250 323759757 323759759
    0x150219110c0a0e041109070906030e100f2306012a020621070f020601050d030509030a05010603031412060909010f0c030b040c0c020d02011b080711090a0515040c020c04060b04 77
    0x84602c0074000391004007620745410034a07106500900d000e236a4011001015102c1d4043c0d00b09100030441c0158022200004110981e2141070820007040c449001600d407120003160540c0413000030b083c0d140b0441040e11400f02203102c3c5c0b005070a401500207082041403581d0740b040c8001d130301c5860241c40c0030044041c54240741003052001e58201d24009220b40c2c20000304078180320350203071b004c161070381107500a83d4184103207242c41c6000d481074040d004101e0b80600c0b480c4c2924040c05015041802140d02a0303d6105841d8801d82100000e4411700d440801d0b0013800c500400e200e810000c1300a6070040d2007030000a09002000418000e54000c0d0b005503000980301c01c071070191440c0074400d038684a411406c100c0200000d40e40030a09024100d000681885042c40300880000313002c0c00c0e04981154403c0c402595810113141014003403038002e00d40c074064604100001c0c6070321164415640036003440c46c103100c2e0300201e000c208005060076000742c204600030101c151010352614015180a030105001840d101e07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323762257 1250 323761007 323761013
    0x903040b0f040e06091315020d0e0d0905060408060103030c0609050a11130905120a0203070203030715140c030a05040204060f060909050f1b0702042304150219110c0a0e04 75
    0xf000f00070707007003034480c1c6440d2080c4041c1c08036000c0b5541055911503919000000b568280c0740003802982c207c00c486030f082940151019a000c601103004006540750f417140039440300c040c40054000c50040d6821640f00800500c0424040e00c0007071000f0f84203140100d4408101d50707500f400d1505000c02201e4105100880040d00d2420300b00e203180d40303001c0b80f004100304821919200d90b90080094550840b15001030409034151003402201c0145401070b080740d42c1c94030325161030251940085016102039107018082c0301103106040c103942c0034100c8128002d0550b150421898001c1c18050002c81c1d110b0354402000030802e01069400e0018041034982540252a01c442d038010703034000030040104e03e8452004c0001d4800c0e6851a00081a040c940d200e0301c0341e0140c401304d402441a00340784a100c1701d070189002d445048a03e24a403182e88100b03c600d850216100200302680681000130101d0b840c04607099007900d02c02c0c6c3c5000c2c210f1000504541038680340f000030880c40403164201c400c030a2901d10811040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323763507 1250 323762257 323762279
    0x90303041802090f031c0c080d020c0f01051e0106050a0e100203122505030a06090203130221100906020906220602070e06090717090c0f0108040b0402090903040b0f04 73
    0x352403041e000352003030320714424508859101b4000300c0014051411814801d20840300c0030744109a000b0b07441159520581c1141030307528080e00c07181214560924000485000d08651016400200100e004c404d690801005990613003202559104000d06003080002c103a44000412246800e00d4012710340d04c1a610303408820340c0c1d1005055004108a4605444807245039880b14041045a841c0c65a2640c98809050b4083c1403542c1c030211210307001009100000c440c0c6203c1665081c4201c43d04140200300c18100c40e0205c0c0111515101600028a440c1c0c1071000da42002c2243d601c9201d0052501552000041e810303042699803060b0580c070007600d50740c404100004907001d065a40020880540f0741401404c0301000204458007800080c80410656801840e00104040801802007440c0c540020802d80d00c0c4000f108461080707a0308035034031000d54010895180120740101c17500c002c582d665000c0c0117081c0703400303801003086100400c000204040076070058220038004c01406540d85180001880c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323764757 1250 323763507 323763529
    0xc03190918021801080601120203092803142b020a14030c0a18080a1b0623070f0c03030c060f0c0507060e010b0a03140706030605011409030304180209 66
    0x4070a4410043d28522690038125450442c9003441c0125450380c40c2001255031241c420b01d451160b41c000300502452401c0801d0007040d4a548101d041c610316640c0400349040d40780b09001a000c41c00c1086d9183c50240100e0007071510003410441e40941c054002c46000b41c0c14011035106d20110303404a0305080884d88101807000c80d41e04050000d0660610410701422403003510700500c1804000c905055500c007074041510018580101695400b21050401e20003040000e0200c1078099034802c0c0c0400e80600504d00410010a041c11158841c40c0f05e13280d405040d40452000e541500641c0c2a19002660358651f042c040c51003561142451800c4d071078420151000c14480f03075806410b00c4050544140c0c000140c6502c1340e04018046880890140400e00400000411917004150131001000b849851900798180c41914800c41d13010584e07907081102211154025180060002114110500c00050180c485440003d0507240340c5652040c0783c1490000104a02c5421500450310b0103c901c0c002100341 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323766007 1250 323764757 323764799
    0x11151206040902130902010e0915010806030d0f0507081e0c100204050d0f2d030801051203030606070c09061205060a05010b0415020f030714070b09010c080c031909 72
    0x400b624506078005100103070452960100300ba03603400e400c2c080da8495540c0610000f406841d043d03541c1410340544c20b0f11400950901d002c03d100a02103002c034100050311303040c0000c1a80e0350900e411080541100c40742d0000405862201e01440702071300c92110402411200700000c083d01d541c4d0710741100c070541448a402d410114880c4180010880c603250200c0049010b60f1000e01b40030450f0a41c68140442c10325400320b0948400901810f2010091960301244440d0003a00d444e03800b070307a855003000280d03c03603668107800030380007071011841500303090000c1c03c1d1092040048102450f11459801c0484e0740650100b00c8440e1959003001c280074040c40442e400420140c0244074641c103100c1c000005101358862048503940c031410070010359100380242c4900150002c2501d03520441d5041004034020409406240c500030002c001030b801c2c0b410021030b440084180c440f40401c0001c0d071100d20058102c100700300036a010810882d446001c801d00d50b40318540c015200c3e01d000ca4244000b02403100c0e1552115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323767257 1250 323766007 323766011
    0x3071202030a02210609030c0309010f02100510050a090b06040b091201050c030a0c1b02010f02151807061e0507030309050d02011a0105210c040e0a0c0e0121091115120604 75
    0x1070200e2300080b0480d14600803c0c00d11000300130216504a1074200301c401604240340c6002c040c89216000000088101c6031304540228415886ea0240421507894a00d041da001c00300300001c0050581140141002102c0201501c098200050780282566812203456041d44000800c1200080300ba1080c1500d002c0b4078540600e042100401c0080c298122041c080e06003c5c4c90381160744034a1080005c50300c14804020040543d00380710306607003014011750320016928040c0d076402003140d6206880108200c81c00d03184120380141c581c10203550a0f440f28105a0802d601d50054501140c8104001c02c0500b0403030780001001004201400e44072040c0848a40c10010304112005182080401c1d800100c03041d41d105001c0c9403203101542204d0f2040d9401403810003014401c0188c282c0541e44448003004003519200300c050340c070b1001100c814414400c001c3c980400402111081c4506510400704244500d001e0f0805008810005083e0507855a07000013070600052100740352410f40150b160007200c15641 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323768507 1250 323767257 323767267
    0x2060c09181807060c050c030f0307060209031c020a060c0e010e060f130303020304080c06030403050409150305030f1305090405151f06030515090603071202030a0221060903 76
    0x622000c0c0d0021240c403aa000c081d001c648505210800c09680c42e028404607001d07140d9505028021010280095078140103444042080c1d05010481d0546032542c2e4001c0c2d480c00c0c000d652000000d40007004500d070107100d01d000340350046000342c82d0500101c2d060340060030148101e01d0142c0a031004001e900d001c0000180500c049a41c0080c0ba14680240494000ba100c0004a1a045003402040c5204e40d0210001400000b415004001042512500d03000d98803034822490a100c1548002e80d40140010801c2008000340142680018a1452a031043c3c04450340c2d40c2d1511461900700700161aa102400075401c008201900d8402c0000c1006031800030203442d042d2192a00e40882046010700e906a4500041201d49800280801428201138582e040c0c4c7e10303404002c0051404541000000004580d52515441c0ca040d400303104040c0100101919814000d1603200209050300c1240c041c880d5001500040c1e44044c05064501c1d070b100c092250750303122042d6041c60140e0250401b10b0607001002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323769757 1250 323768507 323768509
    0x180603020109120302010b0d0f0c1a030414010b130b0f0d0b0610140307030507030501080f07051003140906100509160e1518030d050405010503010e06010c12080702060c09 75
    0x3108a046412502003d8210641c2d820268050315800614580c0410700c2c254407410440b10030781040b4680e0040c504403003100e855460540101502508184091100f031000500260710150700745403c420f01da0000c1883c90764000460021100c0042d860101519805020301c0360410802c4c21100f1541200d08c0c05048c5149c1d21901c8103074101030141f9000300fa04050000c0006c3c0144240046204040201c60f88c9281640300280100000da6003400041d0030b0078000074107200f002428078002031500c4044d04000b46014100061040300e41250300c141601d620701284410140305c03090b4801c0c80003001400302450542080b09000c2c64507008284690070000c24002d054608a03164805000b95080a600540c54080040d0301414004c80da05860b90000408001203010002140706114090b012608003041c0038400380c403103000d140281400600d003400108260081807103090381245060404448020032074681c015405c529003000c0b000b064440c000c0c40240c940c10001c0750b510aa02c410641d0070030400c1c0d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323771007 1250 323769757 323769767
    0x506041107030e040b060f0a11011d2508070902041503090804170a140307050c0901120b060f1207060210051501050912030a0e1f08160c02060307091806030201 70
    0x3d141d0138080d0780da568100e07105440d004200c0b4600c0e407a02103242c0d100c4400b60402400d092501070003e5141d402c0c002c1d4161845501061410608140d4000c4c020300140d824140041d01c0d502c42ca48000310b001d448000844035000d00101d0041c00c451040983d0b614140541400121000180340081601e0480d001e4007140d40201500c0a03145090810000c86503490341907894221003a4028000510103803040074ad030b0030000001d2410b548107900395189a00580308124290000f44103604000c2030401400c0c00181d0380d1015a070348544003c0a0b110744e44800c4011030180c2d4281141d5880703940c0403100a000303040d0100942650203512003014861440d182c00346544800b4403000150500c280801c48800c030365141e0350381c55141444030b0100d9807101c141440080040c1d0721100701900401d40b03100c9081c800700308106e485100c800b054551104c0e94035041000d00e041e200e106c2c000d0040001c1a003280d401030761101c0042d401407e0b00e54400c581c26082c00003951003042c604c94035400c01d500d000da003000181d801ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323772257 1250 323771007 323771027
    0x2120a080c0a090803280f0f0f0201090819020f0102180603040201050d0e1e0a1a0601020f03130906050d0c09050606070c080a0b090303040b130222050604110703 71
    0x1c010041d4840c84548000e64880105400032107480c003001ca040c0100511010494002c05400303c03c0350401d504042083e25061000b038800c90000b4032407108800f070203004510020f680d80140c4000540903080e40c4812086400018068045d40c495440e035007440780e41004007808540850000318540aa9044c01c0030443d5103858409019440c0440014103580c010700c1a5201c60607180400e2041c418440a05900c5010102004103003104401c050f04040340002165000703031780e1003952151401400041508511002810a4114461030440d042220400d101403e1211011516507601909000040055486541010303004100c04510703400411190b084504c11501007140005481c0c0782c0e02c000c12994850500003a00b80781c130400b0b00183c3e042001400030603141c010030b20340c1090b840d90004030742c4030b200c01c0c0c6000d0a06114031011502c80c203821440840d030fa610007030801007030b80c84940c01c0c0c60503c21004098410742e43d8440030000e1604043c09500c5c1c2c1d0b2050009a0b9180002682d0080d0903e284 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323773507 1250 323772257 323772271
    0x6051b070b0a1103090c0406091103060405040804050d0b1509071d01020304050a030b0406050c0c070939080c03090d080a0204091404030e1503040201030b03010b19050102120a08 78
    0x5048042090342c01190300143c0c6440c1d40380b00003a80c038600104002d540300702081c03030180628901a400181c02c0f05501c107007078190b407020011916644032001000050300000e0401c1d203c6090030440081c2c5a41c80040b00313900c0301c2c460b100c04001d61034400b190301d005102c0359044a01400c2d0700b03c10000c007680d000c1d00c181ca01c01c038009030a0780a01900f200403032450040307800070780e0002c0345840007206101292600c10700c0345101c0c50082c090307561004144080382c00b69020002c1264410b000078040361440e5000354080071a6080015100a581008000300703206071011722708400801e1603c1150903920161603580003c0e42d2900318034604200a0080d900d214154041c810040e501001c6900c261640d01250000c0025440c10322507102c4108a440b550081510100d01140002c2001300141c01c2580101a140e010300300c1142c11a9502e030010747c081d1100c060800d03071556849801d02042da441c40142220000511b1051034150709040019140074003000003062900000d0140071083d691081e03070341e130740946 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323774757 1250 323773507 323773523
    0xc0809040c020a0c081e0a03020705010507050a0606030b0402030105060f0915011103040e06030607030c09050112020712032c190503070b01140109140a030221030408010906051b07 79
    0x7a1003002241401c3c0480340081000900e081c0002c1e00c084001141104102c010142030070303442c9038070700342d1351303942c1840100401681228a0402c8158000c1025002050085d4142e500704602c680e28001120103030740085400c3d00e000410700055090911480b81e001c03900752201500c030f54034000003401c0000700614040107078401020342890343c0d20511508840310b40c00400c83c1c1e1074030745440264000380b108440b0f0038001e20a008c00190035070b01c207014000100110340c945980d4141480d004440b80340c0c0100c10b040d46241c0800c500302c0000c01160001001c0007a40d5000601403560aa400b4991090300040fa012a02280c01400c092140441c22481c00082003030003089800c1c0c00d151940c20b60040d0400544904060800010039010704840c40702443d100340d80311510745880d80902914000503035903194000010001c18001400d04029a0408010003c4802542c241c5c00201619540c0503410818059454071907680c100281c600404c4c0e00301c2000c0c4050741310505000c80707c2503e400b0300c041c0540014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323776007 1250 323774757 323774771
    0x60904080307090e04050d1106010609290d0608010b0105070203060a0f18120801050423040c050a08070f141f03020d050c0a141314040609020a17070c080904 69
    0x241c0030304003000040410003443d813013a2030710b41001e0303031034800c400c400303401044001d00741c80d0041c0707004519941643c0f031580700c16117041d003416982003a41131040c13444039051070349003480382c081500b003000380c0f41c0c040fa0700002260483c10200564252000100d406040c003005201c60001a5000301d2103680c414440f60002030031003013013400d0740040c011845000040d054550f140c0c1060216500400c6003105d4940c4800c07949981c4c40c6c041c0310071115840c008405030f0303040d1b20f005501c590601d006c90717400c5800f07200d03080390050b219400560000d07640d5004001c26481b4038020055458209048401031011000c110041100300303011880c083c011034029400c551900001000c03003030103030741661290300000004024a25159101708141c0e070144c2d0540c4041060003015502d0101104103e856000d009880b6680c201e250030320074407030750382242400b61f800340d10340740080f540082c1403002d40350030b00003a5911410414140702000a01201a00103820030401221903004a21250101d03040220b05440008000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323777257 1250 323776007 323776021
    0x102030a1110050430090e04020a0503030d0f0f090c05060a1412011409010302100509281703030106140705010902180915090a06050403170723030609040803 69
    0xc888501c840b002854602002d0200340200038110f40ca034100d0b4030f1203102140c80315403494105259281c0304071340043d071054400d211503640400041d401600c00340c1340101003a200d100003401c5420811689000c541e88407404000d9141c1c44c005e450300c405080b10704101002c61607c5502d640c2a0034020140038403000600070442921803203200c09686090000162110381d241020070014400b8030400c103c00803a1102d9151178940000c52504aa900809580c2004105002a509078110070400e07030740308242050b0b60581b060000c4180880311902c0c0341141c900340c1001e00c58001c9010340844c0c19245d80c01400180002c98101c40c40d030880d01c8001c14015141d420610b40303e805040c1f8030350000c1d00907611850310410300b82d82c00d483c0380c000c1c03007004152030000c48007244011580070100c9085800d680048120004941a9030107181c000d800b0317241444d04c0c225012820700ba241410f0b21034000080c450707200005040440c003030403c10300040c030040c14550700745000000c48914000d84051f165020001c00308401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323778507 1250 323777257 323777263
    0x7030e0a05100207031202120609090a0f0606031202030c0d120f02071b080c0a03060f02070516050108010e010503060a0f0204080d080915041205090f061911010501050102030a11 78
    0x31a0358400100d40000c0411600d40000c1d421404045020a20260b40c40381e08843d60300958010003000ca00500b0b4954a007000c000300c0304809072180c18180100d90b0306d000030a501d41c95050a117030060501203201031661402e81c0950f0050781280045400a000c1805866000b140343c0035010300f03070b20304003405884071510341000304609445001068400030300b41080154926a00500e09044202802c9250b40d030801c1c1c13500d900003c1300c21640601032480a00008410380c4c000c01480c481100018200f4149503a524901411582207544a84500074104050341e80245a01e015041c18441c1a14035450100400d54810010707112081c0a0340711041c2d05c21b80e01c203641c140c030000e000d15000c54110b01540710024009900c142d0f001aa6401212034016078545803601c00c84c0503940c030840d26007446807980c030100c80c0d0b50092000d059221200000345040341d551741e03010f4403a815110344050031642c940c980242c8200d511400580e0300b641003034010042c5c0e82c0c01000361050800740b42011000c1d50403158141c0d007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323779757 1250 323778507 323778523
    0x5070f050c100f140408070519050303070c0e0903130b1b031c0605060a020d1d0303040e0a0f0e120a11120c060708040c05060a03020702031c1d0907030e 67
    0x6044090002801e1940f80d2051041c1090744543e12810442803421030402c00384e1041d4040e40400e54486035041106007400c02c0c4d243c03894031040c00b01e198090b8a401c0028256403142c07500740d0780c11680700d0052103409440352405400c03420303200c02075140003091131642940401600c515000d01d280460745443e201400c411043d0102c0940781036941d91306509900c0c0011030f0000b03503055007040ca03007200401e41e41041c204640552505400a060080303402c0d108480500340404201d00300081c041e850500c43d2020806030001d08400141185d09180541d0f0000403220824400d030b61140c100003000140150126410406080c00f9070031540e0b42c0507505042c1c1ea46500910640982c0c480d4a04000030240d5040107880d940003071109031003298031020012900501d0070303100a000008c0003b0704010314605540281011030b0780f403d000d0308060b40e90700000e00380b160505c08520f802082102c025402540f24142207040c800e01c01c45a6140c10180d0007203280824020000014140d560410010301001040080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323781007 1250 323779757 323779759
    0x50711010509190602010510320a32040507080a0c05130f0303020f061009020a1106070804051006080303041101020705032b090302061615060e0412020c0105070f050c 73
    0x14007607584e241c4009000b41002c9480040e850800100410202441001c84005881c0401c00c031242c00c29012070343c1d500e0440030079001d500803031400700003c4411010349103503a0700d02d980802c00300c958034280407009034009042426200d6490201001305c510340201410780c20032034007130001806601100040e5006d210716032500713294014407040000c220300e143d2440c8090302d2007030b42912840c507050000030703a4501081c0c9150140240400050104800035400b40c609088503240c40e07040125045c07461400c01c00169504000100510204400d020041140c121003000240040003600c0c54568442d4580c00054801400c19024242c0c01000768400c001d4600034250041c04e031040daa0901000040e4600c5500107544008502d640b00403007640a8031401c2d007243c4d000760019192841c030844001d000c100d2000c08940203601000301c02c4052a46200c0d03030700640101590401d1074141070030320f50307681e01010003460110f5001c40705900340d82c0d0b032000550b0020765000d113000004444a240075402d184400c400e017 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323782257 1250 323781007 323781049
    0x21204030f03031a03010f0e0c03060714030603010f020408030c0d020f0a170c012d06030206040b07051501060c110a12150f11070b06010c170c0a0804170607050711010509 75
    0x326520610790700c242c08c9003206008540d401c1d120070080c1a11a0411100000855858203a458200c4000700007550f2002000b000014921500c0c8190700880c1c01c030343c00c10300c020707030000c00c40c2d100040d010040000d9178003840c00205000c05290004581e00e4590440080c01802c2c1103504400c150002826130b4036078480700c2d00030b00854144000c45250300001844a40819000f030101e001250500e2292405480e00944190302c0d050505801e410b1031343c03003400221810320408001a4152100b924440e010340030320386c0c0d21041c030007050030141d070301d0408410624071078504101c040000c40b000302c0d80038000c2c80d070201d10320402003400801c039001400003080107071045007807640007200103130f61800610000f8800c400c1c130951910340c0401103542503000302e402001607162003120340160456801a01a910720001202c03065021a41c505d815034010b80d004403100c2d0454841d0105402040c4501a0311480504c3c14034201516030710360030a00020340e070100381440000240700c0f43c5030321340003443c042c00303102040c074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323783507 1250 323782257 323782271
    0x90207020a05041103240904030f0c0b07090501110304120204092d061b080a02030a06050324220201050307050d050411030d021204090b0a0f0e07021204030f03031a0301 74
    0x1070382065038001c0301d04480720000d40c046d4035159075420030904074404002d8280404c0c1c1d611035400f0b8070710070104001c14060099600c0320f100000d040c000d04a11958a036540e0321130b52850540050b0024041028100b00b41d00240000d0151405c0c0d0012490300f07980442e17000c503880050b4184643c40c11140c0794800c6141d640f40d000010000685112081480c1c0300d038400700f100069070460b80340c0d0340c0c0000c1007110000e250b000124480b100c15402441d04109205c2001035800c3d5a0000a440e2101031902038054090201424240b01e8045442a81c80300014400014000000c0d01030011040b548000a05000ac08008915074070312940980300c10080f0f555040010b800e00e0b081c4281c140004d203c00c20712912524072040d03051440840c40c5146001035414040c2007500f4480510003030900c00201d5500301110034000a21410fa20380b0200050260300d00101c0c003401c0564000b400c1c014090072172000f61074104020800600007074200385d921a014a00050508070768043d4500c034900c144010340d419824504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323784757 1250 323783507 323783531
    0x911060904112b050402030a032a1a07090602120711040c0509030f0c0d02040b0f040c080405070e1b03090709060f09060f0509040f08090d0605010e0901060f090207020a0504 76
    0x80d0f1500b16400c00d0902159a030000710f000540f102154000c1d09034000080d41130000b070140031208031312108141040d80d0a0040081c1c03ca207043e80a00a607400000340076021100300301d881c01250000d03d80d240150001c1d09044c806552441201d592400b041c45c0000d0040034880c1c91082e0b43c1310008020302c1400034590b200f1000317202e600a10300c201d01c80e01a122851440c502c00050300300100d1000351509002110380e40800c8014542e0042032908071300701071004000c40e0b031180314040c0d0244803a00d44035401e040506040e4913200c0d03070b900800d0880684809008588042d807000780780c002808030b030306a50b960f0b40d020f0450401a940c0c0c4035280c03450900c140880e003d06140c90440c01d50310144070800003a545d4186038003603024a4840d2982010f0640e02080114903003106005505000c1c0000301c0c602103420000c5081030a004405950303031580c600041c08241c40c00c110064100e000b0b038009110b59400d08540034584100703485404140c3d07900151510854a40134061002040c00030070070418454141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323786007 1250 323784757 323784787
    0x70b040c050d030e0405090601050a1203020c060304080418020906070605040f050a050102180301090816020a18020301030b070f08070e0a0902030a02030106020c031b09070306090203040302070e0a091106090411 92
    0x1300c901032082c0d09220010388840000107000d03049030801003c40402c41c0c41c0980c84600d10b102c1d4402901140614511000d9680310b43d0011070145205100b50b664951400c12074201720816400030b01c0c00c0c039004101c9481d0a80e21038080c2c030721503504100001403c0d01c861401c0c0348481e4401100800d1401901c00640070b018040d80608200c85600c0c4450740d0040409003010700326000c18038000c010141c01d001840208009401d0108003500c06880443e480d5110300144032401350310b25070118815000401440cc0020446038a81c02c415a8200385070040d80c0c81101800c005001803144041044050302e202a59840e0100c0500519241900315a01d00f00035000e440650b00034040c0002602c20107102c80407034180080d010310301d000303031414650301100300004100201c4000741c56602010740f147c80104240f0800d01c01580a14403d80090051b02c4c6011f81c00ca01139030300185642d02680c42c28001c507010903404508040c03d49000c0302c0b075655440d007020011380146910001450307009404110800030020391 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323787257 1250 323786007 323786027
    0x60c1b0604121b020607060c02120d1a101d21070302030111340c09021c0e030d02030c131e0b13050d0c03020301051005010806060708070b040c050d03 66
    0x581d5010b000b031010381502c18094020f240b0003034002c00c04010007808200298850712030f00e0124810344d0381000004910040030780100070440b51715a6201c001a4209540c21100d807090794040e100c420501e1300c0408040c040000c940307900585031018240000e61550303041c0c40c58464160204100c4100c204400600e640d500003800304034001e601e0010344030f80003034484040e60100203000103140400311000c00541c106103001c00183d00400c01510f4907600240300c48513294040d241c0c241c00143c6414a0403441000071501e01070f52100d0500e0403a4130000c6c100048201c81400094000c05a41c80d21406400c1310b0780d103e82d01c0c0f99100600301400c00b044920101c0c0701008004180d40c1b00d44242600ca10f4001c2c514442c05114003c10501c83e2000c00003420030780700681c1150b00429001140710f40d250086425220100c0d0013102c00742e0446801d20003983c01c082c5440e04030744290b94103400c00e400c9031b032101c1a0b0b04c140c60000d01000c0c2e900000804005040c43c034900500009090842441064039006c0e01c524a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323788507 1250 323787257 323787293
    0x9010b0d1509020403140a050604150e0601030b09010f0501230a03020d060608150f0f04260901030c05091309080c0d0816052802070e011212090305060c1b0604 70
    0x6c80c1080480082d0700095881005d5004800303008a42c6032642c4003110404064007900090b520b03514000706a06d4148a018025400340300759103014540540d03002d08541d03442540e14100c07403514005000c5c07140501d20300c040c4a005881002600c2c421034001441c00104c941c4001e40c4620078103806d101700a1140c00100847d07004034211081c0103d840c41c070103103201040b00c0500d00f41410400103030500070450f0380e0382e40241c020700c2104803030050b12080f05130f10f100d9090782002a200001c0c0400c640d5900d4402c40140540500c0c1581c01c0c2030400d40003c290f541c856200e81c460b183c4a024040900c02410b0498a60f141220215081c100035000d015101420442c1c0c248180c120141500c065140910121040d80f0303d054102e9074400c06c0310782c01c081c03121034602800d0118070808034045204018890464040c0080390b403c0c0389100349501d007a041d02030710300d031500c010004461800c00010b140000ca058016000b012050f8031400c0c000400030040d071010a58404501c5146d0910051009540100e105184 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323789757 1250 323788507 323788523
    0x1101030606140702040504031413030302061509010311030c03030d050106020c090103020d062d05040b070c0503030705090118060c200a1a090d140d020c09010b0d1509020403 76
    0x5524242603800b108503030308041c0c03403007400c110640062400307038011580070b440b9040c880b1301303511030a040c0070030794110b440102040312013070a041c8249601005074a50003e070034400d2914890191b004242a000c2c184401821361003a100c0902c4165000c0c0300000700950058205e80e00c41d48066102000781c20700703204400c05805860300c07000c558100390800c00c0c10b07250084d242150001c403030340d1010700815500300c0d40850320841411584407d10041c5a1807051040c0d0680840c0c7d41c20b2a0508103094400540f0b0031080c0300074445c0c103800182000c81541e50050450034010b447e040d100c0010f03205c8409001000c4400e480d03400c2c0115105400c4210500024010084803440c00c0103c0c2094801010301149580e00c60304094040081550000942482c00c6507040ea040c02c210b1050f001c03850541114408460810200107844806442003154800c00955031006000300b090032000b0800070f43c0180280308014100003014010f100503600030402c12582c2981c440002d580d501d0885009400602084513500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323791007 1250 323789757 323789759
    0x306032a0303071b12031b02010309150204061101020315101101110c0d090e15060c01051305060901060f1503090b1f0e01050a06030e12030411040501150c020907021911010306 77
    0x1c5d205111003005540d00d0b80f102e008196043d20000114070032640101e04042e192004d26000544204c090358081c14456405a112403d0085c0030f4003103291100e001d03040da88180200617404034141c406100000e81640c0c58511801d90034401c94010801308a41e000d07640c00c00703921080d8402d04800400442c1e0400056842e08140d030300c0d0441e2410350500c220940c6942c1007010480c082e060340400306130f02c01d000b0b040b17514025510620342c1c05c2d95400c0300d60f400d00348017010280052000c1444805da0041e00e14000300280c5080c07d80710512141d2502030204000c0a8901260747c160003a0710081d041030700724101038402d11300010405100f0a0302d6070003000140001030000784460118503100c1c140d5000a01d9010707541c0c103000c8120001c0811f1101980c00744201d10700740b04024030041c0114004d0780640c0404100245040511082e074506a0003401c10250f20302c0f24104481c0e03c0041c0c11081e550484600b0041d0310f5095049140598003241e001200f0f03010401e000c104200d080c0000400e502c01e8030184011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323792257 1250 323791007 323791019
    0xd0912141c02030a0f090c08190f0f020105222d0b0c03040b040807061d01020d0c03020c0a060c02040501090b03070909020d0803010603020304050c03030306032a0303071b 75
    0x9402140703141c060744071810703180303000481e4540c024551069070030710001003220040203c14241c0f04000c6003504d0081900d2010700164800340301004070030f10903c500c403190728129a40d521202c400300b0303030103082e08143c40422401c5a100340101c606820382c195440305640c103a03012002080c0414403030000e102c0c0c011034500000340007291100c0e05810741010303c80f8113039250007110300d0968132071003c24071140010800401c2414040000d400544039075030003840103d0500001502c941e0fa00c00c1d402243ca803004000683c0d0342c0e030005540d41d06220340c3c58821952401c9150592a04036203540c0c1c00c1c4e20000140d008144647d10031101110680207e605015a1741c0c1d0340c3c0301c101115880a0000e8140d0031041e0103001002d00c0d600310010080c03015100b216828200d07210f1092a030007c1c2c0040000a4000041c042442801c01c0000403c0c030048000c1c61440c00d040d00040d5880b4041140100d6990101281d09140750001000b901001d0024065076652101890982e007400042900c81400301a40c410100d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323793507 1250 323792257 323792297
    0x51807020d0806060412260d0507020c0f01051c020a27030302120a02030d060f051e0f1903061b11010507021522140c010212030606070203030d0912 65
    0x3008060b0400f443c3c031b41005214010050303e064141c80c60319403a501d45108940700d00c1c0400f0340b42c0c5a80402c5445100041c012001c2d201d0280000085500c800f200c00900d503229070489030040f2007401d150341d9844100d0204691828109550320300e05102080c0340000079007028085a0780c603d135034081e210344841c80b10080c8030f010040c0000790040c4e10122003030781d0100840000300703c5103801d80100d82c10811221050001d81d0780641003525100c14a51007084281062207075041c610140c45120b003848107520021850148400b0760383c034072506000c00000200201102e4020140d03030070040034041c00e441d1341c1101c0031345d8249007080c0c4000f0701070070700d000e8401c20184500c03406101d081d8042c188172010341201c40070600c4045e10450114914a0a144400d203002501100c140c1c07180940c0f07042ca051a070409400e24200b04015410354211f88400741c000000c810460b0307400601120119150342c0703a800802d103540100d01811000c00d1420300d03032105011450940d20300f0f0024556800d0403042c0e00c40d040541e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323794757 1250 323793507 323793511
    0x5091311040506160b0420030a120e121b150a0c0809010306080105070f110d05041214061008010605180609062b060501140d0f0c051807020d08 63
    0x80d451034103000c18065450501c0040008052091880c0c4007208240ca90b00d0880f2000d8508540c2d2251b09030250104e10100045c0d2850201e00300c0c040c045c0c0302d500c3d440b40d0744030280e445240b000700324004600000583d521400c0254510320300046482c00b1103401003031300280003a081990f214070700b81310607000007130000401c0382c08055072a03881d5103400440e0781e030f0510103070804c0d401c450600d0340350040401d000c01e003446103610450702c50381d0790065203a01c041b0203000d0b0714121403080b0180d0008980d46014035000021582218881c0112150302c40720f90812074403100071303a00100000d0280300c0038806d035261540410005d0b41d5810000704203407542da104118654140c1c2c840d811882d44404005103107842d111111076800b0348050015030404200c00d0000e01e0a013401c000340c10345c500711200c404080c000140f1078540503101c0018858200b400300c200007000031801201c001c240c03a6882490508008520704018000c1802070b01046c20540085101c200c480c404403a5000144103c20403800a1441401c01318 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323796007 1250 323794757 323794781
    0x10e1b0a030506060415081803130b03060301060b12090c01170109020304020406030606180b090c0f0705030c06040c09050f040c050f041e020304030f02060405030315040b10050913 79
    0x6403416442400c1a0050b05005103400e501440620002036004500140c00e0b0b000901903554400e02c0c46c0c0358100e8903c0f500b0901149400c0d40c030078481164940c4540e83c000c001e54414040440c0c60f941c03107a00003405440c1c960000c5911070313000306a0041c00740409000c03502032001001a510010a080011580985d00b58150b040c0c801002004000580080c0e0003160046d0001e0000301d50251640c89540c181c030382c80e501c07010301c80800340e01c1c01840362042d00c1080003c00c02101c00306110f09003086045076a000d034114401420313100240a20420108104a50200180c401560480e20301404e09040c4a000c512901b009070341000c00150303648030b0308141c861041d03a2046804e400c1034148414001460b01541000da0820350302c1007004488066010b1800003d4050040582e0340e10b400e240061002080c44007045c1994802010f110000d8400700950364001c5003500201d030803040200004000c0c0c07001114040e007080e0441d010020b196400f600800418100340e410b20010040c0400301d0086901d0450300c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323797257 1250 323796007 323796061
    0x308070809150c13030302061504050f06014401090c020d11010e07030f02041118240c0d081006050415020717070f06050a08060d0326010e 61
    0x60000c6241c03660815080018040f03440d043c08490090903415807010303001039015a1117401002500101c10f10301c035022103c251014801070500c501e680d0800c5038050020f50500901c04944e04082c151a01c5c1c8146010030701800740310400486049459191903c0309074000b880355000040740b040b10070300480400340c00f140e000b00105442172508503846110320101060a540702c074402c10b2140020044803014501a0180113030b20b01451040004a62407602e030b03001504018400d140030350098402e007080104058842c42d10f04000c1d00d01d00707283d07801001807040ca001800b0840680c01000050380944241d0503882d11006c03910b0f103216000701150b07503106040c00a8000c210074000c41e60000000c1c80820f2030b40c0110f80649072245a804801d1000c222281540e038025070007000540001d0f00c00e0801002e00d4103081d171400464103001094084010306c40307030141d40c4409625041500c18024018034000e6403490455000aa44400c540c03000288500030700400c204c004034040c01200300580f5540c140d9840d070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323798507 1250 323797257 323797273
    0xc010f021504081e0912010527010603060204060c020a270e010b06190e06030103080301050f1212042903011502010b0d06140708091905010905010e0a0308070809 71
    0x48080500010b00072514110144041310341c1911202940030007981840c1500c0e210345021003403000b6112460410080d50381060309007d8000310405450061400409000b1425940b884041d07001d48075942c002040709100040000e240c41d03000003c80c0c0003501c00c4074120006592203400c40740318103400c50200e40d0f5260300c19000f0300381c0c64035503c10300c000400c540003c40d00300c0d50600000e03219000b410009501c0e0040f698080d400c0c56104d04c80b044130b01011600d1a0455046444100e01c0c0d000500802c0e000711460100d00741c0580d1051a0300340c074111420708581c1180d1000043c852a50054466200c9403e09400145c0a9690b007100c1c0762900810020032a0550303107004400c0094001c1aa26602595a05d0407030182a072a510002050240200d2003c030f01c180740b103070481d00c83c0c6400408007000c0164020500175a401c0102c1c45010301c0c11003080400710400c0701e05009004084846004065601c1d1503600161048085a01d05006020752100d500550b100352080d10a000c01725410400c1d5045101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323799757 1250 323798507 323798533
    0x30e040f0603050615030a02041103061504120212100f061e05280803030915011e090b01120e150c070b0109050c09030109060b100906020c2403040b0403020c010f02 72
    0x140709071150401400c0b2002078007c2d070007240890700c0c04a511941040008100722050a100044103c4840d0701c280d00d51401e031600418a1041100c41d000a02c924215040101246001c100e004840c11445a04112103030f2107045003001000303580303c0e40300001d422481c020060050690501d048034400f415890420040a9040700000c100750030404240f444860007041a107420000f42d440340e5420b100174025180d008146041c8040143d04c840c000402400c0301440c0d40f1080d4082d001260083e000100c1e42e0440400141d82541c000d21600301624030389030b0030340700f851400105a280f003000805400c00645449650300c0b0303213100f940000b03491b03510081d00410403503a060f4806075011036003120503424070480c44002425900688020b441c0c1c3c42d00d036001c200c0706290076950740032001001c1c100340501c240b90903006501c40140c4000c4520030740c0c10816010183c141803901d90009010080307803aa69207841e00c0c00014040d42503030203034010b2166a800c20034a501942c0c001c1c8103900c4540040c80341c008040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323801007 1250 323799757 323799781
    0x30c0908030304020d021f0c1a07020d0f030e2406030604030c0b040303020403080f03100b03070c110a05060c070815011d060409080d0b1c030e010f1803030e040f06030506 75
    0x584200c0e04100c44001c03001d00004a405061fa00c00070350b81e1a03061400c0b090505040ca10181140c810202c01d101c003d002815400180000340c10340c0c1d80c104000d6000241001390010003044014082c9801041d07082202d1070130103484010303281302c11003480c981c3d074440d0010300d0303668002103400401199051100d50f010885850b1004da00510038a03016107081d0310795a6440c8580c0105070070442020300071084c88011070b4120007000183c1541210241103181915008040040c44517001d44000024010201c041c0c840c500c0b064098a000b0340020703600c00c03610707102c0741d559845403003000000d000b01424003404951105049040b100300c02644c4200403448402c10803c0b1001400e8103070700035075484610b0002814840034021926080d040066100f200c40244609100041c5e010b014049100d900500029041000210999420b1814481d03020781d00d83c003940c460303c00407848105008841000020140e0050308001c01580c251014031444900e1006501034480c10f0000a00b80e80051001a210400341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323802257 1250 323801007 323801029
    0x90f06010b09091f0f091407300e070305030c0d02010c121107020409080306010e010201020322050f030c0102031803070b010302011d130204090b0a03211e08040201030c090803030402 80
    0x2150b206130801d55610901300c1c5080940c0e0096501319228800c840d091100c122801e0340c009400d0515404480c524000c0d9001d84094010042c40c9569a0707210080080499214200c0941110202c600d01c685070b00b003103a5650440da810303031142c3c40ba85000046091042c015048020b00e16103a01da02e82484880038001350001400d0786462850603c10003002d40d44501034550050b004006c034643e43d00b44500010400c607072172007031503041da801001800040307030607507440c0b1403000e04e01c0480c90503038502850910f0401c00c0f00004081b540c4000705280034010300650003580142d000a5540071212441018142c4a008a0b107018260205000041015500580e103408007400348403a40d1140c2007202000900d8652038030100210168040790510504045114400c03400b0b104035540f2075154074683e41d003c00700c958a5100c0d10340c0183c0147d421880d90041c00d000c49160b030b02044001007000e0580c00107003000d004440aa000a00700000c800c80b45014801c0901038030704c824007451a50b034581d021703c2480301c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323803507 1250 323802257 323802301
    0x7081e0a0b070f0e060a0906080907181109090f010815070c03030b060d09150605040b090a020a14040303180911090904050a08030424020a0f0c1a090f06010b0909 71
    0xa00382c0130140c0d65680d00030003058107652646c41d4580d040810003864203a00401c0390b1300c9940041e50a12032441a42c0244000001e451004204201402905c40240c003c2040c8150000c6208040c050151682c094080c181c070075420031180d04940e8500100300d030403015142c003000b1860300c500b0070700402c0c40794015803010703000a070043d4a041078100140c412200504c0054528040800007140c4500040c01000020706003102c09105004560001560149024017801c00c0540e0008001003028082c44458240d01610820640c0300c596130308010b00072a03100c91084042c1500d0010101c0d030120795214004c240014907403030718100700341c8209010003410040c0c4140c409116403054800068401d2000f9840313548200c5201001c2000da1030000b00c4001e004945440d402d0050040310200c6034014402c60b0310604038a045144208142009100b25000380e00c50288034111408200b580f04000030702034081c0f5602f00c1121410381e42d41130341802d940079050215911001c0ca50201c0c0c40b103c6600e17010300c44601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323804757 1250 323803507 323803517
    0x626070816080105100510050c0a020a0312021c0f0f0e0a0303210e100f090218060f190303050c240402010306050306070207210507081e0a0b070f 64
    0x24540003164540400c50300c81c5801c1e021415801d204910b02070184076005410000e020a12508041c005884900300d017126104115002c40c03040c411000411912640c6900a00b85241d1680c59090001c00400c0e69084000903109030042900b02c0350380503050000c468010380d14640c80704076450b0110b030311500c0000b5000401c004036106208640d41c01c02d06000031803182e11450002d070a8a41038000d000c00760326012180030b180c4a58840580004200003000b0400120001288a081c0301d090006059501000c4d40003544a003036000b000c007035100304902403c07080300c541000710042010400e03120940d101541034403d070402c041000074040d002030081c80700320b182611041c1c18070380130341c0d0021181800f4152406003a1000d1005658152007200080c14080e000380a40d460003c4029648049600c6840000d4591003520a5165200c0780c000f0b205039401400c1d185503543c1c0d10385150f900c0c1002d90100c0b0403c400031114014000d0000b401800440e80414440c02595031b0041c1521125629003428061003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323806007 1250 323804757 323804759
    0x60e0d140c041b0f080702030414010c080703170112081213050a0507031104091a0a020903010c1701050307120b04030c140319050a0c140f03040605040810062607 71
    0x607645001d0740800c148800c0d0f060581e0b1908240003800001000210401d0141035402d01904550100856003640c0c2c074041201e110124010040300c41c07402c411005803d11201088613010503900c5002c406145808482081059803900c10900301443d0301c40008100160410006400310818410b80d03901c010a542c000f8840507168860a05007410040221500d82040006004011560b20032100410f026035081241d0001030b07036850204c401c4c0d00907074200090210002031402100740c04030307116000040c1c000d0000000d2054060190b00b81d0144462200454000200341820002203d20864070b8002d80400740721034685a01404045c041c0050b000c00c103030a001c02c4045840e4920f01c209001c5064000d55031959201e2046131641010402c2e107041000820000c020180d1014900714503a40001c59030100350307030380c0c10706510b0302d02844804441400042070004525070428003400441340b650003a21841071288103040c04407069070180c00c429913460101d501c0f84416160859101c244480100e41c499 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323807257 1250 323806007 323806009
    0x1f061b060203010e01080708010c0903141e100e01020c0d051b01090b010305010510080705191701090201120204030503120a1404050d170f040204110f1303020a060e0d140c 75
    0x1aa100b600b0a9131500920b40041102800411211000b400454001c000b0080031100040c800c000500c00500000c00c944240144504240325400d900340c0f0b0403440a201c0c0700b18285040e1200c0d65036511211441c81c1c0348088108007818008c0300ca10300f031100040c0001004191003551207400000c026000c1241d913294251442034240705410009000d0b0546956a40c0b4616000d13081d40e8009240e10340c000d10088040022410000e42c0d441a5041110140e49080342034142800e00130082d88401468000d40c120103143c80c1040d403000c2002030003aa1451086440a408401a841207100c000c1081d80204980010042810002500400b030640c4c04503484c0b00100160031007520546094889400c0758110302c0d102ca4100c54281e400092201581c480743c60010148085c0c2d40b40244007900480c2c64a901c03841d41c0443d04c080b1038204818588858a85101280200340081c3e00c1c00201d0050221a40104145010302071034401b07031800400080c002c501d544c1c3c1c0d000701c1c204004100d009600c5503e07902001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323808507 1250 323807257 323807261
    0x3010803071407081213061701150302090d0c06170f0105040915051005040609060e01140d1b0602120c031b01110703050903010c1e0c020f0d0311061f061b06 69
    0x150703085d8142c1a10b4460650820307102000c0c950001701840b40c90402d801551010322135190449407031003594043c1d82204181a4040d05c103418109070720031506268041003003200680070095904c0c543d51801c80c01841c80e001207000e00c041d1140450790b0750580040205280c02c0e040080160f00c00c008503a580e1400616410a40310195a00c600d80e1030558014031180c1090306c10000141070b04001400001e150000348207035020306024100d8401d0411021408944031070082064140d4410410240082e25040030484410f47c0c0c003440005003da0322100c00402d45100643d1480766210000c1d500e0200e14103031a8011404000100001d5501c4a02541c2ca42081e50094000c3c0d030f000c2c0d10380507585c490000030503084880d10080c240c10300446c18505011444601c0b440c0716100d0982c100f00d0841c0f211030001854415080485961000340151224205a031040c036200525111604035a241d0721a94907118000000c012294107500b5501002c110741842030503005001a150503449202400d59210101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323809757 1250 323808507 323808523
    0x1120903020c0915010f14040503030304080d0f0510060c06090501180203010b0a03030c020603190507031a152a0303100f090501060e06090303090d0b07140301080307140708 76
    0x26821404503039810b402c0001209134810309181180b0103420030280040d201d1101c80350716908000e00f8249101d0600780c4802107801500008040300c1c0c03079142c1341c640bd138400d03800509007850b01c50038144a074040d14200d0040318000c00750b0300016404903060500459600582003001d444030380c5c550b8440b4021510a1141810b04180a02424951030440c0141401d50310040c0825000c3c166400341040400d0b40000c039094500c0d8100c6070107650746ca448004110074100e14501e070501c00e10b0036003400310060b0140c0c0304008250340000d144855464240800140340001c41481e088218108481595481c1444000c1d8409950a01d81b000034040001c0c0140f55410488501c940082e00903010300461680580b50b0006003c010014070030341d0f044c2403000b0004c1480c1c11440340180000700d11108a9076061003a964590009081100559107030f040501098100740d0b14880407614114051561411301c1d400c69061701c05900080d86403090940e10343c014419031384005240c80c012200041040041800042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323811007 1250 323809757 323809763
    0x30d020a121515021b04090f0c06031e0209090f191b030e03130501030b0105040801090605060906010309030813020a05090a0c0f050c0a030e0a0f0801090c06030920011209 75
    0x4582c0c0d820441125119005844940300b51342c0042480c035980d06600c4100c100c400b20075070340412a0800da191000f1800d00250005010000004004c20020742c5503000c242c0c0e10242007002a42c04600c004400100d01c940308110360004495000108030703813203d072501504040e012480e203220400410300d95080340d081e050b110052060072504290402c2c5c0c075000c1c4440030904080a549400380300c1e0140131346051a80b1aa46c103154030385038846e40c42c6e8044d400360780c020700075103000344103443c1e072468608003d00007102c04c1c80c4102c01620118455511a100f8242c086926440d1070000d500e80741c800038000000104104d07403014200d400482c5540b6003003d01809541d400002241e500903c07180070307018400343c62403031040010502c02c82601c0170000464504240d094100824510020008251640c0f082d420840021303500317410004141c181540002c158502950001c000c0380d0321a00102d041d14800c400c0175041190f40c1074030301c000c14030340c1440c050380560505110301520025941002981c0c15007200b5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323812257 1250 323811007 323811041
    0x806190803070c18022701090306020c011b0801060c14030d09210201140103021002100e150a0204050d15090f1a070e032509090c2105030d020a12 64
    0x3000107480200e107a40d501c1d21321100940c2030035200e00b1311512800240c4c0541c0c00f2407a141c0c00100159002d165045c001c4c40d001320040d50307281900d20301203010708000900a40003020803a6800162072040d0030703032030690b101e650310141e0020032501d0b04091006050341c40c0102d030108105d900c207135240c18400d01680d281f180d158400300c00d0811035282056403038a04c40900b5641010080a1080054076180d41500e0b812500b90100b2101130600301d03d044825400c2400403890310350003412082c00060f0342201031038425001c1031039903075420041e400d90050380b0034181c00101210400001030040c10ba40000840c891000241c0760a26899101c400e440c004401d031203449010200380054181c041c0080da10440e80e0600c0311000c0080e4000c2a92903e181c600341c01d0301c44040d1620b0b480030702c54030105001007810540034400200e40c0d040510001050b4401c404880903034451000c42d11084080401240d600140651300786004800c1100281d801805000b040061510380030214055038425964014000510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323813507 1250 323812257 323812259
    0x1203020703021903050705060708070209010e10090621050a060504060b0406090e1507031409030c060601020607021002031302060d050106110a0203071208070212061501050405010806190803070c 85
    0x500a808180740101a03c80c0c440c20307024000700d070002500714104c40f02a50350230b60396085428160303020b000d080340080d880110000002400c5901b1034105024940300f4910644095444c201070080b601d15200740d5841001d00c0f5004000034920ba012169224090b4040d038071840b040da9508011220100c800700c030101d0751900344580030300702403180c503020f400c0300c0108111860020105d031b80d664101822461138801c0020000e400300f40f0139080400d070b50382280840c41007410b290440e01e172660810200d9240da4072440300018020341c40000e0072070194039960050500710340986048006584010044071022903411109001619050010b20340d0b01480080001c541d410410028600d04540c000c241d9141d01c440348400141c1d9000ca141c4007101d01044000d04611110701d0070507628003031000040d500080c250640380e10010080b8026108100a01d510020180c1403c0152014042d50040c0c6000401d084001030300c030700748a00c50090440b00d40420400c42903540c8a4070386958081a8201ea900043c540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323814757 1250 323813507 323813509
    0x111190807061e050709090204081b060405062701020d080f0a1413060f05010515070203010b100f090e0708150310180203010f0b092d0112110a1419120302070302 71
    0x42d1b00d5002e000750795401d42c0381c245402c025981c1e510701100c80c010b01c044000d00584266071000211001400007410543d10fa5024598860364040780c01d500c5004040c00e00340c4081503610118480c8844581c5440700403075511101b0000303050080081000800e02c2e0344503c482004560254014815800c1a0340e101000f461071410a00703903544100d103240f060781404018481075541030f0b44401076400c0742e80212746a0245000080c00b501e00048010340120708003840201c0246d200c0c5000100340c4003500c0e15580c4e43d0b45e511296000c1c0030101d88180001c1e1010010517030780f450881c402414840d0040c1210904625681c0f140300302d40ca080396198103101400c10500c21402d007805902d02c2c0d01c2e0b00300d10070007c0b5401030010400705030300102040f80320001c80700714200040707141882e09404001c11b098005290384498030a010f0461441082c1c4000d401c031400d503a118a845240801503400c1c544400840f1120f071001d0140c40c0210281c40c101640702d050000c41c400e680f170301e14044158082d130700400c030241c5580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323816007 1250 323814757 323814767
    0x30b040c09140c0a030f0906061e06111009020316150e01021b0910030b040f0b06040209030a0605060a0519261c03060e04110111190807061e0507 64
    0x151541052030100b100300034052005409440d516840c9041c0410705462008080d40203041c0244005c0050340382601c04142811500070103914003900100c01c42c540c644800050310521b480785803400742648803001040300180f072500110308151000e8211413a03441c00340d07010144c01c045508049014003100c8207003400d45a01c02c0c0d4400c10b5400a0000c3d1852941034503004a070380c1411401c2074020420040800c1c5014400c020400c000c40d0041000740c01400d0610f001c2d009080c00700c0007900c8210008001c03400515040c4215517140702c2c000c0003800e2492075561003901415000386069884602c5000018071500c4090a04440c2c4042030300c101460b90a05041d00b00350081c05141400d411401c002000c188000040c0c1c0e200c0b50103070400b009451800301a800c4004e00740c40d81003036100e940e409042c0400c100a0a04c00c038082d0300262904031445002e80007165640540080c0c0020380c07600400032501150300c490092035910700511000c100055030004140d030a14140c2000026203650380c08201070581d1007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323817257 1250 323816007 323816021
    0xc0f0206120405161802030705040f120201090e010608041103010609140105030d05030105100809010b060705010f050f100605071505070206040c05030d05041806050901090b0f0f100c0507030b040c09 87
    0x300f8064107590781028900440d005217600940f03401640000864035141c0034005503001030441f40c218400140d118050011042c2c41a04220302250b030300003003c2404402d804005060754403d80d1b60401603070f40e903101c03148100b203545441d58065690f0b0030089440e0b58a4010400046040d004444255140005151411046402c10380c1045002d00c0113014580d50844601d1801600d8504200180c5481c40480d0042a0340c0030542e42c440b10000b1044208017043d0408082810200c50411160380c0ba8000d42c180c03914102c41800468900002c14003506008001038250240102c3d407200810084080c1da00070cc54064803c000035900800030082007100c02d00c03000c03002d00400d8001c0d1031604900c101c0601f03203000c3c43c042d4043d8018242c0c0511000c40c01903028200074203000740540c8080d40d4a54480008024144074a401148038035291903250402081509001c08003402481604107051030882d8180c400f17034000c980500030404004082850104240e010324000c00c540d48209282110260071140d403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323818507 1250 323817257 323817283
    0x114060f0915040f1412120a030618240302010f050a020309191a090a0501080405190606090608010b18040305070507060528020d050a050c060109020705010b060f0405010c0f0206120405 81
    0xe504584243d0650116004242c292003411441d00d0b0b48d95010282c4c042d14850f08440803500c41700a40c400d1500283d0808207184003228143c42000036400640302c0c903846180000380c08156800d040c0b81803284520000c00102c2c0c2c25106072418045841c002611946905030401820900c0b0300342031100c2c52a60651010344082500454034000040002c180e00d43c110b40715650610007448001800e105041c408400d00c03800101d44000d0804642ca40800140054040c0000340351403d040460003039030522421540d00700c010001c0000c0d070012400c80b0440400101f040301048404e01502d00002d00400c480f00152180d620b500782c5a410304c0d00f8801542c5c00400b0342d405482201d07045e00b06410303008a030349102100689007540d42ca070b140401c2602c540c440ca0000892921440c03000113502e14030b0341d01804071144a0402403100710582410030400d801104405100d50320100f008202560049640d41811b500c50095810f42448580001d1001c0e00240035028420100104000410034207000030b15003592 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323819757 1250 323818507 323818519
    0x30c081b0304080c12030a0e150403050a150518100509160b040504180209070e061911060a090b011401030612050607030509061504110403020409031101050114060f0915040f14 77
    0x4514000f403100c8e404d2144a405560000c200c8006401d84d030044601454000e0f007214140c010500d0030b180c500d24031110ba03030411440c280129541e0070400c504617480d1410000104607403401410220010000a0a0325013a80300760000340c500b031524030351003800400e00c0403000c0f0b840d070b45450107010075100e0000780741640341c5040002000590312220400e80001d01450070040740c0c122000899414410302c3c02c3d20508019201c0c00c030048560082c01c8080130915081590b0f02512460700410585224410040c24040c00c5801031103085145040c034080804140740104581c1e50792110106012101030701510142c01400c01c210013150540201a0040114001080c0034039000594940740c40442c1d148501c03590320f40a035040520400c00035100551b40041c010003a01c0030070b1601600c031107000e106a0b881035080c100000b1380600d01c5401ca403d262809014a49444420b10140c0440e80c44202e545901007903644031025221074010140c005000807142160165042a80003150900ca010310248121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 323821007 1250 323819757 323819767
    0x509010806040b250e030a1b030c120c061809090b060907021501090902040608010e0733081810020d06090b150304021201020f0304060c0c030c081b0304080c1203 71
    0x4041102c60000440c070b9142245e084542817001a04108010a024000c01400c00351440041c1441407001c04036031040c01d04c4140780380c2c3c0c0c00c4c0072612088045005000420340c1c0b02d040004c58015120b21000740a4100c0340360646449564400c02c8400165055030030000300410400e25040c1419174070f03003000ca01c0c00245400c090150104410b02070501070160707504d40390f900f000c04549441e007000000e0040f44009010101c00441d142c4c0e0380714414854071001e01c0114458652925034000c2c2c618212403180000079403001c0301e20055510300009032008050341d40e941c180c041100014080600e08209105003d80d0341d18510120b131040c0d41258004031881490101801075594800d0361559980e54184010380d22541c3d18000500c0c8201d010070000b142e9400002d04042241e0200000c6104910481c802c109030300030117000325105203644034000d020990000008000c50100303800360080101d5a00340050081414030750354210b0700598071003903c3e980071606100c3d1030302d005800b401d400c0d202000114102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 323822257 1250 323821007 323821051
    0x30c0806150c030f04080c0906090906060405060f0916020c060a050d0b040b0a09061a0a0206060112150803040e1e18100c050d0c020708030703180509010806040b 71
    0xd446400805810a0300004842c00901d4041c001d480c0800200c8018544440c0e03214070385a250824a200c2c107101c0c6124500049940c80c010600a0048101e58010301c020f5036080c5c00c0c080200700151810f5804a800450404641d80d40302c5c800744100345c203203001900408003020103890300003400c00c41c40c0704d071009020700a03040c3d505c10203a6000c08100302c000b058100750200854004c00c0ca07407c003107800101041000c01c211106800180881c0d22996000b014501200d4001d006400781007080030040e0442e8001c42c010b58802c032b12001048401e0503001916914000e10544030410950018040380c00110b0104440010380f0708040e0312541a0303400320b45002c2162101e400e0000f0080103c0c229078000c0410b04007109041010407144203000c03004200c00c0c840c0303010141c0710790010000401443c2c100741c0c148801a10200d242c01c11a0b016100843c2404007550b01503030810b0800c210308410f648107080c00501d40c2c0d00c161f00d080c02044590302810180c02e16007010b108028000b8000302c0030360001c090305299 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 323823507 1250 323822257 323822269
    0x606090f0b030d0c020f1207060503011703070b1303181202130507020c150c070e01142d0d06060905071101110a030e0309030a0510150509060f010203070f080a030c0806 74
    0x4650304846810f0303c480003030000f81052448540e08500762142230744c0483c256801c000114187d40354010080c5008441144055891080c040d000740ba03460800d012688804001c5004241148281002051028625000110005141d1213042400000c2400310b05509200c550411900700d071020500070307880d000602950b1400745044443c01004011605621034101c04160748070401b81105450110342d032000012a10394003800b90310f51104e640c0c10f00d1000c501d030404c00c410a129042d03840a44402d5014454686016091511500503c0c10254100001c0841c45444094850090002500e003482c4100070150326000d0707440c44550780340681605110400c42c0c25034200b442a480c002c2582000b03c4161803d600640e51280c2e011321544094204004022a0410350050b40328010014a40303500c007805031018451044a40122001c80415164102403401e1054450180100c0f481e00d907103995504080300030180d00340e861701c6000c500729101646c140100c5030702c12050f01e001d502e14207100000451b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 323824757 1250 323823507 323823527
    0x703022b0b0d0f0b091e0c0f010f02120c0102040302061603110a030c110103061508250801051c1b08010b010504080d0807140a020303090106060804081801020106030606090f0b030d 79
    0xc8040c91078400554403800070483c28035200750b924a5500c0c90080302100031f9541d4095498684246100d0030702112039445400419a244401d034010916003800b88599805588020018104c07035400300004000b50305c0b800c00500a13403011082c854030248460500034040c06011148982d203800203d98080400e81c0700e001c0c5100142c001d02509680d00320540181c000344095071003030208004045600300419000311446200d04400302c41404110881d4401c08903031907402081c01d01207a25500140294200348180c144509514040200364582c581c9440c3c0d1411500003e1040040303070040c003804008000c0c081c10800010030700f8039a05281c1049156a00c0d00c020103155002c0100810001c1c094030b00c02e401000505d4903008016a89d043d2a04009449038400c55200b0304540c00c2c0800003030740700d01c41c1400a00c115000007580d803d00819020154480f810240d1182c115921250b0110108029204020080040000c002410b0341d51044100c00e580501c00010702c00d4000b60b0000b0100d0783c020704486 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 323826007 1250 323824757 323824763
    0x7021003050a1e020702041a011706061b06040606060c0308060d0516060c0b060904020a170f0102040f05120d0e1c06110403020312040f0303080703022b0b0d0f 70
    0x8103455607810b0801c0c0c000d01910191090740d4100751034400f01c02c3c81603801042c030540252400d014034031b07002c103e40c104030525208441c000703400c851020309181d4000c091107070071100003031036603247c80044144400c0b0280d0400b01c103c000e0b00800d081c8070401c0141c2c41030f0402007910741050181010030341c401070310004004140c980200e000b0207280007000b000f0b11450504002d0520580900c1d5182c0400500121100c0412180c0c41c14000200e0b20520781400320704c1c800d0b03900402d68480ca5050900c5000381b001c01e00003804240c451701e4401c506404c401c1c000f0380041c6c9001d039802011241350804000070245100c40740c09aa811001d80c11202651001204c2c48958090700d060f4082c010360b0324244021072105402a00040c9051340900c3e00b0118a002801164001c030110344c0341d00016840c00c0f00700d2180307116800000702000d604000080c05000307515408822810014202403e6404921203295544d50303da104400b10b02e643d00c0c81410502c82d241542d8030683d1581d209590030390712901d50125005020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 323827257 1250 323826007 323826011
    0x70602121f0e1501120905010213050d0206030606070c080f0d030c0f080615040302040501120c060203040b0702041d0303040c0905070e03030f0711151e091003050403091a0310080307021003 83
    0xb85101d40d001d14105c80943c003c80740100b1028403e810402d000303401682e0b420b40c10b0702c5408000241032810000301480c858000348440c1c07844e202d0004015442e400310900f2208400c410b140051064001e0000c24000080d10001e0b21a50f50300007001011174140302e080800b80700c0c030480d00815a66100721010741c0050140c0c0ca003101c00e07907030072104041401141c2c0000d52080c20b0100215007401e503107450102061041140ba01503d0319010240d0312030203a8000c00c0c440581c14000303403000d8078041d00040c02503200c05854010070300b510b0445900b141c0c0116400d840d0700c0c000c007404010913400c91080c03c1e0f00041760301e0800d902c074110724006504d0b841041e0900d000240d021407014140440459071044041008140301500da1a000408016401a4141c1e03c9002220301081605184450031285403420041540304c44880504c001e80060401500542c1080b810301e01c04202507502007104848003807002c15454a07032605042103000b00e0403580000c40103030014048800141ca4016030385104510900b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 323828507 1250 323827257 323827291
    0x60a140d05010608071214190305030c13060206180106050a090504060b100c03120903090302210615090105030f07180e0727140703020708070602121f0e 67
    0x1c1400740c400c44d04820000e0180920008140d0500c01e11107881c01c0c4140c0e400b41c14481341d041c002e615131403181c16051468450708000c1000a114400855000303070290a0380e42022000e00440801c21001c0d0005070140e44000240030110400400c888800c1851000038003a541c01c1501050929032684280001940c48001190800c1600d4100f07103e0240c000d000c40f5518003160f2801005004291002d07004514090724ac00c809045a020701e03181741e50140c881840b0305207503078203201001a982c280190500c4520140306107940c002c0c40074030f014841c102c400c4080b0000725810007a82c900103a000500c00d600c01c001c507a070310b0038021808100310b50b05061400048081124000003805002032018140d01485002140d091401c802c92642880d80c01c04441a210301020142c04a40c0703020a00c42d401d03004140054100c40c0f1a4004006044c0310300c5d88907042070800c1d0340352401e9030407424000c641c003846141040340305100d00c10400201401c030a090f024052829800c0d03618480d01501c00200e10888000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 323829757 1250 323828507 323828513
    0x3050c0112020c25091104033012060e06090403030504140607030501030c0905040317100902040b0406022b0e0a0e0403080a4a070e06010206060a140d 66
    0x41a90030041c0e0b00d4050b10b000d20300381c3c03000c8620b01c0c84140c1380c06030310103851001140401d16031050381101c2450200d44e030700d000c3c210780741c00c200140d40c0c00100001460b402c4c3c4010384005411840b10090f001900c0315900000d07400324020980e42590000e42d100c0d40000c0070007c582d6a80c812080c0c2058243c00c0020396510340b414001d181c0016003250300346034450501401901580341d48070b58103c0740140c074021011510368a0b03000c03e5401c1913801070002850380c8080c9111018074520a80c200c0300341c0540d080c101b03030344140b1881a60059813102010a1003c14200860303501070100120354800c2500c149030b200284100c103e100703ca0b401e80300c030800c800400800340986900003503101418400985c1c088500d024a0000c000b868101c2d1107034821410440b403a03490f180c4035807464820b1201c03081c251003644c4900d01007805858481900000f0321000c590400c6484106014000c0603100009075042d0341d14040001a152003005805030340501201d0300100a4200b0800042064040464102005080e141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 323831007 1250 323829757 323829761
    0xc061806090414090c0102330a0e07060203090909070609030b0a02120f100611030f0f040510081614031614160209010f0b04050d050304271503050c0112 67
    0x990404103180005090001100b1300003800c00c0710200990072a006c0c90340040d4001d80190811245074a0f0946e40110140c0d54030100700040c0d4446900d18000950313080070160306292120581c018009a000020509081e04140040540c800040001000b2440ca4950000e0480c4120720014260201200c08689a250540c04461640081801c00900c0f0b00703000c690605011025100c0407203034191130500140c094000c0104000035400c43c00a9070901d4030301241113040b60f01918070600482000c100101e00f5907580700d8030300c048000c540e48980040c640141010342c6141c10842800c1402007560204449480200880f58040c012079040401d40c02080c80680c2c200c01030001c416010f0101003180b13003840e070b810f2210001c12130086591001a0743e0b683c00005c41041c0c140101c01d4079044c10441442141082034483c2d501604c104110b0b4501640d50881025070344801110b540d0f160409485504074911600849080b800341c001c04c414018a1660b90360368405228110740e051112901660040f54003035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 323832257 1250 323831007 323831021
    0x190605132103111f0e1507050d15050d0c1a070c090903020a060e0c03010c030e0a062406050406030f0b030a030e1c11090f010602060f1918050c0618060904 68
    0x22a000c04d02c005600040c56010340014183c00e5000d2103590250155800d04112140c017503901e5486007450f00f0442d501c110080d100b81038001c03410600241c80010140c4484c03281110150103600703680c0b881e90414205070b01c1d443c0c1c05034040c4014141806420302184000c81403400b240da040000103984045880c059090035800e020140007280f4020351030b13000f1840814411400c5c60300b2002000b00030a8240141d040310f9140d05048666445a001840068105c0c1e01040350681e07002c812070003800c0c0440b007014800115400c01c0c070000711701040800101d50180500c1a002d01d407040b042c0704a034052400f095541075003440107410010a101c1d103008071b8030360100c224a010300541c00242001c4540c142400580c04000303006002e000410002500d008600c12118140d5a042e400b524254854880946405030702401c40d408a0000d251101c001c020344c1c3c4a490703100c1c100200d410112078200d0070007600340300465506d140038401c20401c5541414042c21410700242045640d683c690104001083c02080c2c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 323833507 1250 323832257 323832283
    0x3010620030a02070306060501031802090a0204030b0703020a300f1d01020c0c01030608070e0402060f04030b160807090513020d05040b01171b04050619060513210311 73
    0x608500c0c02d940429440140d0b8050301044c401c0b29a42d000440490344a0034042d000340c400d14069200500e840e07080e6a401800c425005401c064030707a200d0005120050b02c170729012075800a41040080d17001742e440c00217a6110400049400001c00030b50202141c0c1142e402c0e0714039075529451034540d42c60362110070b4000720600c8a1070100300350b5489500075400010520505d200c0c0f40400c10880d07100380a00e0b01075a080001410301c25140100b1071f00746044c06041240d1000d07090021181c202e40140141000b503000d0f00144404d820301c1400c486400902c440d2110410182c4010400074903044001a811a041550109908081403800000134000c00540c55012801c18042c0070a1144005419050b5030ba1551024071900500c480709079a003d03aa845561044180c14070145280fa007503200c182e2028014090705000100104110840340303560300844049007004c01d200b1300302c40c00c0150210241c00c1c542c0d484011000a4036035200c42044c82030008003041811412101d100c20148003103042e0002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 323834757 1250 323833507 323833513
    0x806060411121314030408100501140607052119020d050421210908150a0f0e01050103060204061202030405060c0c120a0c110607020f0909121903051b03010620 70
    0x107040b039081d880351b00521490151344217600300c20113040713800d01c5480c0c102d0b044c41c0c15010402c3c10035401c3c0310365508a00710944040c0142d9120004080301c4c10a56444060900c1005940c0e0301d000692b075111000c1813501e2021540680d83c0000300300d1b0010212800e0300c00408034540c2c0300c02c440c0c030008070380402140d004200c04001c19070848511300c034000071406925103032500c202154881104a17a11f03681546524072828800f00445c4000c01c00d6442803170300421684001c141c50302c84000c00d40c00d40b030003030f4030840c1d565a000500b00300c6941d00030400300003d58802400e6142d400d00e61187c69175581c0c06061542e0b04800000d0280400c1410026103101c0399008061588034003070840e014080d0b0401800a44800d041146a00700624111049510080d4000d04038140c0090303020078001ca02e0b070005d0141219101c0d03490080d15840d0071070003a000c4150000d058154240070302c500202542c00150004419484882c101164603000c2c0c3e09032415200c1030301e41080d8a040751103030f6000c0c100021014440c0c2d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 323836007 1250 323834757 323834783
    0x13050301020c0a0201020d0c051b1519080c12040b250905030c01080f0a11090d060f0e030708030f06030a06140a1514150409020a0908060604111213 65
    0xb100841c2c0f081d00b85000740c01ba80d252290001d0190340310004148007e205400c414400d0603428407210700211207440107000c2c20092500c040729486941c0c00303580c1411030000030301c51020b5040d502c43c0d40550301c481075042c40750070910044001c030030851000c3c00042c903295824000400380c011591500c661808024a061a014202c20300507121400ca07002e524001e0142d0400000e40354041e801880c0540504000c180c11661006991002490215070f0384410b040c08004c03410750f590340d038840324800d81e0042400140e01c1c59201d11800440c0c508044110480d0410320041c40440d0b40c80d0260ba82c082c46400503028507681e1600024142400068010102c40c42e02e071040b0310f0340da0348200d200d00c10b8880d204104130b804038820b20600e000000b88100b000c00e80c0e0944a1001500b88602c1d1014001d0200700c0032030901d038950f002d640581c1c0102405a0000e0307121082045001e0080080c9600854292010010158000720310b2503188500001c0c0004400c808000c200340003552645100c1c0030303402c40b201600e10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 323837257 1250 323836007 323836027
    0x4180504020609040618050702280f0204020418050108010c021518150a0b030f0c0105090a03080a030c0f080f0703111204150c0806031519050703090606091509021305030102 76
    0x1420b01c146c0d40380e44501e0000000c50450000441c0f0388408004140c40042c891000040704807400038030811614120502032100060316180081c0001e0100825451b101031f5003d2006422544141d00c10400da0781400d60003142c641e000f0139520b100e0340d01160880c03140c0c1c1c0c2e201c0e2602450b03004000e013600c95125040106c00c0c83c184c24901c3c42c0c041c1822075018484c0369800d00815035214200c544840b00c40e00f04c2603004c011580a40300070400190003038110140300703a49031904403550b0490325140d400f180d1918600146560300000d00c04850b0000c1c2062541410200464000c81a0080c1030006141d69464424403e60a00041e11100701c210042c105d400d00d0b25160501947d00c0c030f1039000d15003d040c100351a02c0b4900590625208810240050a201c941850702e410065000790840c0000f0818801e002c0f0307042640c1c000c0a120705800c0c3c41c04248001c4074601503040700c0c0c055210b040701903d003160300e82009000300f19890460b40740000c0541c80341c00a0302051030111003903000c0c0e07605610005103c244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 323838507 1250 323837257 323837279
    0xc07080115051e04020d0e0106093c0914030705011d24040f05060103301b1401020414040b0103140a05041e03050d0e03041805040206090406 62
    0x7000d41e14020341d500d215a00c00900c450503d101d40c6000c8080541480c0c840c1034107044d4003030a44003c44010104026454010a40c01c49416401c000070403616440049042c0801004241e41c040140c4a010002c43c421182c0807000400b103100a820f05860350003410501290303080b030080184500c02681d0b038901442c980207001f400c00344840359440420441e855031030700340456072496a120307a074690b0115a000010581303403050001d1049440703010700b204d0715000c00c10400c10203019501c1500100b400e41102040c96a101c82c40c0c802039071103000d0b5048009141da030702200790700514104060880c1c600199250107040040d410741d10707048a40c408a07001548142c04031088030f0b0707007034103460410074445220b00440c1550340170f904541c4081d09900110702d80c41055030200d5849809140180f43c8801031240c513014440c4000f100350001940860036200031195803142444107a040002503207424500009001e00d002180750750b1107120741c1d400004065441c1c4c042155102e2400803c10450140c540d214410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 323839757 1250 323838507 323838521
    0x10e09100c17010902040b1c020c12120903091f030f1503020a080303040b0f1305100c0206160f0f050d0c03020703020d0f0e0405130b041104150509011403030c070801 73
    0x2c1c0320088203000140b02140c62085405445038840d1003443c2400044958110010b43ca650110307940d420081c6014100c3d042c80381000701d070982c03001c25580c1c4c0ca00c41c0300680b03405405030101b6090341040100c040141d42d41b81203000807511186003124070300c5428130280d000701213460303090140700c1c242000c003220340084604010a991085810b096041e0701c400742c5554034002100c00170f0030101000702051000c1c81d017141065100e900806100e0542d41c00d540c48505050114800040640c0c454011450441d01170040e25403004a55021040318150760350001d0030b00300d0101c404070a21400710091b40800340304a0803100e0040a0400c1030281c4601000c00030001e501000c407d900601800302880c080364400d00090744074120950303405540040c0041000000c00c00903202926a56418554000051502c12034910860040100000794850042848203a410b116071104465410000500c41991842c00e0a0f0554110314414008078a6030404a440c51140032000c410500c00d59400150003001500500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 323841007 1250 323839757 323839787
    0xb09010e091011090d02120a05010203040c0504090f0305090609190e09060702030a032d0e01050612060c13080307060f0b040509030706270f1a040308010e09100c 71
    0x540e003100c5480000702110000d6400f50441101001100300e1450311074814400305000502d900f881017910300700c0d90b1420b258000c041340c0c2c3c0e9401104000c11b101d04044a900106020b60b0140410500c580e10007203030360a044c60080600001050216164460400b50703001c0c428040c102d0030070000e8100b0120300c908413070b1080d51000702c842c0c00054032310f40001c40c0190054480f50002e504021007040c0541c003034110462110490000003115280030000d070402d0a60303561184000181000c041130f181030075690001e110700d01900d41007000c001610300c00030385150f025070218541902c81400b544403d0381181550701103520381c880401c84000303110b529481500c4616402c401040301040c80350901c02640d400b2252021580c1080c458000414115081100210f840101c010140d054003e031801c0103554450b0213480702c0c001c2040540130055010078801700040d00b0445010903182550f00203120074814000c5805a8009002160502c00100205c000a03c000e01040c0001041c400c0c0042c06898048080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 323842257 1250 323841007 323841013
    0xf0c1b06120b010c0b071b30020c0303040302011404030c08250b0313110a0807061d09010b0a09030209070e030120031b0d02121603050105100c0302010b09010e09 71
    0x6184540c040d89024100c43e45c4641580c85560700c02c0c10075900d40079000c0402d0800e03044000708800240c10b280100780f6030113440606041e1021891401803c0c40701b20001d010544d07100c075903540401c2e40c000046e282240e90910301201107481401184e03003603000d03a03440203041c4aa07855000c80e0550b80401d140f241849804846409030841c0e95800b038040f07407203106109120f0401c1005c601074007010000106668051829022100c1e4030102207400744425601080341c1e80c02c00c1d181070002951080718081640c0480c20110034400380c0c0f000081c6d54004c18031850089410006000d00210701030b0784418000c41e00180800240e00d001c0801400d40d005125909200f540b0300040b4405407005d031600480c0d41c0041a0821b800c50b03944501ca5102003282c1e012080040c00c0501c0720031610711150009112000140740c3c4c10307055040903641d03401c0314035072910340d0020305090078014031041e103c1c8541450003032100d190103a8200150b007000da0050004864403500b00d0002d90020403400c564044c418014040c8800f2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 323843507 1250 323842257 323842271
    0x809031b1201020304020a0e060303070525080609072702030106180b0307140a11070b0c01050c03040f06020d0204030602070605060112020f120403170f06100f0f0c1b0612 75
    0x14040c03c03880100e400075032001400809000d0003e490004030f6100b00b0184c2101d1425005881c0c0c1c5141c5603c10210302c440300b5203040f4040d6400074a040e0303c0010300e10100240294103041803200d4a400550040401d18118400880610800d40031510500044124110340d01c0d611080c0c000d040e282c0092100801c2e01d202203001821000c04812203214410340d03554003848004442d20220190701590606040108024000e15403e03400d0103004010554500499a03800c1008005030a4610040c4813600348a8284200804501c022800c070200d90f80c08000182c0c2e884000c0b5902e0028002d036000540028408220b81c0100925540498001c1c41c3c00d8072003060280c000c101c240241e2080618a4049000a000740101c2d55904030784941c125200b4142801012003281032902410412107240c102c84146c142440766500300540041090301b110318101040900700c290107004464010f1810f010490107130301e100217100580c0004c240010380b0500d51000c0540d00c0302c0042814001d111200c00041c540300d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 323844757 1250 323843507 323843539
    0x6040617010506190803091504090e0609011802060f0f0409020d0c0801210212010906150906050603010f030b06040b1207030b0f04050a030f050d02131419120809031b 73
    0x8140c1300b00d4801030b008602c2c043e059014000d903003d07003900700c1481d042c086c0700208004001c1e000706d40c08444a00014102da182114215007912100101e554404101c13032600c5003da01c865081340e80010740f40d20740c0f07941c0c0c1c50f0001a1f00500c1c0300d10341c841d1040f2440815101c25405c0310784c02114648440369941c44c0030b80d0700c4064003000c403141c8102103000b584180c50b4060050814044116004022a000003907c410503201d401c10758640c0349540d4605c0190241c00e001000310751249401500d4196451819581004001c1000980501001d4115001d5000013081956035070040bc521800140c4a81500c80102d10011f0b50b40350540401c8490410141c0014003203c00212800d01c074071780140007051400b102d52026983c24514118640c108a010040a10289590b000515906a01071002c03040d1a250924006182c4100c4440e544112201c07907031606445100340c075031421b23a0807200403880001c500c0c0c900b102c030505c5100b00854240c015114600c816031892010344078070071000d440000086da4400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 323846007 1250 323844757 323844799
    0xc120417010605030d030f240f06090501020c040e0a12021b010806030304090507051b060a111204061d0f070f120503031f0b070501240303080c0306040617010506 71
    0x3c003030702c1d03010342c050300100540e9031094100d40211000d000000032071007201048107400c1c1c0462003d10880d2000c03a80d0400a050380d000ca03101c010b0007203217403072000c0b6070030040000d4903140c0ca07035106842552160034690031200e081c440c00c40703403c5d80120032000c070003504d44010f500c45c9510050040b00c40c109003220324095000e00c100c140724803001000f4500c0d10781003580207401030001a01c00e2040190a001070000814030030845411165810014031503442d0241c001400e990610034202c172071030b4040c05900c24902c00c1403440b640040d4080c0d808200780400e295a4030710340c0d02401d002c40c2940b26603ca0110104004540c0c1400c3d22511050001800c0e00d42c01e85400b40400454010b02c2c40d801000060242403800e240c0000100100381c1a9203040e03030b10f22804006800c42c400545e03030341c0d54801444500031004810300c1c0703100150030903202c01140385440140180d200140002c0042c9400400030751265295480f00000c1c0240f400392152811581648500900088900300c0c0212295903010107808503030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 323847257 1250 323846007 323846009
    0x60a0f0b100813050c060703030e0633040b19080c01080402010f0f030b06070503030f070e031504060207020a0305070e0a2c0a060e01090201032007020d03050c1204170106 75
    0x2501c50718000d8607903500460900c9443c04080d0b03a94080c02941e20002da80d0b60f030007042150701076a40860a80398020016040c01c3c0043c1055540e40e14102d907004401011f20240000303488076504040c07000d0b4410011901400d034500b50982e000112900783d411010410f141c240c199807181007180e11104c02680152440c82040d42c2c080d000c2100c0610450b0b1007442203590b031103070079414900401d0070980351022551681005104851035040401080180300c081c184003903001e00b45180c101000780c400c20100e521803d40f820150101c007030351800101844620f4046920035540a040b0460507035507418100c0d201c0000303000d081100d166400c0402e01e00c80c4d0900510310312214280000c9005100c01d0340044001818143c100e40f54002c0501c1c002c0810310b103218280000c1c000e0341c00405d10f4101480010700300c03100700c011034594070062501c2072881c4440c80c081d543c1d01a4155003660300d40d4281c0c14251068062000c0020452048102500e40b0a030a040680100d031011240781180c5040704400f103080c0e03901 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 323848507 1250 323847257 323847289
    0x70f0620010b0904021903080a0507060b01021b130603020a03050c03100b0f1e031c1b05030703180f121406061f0908010f02040609060503040b13020a08060a0f0b 71
    0xf4550200e405454035200103840000054030300e220555803903480a07000c1e0007074407080010440120f1180c0a20403140241000c0403401d1010703107040040799a840754810601c1d0b5942e40100001e100900c2d1800b01c1e44d000300c000e141c0081c01e10350710030703580e03d880307641e07061040d040d10301030b0160149002009201c3e0180c40d10303107040208008400120403061054a00400d03c078500001c1003001d20072041c4c1c44c10700a01c61a6804542e2070800d80620f59000361486074142c828000f818966000c0c07101003040071098400c159814509192081803e0340045500340319030700048242c40700c005000a10300301c841c00c89001d043c420000741e9002c41c0541903803925040c0440b000d54000b04441c1901034003243c00781e800e1492422909040342c1b41c680700c038002400c41c2e1188418514041d40041c05000807a04008800014071280c0350407031552425a44400c241d9501030654420420320004010440d5217189407100502510011a26103180220301000901007401d0003443c4c041c50072503100c2e604c3c20000c0800f011102c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 323849757 1250 323848507 323848519
    0xb0105070c090b01050913060501110c0d080d060f0b0310170a06050a2702090105030f0d050a0e22050105040e2a030111030115050a0c1202070f0620010b 67
    0x200d414000702c00380c04007a12032410054100008441591703074085001c0307549001032000401504000005d01341c3c803480b0b0700181d404e500024542c403241d42d0301e03150503641990001c0c42d940c48101410f00c100141c04d064000e110000e600d03540c08941404240c002d14490894401e0110a03141d440d5064041c07540715a40c41d94013a0009001040031a5841d040207402c000d10540000b003042c82c1811004440c001c1c40c0c000210030ac2194405d030290f190060710540502400c801a00580080640702980d91a00c0b04030181404004a07404510b140031b42c1290281034000b40c0b42070704c07903440030041c4480fa80210350301d06c24180c81c0c86c0c000324850406110b040944421080100042103604030078001d5003080a441008007030300d81c04100701ca07031400c1c010501090b080302c000c1c540360b505010350107aa18815181039000c0010130b200000c0c0740d41d4002d00191419401400c16080c40c0d00d02c29080b410020b894003ca84403180380d6000040456220103260307141f2144007035491b861421030740683e099030841041d10307510403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 323851007 1250 323849757 323849759
    0x19020306060a180f08030a080c0a0512040c0e040606090f1509020d0e030412140c1005030403031407020f010605031b01032f0909010e0721020c03130602010b0105070c 73
    0x2e0140081c10082c07100c0150152140780c0d5140c80c0741415032290001e004075040411007a1f000c507000140c0c941c10403046502c43c0d00785603200d0070042180c00b40e101210032a8204170041070074444012044006010420041c1945141509060000d040e1a114400d26145454958100008103200318000503100c00c1107007072154607000c03d40001c0e402140310b0348812a501d5414480b40c4038204000e20090828041e41e00b41c4040e2410804494040e11652112607000451551600d907984120480094060700b0140c0c0c0b00c2c1c44a0a0480061404240c9040c92840d802c050100294000a8030070b18400014004e0008035200c3c400d1646401c40c0104840c0120b1820310000e43c1c56000740c120031a0001c0b141d0554810080c01055036004403418041c202d000ca6001804480d60f0600104140c0540a28602c080060402c0329000b00714800c0c03146504103841001e0001010821290115040c0c42900c1007100c0e01d44540120184103500070f0300c6410301561810000d40d0043d40214140e0b40c0340358001e1140c14241d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 323852257 1250 323851007 323851027
    0x150f0207032004020d0f060f1206050726040c0504090c0b0307020111130f09180605060102071205100f06050108071209081614070b0a0c051e061902030606 68
    0x9080162541610208680c9007082c0d51102d10240100a0100304017054802c0300ba0750306002c45005410075629601414011b10184810100a0b84190b41c440070002d22660381000031141da00101e104004031604616000e0602121107031414046c900130007806000c5a55003007040210b6820020050201c1e5030660104031260309036000e141d2090040c0000301d101844400342211592118001d2031040c280b140d003d100c50942c02c48131130040d020010041203058030601c10046d40300c00b00740c1d005152584900014245920038003811008207029042d0b145580402c7c54011303101c054544003003003440d2030844411140d821300c0c01000300320341042e100d1400c1a2a842012a40011364401d5004120744440105000600e080d00070400d1100002a1141034101c2e0314008102c044468902550390340008414450092110104d4080c60000d080102c0300030302d5460028100101c01c0380159404841e03800424003d5004078145116207001035050451141034041340c02240001c0e6851038100009019411f46 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 323853507 1250 323852257 323852273
    0x80105100c060e0f25060318081303060501060e0f0922050a080a030209040b03010e03090f031203010608040b101203030e030c2b03140c13090c0207150f020703 70
    0x11211445040c1c603804626481c2c03503443c3c040f00510101805c200d4041103194880302501c108007800141c502030010501102142c890346521403009400b4000008400f428608000d13440c00046074020f1091129607510b1201401c01c0756004c162034000c001c5241d01d18481c0c42c002c0c6802d0b20440c002541c5005c1c00b0256140b07040540401c40049a542c810400424041003801000d007031440ca41e9a0301598a0802105210503140b1881402c0e00903810481e0004071680040b06640c0300080c10f4440386580060140000e24140c00710004011b02d0340b0001c00070884a40c81014144914040c2400c031000d5292007003010701a0a00b403141105010030349441c00700280c4250040004025118100c9041a440c40705076402c8c01060b034981d9041c00c221612040c504180c00102c0810003030241401c00c40c2d02030000991207445d00007071405064100005100d00c070707540c0c90011031001d00380b1440c0c10072074a1903011000c1d641c0c2d80ca1340500e40000c4603c103000740740c41d441100d4640d0755503803940c0035144240c607594502e02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 323854757 1250 323853507 323853521
    0x20f10020702100e130f0605120105100605030604020403020411221809030c0b0f070206090c09060d0f0503070308040b16020a020f03011d010204030b0c0a0207030b0402180412080105100c06 83
    0x3a003c0d180303d00303007803115a0346c0c020b40c0c0f4503c210500c00104c0c1440e080c100025a032141c00340150a9051a04120003400c0b03040c2e150041350041e05055549540b50750003d0000d02c05c0d90402580107140071004102c0607916005400c214000c0e8447ea98680a5460001c9030410944109030010510042d803085001154200c4034055100c0e040a1040d64a10383c0d402a50300c0f011943c100d2001c0c0c2840030403240640c1008820b411010304000361074050303000d00102d144828010300c45806190b80014402c10428012840308030305403ca015207445a03898517000b0480f48050310242c4c5da1042e6900400c0300049200e21036181c15959030010100c400709035080c0303c0d00782e8021000f0382d03040d5a03681c40c01e0000d151102e20f0900004901c0c00050303440c1e0a510708100100d901a01800002c0c0b4103000c1050b00755000140e41003a03179082810001c10355100d100040400c05103005170503240e6075107800d03c07042001c06407081d5411a616240d0011980e02c913428021540d28800140d00050740803021000441c0d05544008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 323856007 1250 323854757 323854759
    0x30324060a031a060c0a11010c0611030915070207060e1203190f0905010905040510081e100905060c070c0b0a0c02040e0d050d0908040801092d08030a021803010c020f10020702100e 79
    0x49c0c0c4040540310714007140c1410508003c201400410420304150511101541203413030b5551038014101010000d5540704035018440900c40101403541c8690742da03a94298403a0504000ca965400c0c00304054600741c00e07c413880b1004a82030110a824050191031048103489040c0d40c0e0021f00b602c0c101c10030018050140240100001c40c1501007034002c0c05001200b120344541c8000004501210100d524102100708032440c020700e8603510a00261001ca80c0325080300305000125200c0c07500c2d01703000c00307204020b40c080034400360000341c44480300e0340203181d031412180201c4080044d6003d40341700c15118500342c03840400103007040049010300203140d0301007107002e4002c403503680c10300c0d0b00d61075890300312003140805840c0421010190201ea0301d103c1a034403140206400134180e80c0c3e22690300c01559001c00f40800031859004180c04e00519800f040c0c4620540004000380600e0014540c00f075100d0407000c6204c10305000c1e07052495003101550088455903a80940030b82144001d0000407a6040d0b4021562 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 323857257 1250 323856007 323856017
    0xa0207020924040501030209070e0a0f14040507110705010f050d050a051503030c030a050d090f0b0403030b1e09060103060e01080610060c05030324060a031a060c0a1101 74
    0x142015803a0303546a284035014a0a440041c03000c140e05000202100030001e0703100d2801c2c0001800161501c51403d138021010b41003140821081c40d002503420741c1d65401c1b031020044c1000c1c1c00110b2075906000480c041d2420307201086a522222000c0351020703250168400c1c01d030321920f01000554416000c406025000b440c1c481d00301f21003c003125050701c0c419110b042c01192a0000e000903010101c0c0c5003020580114029484e05001003900360b12402000e504000b03101c40894000c00b91080d83c3c010200c038660102e0400d04440300d615228a07004010b803810307000249000104504c50801c04401440c214181141c2981c0c1c2c42017201308141d1140040c125030426840700c01c00215802210b031007074003801485010b0300f00b0340b420b0a040380c0030a00c554800820490707031020040100e20b011044a0300030300141f000801d80307500000c00d1614402c10004480d00000c00003241855154558482c0590301d40f0b081501250300c207403100300507060003402c00903095900414402e00000d0304000780503400d80c406042c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 323858507 1250 323857257 323857267
    0x103110417190302100b060415030c030606030605180a0e0111071203060b030c070c030b070207030b06100206070f020c030a060c0e12030a120b030307050c1908060a050a02 75
    0x14114054120394005101103584911030501c005050000c462004020740c0d9400000303000d52030095941809440c202e00740f0f5955902c091850f11500d04403000b03480e0013040c0070542e42e10b402d4010700522000b4203a0001904d0100c0114a0510034000c0c0c20484d500200fa0711a8600c40c2c02e07149840c414090321104140c1d6440b00300200e600001e0040c1c0c0ba554030742c901c9481c0c5401d0142030150040420304240401c1500c0c0203002e1010108860580b42c00c02121b420b915154900c51810481d030b403007540c002034107040340003003002107069001a00c40141c80c4541504009074841c0c9040c01440c0c03142c070200d400540c01110014882d80c0c03082121260300c0710244100c0d10359403062030101b41800c014040550750103480382026064030740c0000420388044000d40b0300840f10140c00712810340324090f4061003000c000c1484404e00d1500030030f8200c402d0b002801400e0340d45e07901880c038040d6034a503030440403540908102501350400302005042242144d00300c202410907a610348a048009041c01448200416400d002c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 323859757 1250 323858507 323858531
    0x30e010e130903090317030c0f0a03022a0706030b09070807020a0f0b18030733020c060a060e0c031f080d020c0405010506070206180d150b01030c0c020f0d020103 71
    0x840004901070384980d100e91741181000c0040038a002d5115012040c02c000b1700c13540c0140b88080b5280c400c0b224003065140c1554000840207840fa12030315440e03114521805591b600034605c80200c0500701c0c03200b04c51501c2d0b510781d419002d403220400d0300c50b0f11204540c0010011801494100d51040e0b00d441900c12103c0c0b2640c4520711051524015105108410100100d107a124540107807102203000c0210304001c00b40e031300d46500c030b80348200a01000d6041404500c254450719000c040c4000c06c46420b6458900b1082490fa13900c030102c40e50318045080003000a00460b0341c0c0034641c0210314840000749155211400405a00500e01c400c11041e45030000004400000384880d400214042e4058070349a408603041006444040e0002da00ca44010090788005036162030803680781240c2016003850403641d81c030021700b0541d02084050184524503070a200c0c615003660100d41d007102c007603c08000860038810100c4071100c06440094001c6030750203407042c16103030800084841d10b205250101780081840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 323861007 1250 323859757 323859761
    0x2190809090406020901031d0a0312020f04170c06070c14030a021002060601171303030e0a051e010507090308040303121104090e070801150e1b1201180603030e010e13 73
    0x101c003500e2482d070105d990700181d81e040c021501c00c19030384010f29003000481c212640d00e5480c0090000c00384001c081c2c180b841d0840903010ba581a041c0181241d8884c0d03034a03c0601d01d0b40c48602c15004060044000b52102440d1100a5800c0703690000d0901d801c080c103091100807020717411803580354180304000b40c0b100141e9a441250b454060964050700190034401d0014150000450071003000c59090b4003000030042070445000401501898042440d0006541a60424990440180c11402086002c0301484c2e8140c02c06445c1d042d90000030400d541d650300040307034240001c0c04010000e050403c02000030a10841d002c00c40c02c141c1030300015695169150841c0d40b94016031205000a40303410800d09804414881c000082107030321700070700c551b0319070080b4500c3c0e05540e40a0088108030304d41c0410104000c01040f00f45004408da003c995501d100b1881c010310071801d101e24207030842c0d01d11410581407028000c0400b200d40c1034582680350f4652100548400d41c40e0340801b030f01304507140f04402c481a824 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 323862257 1250 323861007 323861011
    0x6011d06121515090a09030e010c03090e070c05100207080a031e1b090905040f030f020a1b05041a030703080f07080310050f180708040305271e010219080909 69
    0x2411862199040c3c03000348200000014520a00340b440c22007600c011a41104180c1506502441c2100c400040761038260340390600c0741c0051156400305010418516041100d00500901640c2101c50011203404e0580a901c117445c0700802482c014031540c1c0c06036029030020341c15000101c0b00f1003c20701014401d00304413401c84a190b100c2240c070b1a520307103a56801c00400b8002e0a6010b0043c012407030329031601c0000c0402d6040003010013a0852522110034420301000c1416640b12207803100580e07040c0d245000d505002c1c002c0034842c501c0d003003205032840041705d0a82e061101c0607024100203481c68880d120303907401c03945072681e0424041012100060680c2c0040d031054112803034507003401d4201420310255a00d000c01060055651f002000c40460001c0280c9610541d40e20707000c42c841d40e40c0d2504807500c1c040d1500418100d003440740f00d803a040819200c80300d00307044181d42e588014074989100c04524401d801005000d07030400c880448840c2c03044e50b41914694060044a460011142c010403030004007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 323863507 1250 323862257 323862271
    0x606030a031e1b0320010b1c020301060503061003050c10080a0b030c04111213020a1230080c030c0904090c0503030f0d060803071203020d0905071706011d061215 71
    0xd0340381d0003011205d4140b02e940b407111800020021080d418022035440400c46a4041c42405551800021076030709402c904050031001e42a81c41a040441103900500d82ca030008035414040c55080f030a1509002c0c003a402c00315101d43d100340540d22170b8141440146188007400c0d801d0b000d28400c418190710b80323005900d010f42c071414110780c0e00d41d440d031200199440c01600c00101110b28800360409603903184140c13016a64400350281d1074510601c0e04112508042c3d491880032050300c560f081c41030080d500a4242c3c4040b989400c40c00d90b481c401c601c2640d01c001c64217400700510a0101d10b5480c10f2941c042100148500c498140e155203e0000170303e1034004613001452220300080d0407503034000a00400e0000d180460046080c4a40b580e112442d1500c03421040041640c04500020619241c0d008140300c95040820f4030a010b84a20102103c6080c08141d507032a4071400740001000003000c01596420b00071010318422540340d0108000ba081c41c2e0312400f402500c98a100d1000e65140d02c0a0780e801440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 323864757 1250 323863507 323863517
    0x203030f0c0105010b07050705060a02010f05150f1f0e03030d09050708070b120a0b0607060e0d020d111203101a040617070905060c0127050606030a031e1b03 69
    0x41d40300d840d0079200142c219000c6240144080c400040c00007420308141c4a0456107251500031204040740103041402400e080030707040c0020311151a195003405003444600341c80d0403101c2641c0c0e0742801401c0c1421403003c2d20000303101803550386103849134800010711880201a20314101402941006861003944140da230743c2c002c00000c104505042140030010501c0d2000c2c03c0c146a03680d40020f00b0a40002c010b24500c648035500401e480c0d03510011910907070b03404003003084058410b002e0190303164002c2130400054842c0514a00042c0c0c01850040220703c5444000d0081040c07890348035189402c082d141d940e406254100100d01c9030440c0d100025650700e00d00034240c50311b180100c020040105600028061000039052000280d4031200b42000e444050750b40b156602c0401c04510300400740400b404140c0004007803059640114081508001070040040314040d0f02c0b440e00f05a1100070901c00100807900c0540a10381008442595214100c000d04212030a0300d6030070310105454140400460001e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 323866007 1250 323864757 323864767
    0x4030503030c09090108060702030315060903191e150b1909091205030f07030903110d0c0605092b0302040510180920070f020613030b160507021c0203030f 68
    0x4c10261800c600510f0444020891410304010194592002426041d00b40030203038004007440e158a0111410003401074200d4002810b00d50701c0f03003000101407504035102004649103503007251400d00e034202503d0b0040010f8940a15002d0904003c0c00d4940205422603561100703d42003014401c51030000305011280490040920f02d032581d40c1d07550307083e01182031101c18401d001118200001c5280c0c0301d84c1c40d0600141c0c000081c24142c03240e4520540d414450b2191091340c0050f25408400300c802c0038843c2d10140b000b501c030002e240d521030307040c00080c02d001c40c006010503411420381c0c0040c034a44c01c0d490074018a03094407040410342c1a80c40c11b400102142600030515125426028044001d00900c4810010342450242e80800811a030035841d08041d000b00d001d006100000c0207407069154018007955403500070b08034030198001c2038401601d074100000001070000743c1c070b8990340c03262603c1a40c0d0907240082a600b0403a00c04000ea000ea041100501d42140058400304000c1c40c61000c003031002c035118 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 323867257 1250 323866007 323866009
    0x30b040812090d0815010915090f08010e060402010f090b1323030606010f05040b030f0117010203091504060b0d0b1603150b03071713060b03030a090b0d0204030503030c09 75
    0x41e00c0c082e00440e81584080c020042c0541d1084560380c004001c1405000b0122150004031800d422175040340e101e04060030491528640c1058071003044034000c21140c0706480d80d40c2c01d42c41c2200c194000707809550300030900050056200b82c0d102d43c0c4a1310903040004c00c040e04d4400040c02034200c4042c5202000e05a4000c0c00040408002040c0640e280100716240c0001400402d485103800b40480c1d0600548000c01646140584250783c00b4159100007213449180c844400006620288510519096406000f50030f001c01802241d00c511320520090407010002000c034400c01c9001401580c0f03050340c0b5a0118510350701d001d03a00400d14040d1f00042c0315414510b013141c06a4046200c0070040c1407406070000504031400500800325803c4030481500ea54401400f035580e81060555840c039006400b0070804441c0a040240c80703003d000340c5041200e002d0550030b155881c441c0c0040d0801160303091200f000541b0180c402807016001540c1d0150419541c0c0e1745040c555001a0f5407195914008107029121b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 323868507 1250 323867257 323867287
    0x50706030b0117060d060506040207020301050a090b0f01060f0c1727030c03100b0409050d1809020307050910020304120c0905060907051204030e0a06050a120605030d0513030b0408 79
    0xb00007140e18100f4960402c0c038001200c0150042000301400d0700c40000422903600c0d94103a40c1c2c0d171900600207002a107000d00c8220000e00345428115601c141c404042411501c0000003a8140c98440d01d642c80f03140c1700300500361181d400c40c50045499607810203002c0c540c1c400c0c00010b40009030003000121a5541c250f101c4412030910b10805c103000b03501c1410b8100099400191000034514034200000c1c4258500e0f02190240c840d050f4080c00c244150030340314216550014400d0000020401805043e40d12582010160b1006a030b0400008209100c43e11a40c81c108200c802d070746103c0d004683c43c041d030b90103814501c040b061005450303408054030b0400040341c2a000f41a400071048900d1455031170f00540150103400f0b04280b0032100c444003000102003501a607621a0043e078002d290340c4d14140c0d961030041c810380c02004000c00190001070800e400c540140504015614002d01400c201c1c02403103400c490a401240003103011103541c61000000c51260701c0d0484c0154051075034a6580c0a14080c041c203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 323869757 1250 323868507 323868527
    0x123040f1b05090f09042a0608150f090703150b1b16030311010b03010615021c210b130b03070609030b0f0601020f010c02100c05040503030712020a050706030b01 71
    0x401c2c0a420003551442d651040d40b4403101d582e0481e40761080d6201c1c0d0804030481c20011040001c4c8421240c81c0c141815002a100c03011100384d596010003e540c3d1884144614983d40041900500142c00c11400d900d426075406130701c60810300d80003070b140740c6010401041b012a94000800d030b0300c001428600c1c061000742c004000440c0749009088158440d038400a041869100217010455804a0300045d800b0a42040c9450300300100240311b0b003a150161401c440601e4803e041c09449140348060020050158244600d044c1c0e03203e111001d0a81001440324007580001d14540035510704188044d50f44148044140383c4010a0009844405005140c0740070301c541c10240500a003081d0400001e6503c808140d0b0000340781c046206c1075192a001070b8a003c8180502080a508200d680031034a5070000780141c1c07400800d0401e0012103240f450580390b40c03080b4002c540d0160002c00c00d000c00328072298006c20581490744101ca0b00365089031a00e030308120b240e8100800007916242c3e014040d6070301c141582 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 323871007 1250 323869757 323869811
    0x100501180b0a0302090a151701090b090c0a1b0b0103030807021501060c0305300a0e100c17040b19060b0703080402041104030812070206040b0123040f 66
    0xd01500e0402496440e14040d01800004041c0c0028150100d41c45200e46200200001b03204003412075030108001d0038948544d0750083d0494819000000c903054036004112842001030040c1c0850303143d90525107080da00100c18070b0117101c24131100c2040700550400e0100c50703e015a84010b019410b51070010b0209070701901020456120b000078034643e40c210152a81101c0742070900d94060141440c0940325405030000326034a45031072948000321035151070091070001488181008460b51290a240d00700c030070401880300b95034407070f20304205041002e0748403444404d09410301419400a80b100c0203001c402c21101158020211014000c000714074510605101c0d00300720b01805403909003040101e040c000e012016040202d00030200f415905c6583c8084481c0c401090000d0b5110344034108802c45500003401c1c230400c0d81e86c800000e1111407003c941a80501d0b03000c2000d5031103034a4401400b000e0720341500581c84c1d0140010f020500307656148036945400202400c00325043e01d01505103036114213421401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 323872257 1250 323871007 323871047
    0xc0606010513151403070206060315130b19020f0a0207050109270e0601080c010801050316150201020d02070c090506030715030e0c0a0b040e1b0d02090303090306100501 74
    0x440440d242c01c0a110050f6540000f501d02c900400000865480c1507010010756020030001c1480491580030406c2c5105d004142d08851b07580903600c18600f6a80411034442c44070300c0184000b9030005070180202c542040d8541e0040c00030300c01566a0800703c0c0e06c2509030020a220003c0d603201002d8041c406900100000d08042c50294035245008492284d041520f082d4081805144044c3e20030b641c1c0041c5d00c0c200d130b1804558140d038451190555880c40c4000641c080b0310030400010b45441d0001c0d15021010250303905402c2e0b035241810326a41c03404514561420365400303000b260a841003d2014081150003501c10f03a0a542c83c0c4800d4004032078000e001180650080c0c03400707008000180700054610001d529000441e003680402182c2017550700c1c0b049070340c482520300c00014501340716400b50003a100d44500c500c00ba510303003480c403248413449000450301295003800740d2096a040c66025001c0414042c0a1f6031a00c08074000203400c1001c21a91615040500c64040c425940e1061000b800690701500b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 323873507 1250 323872257 323872267
    0x60c2101060504030807030c050f060603011103060a0611100c050403150e06063a030f050c0c060d09080c011d0c0a031704030807030306090c26040804051003020c06060105 75
    0x200034083d1086000240c40100c00080c81820140b0600c5600303d055003000950b00001c84da11406601c03101c054075060b11942c04c1030320000610381e00004490042e04020007040101e840c0007426101030038421603400140c050120343d0640b055140c0650300001c01160f6801d9035440c00c0d440d0140461500e141c0901e18180380000d40707682c0200c005070303040c0c01050464035514400c0da03195078003c00c00480031b04103a04e021080318044012000c0c0103111110382c481e0b10741d4174101025400c1114103000c3c1d00c3c0380c0401c0f90b002400c4c2510909110004010366185480701290710b02207900c642c10964400d62008000d80e6603108000b010b07501c40b000000407281c1e49000b0b016002440c00000f8140503941c00080c0c00140701c0a110302c810300401085070011a405a0250340782c80c40c82c10050700400d00c5100301c110940c00d0031200d50205201e40140019081c40c04001e00050210f5200010000c1d0010700c00c403504241000f0110340781da030f0041d0900050310703103603005030381c800c00c4030281401e0410180c5030303605100043c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 323874757 1250 323873507 323873519
    0x50106150e01030b1201230f0903070303020705030405120f010609060b09210f1b031911030c210705060306030a0209040f290906010311010e0d05060c2101 68
    0x1c080c1403010801d02c0c01251240c21304e0b0004503d54a880c0c1041c016602c0d002d21900310190940425002811110442e886560303a0707404404040d000701c4040d09260410010b03040041e0080e4042c006080c00381c81203c1c03c003600c88012072035129100108402551001010340c6c1e80040034026a0080e212184052121628085600b852030144c184018030400c212402d001902c3d805448220301040c0c01c10490300d1000c0b0420340c41d07440c0c0c980590300c03681c0070b00c2c45c82184000c0c0c2000580210702010307500f03400c20420311a40b6000e8044070b400102036410b01500440d000f1a507500c40a540c030881d9000e90340320000340540c0c1858a03041c0c1a900480c0070700010310411423256404614011156010346c0c40b02c00c2540d8510f001411408806401486030f0091241194500728004018965082000d40d04c4140c0c3c07a040c4071380396120700910004080e42c50031100c405103944940e00c60405044090705c041c2c450b8485989071800c214003200c80100783c24000c55010f800031051604403004403840003056186505103070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 323876007 1250 323874757 323874767
    0xf060b0406030b0f04050c040806010603060503030f0901030e070303080106020106140f0405071206141507021e0f2e0504060c0f0201050c1e0609010c0903140f030c03030405010615 79
    0x2110307490034165500511542c50321440848805600010010001450b2818525045400c07501a01c2074078400d42c000451080e010f48185001d9510040080d030a0161407403070242a50b001d58456810152035a4030380e40520820813039200554820f4640e014107605120780242159a0b40c0d00800d40200b010801901c581c0300c240300440305d10b8051b5004105030f6a107500c142c6140c2e000a14010405286c000c0010b02c0d0261400c20804003001161844484149041c00001902800101a40c040610402020840742280f40c1030307e510b8001d0a122515100500091408904030328204015031071100040603c902c04445091412034078107040d402c1904003100206041ca00c220000d20341098552400156070041d800d80c0d42c140508412104c078040841d01c031131544c03461034a0b0701d4054401c503400b0071480c0710306010b0f1a00800d40fa80e2a40005413560301d8442580040f5904c500850180120300c2c84001c100b0f000518002c11108000c1d6544c0c101441d0090071202c841e0f10000e0443d00043e88089925440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 323877257 1250 323876007 323876009
    0xf07031a0403140a05070210080c092e091502060106090b0310052706010e060d020d09082d120a020d0b030d0f09140307030f0606030203010c0801090f060b04 69
    0x4980c00499a07541c40d0545090080408400d00c01c5008034080381c9096000b0010180e5900c03d580c2c00c55481c1c0b800030103942d030920070340d4100b1000b00c0c03c0c000c418203070401c54143c0344200020707484100c00007803280059081e5400c4220345000110484030174403580c80a840714015007100340c40140195807402d0002444141c2c0e81c0115861043c00102041e054401d0005010290000901e000602e0220003105400000d0510003001c1544a080006041d90f010390008088250302078042440c000342040c98078000e500100015001c2581e880107030000c200d4200281c6920030b200036440400410341c5d00c1200d50300305000c51010003003004004c04d09404035100103840c0c024685403805070301c2e0451400120050007280c0b00e41f0303030144200005621019844205545406025109c82e1401e545070032580076407583c101c003c1a050740c02036401b0000101104105d0b80d910340144000202c1c80d4899000034250390b0906494000903030100f0050000001601c6a00e00140c0310400c03c2011a2425415518034020303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 323878507 1250 323877257 323877293
    0x6022a0d1b06111603080604150501030e071a0918040f020f032515090b0f0f0705011a1f08060f04020f12010311120a0209040f0f030807020f0703 64
    0x6081c0075404200b01034112900001480c99180d8030b070030503040c16040c0c061009a05030000740b0240080f44440c102407090314409101c41c2040e8000a003004015806030926407082412407154000c0040d1b0448800d100169601070500041d0342d5620600400c00d00c0151014030030040c0d00a40180b20000c6c00c00c030402a0f103070307a050350103c80d441c2803080020b003042d0307c920301050349d200401305626002030209000d41c00d5500d2003002d42440c200f91442152180c60034003a0072484041001407482035400d440182241c44102d035119481c1c40f120340d075024203549440e050a01e180c075000781e0b8090b017813038800001c09050080303003035025010f50304020040c4100c5c00138160350301074292020241800c0e103542d01241c081410b4160241d5480e40174a0400301084000d200907030342c021a50400c6da245250106070008000340b81401088620403035000c00c00c00e041d010344101d65000e618040000050a5100746191060090b11400941c3c81d140c10040d04040220b1910368840e0005003080c40011b003420841081411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 323879757 1250 323878507 323878547
    0x40b040309120b0405011503050303040b0a021b0102120f0915090f0d080415091203020a02030d0929060a03030c020307050a240e09060607030c06022a0d 67
    0x221410162882501a00b100c0c07030b0b4801c40e21014080c000000d1010707018500c070348000c2100c46100d216103114201c050000808035081000032034086038a55025a40103098500010304c0d00f402c2000d803010700c00f04030980282c40c0e5004150f4904100c070307003030009a2000c01107189403000e04d041441241c42d00b21014007142c0980b202d2011840441081180f078030304059801c00c0740c803408070384d14028001ca0b100300c50480391960200320602c1d0107a46800740190982c2d20a0b9500d00c00c440303580082d0040c0d00071604020443c4824000704461310310350301070150441e019441c8106e154100411501d44001c0c20345440c16442429800d010141c0c4520746003008584c2c151130194030308490340c40042e092000980c0031359405101d40b20013180c3c4009030009098040039040402c072014060345001d84441d800c5402569200640000046460820070028840c7d2486840d20018010075035448404070303008018800840074070701c6420102e00741c00070303014486201440000e003e0000c1080008080b60440440291014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 323881007 1250 323879757 323879761
    0x2010f050304110a093810021207231219120504291506030403031b090f0506030105031902031005040f0c09050f16091703040f050901060503040b 64
    0x36105912114802d00145000c001075a68811103010f009800c01581d10f0119203258035402d11b64020b01000807040d28601955100000750400041017000840703401507028918031500744c1460344c001440e00522031001d890799400c001e0802802e2283c0041040f20340d90040921010101c4820140e91101c02d405440c41c655401018007152a40011540001c2d04c500340010303c030801450300d00042401a00380c00b07011041d8821458803105440030760b02c2190151079015100000c0c10008010350303000f4040e040c041980b8100d045030441c40903804c0c003e070000070700307400d400d100200142c52040300a120480d00282503505000001e912400500c100802c007035801540c0c4011034600307008034100c6540c007844c204074500c2c0c10b050106666a503074070201e03a0250045408950414548a5a4001c4458401a204a94400081d0144039130082d03061414400070744030004117480d8030b805040100308410701954030303146040c80b2102290b085811a91152800c0d41c0140852640902a6580581c1003044c0910507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 323882257 1250 323881007 323881013
    0x10020c0a0606030f030311040b030a0b0607050a060c09050d05120310031e0209060406060806010e0402190e0901090606122304060e07090516051e04080601081902010f050304 76
    0x36580100061045042c010000b050003505071010360f206010b0f03141844a007610b5108600984240d009500303c10a062011511303d002c030754411020902c02409451504006454032071030000421000c8aa2540358002c2c5007850368004610700090805803002c8101d49140e5442d26180c080c51541500c65041c0800000d40d0013140805510056800c440d0362100c13229031001112590802d010300b6401646880042006424144102412500280e551760815203802c0c0045171100000681e0071341c0240c0a11954003048000084202e5141da2612a00702c214640028407000c07140c140d1104404a1400c00c04000c03843e0403412045d04946070f040005600600c0354410303039003840138088084a070805001008100145980903802000c0148125048140e60f00800d41c00d998049a250b845a4038962103442c00c140548054181d40702c2004040b00c00d01e0035940ea07280c1c00d40144d40807046507400307240108011b00c4140201e5599200001d909001409180c0010f040081c8110240f41049000000035041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 323883507 1250 323882257 323882263
    0xc061a0f03120d1a120706020c03070509062103160314041a07050f1905010b040507021b060405030a060c080a1404030c060f0c030605040e010603020a090b0a0815010311011110020c 79
    0x200c0c020007810729001d4810305c50000c0e41c3d500340d8019000948a0481400940d01d4000341c0c4404442c0020018039240e0f81d010144105200484170103038030b48007a65400007103020180007a110020801d02c0c015a091401d04000702005c04840d8450040c07001044140f150008400301c500600706080b81240e9102001d00c0c000d403500c881d0444100d600e02409210512001c01c0c2001048c5060260b0000d10400f80100100012510140c512070056401801c54010703e08000f1203010b9000d01c01052030b0b0030540c0c0c0d40e002c2818500c13480e1088a0040d51501c0d0b8074419a0082581c54005441007010881c4100206947d81642d80151014061040c030611a504004403a00170a0350b64038810000d014001e40d0741d8002d00649810300600b4440c6041110f842c444640510031030044a03001001c4404003481c0c00005c1c401071036225101c1d03800c040d420602081c02d8008010080032007800030686603203136144d400d02c04034007002549028100f140301c10755070a201c2030025841880c0b0b1002c2100503030f00d10380402560702e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323884757 1250 323883507 323883551
    0x807050d05090604110603070e0405060310060305010506011412010b13090c0f032304060b0f06030c03060406090501050f10020106122405091504030c061a0f03120d 72
    0x44201d0402007044040e0101040b103c0c05a4030600c2d44500101c000002c10205002c125181c0c800201d503000541560304e45074004580102c0042c003683c058000d5400c403039090760115001526142e440c1d80130700c03806590194175807561441507032029043c400c035001007040c0ca000c1886414001c3c00046200003520781484000d80c0284100f4004110348640b070315000d00954045070f095408640340c08841910b880b1a10140c040c03407805c01422481e40d40d61642c864005002058180c1d4000003004c41006854451034011409402c3c003006154480c58108101300c00d07210a1b402c41800541080c2c010041601c07800084010981c04851034080c0340d8800310120f00504d0b06034009110200036100500500400c2c01c0e21080b202d0b80d490040c000090800008400e0721000e071100d80780c640c0041142c0c1310220708121043e80052080c5003c224042050b15110b0648203440e02036180d10740642900c80151030000c041895034601034000e0300c190000d85442405a010f40c20400e205035440e0103001d000d00f008918185 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 323886007 1250 323884757 323884777
    0xd08120a0612080319090f031d0307180f020a090f09060b1206030a05030a0f080a0905060601320a1211090d02030a06020a020a0b13080a0e011e0809190f0201080705 72
    0x6c8040500d0510240c2c90580400540100c0c0000c088100603048540c281c04200c00046c004154261912800741c224403509540c0c180c0e0580c3d00d400c0b00340c245045000408401000e81d844084036401d280074440300901e164881d0f200030b8603001003003041071030500564001036542958403540340c0c0c2d0703130010a04169076078000500c540800100c0c50801d50300010744410b003410302d0303a42c28215a144000e0000300c0e004500d024055074400000150740e5842240d42d0b85001110307201304141c00da0f1059208a00780d106403881c800ea21404941c0704070069211000f0300540446507418480d1504010716a02c0d988120031080b401295018400010340d1401c11245890582c0007000315030303079144402c00a44075011450200c90084d00480411501c0c8807040c0340245d29500316001a1030a03000c900c040c1c07a816802c4402d03074140030524105516003050904d54090a155580b80c0e0b840383d10740750007018100850000d0b141c4c4862242441c0c040070860b030102e54103804d5820700700442580c480c01415503250168500c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 323887257 1250 323886007 323886011
    0x60d0b0306040803070e03070f03080903101404060f0c09150e06030a020306090106080c090409020d0f05010e0f030a020a110103090213090506060d080306100e0d08120a0612080319 79
    0x484100038005008605c100384070b039207442c1c92502031b82c109912003a4a1003240320402a200c02440481c50100080001e0100181203a43c49160b01c1080002d48441d00d8428960411903010401400060300541c00c010000147c10072910302000c03000b50015501e030240803d803000300007a0012190040c1c2c81e80f0449000201465203d14040c9228070113540203e400d0f5010f102603400000d04140292005401412403080550411586406100052249203011780c0d01080d40c5c10f0710030101d00f107100050003d0780100004982c00f10324103022440d10b4080340004550780d00400440718041d43c00315000c2032040d40403008189216488004030041c1410301d030302960001500920032801c504507030048022922840030384180b5981e03042040001340d4041070241070140200002800e84c038004401450001060410203252042c200c00b05500b41c50311042101d50500c001081f1086010740c0841e030341d00641c00700091090074207041503000880802c4900618190022000c500b015009044c0d0750303080c880e4140300b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 323888507 1250 323887257 323887261
    0x207091503120801030209040f020d02041805010c0906020a02061305060a110106060206241807120506060304020a260a080a180e06062a060603101406060d0b0306 71
    0x10001034021248001c8400c402144010000ca6024410181c100d0b900100545495501c6860b030780703200d52010008a074850781c03c0c804c1030016511440f51600000b089520201600c910340341040c01c640c84840700c101849524402000125070000d00000803680c10b07140c05484100f2714104440b260a1070b0080c503030028021404845d090750000858600484074030080c00b0050f5034101c181d80707070501601c0f544507070700025941032840203003000102606100a056146012000d192460300c07a0016502c0e0000144016001a0010064003070142c022000326600b070701c2d5003401e60003c0c500c183c00e07114009500e11041c080f45a15450607098181c1c144800003620240f8541d0300e40002070f94480e010450111f24003400c44109220901000710503658581a0b00c8c0b001d0300d810f4200f000e0754010300c201002000558540004103041d01c80c0d14911116800000c000b40d04210040504000c04100000c402614000507040e00c03081140c6d0094000d5025100300340d50b110701d410408094925852002d8151080c001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 323889757 1250 323888507 323888531
    0x60302071e080c06070f20030909040305031f0e0f07020a0807050304061202090a030b0a06090f05010302091627090e0601060806450705040312050702011d01020709 72
    0x10081418000740400e44c0c00300d6895030000d98416480100640c00202c90a440000d800d0040c041e4407003401228080700e00300a20a0002080c012003100e0440c001500401402540c050001d0400581d20303001d101c1d0820903040a020300c1d4000c40080882403205c1c1c81c00003080b41c0a009111300c10b400e50f040400c296403035003581482c0d03540358414410080002c0079040b4030740d600f10152003035401c010341c020140c0359002e2454540c0c110941c00504034042c42c99603410000741d1020300780702c0d003004400d04550100f4070358954010040d5602d030082c41d08004005500c0d903032aa19a00001c03c0c80c03030b0305d0241d4803260b142c40d442401161000441d0840c40c0c0300c0389018841042d0880000c0c51504030707030391079440412603a604014000c03030386244070030300d54a41450341c00d1580240360300c40780c5658400014460718076400c030399040350707420b00041c0d484070b003c60400034040c000d103c0c0060a2410240040c1019850184030749c6c0001d00c60401c100400c2050001900c03440442c0c1c1c4280b00c008000c00c2400814071000c00401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 323891007 1250 323889757 323889773
    0x7020901080610092c0102090d0f140c010525170d06060e0a0306320406060605090f010c0f0507092406091a070506040b0612011401060302071e 63
    0x2075030003c10b05800200025400350310303001d04420000b642100940c40031400e01c0c1c801c080205000482843e5400307110001c042d07111000200100c0e80100780162500c2030302d050100b00c001300b0102c601001c0d000380c00a400140d81107011140521855a0800704140c800c607440301401100003c010012500100703124a080c10325005400883c1c42140100040d654401003038418406809010340c0140c0c09000800100b00154001c481d08103c81584024082e080301c018611820300045621002094405204c140301051180310080c00f03540c06c01e13a180c203810f400050040c40340540640d0410603c051202c0c01c016100c802e00c15226400400c40350110313220304410010305a00e1008500005050309031a170b82034504291a001c0304c0642d2100003515040c080031000002a0701044481d41d00300300003031400600c00300000e0b80f00e9401802c0038121410801c00308140c00d4607580c1c44214aa040881c4104078108000043d411504642001030392034034180781071009032000307440b094041c6800d80c0048003801036034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 323892257 1250 323891007 323891011
    0x6070804080f0703030210150e010f060906081506030712050a0b030c06031909050708060405060f090a02010e0f010c050a21020d02070e0c2701030c0201022d070209010806 75
    0x100351600a0300c250b01450391003480b1320001c0d00503800848106055031950b030000004182c2c1d040104007080c4c0b61684051066000c0e401705038a00b9821740104800d55200051b18050b00240c0b600c000542003010501c1c82c4403000c1405584140c10020200d1103050003014041450400084240100d113040d43e47da800910766550254040d02440360b00000d5171404408a030311403440a126101c0c50041362081d0b038018510380108844521800c04041001c441c20044184654401c0004210030715106030344460741070015141304000d600c181c202c980140e0f0841c40101d007140701520780c80d0340900600c0c01210502010030018069000d03000b4980180f18000700c14088001c280308081c440f50404060403a80d803001c9102c4000182c0100d8018170030010400301180d0030061020100e41450b0401c10005e1a18803500c140048136920203410144a50300350040c40c000080d140002c41c10b280c0f55509600903800740202000046806816440500309000256810f80b50041c00f084a1917840c1c0d8038603030307a40c1c0c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 323893507 1250 323892257 323892269
    0xb2710061203050f0307170f010312090308070b070306050402210609090d030b01031112040201080115230408070602030d110403030f030e0c310204080706050c01090206070804 77
    0x3000808905804820380c2204072982c0350b40d03020726081c0c0701580c2d80700b29000500b0700010000d03501351000c2040e0340843c0540c040d8401502540301545549000c07013004c2c1090300700c0c2c1d042c403541c0d940800105100e0000d072a826604060540030382d91700c10030218010005030700f01d140c1c068404102c0b10054681801c5840c0e0200c0c048403e103c441d16007504000d0b0921003207a074450f2540c00500d03c40000d0307100f074001102c3c0c044103040208800340146041000c0742c120405070b50001c0c0001007004150340e4803040c0303540142001460394942c01c40c0d8080042c503008000320001c1c404808600c05051144010782140c00810780c1001b41c810035516230380c0c025100c1c0d0001441259960401c2680081c1c84c80c128116002c49615440741c42e0003902d40c102c20b502420440984111500418400310000d4032628242c00000604548241c0e015000225400030184c0f0303400c4141401d44184402e000e2540c0000341d241c16078045040c420344070a98001043c0c050a00c14000075001100441c600c400c00541070094026650b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 323894757 1250 323893507 323893511
    0xc120e060c0a0302011425030f02040e060913020105031f0f0915090209060a0e062a15010509060d0f050115061b0b040308090111030903090901050a120b2710 69
    0x46014202001368095601503480e004a072100c0302000c1f9851480e41400c0325038100401d1149054100038103d8009902c0400e000c03500c0400c120b9180340c039600e20781d800071030901311644058290300000c0041c00001c110070351031402401c14019500790050362070000e0810701d4080744899107520b5400b000c0c02070b50209003044950990b003c0350303241a90083e81c4d0f90210242145052041002046a13039118295107079410000801038115070400c0541d060368460803910ba840400c1c0b00c041403040c54681242401e40d9004081c07401449039545004044d50000f804440c8160b10722603604102c07100c0d059401000341190710700b13400100b074500e6402000044400c1500d454036560080040c19901281c801001000400d240000400103070040300880e402482d00c000015140720f00300020a141e80c400d5030000747d164804a61210545000350204c1d0151406a481c621118580035078618400b841c00801003502451400003001d10f0410808102021860002d50911040b501e0510380c65000b0b0069040e4a14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 323896007 1250 323894757 323894771
    0x50921033103110f060403051612030b011206080709020c0319020a0c090c0e240705070e01090e07030f020609040c080907291b01060b0c1c0c120e060c0a030201 70
    0x183c404200b00c040c000c1440c0160806542d5a5400c641c1a13024002c4000140c11917030110000c03d492600c041100c035143c1c0c03000242e680916001422940018004614441c18124180704a10300840e1038400c841c0d00060168490804441031810750040d2007500c0c8012585480950405600040034648a402040740c03441c0d0341c3d1686103142c280e4800c1c0c0c6c0750364003092141049108504040104100949054490400a0041035691101948880b500750f0f401d600c06841488882445842c50b40100780004082180d000821201c6488003041c1c4030140c132030640e07820341ca4150b40350074045600083e401802007000e68880080075118150a84805289116454010404229a0002e081c10310100c9a01c0c0510300b003c240c3d5115583d002200b40403240b121a603030040710880902503140038000901c100c50300c92014102a80c5055503110520f0f50740140c3c521904902ca820980700d100260300642a8a0320341081c20302a00c0502000340400d070800c400041c0d0203e003020201740d12146600c640d009006403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 323897257 1250 323896007 323896037
    0x912070e09190b040c032f040b030c06030c04030b0a0603030f0305091c020304150503041b15052104060522020a060c03090902130603050921033103 65
    0xc0c0b0702000d041006440e100500400b2504103c1038a900074450400d510211352640d54070081c100c0303030202040100e102103d01c0150040c5d003c46044000609480c10418410340c2400244d07644107481c071103030040400002040c21007005500300e901135a00500c1c1358240c0d00340f920005006200601c4194006010710f44024541c0e40b00e4082c490040d09450010308083c00310a820b141202c0c0c003800401d05620041000040044801ea21041d0f1441c1a41754a5100c1c03030141800040e40468011016601c1b1401506000070100d81e1059800b0340c61380d02c0e09a4540c400c0300140b110703d43d00041d4184188040e0340070407081000300d41005220b40d00c02060750740c19107096038580140d04040c4038003d50112035070308280806d51048518000441c040c1c5003441640365242d000b5803c99200c020131407030494a04030b05002294040c01070030707005034a95000305110301c40659290941280280603040d07410300000031451802031391050f545e03a407407018801c2031100b20f20020100c941e428084100c0106d0080c40c410415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 323898507 1250 323897257 323897263
    0x308010b0304052112010306151d010902030a06031410060906050105030402040c0c02152d070f051002040b0c010506010503061012090819090801050108150c0912070e09 74
    0x1c035031001c01404404c00c3c6030040200c5500c0c103000e00c000050b00307000c265100144480000e000b10f0040d200014504031303c10170311807500307850f4101070004072040ca205d1002c0540702480e5411986074272401a103e45a1040d050041d20140c0e0000d0041c032100d201080710002c000c0380a00681c402230504000d03a940d6031010005a6025200d2030b40401e00900028002d801c081d08814140300d2503103000144054030b0b42c0002c0302c1380101002e6110320500818a003c5400a80303c0d803050741e40e1610010300f140d000c500c1148070148140a4018608401046a0001c00c1800c100e030f0b24030f61403440c0307042d91990344580718208560401c210a030469800c010104107594001c5003102d020740c801400e030708903480d00d1100a580003204d040007400526540d0301c1703041c081401c104c0a0100624401c0f21140c9070301036528001c1006403590006100f59140c0001000075600020310f00c181c405000c040803030140c1e98a09180345500030080c0c01c5410100c51040d42802d9040420040c0a6034590380d1045000d0319601c2d9107943e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323899757 1250 323898507 323898511
    0xf09010e011b060b0a0e04050f010c08040b01180f111c0903020c0108090f070603050403020d0f090611120d02071707031b02030c03010c032304080a2111070308010b03 73
    0x188201c00720320a0b404500990040c003001200985841503c69071080d864030907240c11101540c0541182043d903007545400c0c05030310745502040c681004241010f45841340924410f01c204c041c000071190800c1142d041e141c0007448400385012042100a040070b850840365404a12080ca0807064586001800d0703075103210f0084c0c1940c055008001c8900580300550301c41c0c00180407520244141700340000c803400100809070141c02c0e60b070b602050506103840c0c045c0c903000300502d148003031120f07242540300703481c1d44140103800701c85603440c0101180d03000c05e2405003403005a0aa8001010001890b44081c4500da001410300a10135803e0795800c640e40240c00c40b85000f20b01c00180050040ca601140311005556008038150004080e03607902e1a41d1800282100d04040103400880d8644050364a003412690044540d510010240c0c0c030b545c1781c40daa40c5481c0e80728a09440381030149a00c06c000e03c0314261842000070842c401803c10001204c28984030b0213401440301140021603682c00400c8055055050b00c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323901007 1250 323899757 323899787
    0x1060f120506070c0203070b0c0a140114040b06210f1e0a0201030c170a0e16030201050d020a0e0d0303090605011721221a0a0507030c0f06020f09010e01 67
    0x1c1825103e0b10f4044842c05100c0e44240c0c2d061088003000703c0d04401d4103000300b8111048000828102d04540f8200040034405080c4185907407400c507449003403000c40c1c0c00240d40300b07610440622032603461000207020300c44201d01c0806040880e440940e655100001c002c2c13803001c81001202c02c1805541204500720442405142003131300708001101c0154000c3d0083e0503090020b08200c014000001c3c1c1208085804072410608107448c2d4a040180185c03c4c403200320414140c0300030501c0e9500f50380001e0320a100700b0450b800841d5000851018240c40703220880e4640100070700000d42140780e030400030060b04c00b298055440034600000080c100090880080365901c101020300140002d880b25440781200c0f50304646e47e141420030854642a102d01c40c13080401ea1500c0c613407510281050f010980b8001c00040d08903404000300054112260010150f03680c483c1d0502d40018070041c039280c5a80440d50241000b080035001140d10100da4015070702400c881982a07070790310400d840d0742c001110340c081c928040d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323902257 1250 323901007 323901013
    0x1b040501090e0402010306150f1404060e1306050301090f110f0f1201060905010b0c0c09040209060d030509092d040201080109020d1508010c020d1409010e01120e01060f1205 76
    0x1c0002e070240120080c0e005005041c0000c20a076610541514241120744180c0000c403841d20b11320b0f02c1500070342e68054050400b480681070508020002e0210a11a03d13424819038090030b84072a807441c142c0082014150150007440142010303c0c0560310601003450440c2d000200503e0f800e0141400c1c1c00a1150301300050005447d50740c50800e008281305090150b40080d501c803103011846a44c0390094034020100d48107440d540700704508165041c0058154002c1c45460341c030061001507903500100907002441100d800707001400b03510701911148a122400c0d0703045910311040001b01e019201e080703503060541810409100d800342c801408403080442d4000d0108041c240103004c117108590103001c158420080008070720064202c0c45907240d4060b40320303038060782d1030b2051142e583d0b07418414100e83c445103003821440e403000308142030054050b440d50355040101301c01000c0266031103650315003030200040b01c04028048510801074040c01d507601446010101030f005c0001d9460b4404c814904168124000e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323903507 1250 323902257 323902259
    0x601061e090b090d0501060303020705010917060403140403170403110609210a2a08030406020c13020f1206010207061b021005070b090313090b01020a020d1e0b1b04050109 75
    0xd800b42603005101c500350080941e454640005c3ca0034485c01019500940042a130741d40740800041000c05542c000c000d0341d200007000b10000a00010f0495003140c3e1500344805e046560103408800d80c040c41d80041d180c0040b20f05015034040c003201c001c1041e039006509410440f9200c80a22805206940110350007070340f10070015138070b100d0b05450700880200240548036501d50540310986007155142c17101b0521654100b41e400350400920507100100f0701d96000d0b5090070b28019010f51201c2101841a0140c021035810700307401021f907030450300c4e43c0240c4540b040d00c40b8020360780075815450845001c3e000d441001c1000c075034140201e41003003180c059215100041103040c1d0134000ca820b07254040c98180710092040c000042d00401041c2c3c41042d140300116245c0c0c001d0003a40308910640d1380811005440e1611b000440c1e41d000c19415840703a010b03264008011030030f03e44504066085840c04400d000004662802c00917000400c6010703840d0391b840600700c90071040280078207210b98030039207000c110101c0c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323904757 1250 323903507 323903519
    0xb010503010e1f08010e01020c1e0a0803071205041a0705040b18030708061906050f0112022d0a02011a0303070b07030f050a271e0212010e0601061e09 66
    0x1110f1401849125100030fa043d03440c1d080c9820b507a1203101d8907905075004a510130b000c850030080c1c078a030300541c1d2209000f41c2c8944061031b626121100c0f07015100c500d0010015a80e00d0140e11900c0c1d6182d2440030030081407034142007a01d40300350b0070000c0785910240c1d100482c090502c03e00030b9030141c0300358101d5549000c0e0700402c003a0803200c00300000c9800d0b000b81140040e0b400380600c0124465000c445d030070005000c0951039102180c0458205510804902e80c2158150340d01807149400b0400301c020046c2d07900d44d200701e074030003124480d80754003c01c09444421b0840c02d44401e018240b9241250000c0c04900e02003000a40044003045117150141d00c14081c0c035010817025204207030020360608002850400100042e01991402c40b0360b40f0f501078498103081c17030f03050703d032040071080031610b00041710642c4041d5183c803201c0002d581480388001d21642031400b55901c5003942c072012641c6d24000c01442e0720b544441a01c0b05c500340b2603400484c0340303203903102c000092002007079981d14042d5581c10900303030802c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323906007 1250 323904757 323904781
    0x50f011701060305030f0309100203070c020f1801151101270221060601090506090102060106180b040e0901180b0c0d0e1006030b07020a02030a020d020d0c09020d0b010503010e 77
    0x44905440d0799240c0307a000001c51000c1c030007000408103c0444c980d880c40e00c49402480c204050303102107011441082040902136010304146100b44d1704440d529200d0400b60001415002c0350101940541c003110000620301d50080e800300c0813600903480e0641602c2c8808102c3c4c0c201c607428118400c42401040c850a11003408030030080c40070b44000c6c611407240c6441e100ca513000c440110101c04040d0300c800144107096802110003402400100c8010380380c080e150340000e4461006105070014003040700c4e102c0001811011901e070152503540c1030300d82c0b1650350380c0e5040d407a02c0c41501c101103254613150405400000d0040144140c9410110400154a40100b03070555030344540a001100b139a505403034214502c041c0076000910088082c0816250705500341400c03000c501900801c2517501080402c00140c4020a0106003240c0444805480c003a403400450202aa204001003e80c0c2079200c01040040b02c9601509207003540e901d04010519a00d001035400d48028003e440c0d0080b03140000564614001e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323907257 1250 323906007 323906039
    0xb150c1018030806310606020106300203030405030a030504090e06091b0105041d07030b0108100b0304020613060f081b03010509060103090606090c231b010b0a0b07060c03050f01 78
    0x105e00c1c41c080800400d6824060940701200b404445c90b02c8036410001300c2c3c0e0900807603026001846048401c80d145000c030700c081d501c04408102c0400344401003641599000e00036240149400381c2034841d01e80062030700074541d0f0300c44d00611064625141e80340e0490400014a580720b446202c00520f020a0284040000789039032001e050704200081002042a43c1d0032205629541c00c18001900641810750014007650600c0800904000b102410002c41042c680c0c000412070340038100040e41c9480300c1c00440c03668850690950007440b0503500000e40356500c69401c000b501101ea1b940301443c1c07100c80f40c50101c0f92900e90b8054100380b040c801405549000d41911780c00007414100010f10395269610070060700d0182d44011151907503034101c411119003000c102c240750a2400804507124075010440d4215010785491102d46000c4d0064407880171409600c55144200d00405003440306594403294509540541c40c00c454240c2021840a0300c1c0e8042d004003801480310340311a2001d43e0070f040081c0c05c0e810314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323908507 1250 323907257 323907289
    0x5151c0501062c03030a080f092e09060203041b0614040302010e031504030207090c05190810170607030b0103181203060e010f1401020d050d0b150c1018030806 70
    0x155480401c881d1381c2000104150000c940f40c407285403900d45082c1e240301c8030013410070030690000070b03111944d280307154900c0251013500303a21811000c1d65600e0070b00c000c1100c0000106841d00c00001e0000307000760003185503035000910342112a61611100d0403a000c00c3d40c0360445840007400d010920041d80a0003940451040103022210f120304140c1c50210042000c0d101507016802c040b000340280c04450007100c014240e02c2c100b5a19081c14074040d141414502c01509003041840808528004c3d21920320704014045244880ba10503004140181c03a000c2c29241400800d140000c03a01955001703000e807200101407080d43c000005059101d070141e0404000300c090405503648400f01d1f220300000343e064040c2800480300c00c8000d04041c6075100c000e03a004442030556005040381c2c3c1c0c9865002c0211807400c20036103c08244141044013203030f8255850b4045002221011800010007080045c4400e05e02c074069206002d9100c52202c2e00d002d009020b000500043c914078001015803c02010300e020b102c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323909757 1250 323908507 323908577
    0xc12120405090c070f210c030507060f0e030403060510090b1804031b0b1f0308030c0d0914010f14190515100f18060815040605151c050106 61
    0xd0a40e05c1071210081c2d5501201c9103144500c0c4940c4440003400c0701612001e940c240a80300002c3d5441c050a103009120000348120b4482219510122a41d00b00031b614086110450f910346480e4038001c8050318003203810510300c000d62a000203003000c040c01020020400130303125542d1800d40703606181c0b600f800100144c00b40040f1300c480c20400f426201e80d0740d902c039000c1c20140c902410b10200511403c0003c100030f4582d9441c0000a10200350240c00300c070b403c00600a403055440203141610005841c102030060001c80c803290b051946494103410482c0b200c0c0100f0710030000c2e64000040c1040d011420b5a50a100712008000720340b420100c0d602c010b402c6440740c02c0c80d43c0103001d89400a0210b00c900000700e8002180e10340c045004540120b03a640d900111907000c220a40d0401000601c2e05130000e0001140010030454500300e6101e40d404200500805003aa0010318440c10040601e1383c031a403e0301c0120454441040a0006244140c0d0305894a56491540035107441d03030041000711030001c2070324450b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323911007 1250 323909757 323909767
    0x20d090b0310230406120b01051e0411250c09091704090903020d0203040303020c0f0105130b03070f050408100207080d090302060f0112021011010612050c12120405090c 74
    0x6030300c10640d0b01034018007041c1207403c0036888280001c3d6000e40d030003552403941da0500b1740d0001e8640099941543c1042d11000b1001d40c03607c084c2e06812707403245111074000e03250401c0408a0b075003100052034000c07002c4042e0f50903000010f0300c054241c031030313294054043c04d1011003d02c0300250b56003040b4406802018030b0b003081844030229282aa1045d40300c66020766460388041300300364040c0042c81c10b001c03180c0091410149141ca01039103400c10240b101d44901c40100c90184a42c0c014020b9810110300003c129407c01c0c0c1721001411941d009403003070000f0a034400d000d440110b2099084805a40802c000750400307680d032040c4c00c4003070b41100e00c01711415403045c005a10491a24401d80c084903002c0d038003c0995007000b04a0315030310301068005a185060b0b10081c0009a140d5454038a40174000d450160000d440f076800282c018041c507001503458071a0840418103028000031680f41003407040b03a90095003545c020080d942c0d1302111101c003001c3c00c0c06010820103481e113060011749c0701c13050b070000c18906 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323912257 1250 323911007 323911019
    0x70e0d080904060512030d050c0f0403060b12010f0606021213170703050604060b041523031c050705010e010509120a02030f0a030510050301230915010b0304050c01020d090b0310 78
    0x20900340e0175400b24070ba00104010742484d0031401003c1d003090780c8046803403411071428000b03100c900c16804041c00e81a100c4513200e071240c541380c00d0341e1102d15410008200ca99404000400540094400c00300103100b582d108040f00400030301103c0c020840f18000c81032507840e00c0c610480c0e5801d602c41402060064040c0040402c00a00c402841a84a1100003440d041401c080108a4010b400505607580e45907078240b103102c1c020720015000c50f06200074007800001503800686440605096481268580c41d030000180350010094803a10348214001e009041c1e014000c2801c8070b600b00c0d40c4d40126841541c000501003000001403801e170b2200d01c107482c60401190034000b0280d12a0300d01800180c1e841c270421014200c140d250402600b03048000b803212a0901c050100020603414210185400480c04520b200400b003140759000c022031009880e1a607034402070704000360401c5a080c1d41c0350140070020ba0003988045080c0390350040549540d400c650a003403c10905800c001c21180b001e9015203004201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323913507 1250 323912257 323912269
    0x1407050303100f12110d0f02030d020f15060f220516020f07080d0e04090c0308070b070801030b010e040303140415060501030b06041e09091a070e0d0809040605 70
    0x818660360b0765544500e0314051120341d200c181c0b944010304a12085803d8400074040903c80c8080e000c0442d101100384a40d814050300d203040c420b0000b5414840d126400c42502d401046d002219a0303500d05031740500542c80000311410070b040311000e038041c02c0042001e0051078066004002242c00d201c20b12132a028412070b0704104d0301e0503940601d100703014600c88108544d0400426060343c01d4207024110b803c1c40d0042540d074442c070404040090007021002000c0e03684480c1c2c01004c4041d00059440d071410355070f041c5240154000a0b040d20184140703c00100d1440c0140f003114120707940600884000d07171901254003820b41c400307403040302050385955000a20307914200307425008500070082031480b03a103604100000c035011540003d040c54140404244599201003e07101100c0100c44840308405820019818420513600300380740403031902e176940c801d00c00c81001c0384a203141c51082287c0181c90305842610820180c3c0d01c02c07540080705028400c0010169006130220f2036000e00b002c2101e50b121000241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323914757 1250 323913507 323913511
    0x50a0512040c03140a150b0f0a0905060108010b03040b0103060c12050f1008070b1603020115060302072607030f020717012406140f090d0503070303050702010b010509011407050303 79
    0x4100a0b50841030003400000c8103d5024124008000c01d0b4001c0d169132441941c10045150310b01075070391917910344e81d15100c142040c407003180300601324040c0070f0311117201c170005040550710280090b10510010902050b51000c43e40691340250110003240c1c030315941c07a4040c0240d07000c00e40030040848003007640e91402e800ba642c050002106d00c0c0e1201e291284c1c05d103a80508503802094075903c00c0900b04004900c00c0d0450782540552a100c03101d0080c1400c041e805072440005040c0c00454001000030001e9040d40607086140c031070b20000354101020584244844616402d1401d8200d04000490000c1e000344008441131b11140103961545945810312a85501ca16840360b2042e51544851001c00c2c20006a00d00790b60110001901154100380006001607000710340d1414440e80014000e039980c50000a40b44c0c0c01e1002801003210584624000361240c1140c00200c0c0844d01b02000319010500601450a8982d81030391207a05161440c801100d0141d508204407101990030842d03803001c43c100784000c41c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323916007 1250 323914757 323914763
    0xa050415090b160e0d02060c0a140a03030c03020f0f07060608030a02160905040b0415020f1c05060d02090a1a03031306020f06010b040e0c21091b03030a050a051204 72
    0xe02e00d40f0780759480c4100c80e1003080c401e00403c104a488200f0070307921807803820a00383c0c055421540319514590ba031841c204a2403005000e207049040481a020743c0001ca00605611a036003e00c031a5040e418160280c0c080c0c40c60320001601c05100449a02034042c001e481c180c1d002d144040740c03656550705001e04561014500c10010307003000f41c080b032810398441404c0c00100380f041e500b0052031825480345480004090b0004001c60500c601c201480c03011501a03c9081744984a80c603070b60b140310301892000340401080440e0903406e1800042040c03810340d55280045401504000c3d45a85d9030391040c009040f4250111043d40d0044881080ca8500b00080c240b601a076803241039080782840b0003c0d240c26144541c0000a5010304014080b403e1454260380c00c4440c00050052651140d03014072802c5c0c01034103140300440081040454010042d454034038003c42111068074502c0b110070030200b0701c110702c0300003a64241d44100b00d13a40210744100c009021030107652a000c0d050102801150180c00d41c241c0c0c040e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323917257 1250 323916007 323916023
    0x1f090c08030a1407111512090601030210080708040303020a09090515030114070e130e06041a0703020405030705100201090b0114040b0f092404020a020105180f060a05041509 76
    0x48450b001440644880c003060400c80c14445159585142d03207001117040c0d40a0b560707145840e2501903401040d10124003007814100414948055041c4e9603030400d1006900c502d84c1d15200c14409409034290a003d40245d03aa5510b450381c40781c8042c0d0203503205c2203040c8200001c210000510008902c40d950040c125482465000401c0d43c040509403804056206080040300013440002038005041e003003500d500f51001c01039101e010001c80c0040541070030000150044500300404c200304585110741d113a001140c803404a1b160040204c0480c082c1e4005c9a03015440a03105111030305e41401312145c04201c510010500d01042da589900000c003e900422100e4242807100100d4a09401104c02034002580d6070800100d02100250b014000501449201e44042001140e44015205040e2041e40701400c255a1180e0001e4000e00a10040302c810000e1241d0b49030450003503030085550310148031010001c20568941c1d041800052801410864545c0081010f04110f07000ea405190f194901074008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323918507 1250 323917257 323917267
    0x1b0d050108070603290409080708030402010201051b120c040504180c050321180405100f0b1603080a06080d050405030105070822141516030e1f090c0803 67
    0x582c6420510f0704007505141c10002e80001003c41d0a03800841c1d40600560100948494404a8014480100e0241866000080410511409030000c5000324030170303802000b0503074440d544829443d2180c4000090750b00304010752840e4081a07041181c020b9220800c03545416920800941183d29210030500d140c04140417400510041903030342c0d0700414040c2c010f4482c0300041c0440f140619104080810104004074a5190305506102610349005000e8403c00417401e00030b0741d5207064070940c403900071b080ca00300f2408242d04100000303481001c0b01e0742300c07200b40c0803030b041d902641c0c1a01c0041230340440b55680c1c007001400d40c8040006d0f240c0702c0c0380e5071105030340c4038202001d15095900040a441c148a020810300104260715045131580c3e01c5803c8210004161518204854182e038182e01d40c3d241c41240801040300c0d455512844c018140340584144d1664035003026401c0c0d0310901d2a000f0550814074100418602020452040d040a00b1001411001690351000c401c0d101e42c00a400b141d0012036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323919757 1250 323918507 323918519
    0x303061518060f0207180219180503070b030a09030c0c240507020109050105130b0409020a09061701150c020402070b010801050c0c03042309070f021c0807081b0d0501 73
    0x2841c140a4103031480c1c20101102c03e5480650358156510a6200740b4800d0103124004d4100b80d81a80d0051103015404608003603d8140241819080700c40c0722059000c91000107014500040d80808981c3e1442c003490555a070711036810001c0070000d005506002418110310300007450681800050450320480c82c5140074101e07000000031800440b044144281000000003603a00a00d022045550910303196030396500141030b15110000b940d106164450010402090645198014040842c40f660b10307289900d940d008225580f083c901c61280d40b230401c080061141d150940100c107560304107414040c506070140d5001c2002c9a00505040c1d41030380d00c01d00140305000080c060950042c1303c10410340c0c14681118580c40d181c0c800d501c5002250301c0308802c0740c15129000038030107605250003004461203240c14500500380c00d08500c003040c010700800b07041e811201c181c0c000c400a00512541c46c034445503201c08013603a260030040d102041c41d601414014801c0b070306580092800718141034000c1141c1d45050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323920863 1106 323919757 323919797
    0xd060f11070609060f110f031e0c0304110a06140309010603061e110f030103030305130203330103030f210c030504020f100e040903030615 61
    0x1080c80c07814405642d000881a034000c0d40c040c0000c0942a8140049440010b00e54914036014040c1c0340c0e00b503441c1c0024540c4407030a08000c00c038412416001b50003015080312050300c0b101c000003c100030417202d0810b40300c1c00601920070039026410000050000083c02c410100c15500110020b51071101c06d42045004640140040103121107000781400c4100888035a80360250a007131040c110f0301183c0c41118604250101401c0c15a425550120054600600f40907000300381c0651120142c0d8040c04401c1030001d420074416001070511602d407020703120206000f40b1110301440100082074110003c440700103c64034180c2c4003143e264500c105001c03480c09031035403000d00d0940d5056260750540d110761301560003100d2060411001c1800c001000158a1049000544081e0b02c0388040c14513810070b203200c6c0d109050110704251102a1640003050080e0351400180c4281541c500b0f00c1c204c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 323741007 323920863 := by
  have h0 := BRFrame.cov_init 323741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323741007 ≤ n) (h2 : n < 323920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
