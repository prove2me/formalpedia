-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1703
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:22:12.304402+00:00
-- url     : https://prove2.me/submissions/1dc07e2f-e464-4f7f-86a9-e46d8640b517

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 306115107 ≤ n < 306294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 306116357 1250 306115107 306115109
    0x151501090302030a02101709100b1e04050a0e01060b0d0b03060103030e01030213092901030b060f090f09090102180904080703030c1b06020706050604050c0403031d0424 74
    0x2042000c09541400580c03000180804200d6050b5944c0030200511017044413413050032034040705010340880a0112020001407802c2c10385200040404c9428070140812600120505c4880c003800d5015002c60500d150550116911010712800800d1007001c02174000d08660b80f9400c003440180c03000c2240d100c81e100034071507038800300c50a80c000c2446506644014010300c80d1881098101900000ca92032042460304000d00100340c240024815029030180d00c005d403042000030380d0791141c103441c014212513101c0d00410b59452800f85c0ba0928114010040c0282944200c8c0c1c000e811682c4a070140545880da0b080385d9209150703040006844401c03200c0c0040d00202c008500714460b55024040c080440d0340c0c0c0040b0303141d207503040c00c0000750341c040000b06880d40c0c025840144801b840d103c5a200a00c036440c1c000f07000b0603216007001c010b44d0380c42c507080100306d41040e503040c1a9407009100a00001e40100c030104402d40e522a030809059107a83c000505442d103e155910640210345482040d8601e0f00200c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 306117607 1250 306116357 306116359
    0x20a12050f010e04060c0c02040e060a0e070605091c0215070501320901090803132a0302060a02010f0504080423060a140903030301030308070f0207050f0618031515 72
    0x2030401c2d450a03030030000f072600251000d462160354011008019020f201d44524483d40500140b1000d03420f0040c1548928084603c004040e04064044a0205011a4003401d80d90300d502e426043c0341c0d10105015002081000180400040716640009640e8500c92100080b1f018040c8d2560b5401900c0c200e03007512003124112001c0510741030f541c4988010f0400e50401c0e101c100804880e40d5444030041c40c0074001310b601c0a440c90b01c0000500030142e0701040c804100d540210f62014030380090101c40b48003403101c50081120340400e20307010300c014035082d0300602044020388004201c8844a500d4a022540b041c0c6044a90110001d0100594020401c1111751000c00d13110000e00c481c41240400d40030301c03413140c1c040200405049403410f80300010068449859024040f03036103941c0c4914024000706c0040c8d07000c0f80071480300c004da00c0e0f4003440007407520182c0380c0103407c4558030007583c01404130580208513441d0349010402c44c09840d039103042107410004103100d00e15558504108852000b9160811855 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 306118857 1250 306117607 306117631
    0x150606020f1c0e061204061b020c060f210124170a11040b030c070303050c0a02031e282c0d050a051b01021006030b150a09020a1205 58
    0x554a490380800440900c0741c12810240c0d05408454000351951299503c461050140c150a1109010407907019550642e401c005403164084a4003080ea603c2b400b03400707400d07404007041200f464011030140140c1140292020400c000030380d84c260b0400714032000d80107500359003004016070300c0c4034180355400009180395051010521141001c160b20107030300208900801a11400070743c03906189282202c00625a00302c03015180d0401d5500c5c0d40c61703540840d005400003414400840c0c100e0744198111114028a50019071a0424140c80780c0c0144498840070101c40205110743c6c40809030890040d0a8928017604c1710180c01d00e652000f0b840621150000c040c0c4501042c0400b850070002460035a04100854460050b80414a04980b51401c0ca04d4000e19030b01400440014414045a8480304450701343c003030f141140820090b65080711310314130000e048411030501040801100144982a41c0d01c0508903080d01078079140a070040c0d901c01400800080c170441001d2801d450513110f0160418141d0042c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 306120107 1250 306118857 306118873
    0x201060b09060316120903110d0f0c0f0f0807060c02010608060c0d1806111308030306090411120708031206040c02031c0b03120703030e0c0109140d150606020f 70
    0x200e00c40e4040280500030029094210444e070f00e0107600280745103071580c0c00c280108086860b00400601c3c85000b00000f600c0307120149904940200313904020035165658046544c8416200c40918080e1044140e5030f04d00180000e0000c50307105401000030038055500411003100610b00207084070301990020500742c201c0c80920113010007103c02c544004c1030b180c0c004591010704e2416081000c03841807000b495036281c0540c002d51040148027070200c84800030344078145140d031965056101d00c0112000ba2b030101c0320b8400100064801c6a0030071104a001d071002a0700354440f0300d103502d405441d030001103045d4000b1691500750010107404550001c82a2414002450403c501964034007401c0b6a0381038010000a409610a455034421410794000908498480d01d08180c1a10716a0181e0b009800182c1000000d4100310400223007810030b8030040c2e603200340309880e00d02100b942c40f10f061115030340007015441c184d011a040c0309180141020030f540004582d45411006880d00c03022400c03161140e000413503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 306121357 1250 306120107 306120109
    0xf01060e01060f0306090204122a03080c0c040507020615010e060f3103111e010509010309051605330904060504020c0109060501050a0807210b07050a0201060b09 71
    0xc0010304441d4103050002940c030111400354041c0c00701d500170700c07043c510120300003402103a80410850031a005070b40a45841e0031300c00f0102810302e50034109603030b1005004001c000041e6608000c3c100384011105440c0345541e894009400d48030180da46000603030054040c44818010a20240c4400e0800d003040140e000000d00400e03094014405094011100440e00c6008a500d0880c0c00c0345105501c801d808500303041da0300d4048030001d1400180c51540640c22019954140100d1411081054000b041701d01c5840c0401100c0700d51001104504060720b828640380024810021300745543c90341560b040c400d0b03060405104c0d05503880070354644d600e1665100c4500c84048900c9000000084410055848000c0d0010801410700382d44002d400034400184a044000f043d03001182d061320a84080c44a640d9500800401400c10300910303006170000c51041010074031944880340400401c40c4002c0003443c5589850510540440b580c1d0041000060041d1701c0b81c0e820b1040002520440c00340e1418444480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 306122607 1250 306121357 306121379
    0x7030e0105220f03031e1a0108011413110c0a1101080f0f0c09090103030e0a08031c021803060106110d230705011b020a021801060206040201260112050f0106 69
    0x2c00081d00d8140101c0ea51814944203400103401c5d4851508034a0011074114410401099101c481c0c0070311070307202d146507641580301e164134078101d4100d00d41c0009038030741d05020014035420601130440d80a40e210003882070f40c250b00005d4a0401d640c6005803480823128285480740518106403c1c1c100100b0300d08104100101c506440d801881540c0710b2070a41e0780c1c00da4002d0b1a841440516035100019100001c10160f000746000b2160105641050485a50b000309565a0017100c501c901280315188030132114684507070103014034190319445600c03003060f4403010904001081c0c02070000103925002c00041c11108110b5140904520300d0052040c0d01441c0d013a00902c8003003120210000340c0000c1003400d0140035003010800c0181078012450841040d40c0181da00d50203104200c1c062a1582d071103224000242c001141241c1032038015180595550380110780d003681e50402c080000705015076103508440007241c941d010f0300d004041d8225540322410300c1860300d850000034003080d0f17041c5001444000144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 306123857 1250 306122607 306122671
    0x106090e040c05030a06061d0130080403050303101703030402060d0e0714010906030203040507050d0819021e06160807020708011505091602190303060503010507030e0105 75
    0x600e080c03030055280c500c0c0100c50140603600a0b54944240c005d07070814131200e43c0c0a141110001d4954104004000034001d003041c2e001d20a400048a01184c01030380100c0000b48101d56083c041d403d10701c100402e9a80f132501703810580003590303103900100801a9100c428410400645049100402100c02410f410f030355901c0300030070080c01404e000c0794040c80d0000c40c0d000007680d9000c035020740e26807076102c150391031180c1d440503540c60001e040300d140055107500910071a806181c002010b00942410201441244100309400f10707207130703002003004500a01c005d0b40390fa100e8107034642c09404d40038000402000e52861401218a068001b02c1c03d110030032104420301c0b2842011401e20710801d0791041c6081c1d0500100342d20580040d42810100c0e000350702c84032000000d0b520221202c184640b40c9071020f44140c1076400309100540d00c040342002a40514985c8000c0300c512a24000c6007940d00c900201e42500e009903000c3c00400c0d00e4030341041c4607802c203010300c1c0c2d40840e0f1203d140030101d03c508520381c082d03024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 306125107 1250 306123857 306123869
    0x50706050d0f020d05040323070b060a050a06180f060e0d14010606032004050121111902010b041802010e1f02030c060907030c0302280f1d010609 64
    0x184800c0148107a0300030403004100705004540341c03c035446180d03000e05012642100011914031245280010341300e00744820346e510750016800c00d00c05550b803418511020f425580c0c461921200001e090380c501c0c0c4000e0181040350f4603141d407941048080860f01c102c582008240c0d20180e00248145544400410ce1210040740c494014003954141000c20031031000c3e0000c040d50810002290705a0143c0000c000e400c0e905129402003010050003400c60f014600a090018103e0981e2880404000c0f07190115480d1410000a662804200580a0340d02c80c680691165942640c200e070710580a1244d590307062016501030040002d01d6003140d00b1a000050000c4c103100701c061a200c2d0b503407540c82051500d1055402240d20304d102c0007101a540e03801404204c451803187d40c0005400e0032002c5140800c681d0f00c451728600303407802c5500f0032030082540010390104104a040360308144851809a00050034105440e900180c2011000400041c26121042000c0e1091300100440d50b40310300c015048a42d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 306126357 1250 306125107 306125117
    0x302040213060f0c0f1b0b04060c0b01050402030405070e0405030c010216111905060c030c10020915040b030109090f12080601020f010b1c0302070f0605030a05180c01050d0b13050115020703050706 86
    0x40e2a035625001c1880d40c2c00900c0311f01070104012903d140c0261014090500903480d5920581e69102000306912003100e000308142c10808041181c0712100110b950001d1140098a0601c05450b11560898001510f400f407500f40c600b01305c1c420701c000e44440d401ca9603403e82d0f541c90340490341d4106500403051482524054000014900c00324841481520007034114181550010107034401010301039000940300c035124030014403592038050040d000701c0c0d0840d400f080c0c140d425603280910280081034110701c1a202c440340811f140303001640c2c03d0342101c0403c140740c03104036050408a00084c540b80c049480b8101d9603150540303d98441e5100c3c143c03042d031188003205075505400d852904a00344101c0f54490094240d0785a00403540030b030800043d5101c0d0f48012030401c11580d0741140840e41550b01c041c4c80030f02da0498070640401c0d520610040c280080340c80d1002c00d1444c04540441c00d14482100d0b030302201952580113100c900492070b42807031030360030a2009014050441d01c8240c0c0b40c008a20881c810300c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 306127607 1250 306126357 306126383
    0x20d0314070204050c0c06010b040807060f0e060d06080f0309030601140109080607022b0c1704080f0606040f0e0d030e16061e09060c1106040302040213060f0c0f 71
    0x6814208807000290701a1007409142000744140d88039412203901d0080d80d00072000085030a15001c01a50219100c1e14010921140380c03c1c429149150b25100c04804c2080414101d10a40c9508006055071800404000741c41898103140394140840030911b40c80c41d800820240200390703000180d860550b2904503100d0300390440d0100503285e107600344d88800001d003d40c1c000c1040b0b890b0040341c41500360054010600e10300c0a1585010100070344040d6440210f00e200700060041240200a8030b02c4040c0c40c040d413841c183e100d0010a14180c04110030f8105544920104009401d00d0700654417030f0b0040c1d0030f00b40142c2d49103800058544030080c070300d442019681d069101c4211002c1029403404403c60704190112a183c0d4001490880150f003980131040700660380450b106c0c4030340403003412581c50381d0702d04c0a5502c2aa03142c581155481072019803190043c4008070250ba901d1006000a00c0c10b080040a03603460550040c1240030000d40c5802071103100d10305800494007084040e4400c1e940502c0284280c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 306128857 1250 306127607 306127637
    0x5060a06080c12160905030303040b0f070c0c0b040317041a0c0703020d0f061407120903020703051516030504030203090904261b03040f06050a140f12010e04020d03 72
    0x5005410b002c2040f070b050b11040c8501e000491118010354526940c4200100d0b0300d0f41d05055a910095030014103104440700000d0640c04616280c5d41c1010752440c00d40b02c100140c0e100c02d4820031954000c0041100c0010f020010000072071210100c3c1c002201059080078a07049000075900811000c042100c280025408a00340c414041c45001d55070042c488007408121f800c100304252641001181e0b400c0c03516030500d04d601420002c151081c41c3d03a035a811103134490701c0103c42c081e0108403000c9040d4881c20b00c1c08400148240202407140088140e000c1c514a0b000481601090126207103006052408040c040400d85c08002c8440030b01d0281c508205d580c54502c1c010003440280d030400620060aa1800e18024030b049006000420a040c40541003003858034020780c4034440c0c1e116030160018444020407502c0e0043c2d01902107490345003040840c03440b2035a0f234400140d00290118281020004d4029407038142c071000d09025111300c01d410040c4d441d2586c007003146035401e5807015045c81010181d0500c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 306130107 1250 306128857 306128881
    0xb030c031c11030f090103050c0c0d14040f080105040c050105040b030a051305010f0c0f110604260a0e010212041d060609030a0303050f09060408180406121a070305060a0608 76
    0x1125140307904484c1d449016030940069600528503160004e800d00001ca1844469001034a050380b541a001c1c10b21000e008400751030034501200c070302d150034005201c00038440a181450308001c1c10b0340400490549041d203005083c408032500140c3c14060b090105225042c0c0010990f42d1001d90b15400085d0b98641d040000c581404102d07006107a0742c00d2140d03513a0041c40d41c1d00507080740400c54039048e007004400002518161030803501042c80d43d100c3c0e0009070114403d401a92036007582c1c10b103140c81d080c501d525076100310b60003001841c0c0032070401c500503848d0f560304204540c05c0c1207900c15000e0074181051104100c0700d154030f41d98071841001c403002c1a0783e0b6440c40c0440e50422001400c0f030310b440c9403616014014101c112181203503118007800013010074801040c490320a070342c0500f005141200d00d4200d49542480d400c02d060b045651840e0100c0c04c10300c0c0c4010119207500900c010103103000040c1100250b4400146000f08260801c2d092200c0c1c0e071203807000c88c2c003991714a043c0700700c0c1039840c07c00c0c03411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 306131357 1250 306130107 306130127
    0x912040602031b2a0f0f0612060604330e010f18270e01020702010212160c180b10300501030c080d02010c09050d1b030c08010b030c031c 60
    0x440d2040113407210f0004c6010341d0103018038900c01d0b01da1410081ea0041040800700b01c040115401034010012844e2504000c00050391000c802081e40341090f23211300740c03a1110f000c0713000081c0b0f007410b0f00401460004296140000003041ca8500030208584c6240001e040320b00e2886407400b4014002c1c031040301030011f051110080e0202c20041080501401c1080140c000c82c604042d216501d0940038070b00500040c000c0300c0c40d0b2901030300200300c004001201c608990b07104800c946891040c611a0500246500c0301e040c004101d100801e18809400009210848040c5c0f50201d210b4079604c038840c00c503140c001080e003a076480050040850068201455445000005245c095861410f0008410410186034020554401004079000c20620910a900300c0705a0401d001c04584400f908024600d05040d1509000e80706003a610f20009403901c0301d05650101d500212510842c0701000c1c0040300092003101c0315018100c000b090034801207070102e500c880e2100d01c0007100900382030000380414003682c0801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 306132607 1250 306131357 306131383
    0x916150201140c0a030b04020c0a0f050f030c0109062406030c17090313050a0303050d09140d030605010f050406121a03100c021014181006060201050912040602031b 72
    0x120081c9050081d00f0f84035072002d4500d10100b80380040080300c0d0304040c4240e50391a64000014883c0d0005a100e00c01e5003410440c0449144c13003a054855450001030020381a50344045001160a408a181540594040c14090b08100036011030f101031400301c0d41c420508880c40307801c0000300581c1d854012500200905060803684240c48144401101c0000007004510500c00201c1389244e11981004402d449034840540040d00501c4040842991507111b44c01151151500b042540c03103c603000e034105810300384114003080d50341008005650b000203040390805210b28015180904202000d40144a1101c0c82807007540e440c101115068070366140d481b0445030003000c9a240910300342300c11014010340000c003801401f03107a03008040d50b5441d019550800c5084544003100d40d0703078002c10b000c202c400c0c45802d40d8030748104804102c27800c0701c1d0b100714405046107500100b140e02d410012240341004605000342400400c00013002000d9010041d16107160203200388403190700303440300d04030301d80400c0154038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 306133857 1250 306132607 306132641
    0x80a03090615031a15060f0c030403020919050105030105010501020316170c0a05070b040617040521040504050c090a1a0d022b0e190206070f0501060602060916150201 73
    0x3c002c1c40320148071800704d4560140180314540d00c04200581d569510ba070016008003041c407202c4d2404845030050080d0342c01e4035048038285035482c0c001540107507080d034801a00f0050300d115014200303114001d45001d003034240d00a0001e54036107030000756244602d001c19064128a00111001c0060040706005280c2101c0480350700c415000d0398103500c0704030000044819116401c3c1c0000e010401105403012a41152503141041202129203000071400a10807640c60168034101030714810f03045e80b003a803046c155009142c0c41e0f80c01d00040c4021200043c00175010b41c0e109201000c0b00e5581c4c0010001610340101951500411602d54100b40303000304103101024a00100d40003200d060402c0c00710b5003282d0066448800d1182c54020403044541540c61103000c3c0d08140c144601d50103940030b10000b40d070b202070081031611101d40c50711400c04020031400c640694441d80d00b0098603504004840d0000c000002514425400000d41004800548a1100c40d0402c441000314014002e41c404403840c5090014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 306135107 1250 306133857 306133859
    0x1080f0c0d201b01090209010504020a1803111e0a050f03070305010c1805060918150d080903061b0403240507030e061e0105040b0409020a060f0905060304080a03090615 74
    0x90b90003107070444003203800846a40142598041414028902e1440c4c02070841d545503420281800080d61254010301d007446031003185400d075100520403910007140981111001003c03040d0400400c42212451340d9481180780c805035105540c3c0c1a1000300b1140b0813260943c8000c114000300c1d05041140e03001402651070300c16280103407a0030142115000d0001045010350b6900c03a42002218054070060f550003a007088141802904a0f0190503000311040190801070011480002c0208135092012140e107040410300a01c2410100310482c0c02603610b259200c3c0325008020900442e02651002501101000601c140d40d0f07501c500940a015410403424405440e1a0b00058083c00c0003411174003480c850b10700040c880c4541c0981620a040440a05100340e0340780000f048080c100140c1c0442d03220f82d842c03010038010790310040c1c5040244501e0715034100e5109689030150050380980d01181c0140820401c0200007021002210407008407130030000b0301a04941050b1004045144500b44c00c4502514 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 306136357 1250 306135107 306135161
    0x30a020d03211a0f03120f2101180b060f041e1502070603050606282616090302030106060203070203060a06140d031e050702030c01080f0c0d 62
    0x601040b00707100d0720b0002800700c14034201d8607007280d841c0d00f480ca00d543c0c0030b90000f84103407402d00500050703400020f04a03240c0401e5030040c441e1302e911024820030304500000311021030801d0100b403103502001900105d9100d62422b801d040c075050209000419643c0e40380703580c064aa90714001d44000040000f4001d85850f15400011685610001e82c0c0c1561740d40c401c0009991008080d10440d00205680940313081454081c0c194058180580354030745c44082881009a00f002c11816204200c21021490205c1d0964003005003036040124644251f1840f801009400100712500103070b04800d40794410481c0074610b9a04540a10207a080250300d9420074030006002a40080034100181c000c5051311b146489422500e411551a4460030038803641030105a1202c1c40c111310301800c01802401e254403501c41c044a07140c0701c0200d510f4004081200440c0303a00550404104040c9103007002c4c00c08803218107080100d01100301f0000d00c98079010b070b400103442607400c03010303081030100e010748160000724111401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 306137607 1250 306136357 306136367
    0x3020409050a0b0f030d140a02100905030915030c0f0a0302070f0b011508040c0312020a2f010305280b060c0703060e16061d0d050a052118030a020d03 66
    0x2c0e405601c07a03c1c9408896444d03140c085040303440080d042d1102d114180c1c00500d640c5c950342054150f10306602481d5007604141c01680524106280b085010310b99800c080340c200401c41051210f146810b40c014020401c1c1d0240e004122590f180144400d0703a25054005401c902078450150000c01d06c1d0f034201030120811110f101c6050596040340c10f040ea0800c42c1000840305841c0480300a00898503141d400c00208680c030390440210740c010f1040d102c441c242c9842e040105d81c2115540c460034424919500d622800c000b000c02a581001d11b41805641402040c2401c000700a1286107150b074160421082005440e600c02540120042c0131240c465600d4000a62600040d10041d9011418000039070903c1101040f03000004015100f11032015003004001c66040c0718040829014194400d00d441c0340c1d40c0e5035000203204502c210020710600040d0702d012401d1901d0450841007070184021707401480c8115400350703800c4841101c58034001300040030000c4e01d0440ca0060280d0840301400401040c540d1003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 306138857 1250 306137607 306137621
    0xc02120a0f11030c01020c060d06050915040b060f0304170c0106030b1f03080a0c02041103010825061d060706021c0c0f0e120705031009060e01050402090f0703020409050a 75
    0x1d10600d400800c0b151050607210780c0040d0104d801a04a940e548082d460244090110b08026100004482d500c2d01e01150403154203584c800b00ca83c80350070b040003842c40d060180b1040588241c40e85803d01203c60b00060b4a0700015000620300000b20041581510781001919042030050000f03011641d81ea0409511040041d83c0307000b1b00411031184c44507005600000d40c01284e5200d007056103464806d0104a0740b80c14802000c0342d00c030781c491044580090742d51014501030442070015003284c01502107400000485040c00140788400e4510420038160000913003072581240100030403104906c000000e407640b040d414020030759440403401074030120100c807400d0620b0440324010403c9a200f180295001d00e600c00c0e50350006500409a04034131304114008492000d4200c0864816a4a5500090a18402c4100c1d0103055680704410014003107540a500e0740040048004c200c182095004949140001000c1440700003070751b000700e0121031080d81150010f2001d07540820003030070000c0e40e0401514003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 306140107 1250 306138857 306138863
    0x1b090e010f081c030209031b04240b18100f0f0507320a05011a06130603020a05120103030e1e0108070e0a0302030318030d05040b0a0c02120a0f 63
    0x69400894001c40c482000710a84040302c0003407240c580343d81072462188140100d58020503409000b0180c0715207081000f05030602e40e108400c44144041c0081c0070866107481608031036001e14480b001144c0075250103000a4800e142030707075903581158012854020307003c0300002d07410403004410964101e0303100d8a0700528107056035845412410f00e0804940701e00403100d010300400d0601e00e02e070420411942e0541808100c9030003d036081141d5558103410b01a6006060b41c1c01d94448a0990195903990000a44080110f8695003454a81c80380c1c1d015458403801a0310515900080d185407403402a02a0f0b03807030b1035101040307d1180d80c6a10700109102e0b40b5441003802811440030000010010b0002461031788010f07074910015540f02541140d2100c0580d04050b0400040da20200250b24207100900d03140c07280324144c030100b985030b03814075190102d841c0e100c20802c04244814029540030004554200019140250608811380005011f001b68140c02055030b104a64807002040009401c664090340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 306141357 1250 306140107 306140129
    0x70302060f030f131a06120307063e030a0b0603090a030206060f091501030609240f0e01090b030709020a0804030f0906020304060305150301050c220f181b09 69
    0x40310794484044103211600101700d032000e120705403000c0841c0400a540103000415243c25428014410381c02d40d03008000903a08286c40320303149944071088505d0400c0394001070981407540190f460b00340300c481050b0450340c003c0c40b00020125015007903e4000b1030544a004241c20340d282440c0d89095a80c0e08400d4080300540100c0c000143d21740307081405110075450140c030302d42c040c0d5a544c0740400031002c0c0d86005070600d9600c8501080b0900c040c400da035400d50990700000c1400315414800340070300d052580443c01203503525100b40858055060114115001c0355400b04000403c8400241801002e40000c9001c3e032000c43c404240b1b0741d00c040d550f8040d80c0281c80340071000c00d10800859020302a4000c3c0d070003583c0100700400805201ba80429846180310310344590f11003105000274207449090b6501600444041138203901402c50680086002510b41850030b0210f28107000503000320401c1c415090900e01d911020859188680c002442d150b0080c035501303020031005000644070000c00c1c01044040c2c0c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 306142607 1250 306141357 306141361
    0x60f0b18060f0414030a2306090a12080405030909040f0b060a03080301060e1201050103030503190e0a080a0216270501050310020703021f050a0507030504110909070302060f030f 78
    0x70070040d040392803020002242c00c0c509401c1c420010300008074003100d250948144015980458142a00b80208400d1030740d8010411065951032842c15901030070740511908224023800026550b09001c0c0c05041d030f241803404155640703081c00340c15401050000c41c0c21041910030041006040c0040180303280c4900e00040b407079110002072001400f8503000081034840e00300014040075029043d40204a84010704a100c0001c20600050030f42d05e082c1c0c021002b08901205000540d5801c9281c0c4050185034103041100600c454101592a50300c444040d040c420002034102405100780322418403c0e0b18a040501d03016958003001d4001c000c1040d00d5a00c01c41c0705030381c8030310f00c1b034107400b4860407568010000c0c50323804003e0032001c00941c0818011811b5114070140b5540b0500089966102c003107108000003036521b4880c0c0000181e541c010300b060205841d110400001030301c5605040024201a29101e4059449021551920003d034101a41c0641d020030143d148485000042d840f540c010154880d480e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 306143857 1250 306142607 306142609
    0x9050a063b070905132306070206090601030f2a03050c0301020a020709020f040e0c03220302100c0302090a1e120b040b151206060a08032a01060f0b18 66
    0x3107960812045500598000c000c00300302d83d08031507004000c039003200f61181d0141d5246040a240c0052545011002c50b05401c8a440244000c0781c0c4501d280c0003411440c913128001503155201400000c280a002460b0303402441404030000003402110301003004580d0755540350526518076480110b074180700e81c45c90709030710781018003d450602d58203030010405942019100d0020350000c282c1c60398003982c140800a50100005520360103201d240402c950f9908240341d808107070f0300d45020840d05120200c40540b00095000030b65442c0403c540c1030000d6000b40064080b03010348641c81c1c540d9842012000086204103d5052207003441041007400b010850f0386640c501045101d28501400a0414100050110300c52440b03070faa11001400340d402c1c210400303000182c0b0000c3c0e006c0c0015200d0344880b04002880c2800d80c0c01c1c0b0090240d000046017084e0246410350b00600140080307101203190f40e080344040300001d40040c4003901042e09070210040c1c0b90080700029400581c0e094800291b184102e083d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 306145107 1250 306143857 306143951
    0xc02061216020f15091002120a0e0a02060f28020f15010509011701020c030f0705011d03091e0607050d0f030603031209052d010c0503150409050a06 65
    0x1500702c4610140ca600f8005505112024100520340d00d414025807920b0000b2991b188010941c641d10211150940d080100d40305080b02d40c4a0b240511960141d1028405a503030782083d80d682c0c1060341d1050b5900c4a4064000c003040044412402580300224207480c5102c0d0045500480e10020f1012507862038081644503406000c00c4c46115084000a40140201c11f8001010352a01d40302070300251406440c4400f5919591003200c803003580c031b00041004010444203005000c648000d02021080c070b420b0400ca003d81343d01c16241413600c90905004840043c8400014542d044800100115220321240c1040c40d216241c200807040012004051802c941d4044e2042038181da405940e900040c0502c4551000100403448040d1103910074800c007903500781c80b01c020f0324050b8180e603181c520548904110320350a40d03100500c4541070040620403c98002001c1c01c01c2c6071038003000c403030215043c0c4881c1811810a9680d0728003034503603820002d00d540310f61401816450303049408508204564507070001900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 306146357 1250 306145107 306145123
    0x17010f1d0f06060c0a05190204060b0a0215060d060905030901110f07121a150301050109021612111507020c0901060f1809060f0509010e04210c0206121602 68
    0x141e44020040b80303440c103242c0050b00f1020100f20840c5c83c803c0c1d940d1075961915020b500c4ca1a00c00302c08820010441c2428041e41e00104240b83ca8541840d09030b101c047e40f40c0b10050103020403078050f0800211300e90783c0c0142c660300c0706411000400c0000c040741003054a03507101c46000d81c041081c003103061071a6800012020900c0100c2d0000e400d81a00b17102100808145020041d1490300c102181104d101e140d28030018002c11420b611200304000440915094840c1640514031b814410320691040102a000248405601070410b04801481c841d055034600149911600d061140741d003020280e521308041c413400f40c11a6022101d40d010500c003041400f10003400b81c4400100307900080b0040c940075403501d140c817410440d201480d99840c0c0c0780090444500d94845070380399404000c00c00ca070b420903c120b20702528000c19000000e02e02500d0b01079100300085030081c0582e08500301ea00c1080d100d8000c000c4041d500800d040d9070f6490080820007990000d880d410703051001c2c11218959580000b074100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 306147607 1250 306146357 306146371
    0xb12010311031212060a05040c081009021921050c040306050f13030302031005090a1d0102030408070f111801090f0902030705190503010509280b040204050717010f1d 73
    0x81c2c0380c11039130f2041c68001d1802a02964102d98030420218199856008608102c211943e880c4010320306845440d41070000c41e840251090320420440e0085100550900044000e9084c011141a0f040c020300032100c04810039403540300c2c0780c03c081c440610001c034020030442e4002c0e5800d001c20388854584400103071b020740e00c2520f0f003004020920000b9005c0d030090760b80441d05d1003d44d000d040e80c820100e900508111591202c0d04ea54484043c50419500155004649400001c504618081c0c0c0d0303990b1180b04600e03001d008d00030031105c660200308240d82000c1d0401d00240580249030800c0c001000c030800c00380036000c0c0729800c10365103040a42c42c5200e01d41000e40c008000f00f035014903107014445030310394841840d1807901003024080b40d10b890900032113025240e14002011201c0c56103040d1100e01080315000c800c001180603070600482c048112040d042074040f20000ba444e12001c40580b10041d42c2c19482c4e0303040b400b181c00014000301d011462030031901004220f007409c84034000001c4c4a04001c903012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 306148857 1250 306147607 306147643
    0xf161106011419151d0d0320030a02030712020115092c0606030d1e0f09080109050a063e0f04030507050f09041113060b1201031103 58
    0x104190ba5070951202079400c805030441c001c1e400c885a001c5210160381d0403000701c40d440d0600c001581a8049040000c281048001c0c4e01c08490340c4000500c3c0d02100100079082101c502950742007840100e448100000e0002c007140d54800284501a481c1e812442e4142c0e40a41d8034100d6001a074018021145c400d041280c1c50600c40381480140c40003884404242c135041010f00200d03040350f0301c280904207070b5003907030310000c2441d49044400c051505c4000a5404200080000750040c0102c01e4074500d0783c2c2038001d04000441c011148021540440e5681c40401c0660802d4021002d00078040740080c240c074042e1070700703002000e0681d925a1030300ca403803a8a601c444040d0004400790805c0d44142d02c961031405603125161480100400c030003a0015042500c0301d4115010801c200c0c42d0101002c07405c4441030f10340312546e280c0780e03d800404880e0f0700030030790280c4451050002c4511a41c0e21100c060038440b038801c0d131030ba080758100000c40742d4240011110241c0c142180e01051900050f070300e028400b92142 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 306150107 1250 306148857 306148859
    0x9042307050405250f0e0a090b0f0604050d15150303050a020f010e0a0b0606070c080f010e0c0f040905071502100608070f06270308120a060305120f0c01050f16110601 73
    0x4807122205c400c081010080320142411036581c07111445c500500300e0300d0012800004001c00c000b5280804001607118600400081003107450340c01c1c5580000340c10101c003028511305408420003030002d03c9401c000e071a02d00030010007016082005424801c05640c2151160404607040340e00b2600d42d0b8200c8811503000c1480140081d600b20071090384903034064102d0b03041c407119070340d560b07142c484d141c100501c250006450000f90789000d1107021900e640031b8008000074820740c0c1c0441c00a40801c45014055a1505100800d1140801c010801080021002c10b07074500f404d00001c0d00c90a0050f040c07080e550130706400066039400040e500040d0f8030840c10a41565240040035103071101040f20341d914840c0c00c00070710180316031103d00d0b010041d03004022060380c0d14840180ea0910000060031880700d149400001e01c0800e0002a03501c041c1e020341c4030620350f200c004040300d0555014a480050072982460200403000c0300d030802e40381c0282105030048500c4840035009a80c410031141c8080020307800000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 306151357 1250 306150107 306150181
    0x301050103020a05131407200105040b150103090534030804290705010b090703140c0a18120203060115051606020c01090609020f0d1109042307050405 66
    0x1015080e800300e0010009400c1d2084020510015080b03c0c10300c045204d0804000f0303c0400001c8d400c0e0312600b030000800c05840c1550f2100f5030070002030603a42603d80c1c01c615200880e4082d50001508540101c2100c680c10407030101240f21001c02190003610068403410403810110132000c16090765407001e0810f041c141040003080c10003400e0f03262072400351441d5080458180010005040d45c600a200105100c8800c0040c0103000102920a0b81058039040450005803401c508040d040301d5045112a03403881100030468822424984042c908071700b2000c0080ca10550000c03080c251442039003038510603a1b903250040070361048078085802290040055050b044084042d01a40710303c1000c00604000c194807440f400c40d040c03500210394890303581440c0340c01e42c0344c032601030600f01a0899442c914000e07160f60f003410450110519501400b541c1c00420304000328411003915049020b00040900450541040d0303071000c0c58460300d4091072501c1e0128640800c0c1d040c4140074404004050115840216 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 306152607 1250 306151357 306151369
    0xd0e1c020615011808010510051e3001020405091320010210020a0e1201060623160c1404020306011b06060f1401020c040c021905030c0a060507030b0301050103020a05 73
    0x30110b604000138508812001c0030030400c010058132180b000002e9914040c5006560340b101d170340080d841143c0c0011f500803141141c42c400e1b030481009441d08807925900040b503141b210754080d012000b1080180410f10b4034141503000e03104482c41190b4402e110746402c2c0c441415080402409803040320301341c2c885200d0141010182c2c00401e4184104c441080b184440758040760090071001c800940c685421900302d1a041e809052856102c100070081d240c50200007070300c0360441c0710b5901c20303c0e43e01d4080c402d4170449150581e40b42042d05410070114031003a1070f1500248191740107041131460300c2000c0c4113030340c14540b007660b200e5032040e141d4010000c4c0150031340c1010808042e00301c1d002a1101c00111f00042c2d90301b00f0302d0040031401040000c60b0050400a81481c045881d02e038001ca241c81c0d182300003d980018541d02c422030385100c54584607450704250381984120022104c0c5445103410041c00c10005d41c1c8070364840c0807180d45c2044820394500c101420b07150281320180d8044c100e0036091003589484 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 306153857 1250 306152607 306152641
    0xc0f03040c1a0a110f06011505071b050306100b090108090109060f2f09010c0203150f01031401020c1e010209041802010f18090f110d0e1c0206 63
    0x5001c855032440e540d10780c90700900440003a0318200500410403080680e0048003041c804028400a0702e01e805d0312041c85650383c4030500c5801914540d1214414680d17004900301c80c6419046074a0920311142c031200204126114070656006c2d01c903000010305c801183c0b01545050360280040580f91200343e10046952070406009903026569035032481e000540948504c0148410103000070405004d0b00003c0c0040a6501d000c0560050200720000307a1041c0000890f560301e6401d003040f8003078584500100b894012420240b21610f00228148908100c1001102c2e048a1007000001c01c10300440300c00f00d003030707004001c412825948134403560303c851440e48030040200c48200000606040070702e0001002d41e0724201c40054503544408074001556400184440511194100850440b41051581e500d60380c00c4e204a170341c101d90341e01c860708800c00c840d0410215442c9281605403140d96090301e600c003d1001e4007405a29214001c904880000b8092000078820300340c1c1c01405155858210049982040d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 306155107 1250 306153857 306153863
    0xc010c020402210402040501081203061005042c01060c02060d0b01120f0e0c06040e0c0a0203130b09011806050a030b1804120e01020a0b0711010f0216020103050a050c0f0304 76
    0x303002030724090f4881981496a40780d1030802501504040c014841240d0041e000351145411031500c1070030307001088048980001c0c003903684103021510042d0840b081c3c00303140c00c01d42605100c541c0340701c0761031110340075a01c0d58400b991500b206a66582401c0c1c0e202c03202100c0081d00000300b8003500301092103c1e40141c0369220f040c1004032102180340c1b035903002c0790000001c9110480d9190016640280100500e40d00c842007901c03024901410a0b80b03007880441d0042c81c0c05504880011002ca0851003030040d41c0709172a81002081c0700c43e8036141a0382240d0029135400d0300182c54418409460340b90184883c1c01c41d00700c0d8507502d1070007050260440c003524014820303c2d00001145203210075038110713802c800d1145e400748039017007400fa03010000142060341c0d5500d00c60456100d01e144102051042482c070740c109034141003200401222202441c05001c150407400c41c40d43c40841c0700414012411501e404451003607030204810f584e03446001c42220010758041000b80c405200480404038444020b40d00b02d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 306156357 1250 306155107 306155111
    0xc190b03100b0c01090b010f08070b030c12010f140d080405060a02070b0708090111030a021902040f060b1e03010b040902090a0308070807290c0a11060f0f0106050c0c010c0204 77
    0x18a500c0b1040c00ca0b88002c1d9060305613955003892200f1700c4196080140036000c40e030304c003001c45498102c007642e403003150780680c4d40d030b04d60000082050851000201d804081c141c0c1c0001600c3c3d0303902d240115044110b4440c50b080c504100044d4030380c9280401d2078800007070b404a81d20b800c241c00d2000340b012a8010740e00308402d510821001144510302c04025003840361042c0303030456440000f1400148000c4c01800541d4290b030003405500c840750b80206404009511010f030324200214240001400b8100c000141c02c0c02c185407900100c1c0c0341c03200d100105886160101c0e131048104291844040500c02442a0246490f044c402031091040310f800814140c08018543c4102c07a441c1c0d01c490196a110f01e104543c03400e00041c6000030400c0c4030002d2180c1c50603403041c0b0b518444030340c07440c1031003250014604800003000091008005008410350318214456030103c513040d00e45541c02d000c10480c16203407105007000381c0c80006210742c400e004980c250903140c00645484240c0f80c005607980404000100e80c019 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 306157607 1250 306156357 306156359
    0x3120f090a0507092a050904020f04050907020c040c09210303020708030106090311090103020d1403040b0d0509210a03090819170f011202060705011d06090c190b0310 73
    0x41e008003e00005008002c0c2c000400a20b0410790301c907860500103035000c44610702040090415005007c0e107124000558015030386081c0004d42c440f980c412034001c3c0f51300415102c14000700a0f40000c00b20281c080585041001042c400d034140c8158005210f060500024034030252a08150000c10b401c1551090402500300340c0c50b1b0b034500382c0d640c0098120000094400c1020014801c5c246081041d049068610307089a50650300803d09003010840094214612404900c40052041080b10003c00c0e56055140e2612803c1c840500541010b0310460113610582d1182c0c101803114940074039601030f6111559207050703450942503016103104c00080d05c2c2c04806101e07540c1d482100171680511010036564040c08803402104e172884110f009001040c0348102c48005128892140200300c1c010780e011558143c841040c0d19045003d003074014800001d49044410a050020000507401c1c017481d00d00c400d0b1103c0d260300c00c0600c882406146a40b600d1a03203101c908115007200c600056030070040003c1528601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 306158857 1250 306157607 306157613
    0xc020115091b0c1a1305060106170708060a0e0c091305070509010c0302160b04080f06161b0501090f021c050309090624180307050d0303051f0905010f0803120f090a 72
    0x405005c17030340e400f00b050004d0300309010803000b0b001c490702400440c1003c040a00c000c250b500c541000040038141440034241c04607096542c0c80071840000d001c030401000742840c007500c3d5002582c00c02c4800c10300907081c4000c2c901c2941882d004d914031881c403590b19542808000f10044803964a4264154150300401c0c03401e0f0202c8400c2c8501e02e000e4460101c10583e80c600d0503181500d44450320f1445021a0001030521450420303840c0035100c000701a25081e041080d0030f00080c1040e070301c41e10700104a9842c14141d901000b455640b44d80c4c065008482207021b1101081903c2c0c2107030914503000384a60001c014490301d82c0b414440d4613801030300c0540b51052030100c506404120b030070403500c100c1030464041803d000000030300c11400700410094024040321440c00001c1400002d5200c0b0003014951203c00040440ca00801e64448940d401d400d1072010b665034000d0100140320030301484060126261012440b000c001040381d80d40040043c010b419a6106000300e0204c2c000500070900f9402404a00404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 306160107 1250 306158857 306158903
    0x224070b040302060613090201080402120f16061e0903020103180f0f050c1c0b0411060409060801200723030c01050a0501060c03020a240c020115091b0c 67
    0x40303503209800410741820803074104284205098031004805003003c0c003940049c0d0740144000e0300103a041c0c400b0414642c0002c81c0341d00301100e01400042d14800d00d43d40c041c40311020480c0f5001c803041901c41111021300d00c5103c0c50048140300c0ba180100f0505002000154030039885040da0418a0901c840014030344e42d02c1015909d01c42805480b000f0031241458184803003807122684092080b02c0441c20800c80c0d6691180038500004043d143d0701500b00001e003480b44040e24100e0005005003110745c0c481d2104e032002c0041c581401040c0c00340d031070b10400030501601d8203604a584031203060424104070440d901c0c6003c000343c5003813080100c0c44510209c4140e17081040a40440381c008130022400b0304c0d0402c0b03004121001603000c401040700900c0c2c0400840c2c0c010038034507525500700e000550480b8424960100a03100740b083c07141c901d4509084445080c1c0e040d40660315140940c0d24180740c540d0b80c0c0071040180c80030304403100b1001720041c140c112010b00032228910814403030103002446030304201859034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 306161357 1250 306160107 306160111
    0x21201090506090916170c030a080301080f0102040f2607090b120c012a050706050a0e03060103021c02031014090d030e030301211b0801180224070b 65
    0xa24152100705002082c60012202580003440800a0038065429151804910f00e030380f060000940d552880e209400500740042e010348200541262004c011600c0c10302c5090b0310034803802d580c500958001d5003000b1418002ca030215200e121180d21003904284c420401d200480403030451201046d0109404c40c503081c45810b00400ca0000000f400280e24018030042d0080303c0c4484400d90890070719020240c1e0802400e039640002020800070540180300d04800ca90503091014200e48548040020f2050348a80200031015507651799002c0f01c00042c0501d6960202030000070b5000410710903c01d014449140203040050000b41143c05180519001e80c3c2202d170201940c0d058084c019080010080b020460300d244001940b0b0200000c8420cc1c0c0c0c0e6070784a00041c01249000c02c0b041c524804a8014580601c0740650080c42c96421141e1615944030004850310074443e05508041410b600c404000001c0e48040380c01801c16000d0f003603076408801030792110302c501e149846001d21451002c02c40d40c005046c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 306162607 1250 306161357 306161369
    0x6090f12030a2a0906020a02060d05040f05060114010f020606010f110c060d15050303250807120c030e0a050607170403150c1704050a060c03021b150601021c0f0201021201 75
    0x80c44007a19858010013610550300102e0540d0301080a150040c0c45650840c0d001d003200920016458903245015001225100b4000d8480d20641001250f84148a101860b126801342c0720758249100c0140241c2e220f13441120740703502003180c1e0a0010f0282d800355000c1c3c013a01d240300301a16a4154408000b441d00c2d08808089000e0a943d102d400c0303802144a607409028050440080d401c11184418840304a480010810038082040800e0f0041290359400c0d00c0c9115030044011600c3c0042e03000051000125401c103900060480031150020b0a00741c0c2280203031200500a5480d002c196100c2c41031811421b150301102e06000c02001011817020f141120034036440e400c021518154408004200801c0c0b91040000201e02c0c600b404002800000c02450b015807001020840d5040f102d0107500901901c050255401c0f1407503070540c0ca422000c540043c3d05c403900c62403c0e00d6612203600480c0d80c0c24100f0780e0241201030700e0301d03074148a500452608501c003a2a100140c5804c3e55903407600b09010f004c0c2c0c80305c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 306163857 1250 306162607 306162671
    0x100f1e091b060e040f050906130501020405090403030e0705040605010c030e03120f041e050607020f0f190e0a020304021804110402120604231f170f06090f12030a 71
    0xd041d4a018010340d008003240d1542441170342091800c1c223403200e4005d88111800c3c1c034a107580404122080d0169801450002d100359901c3c83c00f0300f0007502030082c00b418a1041d00404602140383e10700740c4102070903500180d440b292103405698060f5020404050543d0381449680c4441c540c00e60b0303150051041d007051003045a1994a4070128400d000700c060a905c01c201a051401c4c41507851b048140c1c1c002c0740d011507405c001c2884090100c1d1003d842603081c1500103001081455004800071074050454441030041516a41d170320000000328001610004c2d449003030042e48100d101c00d030804c0a50440d000301503599100b0354000001c0d040340c2c000780015a544251008002e12864580310b0620055900b1401542412403120070304c107410070081c0070980112501b1048000481000250301c00707008249146a00d44c4004000c1d290350f17078600c062000d03044c81000d00080b02400d0100340300300f0043c4403000801a0310041403110301c80d900000d080c1d681d40d81d0740325000000041c01804011072110810700c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 306165107 1250 306163857 306163877
    0x60203070209010f05030a0627061b1706090601050c1609060501051318061d01050a2301080402040f0207030f1404030c0b0903031308100f1e091b06 65
    0x502c00c1e81c0b00141e00103141400340400402c502d440104140a04540c031034000642020345400640c641c80006a048a040441031110b504225403075024080f0f4941158019000005882c000c40f4414a281200a2600900404078900317041110420350003582c14180282865074440d1702d507151002110f281c145030003d044007084140b1041c810400034001c01c0c80d2039880c00c41490030030036a00c24540f15004406014190078007007102690311210140a0040c5c0c5081107018074240c840800200380280c030b104280d407040019800c0c011800f101c21a200001003611032042c10801541c0a80006000780d800a07101e0000000030320b0030b0f10083c07841a20070349400d5140e280c080e42c01130881990011811032540204010b101180c3c00301c100300102c41d110100f4542c0c039404a000b290460103248007010101103122404500314401180ca000310302c0c20b43c0400c126141e07411170540160341e58103131604135919080780c0854001840d40c1150316442c0c0100400c1d00c2503000500d68803500e01c83e940c42000001c000700d003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 306166357 1250 306165107 306165109
    0x60703090b0c0c0c2e0306080f06010302180901021b0307110301020a020307020409111203030f0a020412110a08060910140114010f12050a0603060c110d051e040602030702 75
    0x81c5a540009a04100605040103c0441940c03038054031090b030b02c00c62004580007400b620480001c10012598240019012094640a4098501da020710002d500543c50788022842d40060064104da800802c1c600b01100b0007a03000b1080034020b402903010795020803200303040c00090401e50105080d42030003560365008509100c01961103841d8000d00c240d0040014050f10b0307030300005484040790121400903400f207051521380c80300d224191040350044400900030540c0ba4000c40990b1041d610420000c081c0d9940300055400c9101c0c5014030014081c0000702c9001040b030800c0b10058019000e001401d41d04d031103c0b449450544200d402045680c42103a400001c0010380c05581c0c50045802011041d0b941005202464201e00c032056074100300603c09138008041c441e1890026500c5200810005030905a4914001d44072034082941c0f070a0400340602d00083c800c0040e40d103c5e1169801030107003480e180008850607030010b240d0a0003c00b03104001e5080501e0000200010200ba8000755a6000c1600c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 306167607 1250 306166357 306166373
    0xc0f0a09030231180f05030405011b080d0b040f06030804093207050d09060506120d020c01140c010e0102030f060a0812030a0f090b100f23010e0306070309 68
    0x5441d036450303000402c5004581124550304900348154040f030109909035020520349140d0f84001002c3d125007084010f110510602000801c107442c400e03a0342d111600340354641d242d00302582c1e28008223800000c01c1100c40ca1103056001d0744403040e00400204080c503102c0071170700a40780180c1041e6100c0000180c02c0058040e00d1141080083c1140b0050300400c01d01c0120f051042d211201500703480482c3c0c000078080300d100d042103030703400c07048072004201d011010f08001c001080c08884042c0506011030140c4c10754480091800741c41601980200440150440111050a820000d00c06862130900c20103644003020b01902e400c0a03140c0c000140c40e03161a101d01c0601c0070000d0b0509016910000c0c0601500c0e41c0030518a01c0b00400070880d5549485444180c0b0080c0503004400400a18110060081084030b224290080700d42c03e501a502c01e481b2041d6841000301c034410b03402003e003490700c130101c5503d003920311a685c1041418031804890640002c03030305103e000c030755100c002541c0398030090821110f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 306168857 1250 306167607 306167629
    0x7030807140a0207080c0f0a090203060a0b030a0c080c0c0d1103040b07140d0f0203030103110d06051602060c0c0a0b060301060801020a200c09061c020a0612050a05060109030b0c0f0a090302 83
    0x491f0000701d10605c60020402c020350078051000c22079000000202242c403074001405c0100b024182e000c1c0d407894118141c2c00140200c040c2d84002601c071102190104035001c0c00e0f41c10007070505001d440b03402ca604e0800e54070b2005841e940d0803140001c3c4000154520900040e1410341c2c01184800c0c2c030180c402c510702c0d040c00d1901030102c2c284520200e0070f80c11f5590000a8a056941c48485110041500000959080360b160001401d580c240001c2200070310001030040e41c40d503019000c8410984500000c22740b5402440c103008400d901061600700490038640760150440c8026000091b02a00c0c0d0a01d039099900c8003230345c5800f107108001d03010788040da1007000c61100c0319500007501c000b1610b01c0c0000da100a014109900c41c0030b41603051104089000c0c40109040e07401000e1481c41c9940d0300015040224211032054001d18000000303201c903219005103845101c059483c0303404030f802d555170030040900140c04008490028003030710501410242c028a603d050f00c0c0c9444442138614810080c200313420b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 306170107 1250 306168857 306168859
    0x90801051b0403151104120308100305030313110a030b090d080c0405040203070e120706032009190e04050a060e010c02120c120d060306060506040b07030807140a0207080c 75
    0x40e04404031000864281a1000c3d00da02c2a480c103110355440c0c0b01c43c00030701005402d0696405c000079000581d440205030500c202c034400e80b00c441c026920b104416400004620001e4040d07002000054104110050200c0c9000e200e0b041042490360304801043c80b00c071013034200f16903202c408024861a82006c00245009a8061402c4903503860400e009200710f010340d125050095030044045846140200304059030b500c80a040207801009154600307a4a81552081d00d0100e8a00444030f0000039518000f50040364414414924116240d01449900c030340f02e00c444182d010203c1d81c0868110503100303555000f940100000c0c4084042d85c10305500703c543c10714000c10705070714245016080e1034001c111103110035150420542c844403a04060790078802284031045109500203043c00c0403c5181c0c1c4102c0649015410800c1800d0300c400500c0024401e03400703812880c043c180801000030b03101c4c00f48158841014900045140e54400141070160884c81510000d030708520380901440c40c3c1040300f03024880f8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 306171357 1250 306170107 306170131
    0x302030606060a0903020f060c03070c0e0603010e0606100903020a1202090f06010219230303010f080a0c0b090d0b0c1b06071418100521060109050603040606090c09080105 75
    0x703c030000a0714148543c400240510b040c5000041590b440c0c0054030130b6101c9010a580e658403ca180001000b000c1c0e0003081d0010f40d5107000700d43d85041c14030a900b894407090b4010701c000c0d1540010032074090125440d000c00c00a4034400800140c40307043c03811008ac514031000c03000c0c801030ba104000a800700203242140303800040d000c100d016a4002000c2000a8000f500420bc05100d820a02c1c40c403a64400600f0800250900c0b80c1600040000214125000300c120201c055488552a940343d501a410242c510020b010050080c644204000d00f0340100051510100c03403010340c1c2d010f101c1c800c100ca4006884d40c0105550764004001021203068580b4040a400240380c29080075000030704107100508414004035040c0da011082000105030040002c0600e0100c0740880b10080031680101001014040600ca03442142000283e00f1406840c058650300c1045042405005032500b0043c02076490702d0702c1715000030321f0010a00ca681c00d440c40c1030390f4284402d4201114607003500d00140a00c1036480c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 306172607 1250 306171357 306171367
    0x5070309050d080301421709030f0309010f050a0204140406150f020724020d080906060409110406060914031f230f0708010e1603050603031303060204030203060606 72
    0xc3d11042200c0c19070781c1010a0040003080140c0c0c01c40302c0701018819030081c1081e581d031610b050341e2208080540300301d2541e45d5000600d1304400d01d0040042640c46100f164800e10100c001c0e07140308805194000c4208000048841155881c0c0c029507a0030b84424143c00d50005050121900c4c20003042894074060340c0c1400100e140c44400d461211840da54441003220410b810b880951081c0035600060940100010102d0304d031000c51000a111107003074030058801d4443ca0a43d55006003c0e030303849518240f018214540d0341009000181650000445000d500d40583d100256100c0c0f00c1c880c0904008c0e9160035101c0d0070b0400c060101ca11003c1c064dc1b00f5448610081140309116a00b0b0b001d25050a00200e101003140728180c108003601c0e0350321010700b00d0041c104041e8441c200300003071081c0e4656440c4c4100c2c4c0d03610301c0040803603141a01d2080b480008c6d019803c41c01ca000350011a0810720140851349040361407988244454915001140d1117a00001d04106500d010001c403038208508a820f00d01d04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 306173857 1250 306172607 306172613
    0x3080609070c170d060b13080f06040506060d140607030c030c1b06020d140106020105040c1a0a0f050d02071a060105030c07060c0201060509040f021801080a080d020702060a05070309050d 82
    0x8441c072003d0b03400c294100024111504a055009480280038a460941c1c84841c0502401c8030410380d8007600c0e070303d0700c90b101d150404440c000511501654115025040795103a55080c0035200c0d13100c85054859414a80c0000c180340c40070003282e4400d0000d558002840e003d03041000f0143d40c0c1c040901400c20000f018030403001c201e9403140c080748560000700146d0702d1100f102914040c00102110851503140070000140071a01904102e2040d0b10601e800c0c24220340f0b40c17040b6242c240c441601e0480484003800a210164002c07001200780108a0034120b0a0040c2c05440c48140c0c1e001903000c80d0840c4030210a0001c03080400301064228009003400340c2076107043e400c4a540381c083c501001c1d0000c0d03140e5410409950013075102001419000e001e20742180b60030b080c010360100950782c08900440b4029034010380003c45022040c107171a80440604114030b06620360889540040c0703150118144e08000342401641e800005020039940c9840361903c0340d8541c14060480c144591045000b45070b0380c190b107400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 306175107 1250 306173857 306173873
    0x905100605130605031803030c0714030f0f030601021e0c040531030c0204061719080d02070c15090e0c04081f140c090a05010e0d030c030c060903080609070c 69
    0x1503d41c1850107507182d42d41c503070500e0b811a1090710600742c1404000144881e07444450000c101060044203600601649451403503628842d54490307502d90720b0300f841101e0351410301400564010303505204594602015001003e450348011a0b40b08069011166040180c10240150b40c0d0002540301c420041d01804070444065550b00c0130450b005031340c034042c0d4508040c082c2010000850700030380104626070b101c10750740c81c1c000207100000c411846050202c211500789400c110407496446120581862401c06c4e40e0f0b40a5082444203c0700514041404611100b442c1c2c41e203410b04516a403100c101600d0000030084e02d003006400b0715642c0c0810042401490000102e00700811301e6030003003044600d0341c5120440240700100c3e031514400580300600814646805c083d00034028110b078581c810554039801035611038400c0c4110b80e0800301da0703041c46010902582002da03500d07001c3c1c00c00c004101030703079643c440031550361907400c0b4003080c1503200784405800e01001890b031002583c181080402c80b1500d42e110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 306176357 1250 306175107 306175109
    0x3050f0705070f120302030118020310210501090b04022812061b030c0f0207061706010e060d060603111c0c050408032b02040f060e0316090510060513 66
    0x10038020000348402c1000000c0449402090300080e4940c0c0706000603c0050285d032003842464141f801030b9000c00074400c04c62080f01e0054109405010360760b89081540200c0342c805029090003541100f4410010074001c1c001d0692582c4102d110f65898a860f00c100f20752107003080d2182c1402004a803d200000d81440084001d481492450100d601c04518110002d0108141c00003006023684025114046d09030f0040147c4000c182c8494400c10203003231040307070b03600e180e803003000b0000700c0c240c040304000200c40100b2a084031040c50000e078035107070050101b5856841850302c40c4519550300001c00c141603141c40796031400400e080040e4030f00124969192503403000d69807115100c82e642c552a044490181e4222001480210241d944518407802401078001402952103070802013100c00d0490800c541c0b0031a8162908a128098000e007041c800300c41c60301d00d00c002540c05204013280f4902e51001e0201940c000c0c5015400810640341c1200940d40851082d4021030078880c041c480010401003e001e064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 306177607 1250 306176357 306176371
    0x90f030c0e01091b0c0203030918040b0f0c0d0b040902041d010e1c0503090f06090f070806010305031c0204050604450e0705121c0504060e0f310b0103050f 68
    0x141c4175685400000e0942c45100301e031507804804100c840c0000000c19001c94411400307610522a2036035040c00030342806030121042110108100b0007803440b10259404841011000b400c0090243e80c568085400c454a09410151081174203e0309030310828240181032022958078041c10140b0780030b0400d41e42d1410000c500a0501c0000b00c0041e48207142081144000d021010490318141081811a51a064040c40302c071041d005600b80400c1148001030018102e0303038001c0003180307000314441c00e0400b51f405240d05060a25000c100028140d41e80c0e0340a4009040510302c1220404680304554542000070b0700c00c41e200c514956180d14141903a1030303410509020135031000c590048100c0c60310b802c0107580d80046901c00ca8010084012840005212000300311840c4401c811044d0010b0130340d6030740558840c0100113a181e40c1414078504009103150003081c8050001c0043c030039411074074100441094649000380c4078000644403d005c041c0200c4c20407038001c0c04c042100d070038481070108005100a001c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 306178857 1250 306177607 306177617
    0xc050409060b0904120306050a050a05010804033b0414011401110102070503190206092805010e0d0216030510051e090c091b09040507090f030c0e01091b 67
    0xa4001d00c00701d5003242c80361400003009031515103428a460b0030400398114a00c030010b40f9154010426003400841c010030b5900040c0324540c510716002c011140107000520480400c5202b20700100341c0015400d84c9a80f101040c0c41380201901c01000c0c19000b07800ca81c85107031145007050200301c5003d8200c0784a80c103440c1003000c0c000e041d44615005a42d4000c082c4e0100200c0d41c030000b00101403142c003101404000600c1c0300c01403101844100126036515041c1c940a200d600181469131800306401503c80c0781c01c0c101001d00d075828203540c560508490300000004920340100114411140d81401409007030f4010b100a0b500607419034541c250f9030104400300651983c1e6803008078582194107030107200c1501d4035181d15080707403400c070944035114441482800d0003445404c001c40c00c0f022443c10ba5000010360421101e0504500b181004050400a081c14091014480001c100c810400c0e07903040241d0700642d00c80c142186404010310151005910118140c0d18181111540000300d1420a100e06014589 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306180107 1250 306178857 306178871
    0x3120804020112110d0c0306080a0f0b0903090102030f090a030c06021f15090504050a171309110a0c0c080102040801060e0108070f0b28030b040506040506030606150c0303070503011a070c0504 84
    0xc10750084c820380e001a005445082400c1d0200840c80325112412441282c00030380c43d8440b1b082853b928000e01300040d0160300140180011880b100005d1704030482c006288505680d5251543d0800a080e50044c0c801078100d0203818003084500314118003070020785641040b141c03000241d80c8460101c40c0c061100ba6588500204060100401c8960314050300050010b010200c111002c40e8031741c0c44031002e140809005000050909507610981c0e82071501d403003800745400b103015002caa550000b00821108803030407210100301910244042d0003d0002c0000004030309007810800070003110164000c0c8101d0f8030800003800a41d0022054004445010b10500d884a0f410001840c030f040844100507602103030400d0070140c4070340c1a0450003801c0c1c401d940402960f100c0e038042c80241d8004175192600b6602c901e01080d05410805006240102840130705818905020300c5182503a02c240d650301e00081c8080b0040c4107401050815001d03a00601030020710749030b0955248a01d0800c2440b84031700c9144c0c0c92423 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306181357 1250 306180107 306180131
    0x2010206070f031409010b09011a0712030e010903050c2e110712030f0c1b0308060d0203100905150f0114010903020301020d05070323010509090703120804020112110d 73
    0x8a29912401c15800603c0f61170000031550007022001e0f6222301c03c1141500025040014000708100c0c460943c0d5064a404055142d00c40c650040900280405aa50035030741c001800a04c80d92800d01e1007075a401c0e0f0b880e80031482103842c0607500c1490030030052181014049007a07403030007104c52231410150081000905000d40030014061104040c0c406000d002103020302320752640c003e04018103400c0c001c0081b20700001c021109480b4852034041116001056507000c02e00480a01d0b1344440014181c2d1441141503000c41e047c451500c52106aa903220b03080341e020454103102032540d9101c200d01c043c101d440d00703800841c507045042c070405144481002000030a80d1090107201c0142d50081c0c001e5548155940705030b8010302013140d88100003494400f58501001c03003001c0507510050803503081141a401c0ca010082c0c202c0024020006c81d2040d0b0000000145480c885404a503246807202e284910341800058560410702c540856540d1400c0a544000036000080c0c0e0b0499442d100002004010340b2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306182607 1250 306181357 306181361
    0x50a050a050c3a080a0c210f05010b0a05070f061d0f12030405190206090402040323030a050409050a0f0908430309180204080c06040f17010603120e01081302010206070f03 75
    0x1181010300247c2d11080040c102e9050708005102a40f03000c003007007281c0e1b0b80c0c805085140030b010510400981c1c1080254081156409a01c1104d070180d40000b880041c4103142c000c6103603210f24003103000c0d00149010300c80b1241c140041c140b40c01200c0003091030340c0342036501c081d1034003840c0c82600f50072104030360800300755241c0700d041e24100d0300040c0003199a1512400c00d000245101003152488010f0304103184080758010041d11500030ba1034a80034213043c00c250301e0707202610000b0000440c241c1d4810110200800b18041c40640d940981c8500c1c1d42d42006150140244802c9250003044081d15110020030322200d00c1c500140096418000328032012918040300e580f078182d40719080c0b600e101c01000500408503801007003203074440003c403605a1550403e0103000e0069105104e03403444030b400708100d03424460094410110070400001503141d1641e41c1c1e1070b00e9444500321080003e40c2c05100084d80d50304041000d80055205901080f222503075030000b95100e4004142c1d804004448840020b503070301075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306183857 1250 306182607 306182627
    0x705010f020715050709030b070e010e04020d06030308010e0c1b0a21090801110301090c021c020d03050919110f0406080a02090c030106050a050a050c3a080a0c 70
    0x9000c2550b0780c100c1818801c1d040448080c554102528100c0451107260041c1101421268041110b81443d0b40c0d4500c142d44282a040c4040d050084020310404140c0d03640c4000c100026001d1400958a811401e00800321a8160070081542710204140615061400c1c25150b000000d6204400c035a000c142510741450301d11280207141c15200800054502803890b40401e20241c0703036403081c4400c0d9541f4100fa00740c40d02300e41c51800402007000180a20001a0031103001c0384441d0045851b040a052484814042e050403a81c0058104031343c20207038658180191500240d482001700354140f110312401c0e0306134580c51001040e4900100d40f61455488048c01d0f5001d450300104204000c035501e00a0f0742c4c64a0b43d82c4022440350241100080d140300000c01501e040c2e4810703a540342d09090090350256015800307440c0003c1441005d00006000c1001041030300c0800204c04801418124154020342004d44001809880c111480c1e1080104540c0036290b254054060000400c05004a0506a80e8034000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306185107 1250 306183857 306183881
    0xc0a0314120a1409270906130c0e070216060f0f0e090a050402010e100314070807170901151710020c03070809150c1b040605011b03030609051006090902070314070501 73
    0x8078180b82e512002c5d105091449610840c080c0d0b062552031880c0d42c4a4440c4001d002062480f80c0c1c1c10500c03c135070b10780fa041548060a4012541901c0000044140760b072569803042001a060b00e024a400c2513105042c608904050300b025401070070114001158404000c240140955032800081d065a1190511091020015110656410115100030040d1000c05180070030f0000301c0300030501d804d100b148018440c03d955540c81c007400401e41119100751001030f144240c15921142140703003190314210004c0040140c2d6070320030340303c00e03640b4080707030800c0c50726034555000342d20500480706180d001104441c10f19500c40d00040e070784c21080c00001c4149030075169800c1090000301da5100058400a4404203504080d2080c414003440002044140c1700c09000381c07800035075011494507a0801020140084500c00e040108809031903945090441300102c54100c10040070b602c040020981100c0c0c02d0018082803802540b070032160307172030190400c000d80810030890764002030341a0522500b076019100c9503007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306186357 1250 306185107 306185149
    0x306011e110c0f090103081c020d060e06041a0d061103070f110601080a03030f18080301090f150302280b07020a052706030c0a0314120a1409 62
    0x1102140101441c1d00c14440d54881d1065100b01071440c40c0051040802820062207007076241c1c2940e0b207180d02c941110780000b2070001981c000850441007070001c0c1102c0a0304020009a89261600303c402441c00544080d0090340b800e40000c020b00d1480ea040d00000109840a4000402510300304004000f9400318100d42e0901000b400030300341e48000c5080c00d400087d40d540c0004a4a0382486840d00b41c03e11035007500d6440003482c200028004d41026441a004001c00540840c26688150031074031107000c202c41d4500b000006122103201c030b2140c60300144517404e00f081800c0303e0191000140556000292003410100007450441280000a030b201c101c2a149005810b80d035140ca000081d08001c40480c070403201d5500108650500842218041c0401c5540403540c80900400c2c0c83c0280b0090b0400b03415024810b80d140050302e91440c1e0000441c41100001c00607668005007504008046034800201c13901007106000e0180d000344640c0b20b06149a80a9030b5481905001946100d07041c544101c41031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306187607 1250 306186357 306186407
    0x150c050307060506010915050412030c081803060903090d080f25032c01030911060a121a09040b09010204090e0c01030c0509131107021c0302010c050405060708030601 73
    0x101504150300480b0280c0301c50703070b0342901d5018940c0d807201650f1000c00012303400e0004002c000078248001044500034200108106865151250720750b000941d00d1440701a401e02c0403080c0e041c00c0040c140e000350040042c504061462000402101501c2000703043d9500104800c4c0000038900c0449c0d409580c0c42c0b000b0441c00c0f59500540c10f412813505010f1b40402c02061701384480e9115820800200e085070444005158100310044d0004e081c0c0510907628540701d00c02e02032150700d50800422242240342c80303803d800e6103815032103000d540c48180d001440030115050400305880c1c2030100e54002c0ea0000c0d881c1c140741d48034028640240500c0d030000660501f071004500b40080302141511041c4801e81e0140100a118503043d146841007040c0a40c018260030a105002c43c556440006030810401c8110301e40040e4ee0001043d0320300803000420400391181a46041580900c00c10f0f40310304440c1031079800c203841d04000410034040c442c0e000d408520000b0005119130300c500080340559406085012580d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306188857 1250 306187607 306187613
    0x906030f0d020d020f030a0806091b0a030207210507120c0b04030e030d020610060e01110a2904080a0c03182c091b1c05060727150c050307 61
    0x1c03c2e141d40c1110142c001c407102c2220f21040441110341c00e800580752619281c50381000e011070084011b024503591000c9a02c01d1a4905141e001000490269600507886981508291541c41c4140f01041d2a540c900e40c509400c40740c210054802c03858102001100882164100350340f11440d40307800401c455a2001000f00305a00700b1060b40a4460640490b401c0c0380d42050300342e0b030b101e0f001c1d140103031b1044503030001700503043c441c00c0503003e2900189804118900d0f0a50101c1c64841004812200c044659038801c490010503541c680c14a6000711a00410f81400e4807511058819501d05400300600602c0e1070051602407045120000c94405004401c56614541c1c440d00ca1002441c84003041c001a0180440d060700c0c110315070041c80345601504601150400d1500404100c12120750489100c004503e0310420441f040c3d01014000e4018003200e10705140010040580c84441060b81410f01275512060400404581e0603914419820309503c01012815111000c128200400d607100000c0c0315010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306190107 1250 306188857 306188863
    0x9020f0f060c031306080f0f041101020a0503190f0203160b040c1511010507020a02030309060c010e07061e0918050702010f09150e060c030c0a09031e0b0606030c090906030f0d02 78
    0x12078174150703501c0c0c280740c50708003c1c802d003000d00b6510200480b07281d1020402141d00b541c01c620320400d0500440c0c202c80081e81c0c41c1801c54014418884d400105180b8902800d42c00400c0403040c0d032001e2020310324006603c050b0003041a0142006880802c01c0700c00a402c0011404000029082509104200c114207280c0184602600505c8100950a141c01b00f1801030001420300d058540c001d0285040c182c9020900020f5040003551104139900c030a03252282c40828046800034180941d81c4400c103080d85956001100001002c07402001201c074000c00c00d006044002e59290100044080b0305501c80b44022800340c00e00e940b8403075815190000802c2084a1101c0710700703040f1881d1200b40540041d8005140e102e000031114964030810030000528ad00c00d00000a00100080d4200442010307101c0d01ca8450032040060301055150707820079480300340542d0109642e40404110f0f0114598a042541080980503507841e41c0e00a90508011641613603040c011a86012800021140358171000203000390703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306191357 1250 306190107 306190109
    0x9010b04061406040b0d021e04150203130501031509020a1716081603090b1303030e0a080901032d05190b1e0f03100204060f0309020f0f060c0313 64
    0x44034528040c0c000401020200321400d0040c2c0040241d404d051424180c441654000340e2402030155003000221400e00e0500010800340842503403940c0c846040c001586048420354001d00e080d5403045c0710b440c60701c0400d00211400d07070703c0030b2901081d4044d000d110040f8400554000728101c50004c1018020554000c1240071a800780010845540e1a500c80401500880da8000d00000b42010000b444640c9541c425800314103003841d0000c2d0280c0e441c2c0360080950340c140d540c1095000b410b054a000e143d898061034001b58a0704002c1c0c13109481c1691140d006125808200741495101c00c0c402081c150b41480ca078103980310f0691150300c00300c000a0110020070741291203005180348404d515880140078411140c1204001d0319141c8005041148040756000813a0311039840f1101558dd40c510b07444c00d1000360740e09070840002580712424008040e11a080005000e4101f500c1c00d440b181c00340c1d035103c02d071240c0080143da5001038403810341c3c0452003902c10303100010490312000840c0c100d00003014036088 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306192607 1250 306191357 306191359
    0x90105010e061306180522020306130603030e041a010f120b060f0712140904110d09050703020f0102121c0b220b0103020702031b06220509310f0b09010b 67
    0xa40c1c072600c0340704005548100d2406009085087e8120304d12004a80c1d009640000c00144206800b044161821042d26a00d81080303000413010a140c8103603043c980506e4903000440311215020040b40800204003040062801d0100941c1c00f01140020000f030f0300c04d40c03035041e015005540e00c40a80044080c644d0010108460244000c900310745c1302c6208451031403803400e071244440d1500c02c100080001800e565666880242d100300140601403425208420442c1d201c1d40103003001603d54010071800c0008949906d040d908010001d0f403400441204443c42c02c0012040810558003000b424001031000c00e0b4907035040120448441485a045c40c0c2c80715041c1000042400034094001c0110140e000b100b00013074240d0311a5a170000a02038802e8441103049019260b1803c2c010301f00b00025031030b41c8030501d4400c0000c039010103200b50f003064800d2951152107030100000c0c00000305180204d00c0ea050b180302c540c580d0b2a03c407100c00c0000d00c80300c05134040d810021902071810509255402001016012 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306193857 1250 306192607 306192647
    0x30c02120111131a030c07030905090a0e070509011505131d010905010501020c060910020a0204050a020901090909030c1403120c0306030606010e10050f090a0602070512060105090105010e061306 85
    0x84d080c162028240c140840b075407400d5045403030f211040701d0281c0006504030244101c01001142540350000060b1194000d0440411208a920070050900c0f540b0307042240580710b040010301902c800303680c032207011042d02e142c8290358a404d00b03030a823603614040d040349901411060545072480d4030030000038180c030000101004280d9039280160b82d80c1d082c0c403201540003441030000c00c5807454910701400890072940181d801940702d80d40014104c50049420b00c9501d070340440d004440c1e5034000d0030b49000c0c12203032408000048094a0150600301500d100402e020b1b0700190400000800f4016110f0f14051f5030600001410003c100c0c42123608115940ca0007803041c1310000d2129031003844c001882c82e00162090740030030300f05c0c14120303001d41c880000c07000303032490401005213161100da140b80010311843e406042c1381ea081c10108013500352000500900b07a4800c10042c81644d640160060442d0005d0030070300310300101c00c80818814007030306900b410140d0312050006200d64106031421240d604034802 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306195107 1250 306193857 306193859
    0x6090c030706021923010f020a0f050301180216050102031003030e01050702090c13050d0803060102010507050403150b04090506090c09010f0305032502090a0f050a0e0a030c0212011113 81
    0x208903030307801c3c40c4440a5224074100300600040f5645d1050041c24481894010070100b0110303541a00355484031150380d14a0742c2c0003031400b198540c40f42200b668100a0716109146525008006400c045101401024a54000ba15400ca1030043c41c1d4400956403110082d03460340360541c40300d40038924600c002c1e4040341c1155540246988194111841d259004040403c61f131210780400380312741c01003002010b8100600d40041240c1d9144561203140501c58850603aa03490a03900083c2900c6018010000703000e01800240006460107101001190701c2e0350002440407140c0c40003d010f090140c0011b08a4010103060100791a00400c04a20450040e180c2001c0740e40c1c0c1e80c032006100c0d003c0388005001038009100507420120030443c442488541c5410340da000586540014010302001d0f00d012604650701c0d03800d004c651090340107255001004000c20410103c14142140e11215100001010850720242c110b04551b00c2101c002e1481e4410302c000c100e100c0107650340c100c0aa100681348e0040c2c103203180c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306196357 1250 306195107 306195119
    0x3150a0f02090904030305040203250305070608041a060102070f0b0c1b010509090613020406111002040303270306020409020405130e0a0b0405071802041d07021e01060806090c0307 79
    0x71520540d8015200c100144c1d43c98508074010100604100da050150100d216090244001d031514040031101010038020311b1880c00c2032070b145d119440101407001c6501004080384e424072505a032901e404a8400c0f01e5512940100d003070442e1600092001441e40e5000300b0322312280c601806401d05000c0444d01283c414250084c0c950f03480000c040d0004404000c90300c01e80c1815080340381c0022020b081404441e0a4075001e10a0b81c000b40c1102000500c8401c3c0e54620180400403018840500ca4045281a0840c1c0300140303840e20326001d070b0078100b40c944002e9003006c90844c440801150400402c40d22035441e440340364060f60140c843e6500c119038120101c04150201d128480030380e4460070050140c00e51590f60031450910081080c0c030680520703180003a0301c0c0d001c4102c3c101200014440180e8640c2003000340c001c00411140c110620302004c5c2c040185464000469421300611800880081c20307541d6816405407138650058841402194144010340c04002211020841c084090b82d40c1c56071941 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306197607 1250 306196357 306196361
    0x30305060a0b0d0c03110a05090a061b062721170403080c07050708060402090f10050603060d0c03060522111003020903150a0606090602060a0e0102070203150a0f 71
    0xc001c0c440c0d1a2020800001a0210fa0780003969091050a02055480341112026001d40003061f000012038000180007046242c9000064041c05550070140e140010102c004c491807031045000920b45640c64018200110301904050903400700090f154514150a280041c40400c3c40891181040e031111201c00c0d06038000c80345003c0710355001d691140c2c180e565850403150202c0180107500f61740404c000800214030240710000103041da044c003c0131582014030500444810041c0b0041d912400b541c01d0141241e1680c07444021540d040f20a07944075222240000d90007483c515004104124400e800010056550482c40c807816907110082140d140c0b0400032002c1c106d02c1c4030300178000b202042d0144603600e000c03920145c40589e0741c0b40041c2040c044c080031a283c07000c1c0ea420f240424480d1000c20010301442e0058001504244c900000d100d032800902a42d02c401c05011111070f55221800309014800035410b40b55103e4004080740c0314154030244803841c1003803c1c0c40304984641000158469000d1318 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306198857 1250 306197607 306197609
    0xa14010603092a1d0f070302120f04150c0206090105090102161e020a0b03091b150d020c060c0c010605010305010e07030e0a020a08010c030e0a031b050102090307060c030305060a 78
    0x441640241803000d0076045240300c80c00d001c030007401c01c00140f010402a801002d94041c58031011894146030508a0603030b080344400501b200704160041010750210f592200c0c0c59504410301540c0f844e06da440304c2ca0b0880315680347d4000d40f0507240c507000802040c594009506070140194100030045070300e030803028030700780d100704201c5099002e20788901c90001403a10388601800384450307203210260b004a60005148402c960700c550303107800b03021050008444c403c3c004014140000300f19086c43e40540d401040e0b004450342c003035a080c1000403c070f1040250090301161001c1c10401c040d40d05518040040b0401c0303801120206031258a4000c001c1070550091054505a544131140c40d0303d0340e0748235030302140506100d566005207400745016040c0140c1b250140d0202400400002140705036600b50000c08840115485651503403040c14124040394010050000c034001c64a00c1d14101e0301071742880390181c0304100704160140309821000818a0b80104040b91080c840e503001d100548a2808000c042125 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306200107 1250 306198857 306198863
    0xe15061903080f0c03070b061e0901090e010209060a0807110f061305031306050406030f020909180a0b16030f02090102061614030c0702030c010f0c02091302090a1401060309 76
    0x180c210600100d40031001600605107150381062502000b8080103046801102080380d420b682542402a18030301000d184076000e2501422079460911600062020003061140c0c045495441140c02c2c800a020b4040710070074170000d0055035403161a5040100411801c540620001c1d84003e25100e0321000840d00c0035409408400901d0540c032150044a00d00810500c112058401040301c07007000782900550000801c2d20b81c80e42a05c441c50300001600341c4091a40e0345110603c10031500000c0d0366140c0e81150050f02034240300c1c07252004890002d1030b00002003009441c60368071004210204c0381c2503401071000d600f070365002c0c848181401060402c0c0e010314a00c2a015800080014604110400340e40200b101c0314900704140f825080e40c1401654420ba44d03c1080d010001084c20641c01c2c01c10520303410907400c0c40c0240e82c1c0d4200314170080029400ea10000d200b0b80081c00841c0390b50805440c6035407500d4005009544034240020400c00405c0c40604842005003018000221140030f84200180315070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306201357 1250 306200107 306200149
    0x6080108060903030a0c1e020114060109030f0b0408040b0d02030412050414010f1812020f06040510050d0b0a06030507080609060114030c0f160c0503160312020106090e1506 76
    0xd801020324090822106d144d000c21105000d44408244c6d0000f10b5441c9149540000032030445102d0350004150008140d035041c402c490004100040e1080320704255142c1000b40c81d102c5448500d0802501d00c200d034000c200c0c64101050020790b910290780218000d9206845040c64018200c4040e9001d0045104601c1c1c08080c0420101d00e40d400317402100764010640c900f0b00c5501d0302004e60b15040043c0d030b070008600c6140640441e0300314281a8620165020304403001070415261000081d040c8440c64020804c02101284c43d460820300ba070425204890000d00f90140103483d150000c0040c031003210350000107291440414140d091801d030340da00410069440e6296128520703a41c00d50b5078000340c811901c48004004040c100704c484006885910302c4035500c59034400881c24076500315162500700d98800c0e0414110380c02c151403c140d040c8201d90f03000c60340802410440c0340607401850903a00200280e03042640040b400c54021441d0b5040703184100c56802d00c0c0d10743d1070038850408280c22600031560 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306202607 1250 306201357 306201361
    0x30507140d080f07050f0f0c0312120105150c01020a0f1d01090b180306010312090e01050607020f041407031d1c200304030b01060e0303190f0c060e06010608010806090303 75
    0x300882c000e000b01d83c0180c0c1110f0b060449051b0603850000724251007400e40c1c20200f1010854607051000d04005c0d219402400d0170404501d60440c140b02041c40b9940c45141c5100c00c0012103200201900d1415506000071500c8000710130700039286111610311000010070340346659000c9034070840b0181c3c1480060b0b460402450500c40b50040300c0d400891030140f844800401241907940800c0b40314082c52285000280b00180d22902400074019038201016043c14100144601c2e01c41c0000e4515203501150b0b40c00b840e03d000e40118004200c202004140301c0c400c82c0c2003109040e0160003050201d002407860b0b161024100114940b00d030141c141e5641c0c41e0605400324150240f113030041d6404400038240442c480c0d907000c44000d103980e00550045a8041d1130b0f900420a094000e4500d4018440030f40146141819851040d0304030204144010148a54032000008840c41900310120403580420100084414452000d698503002d200c0d040002d5007460011480b1000401c60a010b10a03807002103081da = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306203857 1250 306202607 306202627
    0x9150509210a060b060d062408160f0c08030a0501170102070213020705030903030c0606030705121e0309030703080702030d0e0108010306050a1433010c11060c07030507140d08 77
    0x54003240c13a40700d5010000380012030b6104001d04c10341e002050703000c940c11000c4854a07211401440305100740d0041c0911801046003c25902452011581c120319060144064030042034a044c0203442018000c48004820400b5401352580b00905032100c4030a1403416510b490000c03800d0340b05200c5c00941190751140c50513141d00b21a0050408144140241ca05041071803021929542001168603242d0b4000c00c1030150506080c0a28005480155590006805d01c50080e603561000d0b40c200d480c0105124030b500e5240003050040d40c9800308000c0c1600c0b0059500c1c1800c070250303008058140d10902030380c4001440240945414000c400068450101c1e81e8a95107031600113140c01003003117842503195140700d4460198070903a14807510740b0002c1c0c0d01043d16049803240d035204030450404518044840c1040c0c06030b8100c0384003081198003800444000801030042011402518121000d81c403904a01004101d808901c0b101a144507041c43c5551a403e4410048440106400685007030010003140d039103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306205107 1250 306203857 306203861
    0x30f0d0e0909330a020a0504030311150709180203070c0221010c08011d06060d02070311060703200f04090b031504060b03100b100c020109150509210a06 67
    0x8480c40310415160020291000c50b4964900c140741d9840d020404214200c0400e83c00146980000748000d0440c104558403002074100e1003680006001c0c4030440c6042d0840c0c1c10304200f0007004504811684200342003500e8047d1180e00c541c002c200b52240031348091380c0d000c5c110303200b560301c030b82590b9a135200410515001d01800c505040c3d0050f540c26110408078002081c2401440c1c46550700c3d40e0741d03003255071600048000e445400006181491003250611042e40d4640c0d094030280c9503c13030030050765450585002e0328880744150100055019640c20070000b240c040e4015480a0090b031080300e070343c1c0f92130b5003819098840d02c440c81d5030600b0144411300079404142d1000040307440c058100c60302c80d04408403403100b10400319011507010303480d400304507103030700301801151070f00d900000c404d0180c1170100d8001000318039504042020030544404c03120540e8801c10303454008010031080c0e601c41c007400d808000d107198407108842d406040021000045101000a581c040b41040c0c0007a03c51120f01e96650b00c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306206357 1250 306205107 306205111
    0x1b120b0d080c030c0106080715021903050306030a0512090a050a06020703121403040620091c1703070206070e010503040803041506090e03041d01030803221a06030f0d0e09 75
    0x1202c1d22041c8000400303254244039a1000e841900000c0c048113207032900300d00070082102c5030301c030443d0401c11aa0f94010034100729407e16a034903060080c1c41c0d640381c03004a4039101064401500921400380c06240a0740400d00401c0303012001e48030520015190400d01165000b68400d04005a10404040003ca40c10303104420113501c2a01c0c081e03100304074003400905070740c009a6003030b80e005680d0b00d0080c00d202043e0014505130040c0b00c0a07a0300745044035001461455042d401003c50b019a544070000301b200303d00d4441941c6008250722034a80c24200d400a41da40000c5a143d400700b0300402c013492440d070049007030782c0c8165441784440b407a60b82c403036a41c0c8044041c05194400601d803a810040384034012400b9402c1e2054540000316100c901c2c1c00201c0700c82805014500906078011001400401c0000003203950114480ea11052064602542040e50040b581c5000c0c0260f4030101001c0e40b0b0440307050019019000480440d543c1a0b11a071505407a00d10615000c400320307245065040e5182040c2c2600f40d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306207607 1250 306206357 306206377
    0x41d281d150c2d09010305010602210c2404110303160609031107060203120c0f0a0c030c02060d0b03010e011e1112010906170106050112020315041b120b0d08 69
    0x1c1030b40c0110003c4450080d08003240c403a4840c1c2c045144452564544601401014280300902c2101c0300c03010b104400311040c0b0060380c10080700084500309054200030201a95503031515188004101030401d01d8400340594048800214030304009550f0719000041e40c0e41100f003101211001c1410b50389203001000440002c406022082d000e8403842c50042c0300ba0401404550080e5554410080d002195000020619018540180003000d062100b15003a107884104501700140d448005080c140c0780000d840310002c0d07105000055014488201350009050301c03505800a000314546040b149003a14000000310500804a90380010951616006003038071b4034049240528169500312080e200c46400d82021200b02c0c0c50b10740800c1194525008908801c4440c0001c20a181c18000001c1403011450096107130150084003064100b1441040c4410020008208009100d84240140148031003040b0310b401007081801d94050203c982d00602500d164001c20109a801e6107588076a61504440495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306208857 1250 306207607 306207637
    0x1a1e0f03090d09081e0a0605180d020114070503070504171e06040f02130207140307051c120b041d010603020406060903080304020621010f05031002041d281d150c 71
    0x719002c0f030140d1091038014449ca4121003000d003200b41c622481c01c2070b043c000d1030071a80f4240345001001a81400716408c0491440d0072650303601c0d2000c0c00c84031806950811001c41094055140413400001240a240344c4110101014101e00d0075070b4075240c510481d00940340402c0c01d81c03848014035004086180d6406000c10050034a500e90302d80c04800112001007070201c0c1d0000840310203001d800c09c003820030b1011020010440126400b4003c0c180349840328404071441e1644c04044040da40ca8101d00d4404c03001e070400ca00e140380d5100c8198064401c03440168051480e000003c42e8040c401c0d40c0d010306a85e0000355442c135507240d81c0d0038003142d90b1140f149004184030b071403851411003090103035842c0200500014890643d061130201403c11360380c0068005c44e1441084204a4951544560110a040140500010b40c1e031124030b1603000c40b05000962640c072450405a4452042d507008100b245045810380091054140c64955a00e04450142d40c802d14814002000d813071026005000200e203410030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306210107 1250 306208857 306208873
    0x30605013c120e0a020102030a030f090f030c1b062003070803040b0906070318060b0a030501020d140a06050108060d060902040507080402040b0103061a1e0f03090d09081e 75
    0x2031444901108000001c0c0240302c80d401107000c07030056418004141c030152009420a030700203586c034424170310407009068440180d061a030a49600420a1a0704070608840d0007400e0725004008944001c022590b40007202d52200f00607941c0e041c0074042d0383da9038950181c00002e07044403140e50462018100c05501c010402030000500b10303800796015a100b540584034604110b80300e5800c1c620000c21031400c2500c1c02c8840c92030b58490081c0882126000100001d0b10200d10006c589080e45039080544298000034400e04261400d610168100c0b2088900301496260503802c503082d100e1a00c501e0b40081c1c03061000c40d00d079103000030701301e8142445034000103400c0805501150542d0307000c132100c2004c40c20303400401c001c1d0700b040c1c0250850a1800d10782005014100540e20803c00035080041440e0100440c3c00240e0f28070681511101c040510611501c414045651040560003140c1e00c509034000c0055100c0e03058014400c0300b00ba06c4d031040190124000710041d078500e50720743c48060382440c812105 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306211357 1250 306210107 306210197
    0x16051b2802130212010b0f091806040c05070f0b1009090c09050c09030a06020d0f02030a0b12150a0203060607200424030204110405191503060501 64
    0x215000c0103080c46440299200e0350300400003107401102d06020b449004000c51061303103019203610b9042d9040100a9900c4101441c03541200d4001c4050301e5400c01c88507034403540341d0780c0c3e589034640c4210002c507130500c03c181101108854030f00505800a0408040054240c005003c02070709991144114140541c016a03d648880c1a1400f50006880343c3c20b202c40c0c2440356002c1d1b03004159200010840c0d080c070b00544200400ea1340c0f1503920b00030304665408940b108a00c80b040d00a80300344055001e09540300e0a103842000018404c25a0b203505c1840780d001c541440c40400300b08050304502d5448254456903440043c80c001e580001d1185500c078404010000000d41e60151000e102c490441c404030722107a10b0028401118074a00082142c2414071800151101e892040070040d40e90664012480f400b80d000f40030085e0103640c1180380e00c0351131521800452241072042c03034115200f199006540001c072070820350484641b4040c0900007041541140304c2180301a040c000c42c15405120810201a991 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306212607 1250 306211357 306211393
    0x130e0619150e0a0c0c0c09090c0506031e0a0f140603010614030d030b01020c04110310050f060405061b010c1115060913170a020d1701050a050904080d060b0703030516051b 75
    0x4d00004200f03680e0b41c0380e1100380302715a4580703400780c141640d80310f1031410150039601a00340d0131140c1929028031400007858002042e00822403440c110101804000d014210914050700c2c201d8519000398a00038000a103400c1242c1140c400010140c06000c2034951400c0c102c019010442059040d40b01d603c015995945542c89502c0c00704a54400003500c074100201c1c03521520080c2e070b00892203070101c1c0c03c3d49020b076628101243c013198000c440d46eaa039800c44000141c20f90300070a02c0304d5100c0d440c00c100001c280b07420005d0103442a22041c252102040494034038168440141c4100e030b04228090000381032810f02a40786094240100c0e66400310582004c6041126440309501000681042c68045146c03900b00d42078400e41006081c00c480309604160120750800403a1203041d10814207200420140203680303085441c807824a01d4140152500c03180c110340c043c0e018070411400689040d00141c0084403403424030310805100d565842c0741018200c40103000710300030400c0051900452100c0d8040079040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306213857 1250 306212607 306212609
    0x9070e130b0103050601110607270e06030d1e0807051b0106080d0809030a0c0c1509050f0607031706011704051e1605130e0619150e0a0c0c0c 62
    0x2004020803251840720004058803000380509060194102c8010343d140f40c0400c150f40d010030340d85441c2e00c44c0a050140342c913400840d1941c24092451400d4041214850b5000b12032160100340c04564a211003004212400b5015251441e800f074035520807001036900c03e5403101d400143d00e00e012418180961016072130b210300854002c07030301d039900c060400100c50b00b440251740c044030a08180c4075074500400010745a21880007290104416030100d4003c00404a511201402c580e044610001e80514005040780e0114001c1c18890008155040460329082d002c43d0b01c82a4541c0d1100032030b9481e040d03986032045014000034140865010640d841c0380910409912130382c00364004200080450030785491404400303004450680002c60f401103007218420a40d02251426511341e04102120070f0020018070845c0d03580d2076180110014003240203042c081001d107848004504000d00c0900c80210b011411862041e45403c0520800082c1c2a100d01c0c2d0010800d2205030034024444070407035942982190032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306215107 1250 306213857 306213889
    0xc15030f2401030c09090509100e03090a031106040803031501020105180c0f011202070c03021c2a0905010806090f0d0f030203090a060203040b0709091104030f1502040b0a030b03031809070e 83
    0x70903140000c3c2c9c1c00d02d00440c0c10505840700594039240140d8082038806160340000b6000c18603801c1d901364280c0790641240c00604400090760744900304034150800311802000c62900560a260104000c1680c011070b2610078008c400003000d41c24140005c1c080e0750500090b045040c05100036036030070a41e81d580010040c00384502340364051103086104000f0805c1c004a811740451080c5000c540c0000d00100d00000030040c0010720380142070030700382840c4205070070b600701c8411142010000509194002601030007581c0c4141a558010806110145d550700c80c580a032000403c980d03143e40056009500468001c1114410307512000400e480748400e9910036141120200820001c101503143d2242e501805001540000d0004508400c203502c181c0c041c42c00b002d008030032443e40d11000c1210540464003e20441a0301350744560340e8808412240c0c02170038007040403d0504c5101d040030300d0044111481d1f401c0000b84511304240400900011680041c042024803151000c06049030351000041000c0d100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306216357 1250 306215107 306215113
    0x180f0f160f392f210a06051e040804180905070602070f0801060302032a03160501120509060a02070f05012a0c02030607030e0c15030f2401030c09090509 67
    0x1114900f4816041540120341e00050f80400c075035000501d0351180b01d007036120071101c14240314034007031a104c0600d0342c000400340707103202d403082c2c240c104441500898403c042c0c0d04000410070f02044070341c1c0c23031100c1c046500500310b4004000a2100d000c498901e12590b008101e00003c140710560303100c619021003a00203002603405403c00b00400e414049041f0007524103880207105403451a400f00e940d8410420a05441400002c05401c90554140c04081001d074000c04460088a080841c003850b84094040e141c0040e556041203224400c2c1c0b800707018000e030600070081504e46d954a4441c00250455a1700721600c400401000d00456424040d500029454000340744e01a0b41191000084917510101c030402d0001c2aa110809690003050490f07008486007004141d100551100506194240d0200d66120181004000300890060043d45c030030300c2d01c0c44c23101c0250384400c0d00412405200d1103c0c4048200201c8695550394425004001405003a00744032003101c0e202c00100003a01e41c100d8110b2111380c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306217607 1250 306216357 306216467
    0x8070e09030c0601050402030c0d050a0b030c01020c031905070b0d020a02010605010f02030a210212040203070602010501030203030415031104170615010c060506180f0f160f 76
    0x8052140259044060a0021860b00001489050312a03105108141c130455020001a5407645910b00715038000200f80c10400081c9030450b0380c08014401400490300170b10510303062402ca940005034103c0742c500028020301c005160400324091001c401681107a01d4011440001501d6580d403029080d4015404400b5868410300d0704000c3c21101e15a0016040200c061400035032190044201ca0701c00c1c1803490004d04080140d10031000035001030318101301e02c0d0f100003804008400000c41d0385005034801c40a8503840c41c0d90350012403d0328400e000c0071354903070000c000400c0b6452030b01c0200d05000110b420302180c55070030600045c906412542c070034182c03400310940d6170b459908148441640241d5207010341c0350241584000810000440d40001c100c0c9a45a020501503a1440030004c2d400400040b0b10040d468110003462030404103659000c00d4002d480017041c0c07802c0c0040308547d100d00b803994030104003105492044551000502000000040d00001c0c0da00015207140418502500120610021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306218857 1250 306217607 306217619
    0x2106050f091002041505360901050609031507090e0f07030509120301050d0203030c0303040606170307030509010e040b0d1202160f0303110312010f0e0109020310060f020c0a0807 78
    0x25441c240090b0305a01c100400d110440300013442040800c035030703d8441c0d1102c403407801110342480303015030000191283e80351a10120000c0140500070503019541d801490340da807400d00c1094028080381d90b515030070001c0d6031035241c14440c0c1480e900c4400703450160340c21551603521100307000090b034245000100d840104106680c040c01241d13041215180100784440102d070a88038640410f0241c68424168103060f542950f5080081e244880c1103075041e01e69a040070312f444e6004040c1441403c1c9601ca9410407104d00841c040107482c240341d0961140361806550500451301001c0b00703d91075a0141e0746125000003500c40d0660802000d02c603070b6042c0003900d80c0200280c5042d400004c0700c04044a51481884a82c030071107100d204981d41820a03102c140c04030007103e800d600a048039034114101e100c00000c0c0d00301c001b0607002e0488150b200701400c607980f15015a801e07480300710f90119000c400400100400c52013080c0c2e01700152902c1c41603500c0038055000040702d0b00c8541d03011410303d034000c4c0c4040c42a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306220107 1250 306218857 306218863
    0x5060103050f0402030a110301061a0304030f170a0915020a030c030b030a0c1203090812040326270310021b0a0203100e0309041d06070e0a2106050f09 66
    0x14054003140070061803d030b80080d940d20700603240241a0019100c0d030150607102504803402815030100092145000740101d40700ca03401c100e800380c002a110000b000080c1e07004000d031400203c0044688061956201140e401802e601402100d66000c40382e4909200f403803500c0a0f2884556a95000c00c3c134038030206004054601c003021040c400e42240b8030140018038201d230340c2e8046840c642d124060030721840c142030340d10219030750090416020b48000440301410050041080d00d2160340301000c0f0400160007088900c9044c2c4002950075010800115a00100a02034503d030f011448209000e003010008a820203922481001c0d010b03401180b6018002707480131948101030070071402004040381507000650707101101f0417401c50050303459049440b010410b0040b03c8114401400521001902c1076011400300508000b03070031180543d0f40070414492089100380034124008090b03100c030900740703206808806001244102180900079600c00024003c2c05014801e542c500c41c04d03c131900c0c043c0381481c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306221357 1250 306220107 306220111
    0xe07020313120b10050d03030905070302150307140406080126120c0111032e030b1e06010e1003180f1b1401080a05061206090f0106060513050d0c1205010506010305 72
    0x1180002501489103440310781d031b1100c2907901440d021580c40c4c080d0912034101003072a040603400100c1e0307244c2c00d9403280703075607000b14000c14403070792810a50015203141d159203003c0da0040800050300100100511568600c3c00d030101019007903000c407117541c00302119180c60070350015008280004620150010b03000e104945110744a5030300d0b10318500d80701da2046070403034030003d04840035440070503280401d020310504034001c0d5901079500303030f000d0400034441030342440d0b04070404503250240d4000a03020351241000b280103100180082501d50702602c8164080c04171141c920418012014078000803882c00040c13100158050268003000c2c6428803901c91100e151504030350445050304004980f00d9030300013807059105103080b600140686500001400409018181281c5481010240044802c0c0454400c00c3e60082900810076107560300c00503925401000b800d2940408075013010801403c00c00c0482640700d01c504296000c1c1038803003584050011801c6015149695140100112543c05108841d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306222607 1250 306221357 306221371
    0x1215050f031615020d02070518090f010903020604060b19030620040906031704060503011a040305030a02072405030a050705090a0b0406090905040809100e0307030f0b070801030b010e07020313120b 86
    0x13011032403c1502149d941116140784840c6005110000381048106001c803d07070ac2125a4001e01103000e00307080080d0b64503010345081e500c651402000825510f414105140c07407134400031150840d20321719103c40300180881d860450308444c1140c1880e00c400d0032900204098241440700040303103425400e19584443c1195410a49110104014444681c0180581c0e046138181c10321112000c88050380d0000714041d651005103140b1000c83c4840d41260040340d100183d42c10310300030b990350740036021700c030300344400b209960f1703008100c0400c00710f88402000d030480c1e80d118105080c0795141c41d0344000072410b4412642d00c6400d1079980801e00348003242c2d0003d4040010501c4a00074001810541c844485a1241450052044c504000700c00d210030300400c030104148000500360360040d5940c0c20034142607901c0d42002c075100303c00140040c141c103015511803410780c0e41260f40c01585038284a869074003588081e140320154031027070004103078104040c074509016041440703000c000e041c66403400700c2105501034855 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306223857 1250 306222607 306222613
    0x302070e0a0527100c050c0f010501120308060414011e0911040b0a12020f13080610120c050301020703090501110f1b0103021204080a1215050f031615020d02 69
    0x840a03820707041d02c1d00b209610101090f24a02810b00e0b0090b4982000c03814030390303102c5050894500c0041d801c41c000d07000c1c0344403090039101081590942d09080b107000f400b03030b80c05983d04d500e41040800d109185031584184007a00003d50b00c00d815082811502e401d030300500482e0042c9681c260100c20040040c1c00a00003103109200907504651050440d003d24003410100c204c0105070100f80501c90800030390a0340e07160308115520a61102043d071190320880d8001c4c0d41e1048504005491480001e505104000c59600c12a100c3c0c1401182807802c0717048842908d0501c8102c1000c00c50356800e10080000c1c038070a49503036a16900d020000751103410001000021600500e200012a000204100c0e000780306904404008080c0c60780181d00078010900c08042c00c04a04080104009044000700380350004c039181c4104e1582401c500005640f0b100c00584000c00c000c0f0001c20203820070014068841e10014140c5213503e801082d40b55140344181c0c003806101c000c95803803603001501484208056180b0b4409 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306225107 1250 306223857 306223861
    0x2d120c101106040f110d080c0106050901030c030204020a050f0d0902040e0d0c030503100f0b0408060c0c030a080411180105010f1d060d06030b09010506130603031b0c120302070e0a05 80
    0x7160384400c2c0092003d4400e5206801030030821070f81400855040360700605000c0c6d000d06600748180c481c3c0054402d1102503180c034002240610703100c4010b50407030764400380c410b170018110380c240400380d00804c00d0003040c01402d0000c40a030b145400c02404000500d40000200d5608a004010980c0c0929800c1d02e13140c1c100c0d18458a0240c0d012803c0b1000e150581015542e0792a221001e80942d4280ea01162a02d10100c00118420340c0300b100400c100c5105104170b4001d511450000c0381d49106414900c0715a60041042c42c0001d4001c1e0040c550007800382c0c5400c600803010801040e0070072a004030311900815031600600c019a0030401c058281022490600c44210640c20b04000240f0b0909201d81702e0800401e805403105859000324010b0369014041c499035040081c170386d50207010f00f6584144100325815104c1984511845010210394150780c3d800aa4850903041d10480c0d402c4000a564071650000c020550180c0180c01d208101d03c660b0061a5507454018a954441005406e41b8071761420081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306226357 1250 306225107 306225137
    0xb010b070b0a38130204030b0901060f030b1012050a060c0810120f0203030f13080c0108040303020307030b090702074401060e0a06030302011a2d120c10 67
    0x50b00c4107548541c001003404845a076484020003202004450b40c03182480030100f40340c82945e0040d1048038801d8134100401c0c0c945c05102801e80e2158010310400d00500b6100300045400914030311f030000840d0f070204c0c60703198807002c15408110000310255100c0d80401c4040041003403a10443c0000441b80ca4044c800d4100820000084400c0e489180207691807240d90105110b0380e0007408103a40d030300030b0860b07980700a04803550711150012001246010102240010f0103180421040c48490051b9103084850341e580d0b07016802074002130b00c500200b55039144000000d840d50003005002d1603140e0002c0400a00e4504026103010a162004145420510400c00f803c8038420010402c186d4800c83e40d00012001d00c421401000340c2c3e444401074204400c04c0c0101080301d80c0c008000c0d0790095000b4803288030100c0010011030204c4002c1900511119002140c04144039400c035400040207040c0c6005004080000d1945110341c100448182c02100d0724550344c0c908040c82e03440d240c0590500008011002c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306227607 1250 306226357 306226391
    0xc030a110d0201020c0414010e010608162106090e070f030803070509120109060914150615070f052401060e13060504051302240319090b010b070b0a 65
    0x18a81805400340700402001c40e8001e00281034454030103002013014048030b5a00c0d01d06144281b05030360b11000800d001045a510950300b60344202502c2c0484040801c040710121900a0322600307449900200c0070f80001060315600844c401010000c5c0d012400b134a03407081d59428410039031700c0b580c41d2580d40c0f00208002905d02060b02e030b0081c0302d030a2140c4c4074503000c03000c500c0600c400d810340d80d03965280035012001c1110070380c0907a0100b03004003001c41d0340c60131003920140d80c7d00701f01a032014100110030011b0a40d1920b0100c03003441d41100004c00342051f1031031761202e40f002e0002d00101c90750781069581c481c5442c420030b2403001c40c045543c8010095454010042d200f0480e204803d405000f000d41c40140c080410740110009080290080040b0701c1c0103441e44440307152a0f58124403c8518011042c410301c0784449091488442d1800185180c0b591041030b0f0002c000d03441c202c03038160385848002002c92080c004c007074003c01c000c1051668400d00391a10302240d42c13000303050380c0e015407400e4902d9070b0004040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306228857 1250 306227607 306227633
    0x30204050312031b0301030f0b16320a110f0c0603010e070903120305160302040f120c0305010e07091b0806060310030b0c0706060819150f1d0c030a 65
    0x10b10b0003941c0751602d200851400c00492080c1d50a031000200000410007044240003a175802286941c85c10b440d080300390441c04040d100305100145004140000454071890300703c80c07100618a0103508071891290f8009550040181c00b0080b40707070007010008055081c0641079410304410090301c0026040c0e00054031500040c010b080e44040e810300010b0995000e4210301004c0c50f08605100c441d0701941100070054941113450011903100301c00c1c000b1545000c0e0003a079080d1841100b6501441d800d010840c2c1d080307082ea41c0c00b0341c0c018034441c40010100304280b207501040a003038405049064203000e285000d540c5118000008800c481100e071001a51041c1030581000040301c0895a94903680810b000404083d0030250403407500c0d07000c0c0069400f0480081031308a1042c030717043c00030b10341c1c610415403100010350001020302c01151004c00082c51000111490140280e00058209103040c1c0c05800c407811000980340122962070800c43e81d0030200422a42c4001c210010500c80d0550b98031040c94103d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306230107 1250 306228857 306228883
    0x8090a05030a11071208071b080c011409091303080906010e132120120403060507020f010c0c03090e060102100209060708070605010302040501121a060411280302040503 74
    0x450343c80c446164091020400600c0042c00360040280181015845940100411142d541c41e0360002c0c43c00503030408404003100e0041001c1c00480ca00c0200541d2401c120000428190004201007107940e600d00c90361500400500340001610311003442c0c09060200043c00302c0c074456100500401c0020080b04040e641324500d1207010302c00c982c15151070915035554140c100448208003a01c805203681c400b00e00301c0c810040c0560030555140c40140181c903031080b130100c1001540104000d00200701503030032564000704144103c4600b040d2045a56084070b482c1c0300d4003c00207080440c800c0505034003e54800c090300b0810072204541c00e0001c0043d44c0c0e003600d1032840710300d15004600b0b40c0c120307179510342a1211030f40c101e072940d5602d58440c60107800908090004030f1040c0c0c40c1400100e00c1c801902202842c1c0c42d4068041d40d0300d4000701c09041c6d241203004150356030064580c840c0d41010b0030b080780985140240c03409011600e09482006d90075a072140f402d200205481031001704410758001a840110640d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306231357 1250 306230107 306230117
    0x60312030703180506090c0316051c02010e0d030c0213020a1d060d060603050109060909170d0b1203030601091a0405040f020409090807030f0206060f040c0207030506090d08090a05030a 81
    0x5a55528804038201c8081d01400c00d00404041018840c004903602031f64410880603241b052003110900015020395000c0c1c00d03045020035042d4082c410b05404c4001c1201d005052924109500e580012206212182d00307c00180c40d0b00d0062045050450088142416011055007806000f040091449000710b004000c107240005c00e4909a803180c0048411805000d03105000303aa8032990060042c103002e00c5035840d03107490144001504081032003000202e5a0082003040d0307845459101d10501d80161780300b11012035803842490110364580c2500c1c1d90760030f801800f558403485c0520000d445220076500c400503c41e19900b141c000c0d9214001100c0541e00d003103600064031509800200b000740140d821441c2c255150082c0e4000740581074001d0282d4610030381d41c41c03520501d420800ca03250481070300c40c031760007104042d01c0e4541c52500303070882e11604c092481150b02d010340c0c1743c1354170380380510a440880c0310780c00402c0308142483d40203003055400715000000303090150b400d90700d0325628400c154183c01000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306232607 1250 306231357 306231371
    0x20d020405040f02030118030207150f050a021501090b0f030d0e042c07030507090204060c080903100903051809010e060f1908011d01050702100b0411030a02040e060312030703 77
    0x5a0b46000d0074250381c005c1c008010740500820300700048114010150054440c090000444510b203c00740132108040c1d595100302c904a043c02562180c10070b1000780e0541c01001c1c90032403003001c0141030a000740400ca00118070760a1560a00501205880d103050082e0001c4d007240107210b42020400e81190026035000510b1110801036a003c0f98524100000d180406509501040c0c40090341005a900541c01e80b115181e5030012441240301f58401d003c0421040035081c40403c21050141c82c2c000320282c2500d85140d81425038a017205c558903001c4002c0347c404103040c003110050540c80650345405440207440c03941000e4001000c83e40c000c00c001c3c840d0b03005401e0b42140e40c40302c0050415078180000c0c440e45441d00c1e00f001038080c044030b101c1140c401c0101e01e04622081c0050050310b0196800b0b402414102d2864145440030704840300c2c00b1500152120740e191204503698004620600a900c0010703107950410466100d545405000c451280e4030000201d01d01e2100802280d420102c0b07414001100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306233857 1250 306232607 306232613
    0x308190207020303073c03050703033e07021c05010b1201050405010c0e0105030601181205031b061e040f02121e030a0507060b1c14060a09020d02040504 67
    0x2a104800c4025098080401d00720100400c114401002d00314440d010200c400301d61b01d0003044450020050b8000c13084180c1328602190140740141101406898049482480742c9450340a621200500b46600400c80c2502c0f40074403a148030b03d1b40d1250302d80700d40b04c0c07910b0440d0300041c0c1c1e9040500b14000350700b540c003805030341080803d600100c4c440c88040d20115403610301074001c60003404211801e8449500303045c503d9040b2031058801c0f00007150142c48440c01c54440d08011603207202c00248180a00c0076800006c2000c0d14003510119a540c8590000c40e03441d10500c0b1540c04200040c2c80d0b4911552080051200e00d0f4819104031203080c421110a0900d69030741c1c10602c40b049105d00d80613402c050088282c2220000100d4607134181c0107041c00e04c40c0345411507000a90b03640306400d0100c0000d001409100300184068103d40d4213610000c01c2c1440920f000c0b85070071039900302d0030f03011200b0b151550381940c004030041c06070300e51200303405030704004200075500400d041000c020380007441240d4540000c1c1c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306235107 1250 306233857 306233861
    0x702100b030322060806031203071b06060b0a1101060605070f030c0213020d0b0a1809020109030c06180e04021c050a0b04061a0f03030d11040902030c0d0f09030819 72
    0x1044484400d4400f4841030002c020100450134080c1c0c00001e10f0f5072000038000d09000585080e0888180c095600d180d071401000c035071084c0407030004400e495482c00e05038040703107032400707a08042c0c19510051507827600c02c980058100c4100340d100c1d40311641001170030451250443c0036295555007000c2000c025164610b0120b03001c25640800a52040c10503103180c0e110302850780540000d004010080110480c803400300641e410240c0b003001c548000009018400c0ca105030000000c140c410b04010503155203d54944a034400d00d5081840080c0c2c2551581841d1010303c40150001c10040c0b040400504281d00403034112501c200200201c00607e2100c24100704040240c011100d4000250b9051410f203494184094086015100f001d090b10040c070100038036040c09400441480100114a015005401000600007201c040389250306c090000041d124400c0c0002c500c01c0c40340c0b0880c550ba85041e000c0150894500c0800a0314561614225000290308100c040c2c1d0400c086140504201c0303550714134000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306236357 1250 306235107 306235117
    0xa03110d05030c0c040b011b030e0423060f01090b0f1c02160507050a23030c0d0b070201051e0a1d030f090a1703030403050a05120f0403170702100b0303 67
    0x1a8400007403c007030f0709207011601e800c3c1d05108070b0f014450341003030303000466a200b03285803501c4144031020520000240103002542c880380002c0c00203e0034600ca006e0b2011040704c101e490003203000145017004800e240900d4020311076482402c000d1071550a1002c2040607005a60f188080761a0014074913003154880c80342c1c5001d40d801040259030750082c00b001000c0307407140054100c1e03152003401008207051428000f402e080c0c555100701d0548061051800d10600714501ca4040d801d0301034458580700548400201d244000c0c001c0075400080d04010034000e0840b5002045080304c181141220381c0200400b280541d0041d0458001040300b062100d07103000440c0682d113100889202c0065455503141284010b0259031130f08030380f822400d0795107a040701d90303864801014400d140c000b0000507000038064405044210100d117066401c01c481410b203a08209000d403142c0300c10742054020082010b50000304141c40d42590b08000000d8200030801a60b00c00031101000b40c45620b40f00802c45e65141081516 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306237607 1250 306236357 306236363
    0x2070312170c21011401050d020f041e090606050a12151206050c0403080703050a0c060612051903200a020301050f010503060718030602030a02070f080d1a0a03110d 72
    0x3003260700b08440d00c2103940e40210103440c07180742c45551004514240c040c16074120b8100610718542248101c004440741e512440c15825582e41c00e019044030f807440c01c005400505036482c001861051405503026030440198070048213039003001e03414095158080241c0302148030608000650741044003040c0301411420307008010141c01c40e4800503041212500d545030042c0140302c10002612060443c0c000c520460202030a0780c5400c1281c0030000740300e80300a06507180b45103860068a815a82c0e04426500d095101c9034050707210340b0803001400803d00c81090504810792008825982d01c2d42d010700800301d280700401540c440c81c1c40040d5031003000c4c4002d14030300d0b034024020407171850b0800f604600e02c04e081c06075a0192203808001203032030b40101048081d0b1025034050f440c0b42d038950ba0b918000b9500090140300c1d000d4080c032012000620000b91004581c1c8074407891500c8040409512040b03640d242c1d201428501e001c071840615031241520401942d4100b050743c9100703043d4001082201613254401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306238857 1250 306237607 306237647
    0x170d050d09150906021c05010e061215010308070213020a080c13090e060702190803010b0a030f02070f0209130b040f170705011410060e01121e050402040b0402030702070312 76
    0x600c007004078580c010182401c0103185040700841d000d140f46c01701c0d81c003401174415014082022914601d000da51403024690b03001c040b260240d9102000c1e00000d1030a900c2241c85c402e01058a104600d004842184043d02030442141080c1c9602c0004101c41d41c0505a40000c0c18001a000b41c0c44004050080103008450014885c01c05200d80301640c40004541e14801809441c4082c007500c6003101c800d61150707070040c44050440e42000c00c00b0389258003504225003803540e83c030000b002e0071080b400541002c9014001200144420f801030102d00300d40101003280d56420a462403001071440880c0c1ca8201c1c3d0400c12000250119180291000601690400d030841d00800c04104220701508070348001629006c41c446039480303100118400164900559005c40c408005406132075105040469241e2020580030800c00c04007040000003004620748101303d80c0d200c1040000f9030406000c0c194011409490442c91440c0c6100d0007500c0d00417901005000c0880700344000c000900c6080d41d401c850b540c1941c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306240107 1250 306238857 306238871
    0x30f0c09050a060f020a120306030b090d020c0f0109090902040204050d240537060b0a020c06070f1e05030406050903150402010f05130906060207170d050d0915 70
    0xe80030361114481c5610482c0304910100e10f0034800d0000003443e140c16002864403020b2a42c800c80710110389291181090381d54500000414100d5441600a004400241c81141201540241880d2000c11014080c0650300805070740c3da680300a481089659146c000202c0100901c0004d000c1d00c680e82c851640000ca0360000f9092206503002e180c0b4a10b0254414440750f180f0bc6842c4080e16022914008103141d4a6121604081d0640324814003080b8032504001d50a0343c02010001c503000d680068135a50030102c0c602c20016010441515140b40c00c4811604016155840c0f02c84a882140001c1c8010502c04040030000705514000300c5881c0e02c44150794507207448120050850b00a0780715284a4030031b440c42015900c44412131280116010307901c038200582c1c034500586607680241203400003114104c0c40080c03078981d9840b400c4040e15055014202144c40d044280b590f0071034424040019411046404002507004002c0701d40d075102a1201041907441c909210000704100c0048668080c10425 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306241357 1250 306240107 306240131
    0x405280902190305060d02040915050903040f0501111c050c0d05090f01050711010509030a05150601081e0a09290f09030403030806041d0a0c0f3003030f 67
    0x41d18010602401c0c80308542c10412084059072019a100307a0464a04049040503061941201001d203000340c4684504106590480c400c8a0044a079203089410109040c807003540701e001003500610007440c0c2035100030f9400d4203503030b110b03100e10740403009581e80d000e04980800d005000f6103d40c9007070340041e64100a12550041c0241c1d200b651f10601c2000c40e08144541d9601640c1601c500f503401170741014490481c400103440d02d42c40724958681c1032240b6070721640007510400403500c01801c01252000d140c103229002418043c1c001d8042800007002440035840094104006a40f0a640020220f110011400c108245410003032103000d80b20a507005c003010709075441014501500c680c01c402c403415139070307100c1140c2c487c002c034080100002d6240010407650320346034100401000010028112410401e4222407821001100c2143c10f0b50b9006820040060303010030100080281e8038000160500c001c20340c000c3e50651501d50b240402d5108000001d040c070035400f0502c00658428100611034540f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306242607 1250 306241357 306241361
    0x21c05090703021201050a0f0606120b01051b0c0906011707140409060e06130209060702060d0204240e0117010509130c06030b0a09060302030d080a0b0d0b090d09080304052809 77
    0x44030002c41c1400e00c890462031208034030510045a0640e501e07511640644611000500b100e0058941000700c1800222110300242030000302c0d2281120003004003506920074000344003470051046060099554078a1140c4127690400f90f48003689281103c4104681d080c032400703072300858005000452a250001c5112503040005030300600307088950411400d50003003904207034418a68110b811072000d000c40f03401400c1c414040d0a54191181000d0300301600c400e03840f07522900d40c8458640220603818804a0560803440d4070600407000e00c0d008040300c3c2400001d00c248481031040324000d940c01d900160b4498003210489002a40c45550090040d9075881d000380a00031100c4e8041c45030302c204800090b0b03d416480303035600f1a44d018018001c004030305001500ca0302c000501c100e0301c2e2501c03002405415a610000c0c0c004882c81384211040da818003498940c41d001c4d20b903214805005079001c083c84401800015034003161012038040710110f0786044280362814102c580721028604984004c292480c6039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306243857 1250 306242607 306242611
    0x4050111030708090c12030418020f0d0b1e0a061b021f120207050706030207050a06180c050603100312090e010e010512060f0109020a05160c090e01021c0509070302120105 75
    0x5941201c8403d0300c1c445c1000741460341c0201c10840d60703200300b0081081d208258044203c007014504014100580d0031501d0015070300031040d05881603511545500746280001c0042038140700c000480d1007000c0b03405c01017081c032802400340c0000e12030406440c41d9081c48a01c6c080e81d4103640600300d1b19810300a25243c011040d40c141003030001c01c030308894030b01e620700840c400e0380c8296400c20000c0041501e031800940083d03101c18020365050040307003140e40128400e8000e810305a4400d4050304080019400e0181c2d0b050843c0e00400e108941c01c20901941c802d11030300020940740c20a40e4038002802808059440080da503000c1102d070081c41d00001a50026a45410304a410039610b8062401b00c039610f440e1902401c0302c030b466480c070007007005202008099001d0130301030419007480703460540043c4030b542d0003805a41c0c040f21484881101030105d41003500980020a000030000d6081c0050b80800f00d429410003c120080d2a660790002543e505d4100b08200040d90041c00181007a0388810609001e4101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306245107 1250 306243857 306243871
    0x2070b0109061719050a0503030403080f160519051c050603121923030f1803090d0807060906020c0607090e0c04030813170a0b160503040b04050111030708 68
    0x18002c4005500035649a80060030344840c07014000c5482501400c0c40c2c0f01c00c100c00140c8280c81034003031100c00034008000035401980652140a010f103040c2c203801d404443d0040c400400100d80c40c140040b595000b9098902c40d080402ea00c268a100c005400c864074040d080a410b1200e50328040c0d500c26000b03661041d406150103405650000c0f400381d068002070f1281c01c1ca1551803100920035000403900c1010803c0210f000c10343c50040c0000802003068007600283e4110300b000303840c4030a01c072121280c070509030f4280c00d400014505096041002403c1d4941e0320502504c110800280385041100d00d0340500c41c504d0f844030382192103000c00c0c1c1045580d6142250b2280c085010b412000c0b90800f0754010440c4104100310909142a04665407480143c0012505c211100003441003c82d03420540588940700c01c1c421781c010305200d19076040405c0780690140c03120f19400c40c04140841c0296000040f0785e80a90082408600c3da210351070120700400b01c003040142500c1c0040140989564032400581c05003030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306246357 1250 306245107 306245111
    0x10020d050f22050102070203010f0515040519020f0d05090102070212010e060411040f06030803072c19030b010b120609061807021203010b0c15130803060f0402070b0109 74
    0x1d250445011030200c2074507500c0804911515400c0038a499601e0115114821800982400110350100f802d4442443c400c1040f55112020071206002940307259400c1401104c061005041c05601202c1000b10b401403090300d00c0d00040c80a54454040d01200c0402810742002c00c094548400d4050003500007000407440340e24894110003c510050050f80c51502c0c07004054140b545559031380c01020034400b0102500540c40342c83c4503140a50f64429400103501a401c119524075100c00010440019400001c1001d042c16a100d40c000d01c40b0000014801c90540e007000c80e045111104408a1146500c002c103014044800071444040c0c1c03c010340b0075402a224404d40640f5204200300000130202c0c0e099408c056503404100314000e481103543e4001c04140182c84050301c20300e164000640c8260410700c81c00d417000440405140c410042c05100c0134543c64051071174202100c820725403a4000134003610802d404004550039030346109050401820040c821503554209241907100d06000341324081d40c7c58 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306247607 1250 306246357 306246361
    0x2607091b020d0e10092402060901060e040b07050705070803070219060f0c02220504050d08091207060b0904060e10150504020c070b070c1707030201140c0f10020d05 72
    0xd40000303400000216107480744181402e0000900240189981c040410080e4030100010092800d80d140c10b0701008040e4644142015110003a01d0036001602c104040d80c50210204a82080e6840243d0800c1e44110b03079001035207540404039030a00409002034058008c1d0003001410400010060804900c240c800f00032134480318004108040f002d2059402140c0c4080f0620001446000d600d80450320082c64100e075a4080d42e001c2c0c42c00b0900b902c0c4c002c1c03000c0c5d5480c10701041c400108031501102803c1d1500c400c00780303411f03a0320a031035000409201d528407030086071010402c80c094000c000c0c040d0000e8801045850f26041c00c5010300441e048442c03080c042c030921007200408500410700314140d002c3c518515507140c402440001e50114403070a40742e0191440208403000340d040101049402030320740030031a50610140203074094019002010303681c0415020030040c4d820a6089007020700040d1480d03101d50810759600c0c10500300e2400c10b40c19000d01080c03401e8418083d8041d028502000c041040b940e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306248857 1250 306247607 306247661
    0x10618050607030f080601110d0323040305070f050c03010c0c0b100b041e0302060412020a0e06090601200d11010c08010b12100b0c0d031a010801260709 67
    0x80d102d03486010b8009000c00d4601c590071805500b01ca40c1041c010302d0078101d4660b403102413a0510311404041c40009449150440b201e46003442095420402031010102908203940d002d4840c0c03051900003000082c900c0008000d1040601190703001500240003408910403008000700590b6800030100d4591011001059640c0c1c241545041911a505031f8030740703010308003808074149400e10300710b000f5089003400000c030060311010701400081c0841030403503041484038810054043c88540011111034980300c00c0003001d5517580d0019420084c00c0c207144445c030f0020340399030710450604075403000c041c0710711321048115640c81440c2c81d40d07120109000704a0030030044004c41b403070a8284542214050184050310808040c40310315900a440a08400522a550105082240c2141746051803582040a505035016014091101104140368075282100003510010307280940c117029040d01c2514800c0311350301600c0e0795a28002c0045003041120070301d903903518444000e0000300c2121440e22090070410010b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306250107 1250 306248857 306248869
    0x290109020405100c0b063309151206010c0f021c030306050a060507080c031902010207050d0306180504060f1d0c011103070611130e04030810080712050c060301061805 73
    0xc4ea4880300141194448404001c60f01d4107605201c10415020509611481e001d100c21450f120060440c0e980c484c800c24007000140901c410b42204515010081684159480790315140d02c40c50034200492808034a04243c1c0301201440700094002c4800d1243c0048076202d03505e44100a4441c6d50180021034644c0180a051049481528046001440101c4c00640d1000240c0810160441100d01340450105000400c0003d2811100941d43c00a440024008180649000700c1481d040a1101501d843d90b0307030a0442e0140308030340c41a55100d0105042100710340041034009480c1c04140031b5030401070443d4107001e0040001200758400c0c18480b410a5008164604440c0c407000040e5080149a0b00d840e1b01910031207007108a0202e00f04141f81c03c4083d010706000141a000c02c81c8030040c035142c41c0c05041100058035032148000d100a00304a88140018800d0603034503903026015984400385055840c0c00c09034070346154003600120010a404d54401b008140685900350781092169640040c40b01d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306251357 1250 306250107 306250127
    0x141206130204150c02060904050f011d0705040909150c03060509090a11060a0e030303181005090316080405120c0a0603110904111c020c2829010902040510 68
    0x440343e070300d035080100014014011250381900180c01903151064400005040f40d00c211031072035003210b07441c00600c02c8464040c00010040701c003400030641030400301e6014000340102d105040c08191a035407138a0804c4400148050103440c190414000000d030408043d018054601809019210800000d10f00c204000b40411140780c100380800c9004182c0b9003403203113070b038008801e2070b05100c880031500800e5107041000f10b01c80c071859040d00f0442100c000c00f1324280905000c800c500d0500300750500c5460344010084814995101740e03090311521407440d0038000f60140b640480c5d40a201501c000e1800800828010b201d503104641d588801a11004154100d2322089804c0400c850244600d408606207607004030a080e0b2030940c2c0f1404c00c88075070f1881e100141c1303000e070080102d81c02054034190204100f1010907218148542420030100c0c0c10300d850f1001c0d11480c0060854103150098821000310710104e510407422071002c084156071100c00841c040e50080c840c03140209294101048894030075071240c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306252607 1250 306251357 306251369
    0x11d06040c09020c0a0c0e0a05060f13050702010e03040b1902061b070f050105070e0301060609060221040b040611120f090915040e07080c030d0816141206130204 71
    0x1801140c2808042c034029006200c040400e840760100c02c80c0803400c641122401896481c22101c0c062902d65840e8040d84d6000d852507014803090180480c084d6030725112881c4030981420006566aa05081280900034000004416000026001c1140742c000c0005013500a03c07821700f038590b840d00d601c0803a915041150b102800d00035001c2c074001c8811464004088040c001c159000050302e043d1030341070031611f007524603001080040d0005805800c003801850001e0600b81490710100b480c01101035202e09480740c2000f1010f8400d41007030150000801510041c24007807060035220303500c41601500750759031003220441ca4031403c8844880120058120703a41406501d00482c1000c1c485001e0100058015141525401404d1151001e2740c840f44140d041500d280f00081034114908205141000c0d03d0800590003074020b502c0008940350004480c3d0703088440c406403401c854040704400c03101000e4a100ca10f034120320004070543c2070b41140c10b04502507030342107841c03c3d6400c441221a004a01c100d2041c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306253857 1250 306252607 306252623
    0xf30011505030a0f0201030b04050f0604060b041206020304140303070906082a0c1f0204060305010918020904110907030b1c03090b070807020406090e0d02070305070b0c010e060702011d0604 83
    0x200d070001322110704a4940c1c40c03060402062002103980024241c2d10121550340003a4a0003041200724601801504020400643c00c41c2c9010b04010705d044004000b0103024000540020219040000d9440c118501e01850310039070b51203040400e030040900701e003031150000080b101e0000c900201c03200080c00c1103580d1700d040342c0b00040d03c0104881c54140c0007404200c84501410b001e00000085e100c021440b0220154030040c1d596003042e0b070184c1110f5041e000f0104092901440d50800e90100802c3d58141c1d4040303456180f29625868518110003021003a150030054503400d1141d4660141c100e140f0f038503411507000400204031160502d00324079905016000510781c0d80700300403600c25140282207260151075001c0c82c1042c950040f0301940c25a61181c0210f980d100c1200c3c0003031b0824807541f80c0344081403014110030362031034440325990459030041400c403031000510091484025805040d811030701e001501c030035280041010740246410f03002c255803c2d0704000740400c03592000c2851841144d1000355 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306255107 1250 306253857 306253873
    0x181b0102100908090d050705040609110708070c17061e07020703030e120f06010302010201150807140f040f2f03011203020316050105100902090904020f3001150503 72
    0x44809400200c1c403e4070105010007042c80203848004d00300503000e00403402045030610f84424001250201c3d442007032058a0079080b08054507552048cd54002d0300310901caa01c1c0d03078039801c010601d00c00035801440e501c114807204001225021505070702c00c0201204d080740440301150000f41c004402c0b41c1204c01a04000800c0c0000f0b40030312042c0b2a03191015115040d01d801d1507111929107070820315400c0c03c40e448078004004569090060410a1501c014201720306490407005c103654100d54028400c0507400304c0304080154842c1c40c82c01c0305002000b8802d000c01108000c921004000b003582c170805006d544220740b02003244145005103200c1d0f00200303e524680c6003008141c41c40d4032210003103045020803c0401281100290202042d030302032000001c190811859104454a9550100100b01d0050000d000580e844000040d80703d5015122082d003010440300141c0610a821003a00403240c00d01010300040c801882000d0311004400003c002e807101c5180400d40c204a10310510340c0c55400426 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306256357 1250 306255107 306255133
    0xb0a0921050a14120f031006020c060f07170f0712140403030c080d050708100602070605030103120c021f03050a0204050307180207170a020c0f0310110702040203181b0102 75
    0x1a0700c07852900340000c3e501310941914800f0161380c41005010107412003c8240050300d112040304400500c024001041c003401c40d1404a000307030203008190344c1540700c0402c820301802a031946502207001b00e903940b15034404845002c041c1e01c2c0c101842c1a03408a285525000302e95008010302403007108880d6460b428940395507001c0765880480c2a089a01c1030061080706070a840500071640101c1d410340b070b0086503141580d10204e2814044d8040c00840d40b000b00100049074015084030b0540b6005054010742050800302600c1154906200035003103079003500148410544e410180009a40703a030b40601458598800c020240d00a03030003043c0c1d168003c094101f100250b0b00322242104880c2d10009420280c41d80c65030054003044640624041500240b402010396060120080703109003243c8070303509500f0071004659500c80e000b103102038640e520251400a4020003040c7c41c0400c0c0d00900641d03032071402009164003844a040c80b440076114030080c55400d050040c0106241c480180c1c02000e040d84001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306257607 1250 306256357 306256373
    0xf04030918090b04030e03060708040f08090102010e0d02010213050d0b06270109090309080319140d0e0114010b0c0c190801050412080907060e040b0a0b0a0921050a 72
    0x2110800001c2d40d00d42c0031400050f561028688541c1c003d440344000a00c0c0300c8241070420000400304801c1100050400c0f000551801e5081d100d9500100c486440b01d01510042c3e005010f013076000401885802c803e80000703603054000303140e00501010f9200041f580e45043c01181c00c0c0e1b00c94014028a00e40c00003403a0f908240c03100c48101c80144212030403401c081144980307101000e800c40c44809845004034000d047d00180100000d003040340045140c24948600da00194128051032000c01c0420070032502c60320a544265090305400080c10440503154400c035030300034507003d6070804442e8013030800003400c0769106083c0c0703040b0500140640f030461624000c20507450303050007000014092403440440d00038030920900707201c1c80c4070301d0714243c560b040160090001c080c001c04030300542d40a030800f800080d80c003101da80361a680940700400e002103140c0009462030710b1030b000340c08200804110b01303a01541c0035000c00304546002c51042406044030360001d0105407030328000381055006d01580c800041c090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306258857 1250 306257607 306257639
    0xf04030e010309050709020f0f0708030403090b1c0b0f060f04050f10020d0507031808010c020f03031501110f0f07030c050f1c0609050609030715060e070f030b09041a0f040309 77
    0x7030441c0f030301d849c019a9024040760001c04060304d00c00341c084104010103402140c11000340041c004000d04021314804010403c100f10a049444140c03500d0380c1050644446504104141d001454240c448150401c0128640c1003441118031651415003040008d08104101214044007680a084480b82c450340c00d80b515441b4160480800c4901c1c0c0200c0c0c40e591100f0300070405400340400100f265500000000d191422000c000784a940081050000f4103072204c40f58054124217080c0942030110f000c440c00d0402110440c140c1443c0a00c804a001e003480120b03c5034140c034860035084540f83d0300e903014405a21300314000c16400503103c90036506000000b41042109520400b00840c0d01c1606a440300d052500c207480f002626400400c0341e8042020010b50b11074100c0500004002079890a5107031910040090021014008184081e0341100c0c0700780c00044103d000038060019600701403401503080e20103058560001105000481c1e03140d1300c6060418091a0903680390700c511030a0403841d202d0740c080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306260107 1250 306258857 306258877
    0xf0f1d03041e2111120d0f020109140d020709090b0109090813030b150d050c04110409050c041d0708070509120111070b060d1e06060503060f04030e01030905070902 72
    0x1070740b20001d00e0710b81094012a0440f000d20034940c0070421490b0200a5810008003144540001140741d1811000010b98422110a41c03500c80118002a03805034010318001002800d8031000300311021034007000007440020070381e6541c00c07220213680c2c4150030011a000e1450080074010f814004203c20f025580080440324003c0c4c0c0040c0c5010042102c041c500710242d8001c9402c08100c004001c208a250b1503945031a1a081d11742c60300030714082d51101c7c0c4a0741601e011074821580d075540000070082607410b4034058801040104140d080c041c1d4000740d260001e02c605201d81c1080103000c104040c04070721841c0500c000d40c07900e080070b40b2051400d40b2103801ca03440550b08032403c5100d42102c0402400b03105a2641301001da9682c404e0b25090820315030000604050084d400410b40c0d0000500c500f1001c40c184440404d00404103040c1c2ca4020f01401e8a40d00c02541071148c4818400e18541d504403150042d0300ca0b8440760304c10500903006400b520b600540c041c0080d00000410003112009030010044441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306261357 1250 306260107 306260159
    0x13210f03050408030d0605120a030c08030a0207170306100309260c1f110313060e0307061b1d0a0302060f0f0705100b0603100b1308010f0f1d0304 64
    0x748420a1a00e15008115a08810340d180c6c0c400b000310342440b00c0700a03c1d4100301400f03440304e4049034034042c000340030b01e1a00138110f240001c0010f0400000358103580c00345610403064011100455452102a0410ba131132074480c0380405880155580170b44188202a03500504009180098003800300344d41d010001400046002003000c2d03c1600000e000103501e42c50325000ca04014507451580b20100c4506a8514030403503010814008400c03a480c04820380c1652040021a07030040d041c11481c11070240004c020500743c1010f400c001003c1d2031303502c8840318404554503030207103c05c07044902e10b1101d00148096000814444280054140704004029040e0041c030520700d403030034214a4142c02d0380035220603101034209820350903804045000d41410b03200e003144c1a90079800c1104d220070618105210340c03094900005a001c00c03000040480c030000706440c2000700050403250030010090701c00030710480c40032803400c0b00000f20120b854112000b9880600b00031800c05041c50210300d070b4071494084086900b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306262607 1250 306261357 306261359
    0xf06060f080a02072103110409150807080309090a09020406030b0601030b2d0102030c06040503091201060b160f060c09090b040203040f11030f101e200a0504031713210f030504 77
    0x47e00c5080140001d12540400282402403c2c50740c5c482e40302c0c2ca800100700c1da000600f04003c0721400000f500c0c0320b10411036502549d6125002d20900030a44510000c6d0000e040810000a000541c01c1f038034441d40c0280c074280031000e14101049800070801251200d140a04c01c0440c50180c0c80148004014006004984c5441c00c15030446240030030445046442c1e0f0b100042207600b03800e007451140c1c04010b85200034850103040039030343d0901d4010307000c0525014101c1c0401c041071100c01c0d04103101c8160462402c0201300c0300d2480c01403007010180101111582801500702241c10f00d482102e00c04e54003e0b03c064010600b0356644040014020001c036458400c2c02e041101c14101446a44045408170500160280010041c141240040706000e9102481c02040a0042c52145400d04226101c9a4070703030740d13a2000010079165402281c1015040020302850407400308100301c0140b51000d0004500146240e59405450484c01030031449002101d8070f084040010b0064040850880d21a0030224181 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306263857 1250 306262607 306262631
    0x3060e030a0e0111070308030c04090e0f070609080c06030915070f020c010306080a0b1b0406110606090103081605010b06030405030912030f0f0306040f06060f080a02072103 76
    0x299812501252490300000303291841650801402d00c5100c500f800d010b61480303810703280c041d11103020384405401040c00100246580130b000e004c0b0340241c007120314204000c3c9505040180d50701e80e200c07480071040c85807000c00304000d40a1803245013126a03082c01000c10b01c00700c46c00c0c015940c03c068003c5210340f08040c03141c00f0004000c1c200504c00c0d030341aa140031901441840091510300410348403410705203031210500000a000c5000701da21900561102c3c100e031242c1003074103001c1c5114045042041400b180200d0604c0d44111402d80e014040d600700c80154550300200480d050080c40000d18500042024156142003100204003c5008000000d100c0c0300c035070003003009070780110380481301da400c002030200740c900d40181400ea806000f08029820405804940c00b090b04c900d01c001d0082010100006141d41c0d29500468045800c1c00c509014003a84c409004d003501c0da500d504480031558000c00540808014400d80d219907800c020000c010800c1d901c003200089010400f1074040580b034007402c840d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306265107 1250 306263857 306263861
    0x1b09030a0210020307062a2006070903170f1c0204080316062d0b030c03070905091c0e100201090b01080f0c0306130618060e03090f120a110a0306 64
    0x21210f401a550f82c03001032521500719180301c2c515080d4000219151480e0820103c60700001004605001c007621040d82006100c460002c01454558030501040200a940c80301d0160304030b80c41040c10102403038075014203420341d0050b00c2e4028200c05050000c0341680c011140d040305041c10303041c401440c1c56207a56505042d6840301d00040c4c0b807030707072a040800108646c5100d032204102031030210307a40803407004101c9140150882044003840d9114042d42d18079503401e204001c1c0d258801011a20300302c0e6583d0034100500030441e92200300c0e0050f00014800b5040d80d0180036074280072035503415164440402003110325503484008100715981c0c1c243c400d0001f400580c185020300b010500030040707a000324000c01c0c50170348480c1a460007500818284045046815102d40843d07502807004540600405103008284500c01c40140c6190b043c030340324210710140403000344410081501da50b060700782540309101c240c0d042d210f5200712a43c0135a0081d4040b074400381d081110005c0044c504c0b07902999a840e0141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306266357 1250 306265107 306265129
    0x120a18150906030203100306051f0909050c03070f0e040c0509040c030b0114061603210c030501060509091f1502030c071706040f081b0c030606091b09030a02 69
    0x8a2200a144411000341c0244041c001810549015480c500d04481c1c40c0d5440c8229200c0201016260710100b004801645a0f40c000d410551041c024680d035111000f1000c2d002400b000d40b400e014803200f0015a09000c9458826128405c2ea1065001d2800c60f40183c00309004209481c0c1c90100c1401042c01d40c0d0f59035059001d5401400d0740016613003541020300c11180c0603401030706d802d0404c0892814945894040d0303000e401d80c0140c6c40410780c2c118181130350118445082c03001c45c0e038652003c1042030a0198441c07281c24880355010019aa2500000c2d0ba0a01c40e081280d94400c0a03500001d80e500d2201c51850042c0100e580304440a980c0d40076000844040d0b034509001580000c121441e90703810401c04c41c0004c2003542d00c1c0301441d0382200f001c582c62358400b0b40045d1504049804035000e20082d5000c40759140d40c80310a40c82150135a114140d107030f201d4284078070310a000d118040364107454400d8400f40610320901e4451915000c1d4549072076258428400590540a605102005a601c1986100c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306267607 1250 306266357 306266369
    0x40b0d1a150d0302150a0203070212090a0f0e250804064710051b01022205031e0d031505030d0e0a0b070b070c030e040f0606030e0c03120a18 62
    0xe128001c0c042c40044605d40204500030710f620610401c00019400584082d104440c203040c20b40d90701d04400841c1c11030b0015041076002c030400d0600050b0040070b42e90720511030703114a1804140f602080c0707158181c0f44807030135040c2d00140300304004c2408603810340c1c0410541907008170301f00f904040c20902030400c005403010a0b00b01003c1c4954100e20150503d2640e050080d0403216541480800d00024045005e081c150904600c8084031030a15424254100e03542000d0740c8034144680d42c00003004181f114003034000c69009014610300f100b8a080c2c3c1d00d03c6154411409001352405219024046006102008404c0c040c1441b0400010b42900c044c807850b41141c80b40d59030000281c040406014060740c40c3c1c0d01214850300c0421800700425500d60382d039170708024180347c45103507070055050890328132111000c0c940d401864607907800f4a14001d80d000800710b50381910240b00810f81d02100315110900c50010540680081e41c0a05151040070003d207420080313401c0c25802c092004840c1c013204041c81e0019 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306268857 1250 306267607 306267613
    0x30411040f0507120605031212090f07120201110102090a0e06150c0a0303050906071202030c07061a1521250306050a050904120e03010e010218040b0d1a150d0302 71
    0x3209824944c0d01401c409004240c0c000c01d100510200200b0180c0700d090440500d1031140d10110f4071030f90301400a0380c100c00200c1d0031200c40700e03180d000c0b5441d4540e000d14200d001c2900124468014041030003030301d42c1c400005080c05803c0707203001c1c890400c1e2180104800c0e804510b500c0f44205490380ca101030150480318000500c00790103945000350407580007808208050b80903008014407958010700504840005440143e26500c90b20000d030801c9c016441d00034030440c10012400e20000681c08004581c01c01114915803c40780c410900c4c01520a10100400d20031910110382010380b503d07600380d60400c2d04000a400d070650110700d0180c0c0c24045202d800b000a884203010061480c08802180c0540411a40e138030349030400c1e50b514001640380c000b070002401051650036810756000e61001c400004003078003e544e07a1001e242d020403d28041449184618035142c01e030101410301500c01c90100d42d02440007110744800d1030488403191001026198800402c444400c20b9403030354030301048580d00c80d07001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306270107 1250 306268857 306268877
    0x403030e0901090e0a080c07170a1a01141c0209010e070e03010b09160c05030c0304080f01090f170f04090203010e0a0b150f0d06080304030c090c05030411040f0507 72
    0x8101d0008030603031294002d2810030400c0c80c6058004036240604a50140c1401d550b56590383c50300c3e04091300b035403080300904090709040141c2c5001048820040384210880500004c100d1003180700d1000c00e020300c0103011440d0301000707080c0c200f10071214107004040f031001e00314200c241e001600c0c010702604030f491040c88060900c883d19070001011a1211001c800078400d6502800201d407546c64014404103010360404e00c04280c89000c2d454289185810500381c0e55241d08845050355650300600c2040ca052107250f990fa041c0d41010f100301d50205031320102d072404400c1c20b0384468125a9a000d840c80205400708441141c4600c44001080100101013001d0b0b02c2e585080c0321030103012002000000e406040c0b0f25411aa5a50700a0100c402409a071845495100c1151041403c1c0280c59500040d40d19007140803a0200e00040070304216481094035101c031030740750070402c0d0a60300c0c0d80460700c1c0401d806001003800951070100302e4180b0071024000007041418a000e007001e4800c20b4946501007030091407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306271357 1250 306270107 306270109
    0x30209060a0306170d05070f0201111002030117060108060411030319020601210b1902090d0c030b091507051e1206010809010902030316030201061a030f010f060c060c140403030e 78
    0x628100500c13003001074800c0010000c1c0151140c4100315000704490ba081c2d04102c2168002c104407000d11030000220f416004d50102600300a60081c050400f5a4500c400d250900c420300003016410380d040726029004c552115a100401c442c0d00118941d4980414440c2100c1c9600105101c071303c4134501e0740201220751400920f002e890064900e1009160003208c20100820152880150894440c2c0c0e4009030482018202100a01924801650020310240c080081c00040c0e081c07031b41a28001ca04d4a40d40c0d0f15011001903841e1a02c00300c0c60301c07186e8000300083c0300c98090360103040b0b010042c250740600720900c8a100300a0740e204242091203410340c00140616941c0c0a582030394402075900003040441c40b1a000030f9500d018a081080311640c454010200301403007904480018400d200000072a1124107000030003540040318120805450080001030110580340003c003211030503181ceca4407000c0c0d9515003201401006010310180a10100310034900000240280011030082e9100414202404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306272607 1250 306271357 306271379
    0xb090f011a03010b160302100f06031202030c060414030d1b180605070f0609020306090d080604050f040f030903080a0903060e010606090b0c100618140108060a0c030209060a0306 78
    0x210801015140900060044c400a5000c90340105403000924020341001e18049107001000b4048010040c2409081c0071344410903006039040d03e10400908218600740c01d012070741d0b802043c0900105500100c00318020641e8a10f101d41d0f034041a109581c41e25001c580500c050700c0c61448100e24564014211300c0d021644040c400c2c0c03101d00580e10301c3c0d00d00d51410000070014050f924001d40382d1b00e1030030155030400500f0f0b84418030040c0c2c043c0590b8402e14001300b009031520050070703240011030081c10001d40742c4c3c90036200d294420344040c0341c01819038980381c56041032014220011002d019816030b010011811802c0070b091000e0b025951071070700341d0551034a5010394598404000c8540c0c1010028000c46400c4a8000203441c000c41e84151103541e0701704007614080511540350450b07403a00c28041241c14550300315021070404400c0c1841601031480e1354102c07a0700248281c000a401101c00b0401007500f0b0f030420400c40b1070394600907081c442060005022588071031441c2e1302095a65204200540c024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306273857 1250 306272607 306272639
    0x1103070e030c0906100f0e0a1e090e06070f0e0a030516050406030c0b0703180608061e180c0702040510050a0b0406020c0d08070b040609060f09020f0609040b090f01 72
    0x65410064904100700429049440b00e0008030902000011107200d40c2d21414032032900180c000c280644441d9609d0780c43d190b900708079a1298549690340c402150961036802802d90010b2200d0042005039030f40c500440b0302c00e4505480d4020480f80d9003c0c41056901c46410a020f54007a0015044040f410410130b81e0903c01c5900c8079004906140040002c81e118061410442d0152000035a80300f40c0c03464211008a904440d088a070050f0b4003001c1161a8081941442a0310079a82d80c0c640502d040d9920741040d000701070f202d5000c01c1d01c0a803401c00d4441008119000840fa565190601c01305030f00041c11b0710011603203101c0020506404203c94600398024200411110f11114580b03428808000d407101518200c1c81e004001d0822400108202c1d0011a10a99045041c040c84d5060501c0c18202811070796105030f90050404142c41a03283c514822100f860f40e000742440140c40707818060006d560441c050f2250f00981e1580a118180c49e10180948140c0c908030342141258100042010381140c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306275107 1250 306273857 306273859
    0x506011b1202061f05100e030d0504081921030204080307061b0306080a08070f06050c0d0e0c010f2712060501060f050a200106120b0a110304080c011103070e030c 71
    0x100401301d1340b0f02d118164004096034020380382079000c0345030741c103040e22110000c00c00141c0503c121040041e0310703035000307005d0000d0b60700c0d03e026030f14100822246108100304424000d80182a115910107124070032005c02c5d24080c0d0301b0300f0302504050b0782d4803200742944c1229a003912107a440d02c840f0f140c03007007031b0013030b16410f8507903030705080101c03d09182c1c141d0b5880184903c0184110720001c0d4400c02d00900360004105c3c00d90281080c8010b00d0604e60040c0e00740c100718010840d05040000c501c01ca541d000c2004403e40e00c0603075400104000080f4111001c200c400c05400c4060402d044061240110714141c10141c0007044824149882c00d2603e40d080742c405078041070420150008405071103a01c0300032a103d8402516004e0a0400d0846407100c07a042c064044000315803801c04005601ea11007508001c40c40d008050280c06a03454050880c240c40c04d1103141c2c1015101000014002026400680b144007002000006c4d0451480d03106a039541c400c0d1020700100305d0b101d9500a103860b00708a1580d0b91a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306276357 1250 306275107 306275131
    0x9090c0519050607060906020a0903050d0306080d0309020d0501050c07150b06030f0619080c01030608030405060d0908071209230f0907030e120c0f0307030c03030506011b120206 78
    0x1c021180e030a00d020500569200f0b0800040d000b0520040d078104006e8243c002d00e08540c1e03180d503040c01802d050503600c0101c07281c0c0140d0048074100c1e4001d105520464201c0c0d000b4058117540e09030304800403c42400d08a030301140301c03011701c0007040c0240718151041042081c0c0f03503a11401800e00300038464a1040004126040c0003080c2e803240c460f60150780d005900c0b101ca40c00ca51b122803000900342000c61418466280b000d9500203000040001da1000120f400e07242004503e80311241140c0303078850b80c022140c00a00c104420030740800268800d5a00c5802a500c1c07034200341c503030351343c0d204800d5500760100000703503a00509003c0359807404900051406071014181c403e4030854089031104041a4405200d66208000034081a0003a0850140e000400081e11b851091038270103040160807401d2441c0151186400b010079012000040354101d1343c050300d41d01e0b04542199011006004010050b604011030103142c68962054445003803451449604140642425507100a1070158014141d1070300c16 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306277607 1250 306276357 306276379
    0x50105090c0a17120a0504380405030a0803130b070306051003060305060f06031f090b0a05090a081c320c04090e01060e0403021b09160e0f060409090c05 67
    0x4140050284d80413a885400561a0401c0070015078090050ba4014041c481074154144a00e1210303007000070760b20910018400c500c01052156812074000d5000b641d070580e01c0300ba840703004070f0200c41c06154400302c1e9100d011100301c0306503039020310480e041c0c910f14046920f0310018055403030003290341d100e40c2000d49010030085185854460361007401400030440c1c11284400324031191001d110b514413403880094a02030141c2160307294001802d45000c2514000050070120f00824950b002c0e6502454007003006000e4241142c4601100b41c1c40a4122001c1079500307088000d11110074007850010a00c000700e010798511805079000c40802400116100d080100010418590450002e0301c003031390b0700c0d414000b40c40700e1201f0b08140103010503040414903490b84003c02041650001d21064a00900200c9640132031045040c000c9000c02900c1089030051800800d1141724400c8655020ba0b060040c42090030801040201c0d000d540590040c2541503100c03100f0405209001e00e404c0d005110584100000c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306278857 1250 306277607 306277649
    0x309060e03160e0712061d010b0301050a0510032309100b0a060f0903060f0203100f0b0304080a021903020f0c010903020604030f0203120414040b101d010c050105090c0a 74
    0x81e00c4140110791140a00c1d101044056126170030f00c1102440b8034070300b0417402ea1200c0c455081031051f46441c907283c40320900042039880481c0281d90403240041e00c030728400b42c1000c081105100b4100ca900c1d04050b559180034441d00b00c030801e1481c2c09045141c607240c0384d0501201c2141801d841c040300647e85402c25200382da85803242e0044008032140f915205c030800b0180003040300c070742070f01d584040d01c40390800ea4a2104a901c0383e0046000d5070300d080c0d41e400c14036503804800700b1000d21031050740700e4650284009404142d038600204100245441680d035400030700d20f6140d003003000d9001e0640060307000c40003050320b0390020132840040d0282400d007110014070716800070b003162003140801402030300798003211030464a041011110440c4c00f01c202c15195a00d42103522100e080c2e443c2000d1050b81400710b04401c6040200d001000040c150361400585040c1c103801d4003181401c0907446040128011040d00421000e00c1018000d100b10400361240148840401c114601c2a4110f0450b5001d0a8000492 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306280107 1250 306278857 306278893
    0x190c050306030a080c12030c090406060c0302070302013c020609120d090309270f02270109081f06080601080304030303271101031103091207060b0d0309060e03 70
    0x600e039070002d40550b85200032054541032528107081d00e04646c0010080c80898041c08002c0c0170041c609507008c00040345d440c8405c03103083c40b42c42006001341e00203a0090015510903054110329580b442440624401c128046010f08901541e589441401c1024810803080d4127010158200707606000400812810a542d440d0034859808400ca020390b5170ba142201700750142000780024005526008110781d10030703540b003055000d00c0c215104100d1400c100400740710102d209039044a0344104007262020101e8038074203041511180a03a042c412940b0000440701410080c005100f05100041d425aa081c1109a401d40303065400c044070f6600840c1c018030990800206a030308403600351601040f00400b0000481e07452007420701c802180349081e1000c60138403014007030400018000f03030b030104507400c001c3c1007007070141c0016a91080300350030100c00340750316a9020000e4040c01b40a24000541d240c08540001c070220303620f06045001c2400400d0801c42550400c2a00c1000c070350039805400301e110782c0940c0b002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 306281357 1250 306280107 306280123
    0x4020414061b0f030403050f0d140c15070302130905070f0503070309020d03030e1e032205040204030506040201020d0c0515040f0f030306090e0a08030601031107050105190c05030603 80
    0x40078000c080b55542603070350020340b141d08421003101a90f0200c071441414a40301d40c40b90206035004e20681d95206c101c0400007500c0d6030750800b181d80d420703d40b100146201380568070082920b038540c031551344007410600d10283c0850049545850043e07580d031310900741c0a074803141940120802441c141c20840e076680c0010349082d01031000e00c0c0c140da5994414005800a1050342c4001c1d400481c400e40100405406502482103200c00400b143c840803400403148682038000400600250428000c0034540e0301441001080b2415980c1050b09040e29100810200d822645c41610f039580031205000955070103012590f4900350324a03060340d00004940703d070f607a1074200c5150484040200300000d010321000c1008480c1040c2c0c400c6445080030b81d181402000340415018001e51a49089a10030031804d00141071820fa035848030106003145d4403400150014400501100e04540e01009600d000038001e104640c032450103507172505194402d01040310129042580440d0a01c00100240700b629900021445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 306282607 1250 306281357 306281359
    0x309020906012715030518151005120d17011a0306040e060702010e160303140d15060915030504080d0b030c030106030302010b0f03030f12090312090102030f010504020414 75
    0x140c10340018035884400300115420043c28640d100200c0d160301d01066500404d6120358091281d5210301075072681001c001d401c10305459110310000c4662050400e01c081c2d210f55074002c0c651902d5039a0b0007094a04040700c020300d1203608818440030b6290740000c83d40461030b0b04804011482e40c14100c14011035101d04203a240001004000103809581e180c102001c4031241805564841c01c003160b01074007134440c4101030003113030094044050500d40740144090850741c0640e1003141d446c41c1640402000d80c011100d0034049621008025004825442c803032008000694500618500e8003102c0e14440080c166601d080608120030f001c0400c0070642620044409c0407000510f21a003000028070788110b5a0146403d035081190010500d601903018427407004056840b261991640c8080503280c0c03107a1441c40f071560b8400c2c40000410310b900c048040d0f122003894202c0c0e18018082c0014694100c1c00c8403030819a139000010070001c882400d61391780c010070781a01e080d81060309062101c054074848600a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 306283857 1250 306282607 306282617
    0x106090b060417010f020711030c01030b0d0f0c03080f04061418040c171e060405091e070e0c040501110a0b01050f0a0b07030c030f0509010906080604091209050a06030902090601 78
    0x40d80400401e501003004201c0c1c28400b1559440301d440c060234480032194409100c0d0152580301c110a502078090385031117480040450a209250f0780c0e8041800d600c4a40c295408e60030071101200240308500205240d40c414880c06840305d207400700c02400a00d0500100109a400f800b015000b101554182d110f0044121008264125801c04c00c0b20707800e1320004101c8044c501d14040c4040065007500c00c3c0c84140c141562140190749620500094800950350345486a01a0003625841d5032201c40d1010f5483d2654155030001d84d03540d0b901e03000c4c440d094420f0200342000203801c011542e04110600000190007000e44140c00700d07511140750300c407c1441094011481002d901d181030b5242e60204c00034000720044a500c50030745080050103608411070450115074041040c1c0b840c24007580980d050840305075120101c0f582080c100b290442400b410140c0c2040d110186040010702a0010b17904080450b500e00040d2441c0c50100141090180c1c041c5082c145000c0d010409a22000d013031503030044081c01c007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 306285107 1250 306283857 306283889
    0x1a071b0b0702010c06290a12170a0203040914010f06020c13020a02070306020c070306140f010b1605030304030305100b0414060a0c020909030a091505070b0601111207050106090b0604 80
    0x1000c40070340404d0388105048a4207543d41050001c070086d03003218195058444205036515141120070200c1e101d40b0113400340c420180c050f0256a1250b0085c8801c0310079105403401d09540350180010756031510314480e613200d8010010702882c040d8102c514001c1500b0b01c000c00080c0f944e02c0220300d04003e510366000c003294001442c0040c69000704032480040d988104110b42d1000070605840e1241c40c9404104c4420f800c1c030a40f000c4021031013540314000c00030f0510380a226407800358400500d5200c1080310210350300e080302c24004540240060351243c0c0c040e480c0860280341144214000030001d030400380c0c0310881403106004031641a1451078a604003640e51586d207510340303102a94032401c1c50b80001c1d030008081d01004a8203c0c040050078280850f52240000700da1124000d403016080d00b003850780002c00501032000441d071303c144080d030040d00606001c0c005940c1e00d00c074981016010583c8018000300015031400b0008248a01d070700a0041010802c100340b40480026690b11452007078501040320448 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 306286357 1250 306285107 306285113
    0x31e0506313f020c010906030f0b04020708070c15020304050d050312100e090703110103050a09120c290408130807150216030503030601050f041a071b0b0702010c 71
    0x700320620003806591899080360700e00e16042c0200030150003481c818402015402807a0000800c515003030b0058458140142c2000c2c070440c010301e91b4050b586901034407480215040d48441c402007180b00e01502460ba80c440d03031800d208440700460380c0845010301c051503080809a5011041d202607807011036001182c4062410401e00d1402281802000c9034104000d00c002541c0b0030400004031849000d00c1d41c92584c52200e415191000c0c0c0c44050400c10003040c2d036030302e41d600c02c0d848158054891003002410b405943ca980d5005035030740d2200c501080c107280b01241800f10701c402e8202940701310f0a00c030400e100e00b03041303040d003201019100034003000300803811b8025a5108014400544280030841b14001d41c1c13418404041025a02da14000d4028401c071703e17000500d4108100b00b038a07000801149103490b40d0b0011269544202558100c01078203010100700b55812500c4d44202070788c042c99203034131101d242c2080b040349244030100804ca0045c03c4c001700010b2200a0036200c1c00ca4090800d82d1000320141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 306287607 1250 306286357 306286373
    0xf0109031209210b010603050901020c01090c09110421080f07050a02011205042301020904020d060905010e041104090609050f0f0d05040f0909050304031e050631 71
    0x181005050184852036044420703800410403049440102c0f400011400c01085100441c100e0751001d400902540300600c48503000e40c10058121942000040c80c15031031910141c21120807405c12204507408031410041340313040c2d0040d0b1481c0700c1300503100c030f140915200d0440c00086d13440c454640ca907103080d5001c005001451080e982c60150440d01640d4842c000c1c43c200d40c5410349100124049003652481da0f104180c20303c1001c1c802c0f0b512060400c901c1d008120182007a0000104c0b09050f9902042121a2504c4500140802404890010420354240314044042d80d01c1600205100c0650031b04000200c1d610402081c140003091321300082c2002c075420504040c21340d18401034154415403440507140080011a002000880001d650a010072000120780c180300303c0c071a6501d0315840c1d00c401c1c03141d0f20080c2e000b8076031140305908072881c240d52079641c00c41814034022203d1444003106c10390003d105051001940c400030011114101c5039210b0a00d20102000c208041c2c9082d6403a500c0908204600b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 306288857 1250 306287607 306287609
    0x1b12190219030c05030111030603031803030f04060801050f1f050f16050a03020d0915082508150406120308180609010c1701050904030f021006033009050f0109 70
    0x118540100b916030400c1070b48054103101d8180030398a05110791480c10601010359000e0071008019610b003600c4800c0002c0c504480c0000b40750316001c02c00064407030a001d00010002002140ca611540758504003c002441600d900414026210325070003049160740350581303100702c48141c20141e84806580420359114021a8203001141030f0011104003844400900c1501241c81380c3e084030312240c00c2c00400c40380255244a0b0b045810090307041c003608140903003441584050b292100a417000c240b00c0c1414a8200300200b6040410b44500500c0350705400b08009038982c40054a0920030710b460601203800700080a0406810000314001050b1415404205611003428607000c442c041d0503c580c80d14001c2c0810203a20010600c1b50001c216600d409002250403144010076034500c540d15500c1c01d40e003840ea488400401c46c00340c405a540700400328800e8401540c01510741004030340c11018200c41c84014016025410b4111400c0d1402150b03000d40f001c0f06a0b2025117526040d14501001a5103405135 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 306290107 1250 306288857 306288889
    0xf060a0f0e03010c030b10110714031f1d030a08011a0d05010902030711120901030e0f12090405010e06030615060c1f0501120f06020325021b121902 65
    0xc0ca2144d0400c2036140c2c001c0851420201c41014030310290200a031807032000c000d074803ca10f42016408003d000600c11100b01c9512020b000e507601c240b4403000707100f078401c185a0607900b8241c0d01c030012411440c00082c5444d020304540025464081c10a4028126a40502c64150b181c030070028a03101c2001c04006031802d0380c850001c00e005a58540180b1000303500300700e1f40000083c1c5860701d84249060001111030490121140c8603140c11502001140504918042e210f2180b0999500c40d80105040083c01410340500c4101510346003032000300001da81060b4001d0231200041e0090020554002c140c10b500011504900b5001c008282c0104000e4003032140414071b14040c420039103070021070303c10703061034a2400ba490400003603803207100e80c25082d00c0c000c00241c260741c21441880f00080760340c0d00854010300071160070107520f00c100501225820116107800016040b4a046907074543d1103110703a03005410704440084e9010411011543d0302c1c001c2100140f00d40a14407420400c0d03440380792106680c3c140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 306291357 1250 306290107 306290111
    0x4030912030905061b1903050304061805030d0b040f0c021c18060806030d080c070f0c050a0801141005011b080405030f03070506060a2303010f050a0b01020601050f060a0f0e0301 78
    0x45c421959101982c5c090080000307004200300251120440c41c4001040365050310380030304546503034552800030000c46090340b40341307551406414042001003003d480404100c903000306401c881d01e001e004c26034128490a6a8450400e00b04000d170350380100b9840042c0e80351109008040260581c1210216805141c0c45105855614007103209030b4032200280c170808003503084070700325003280100301c6158408561154801c0c0c0305110200003c0d0f00c2c10b4519001a0141c424601c07074540300c5000400640d9076078840203a603036582c6c2c5080b81015108034803540c800641000440142d00d0880003034403032995a40c1d10000360144c0413880d000c006a403003c0e60080d103001b03803c8446407980308108590340e51080009075014460000040d510b8030b041148101980e94604041c106203080d200c1815484440100b03da605549034042801480707100c0c81040d2061304460340200f0741c01d48100000e820f015040e00424040c2101e000d02008603100c4104a50b444031961801603540f50519400302c0d041c4010a0400d54154 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 306292607 1250 306291357 306291367
    0x18010f0f030c15030902120a02120d0206070f0507020405010b030a0b0904170d021e0a14040b07032006040303060519050603040803070c0503220b07021509030c04140901060e0403091203090506 84
    0x9100099001c41c1d28800c1e501400d8001e51005810365401d40c410242d2f0042e881140001c004501c02c0c1881072040e0f807035003840c0381801d8165002500307645d0240c00c9044c4045000c01008500c84090180c4072a840c42529092000d0806850341100400f0318102601140d0000451006014190341107551030400441030540341c0100b008204215802049a80f0015282920040040e40494200c07004c071405000007038036045031540d080c1c2e20003543d034000a0741015011101000f0000512640744206d110340d80c0020880e0415040102d00701c0600340c4d030340d50921206001d0000392106400c688d000760b0800e030b003a9141e0751150002c403041034101000802c0c9000c01309141c1284044040300150070400c6da0805003995882d034504105500540700080d601a000c0c2400c041d2840301400140f91001d8040c0c02e4610100c407020100c0c007a55903100521a040c2c190004001c81c02c00284640c901401030f0403940e280038100f54500502c0010326004d070707008072000d042d40f4408040c0a0f036800c5008000c09408140c0358 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 306293857 1250 306292607 306292639
    0x515060705010f0e062203050d020d060302130c091a0906070515070e06070f060204230a0609030213150513050708061f0e03010b18010f0f030c15030902 67
    0x40c1c0440b064a201c020b060940800c541071300462141e00c9503102d40252000704032549800301c03003003100c4c030b109405124007008034141414887c0010f10300d8421201c0c010030b89600c3c3d0b02c14815819000d0701405660341c50801c0c0018019400441c0300111090401c80e0040b0b101d182c070701884148200400c09511110000e14002080008500c54261695102440764035540d040d0042c2c86040758540804d9020000b0010039000550100841684900505005007443d40340d096407103800300b8184200c10b659840560260071413409074144e0000d8500e601d401c00079a8650350124081e0f10106540081950b1107418801400305c20780051f000508009100280b800c9107000c85400800061341e644c0b00041d032960000b0b4050410b210040704c60400c1d142404495140344904032050000c404185d0303030554840300e04090344d5892201c111202d0300034010006103945441e108034040381140d17000004229035068100045250010b4010440d1f52002d003510302c01c2e014050407402000c032108020340c8106001c00c8007405c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 306294964 1107 306293857 306293861
    0xa11030c18041a0915010801031e02040207030e03010c020a02010e100e09010b12071103090108130c0b210f0105040c050409060e070f05090310051506070501 69
    0x8030814031030002800c0d50360543c04480d04030b00c1d864103014145002c140080d04250b0302c40c120500c0424110019041c801d0500c8058505034400302841e25201980e202c440e0200e40c010011580c1d00305526018000174002c05903240a90310740f0035043e0300b6a000190f83c515864050b1280c0100911080030011107182c60000c603000c05c20382460724249502e420844a02070030066110b0342c1c031072822240d10260b0840c010464030070040c201c65510035120021007101d92070f40e0700b86040903c9541c4e020034204600540080241448000440055001600000313000b980380c4400322200e82170b004150b0240b440c40c080d1001d08155075184010480b42c5460f9010401c00e1034a410142d0809070396100000c00c4510a60020388407200110800c400a076000400f00741c04849403e0260601415030301190355040240c05d032031242c9503030b80c1c0820a01c028222034030b80c003100f000700926900c44040c40c0081c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 306115107 306294964 := by
  have h0 := BRFrame.cov_init 306115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 306115107 ≤ n) (h2 : n < 306294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
