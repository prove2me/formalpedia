-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3590
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:51.567424+00:00
-- url     : https://prove2.me/submissions/04b5754f-c0db-42e6-8fa6-08de91781d1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 645503597 ≤ n < 645683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 645504847 1250 645503597 645503609
    0xa03020a0c1e0b150307140a0503030a05030124050d050604090203030f0a080c070224040801020d02070201031a032d070e04030f0c0201050a120213090c090e060a0b1b1009060e06040c 80
    0x10187d42856030024418812a510aa50605c070000c0c010010750b5004000c4c2d8102d13000740d01500702c081d828290301030840e1219484040060424440b550b042d1469800036908108043c0000400e0b41b03041d0080380c1103901c00281d8500b071041c0090b1a4040c41c5d0f0141c50f60764032064020f503081c10081a90300080044402c0400003d510102041e404070028601044030000c102010003107503980d0001c200c80020703401030306090340440d01d00622605001d151704841680140018060601c102210140b4100030a4811164440010b54269502c802004100c00006045a1200d0001d20701d00303850010404080d4015040401090311000c000607608941500c00e10041070501e200c0303425a02040700001d015003d00c6104110b0700880001e0b403c0e01e264010904038159958104485403100c120200300381c1c0c251591134102100000030800d074400341000c0c100f60514a203065040e400e210990a01d4010400c210782d902a0b914032000d402c0029601c600c0158900c41405880f842c82d1986035640c0ca1804c42c4101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 645506097 1250 645504847 645504869
    0x91203030902221515021f110c0709180803061c05011d0106062a020103060803040b2106011e180b040f06020a0203030a03020a0c1e0b150307 62
    0x210071555001c42110404800281c0b6183d22801c15039102c01030400c40d040c14034180c00a49001c2105600705080c034002e01900e4008080158091120110344d801c5140501011a80c5100c20501015044c0045c4540c40301c61004102b803070b003000140e00448124000c06c10320b007924040746000145136803050380e0740560111105032603041070103002d0488505a800c01080b80d460540340e51a0b034032000501c01d000b201c541c4001c1040d43e03180c080c01d988050084c0c2c0d40340ca10700c503402c550000c0d0b8502c0c02c40c5140b03000c3c0b06242c045000c070fa4682c00300e07245400c00e4101e000c01e801c01040401144011001030f000d01d000d560500002d03404c2c0340c00068020054008034541c80c4090288000c0c8490203403000004507100c080c1c0c4510250f9903050300d003845800c0350203002801c500d81c00300011014030004040e400d89800401841c41d0000500d0150000e50212410300e041c04190508500482c241648a099442c1d08603080a0400c0070ba00d0f1420040100401c810b84000d04400084510b8031300042c1c00054829030b40607 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 645507347 1250 645506097 645506111
    0x50915042909090403030e0f0627010f0608060901141605070c03080c0f101103060904110301050a0209030d08040c090209030c06031e07020307081c0e010c081609120303 74
    0x462107120782c0d0740d400c2c0c121008505210802d5819840f058240c9840010f40e00c102c0c009004094890009403808a08084121a8031400da007001545130121f0400500000381842060700070700c00d5540341d601482640e000841001640a02801680c003030061402080c502840d104100100200b980340c0d400c010048003003003180400c080100c100011715001580720761035040213078003140e80d04200209490070b8010380645c040100450f024000d100001c403100182140e50b0030050004e0f40c8401002690707a070303c4429491110b0340302842494082e03014100c0c090f1ba190a040c1c1894980032032030351b009040140c008108008104403e1200003034580c03182025989441000c0000c1c582036220849984c809000414401590400d10140700c2504418140350305582e10503405036140d00507084050180201080b40c480324680080012600340c04642e000039000c0d09501c03015084505050410010401404c10710000c801420300a41d9030100a203080d0075214200352160311074081030720000b001d050310b03944 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 645508597 1250 645507347 645507419
    0x120c100e04150608181911180123030606010309020118080d031a010e040e0a02150304060c05120c0912102a0c0f020307050607050c01092c0402030f070605091504 71
    0x40c4100c460000508234944820300ca005000c4a000a1040c401ca5100102550940c120072280c203c44555001b0040d120310764424006501400c0415402c9040000c0320f001d120000c020751040101400e5400c00506400c0300000d0007808655030114640d8080c3c03400e0340c444a0310303a440145904290001d80c2d0116082044240c060b1a000c1d28442c0203601003004031048080194810145200303078011403050080054824083c0c1d494401c0c2106400b05482e42c070001241801c204009040740d030406808403005240ca00712413030414040105000704d82da11540719407401030907421010740fa007012801034440700e00010000f0b403a42c0251134004001c01d803028924015036909211060044c000a0610795580711280340080e1030b907030104500b170702203060003002003681d10f1460304446242c141d48003e102c12004122003420b46440003082203034103220b401c078003000005e000c1c13003040020000d80d19080d03244d004010420164060b2484516141c3c401031004008206405040816900c141c034010039035a15101c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 645509847 1250 645508597 645508613
    0x60312091f140d0902180103030206070503090304150509040b0a18051f0303171302010e09040213020d09020a05030d0206010b0a0c0f0309080c120c100e041506081819 73
    0x40b160252103007000c00c1d030403d4610b454002c4208580308a584024019032080c8031046184d00f80009030050340301000094540c3d0095004581002480741100c1c03e060340c0e4550b264002d041080700300d00003400441c40d41801e0805000e641942401120301e860301908107010392003088610210640050340b100e01081e151901c0d10410303d1591040c0d550071600b00d449040103040014401d1800301a0000c036000a100d0078101e00034500345940c140e492541c1e48050b02c3c200300784501c019006a0384240038255248030399180d803009002c0409031460110342c1c000306004110014800d03900081c0aa000914805485980410444d06640c0c07840e01c15500c458203d00304a40d1350900311401412007001c00005000d050300034404100b180e07200790840b0713040c5018009200b00c0701c075014540090b81d0300010360610389280810745140103150300c3c81c1c01140f06c50844001800d482030b40c61044218080a0f500b400090342c002409075014030b44900c4640460107071054203070380c0c00c0c110460b0282e02d03c901008200301322a0b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 645511097 1250 645509847 645509867
    0xf0405120a0507120503040203061008101113090b040e061e04142d030a0c03030b010e130902030d1b120903050a0b07020606030d020613080405060c06060312091f 71
    0x202404406484e10414040c146610913941a4401c3c031030400020343c0c0600c0c05800381c050702d03880f0303015040c0119001500d0015000500800300e00c1081800300c00e0041c1c001e2110702000b41141000410354210203c103000c1100c00004a000302e0f41c20100810140703000c02800c80d000b40318414110f10b940d6450342004c01245082012121a03402414208104048141401c0c402e0ba02003010180d002c890804102d540c038442c418402e0046401c0382c1105020a01950007604c001c041070401855011507800020b20000812014201e070603510840081542410480071a65001c203003030807000c038036540c14140940b0b0320350003006108100c0340551649140c07040301034000569010302100c10301c0d65249461034030300760704581d02c100503ca4040065540d00d000100440550502c3d0081c006949501403010802000d19009440205040200284e280c44460040240302180d41c0a040c1a0070410101401d00405020321000c041d4244100d40c01540c514800740e5140b4048210136854296000040e40c280d500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 645512347 1250 645511097 645511103
    0x31403041109190b010c0b071d0a03051f0209061909050909060411150703030b030304270506090c090f040b1c0b010816060807030e0a1203050f0405120a0507 69
    0xc2e060900a010030b441d000c181031440700201c00c0c051092450011228019a0351001e810401d15801061200d801000c90000358102880907920700001200440c0c0310040e158411103690b404100b50345030848a0030b044115424450b5400d61030010000009040381c02103a45048041108030390304c80070640241c015400400c000b0300040e54502d401c101c01600d500c01100c00313031050b42016006520070315040c3c041000d40101c06481500b410082d0300c0450061442d510025014401080301003200e8a03202641c0001c00810381c0002c820041255403007003940d1010341014042c4841d541806480c0080c10141c0303903960815a94161880e03d003000040250540c004034682012202d0380443c0d0007524529408002e130b014850420b650399030f415006950b0007400c2e64404841c107c000040c44010b03c1503540c070703420500b0343c540800e0024403814003070b05010127420119000460055070f095560380600405078410240304895481f0f00c3c2c0354441a80f02c1c520290910003003440068602071690244054403e0590 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 645513597 1250 645512347 645512359
    0x20613030b0415152d180203071101050402010c02040c2f0d0c05031b030c0f0105060103050a090b070e040f0509010506090f280905010f0506100c0314030411 69
    0x40c90306111444110034012103150074104180b082c1120104c0050b4000c80300440d1041c2d04841580a015085841081503808404406031000454140512400030541244c140044e5030b42081100a0324600d1100c90001c150790400d0200400b50ba00309a40d40320a42d01648d0205017103042c4a0200d61030740d51082500c483314020340303170140c503c0c0c804011407907400d0408044480300712400e802520000482c9800402c664020000c00c400c02500c42c0300c004004100c034044908160042074201d0510f0000a00100669076800070082c881d03a05024240c0c00c6a0b6800c000c000b540381c103031a50942440b00030628030500640b2100c2040380e841d03640c00700300c0a03802880304001d681016407005000c0c3c078080d102d0a210360721032070114041034905984540a000c200003c00000303c80c601e07481c40450080001030181d180d507a01c2040100b4807c2c00348107071084121500081614080003080100b1200c000400c040100b107049600000b03401400c402c50420348511a50785940da0382c41c0009501d0310040000703402203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 645514847 1250 645513597 645513601
    0x1b250b030c0d0b270a150302060f0c031b0c0d0320030f0403030206150105031303111608010c02062503020706020c250815060126070215150904020613030b 68
    0x9000143d03e040c0134202c0c405240e2070b0504864151007031341416407215001200108014640344000b000119010030f0380b82d080100c0f055410781541c0000a45101c141030600d60301120f004180800c140b00c000442d00d580800c2c4071618010802501c542d80308001c569602080440c0080800030380e40ca80606000700c595540d16031800a4407108140c0311640c542c01102a03403544c030b40c0940c007035038070451903128040683c8110b42c0b011102180c108c80c005895014501026185130059994a4050301c0c648002061410300308030024505000203141d08030102a842e41007040f424029030140703001400340380140e03c40e4020f0414074000e12400c04409914810300c10746010340303066402d00ea4200300d00716500d05400382d607500080e5125a41d0890880800c03003904006180c2790302411006031070400b1070060100f481000f4503250529003065a000015030311940388010b10034901440c4075803100f64070003000d0011a10b003000c242d0504015000900c24400841d008a024040e00c410304000c5030060f942024034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 645516097 1250 645514847 645514879
    0xe01061a03061f0c03020c24130506071a0a0c051605031c0c09060504060e1c0209010b0417030c070329070302270a090b061b250b030c0d0b 61
    0x100c113640300c00c41c00340c01803414901591901138603100302c0d14040d02c0c03000c50a4502c181c4800c2503070700481805900400050002ca4991645405406814422101c0c1d500310713183e0a400c5404841e00500d01c0442da403c001c8881a1554003000352010b070540c801c9255414421458a2811401000c0301070808036a01ca0901d00c8000003600207c40114032a114954210f445034000c4429105900643c800300310004070003a0b541c2403402d07404614000380240038000001903800561400000c0c3d00500001c00013003024041150703054401c540311114a40107500d84507000c1c4010392a01042d110262400100f410100d44980511031048039441c20204400040d1510880c0940250005950001444010301d40c2c1400c00e15a8000d020320030030010b240252661806007500d02800603d000150000da09001c052004079109807000b40f0040560040c00651050440c451f4043d034809912444070f810305041004807066003403c6981108004107a95070710100e041d1030f1000380c04540c02305600070b000080b40400d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 645517347 1250 645516097 645516107
    0x40312021815040e070c0308010b030a1e1a060903072907050d091d151302040e060906090408030703020f0403140607120605010207120c08030403150e01061a03061f 72
    0x940d04816022030780780d2103605c0111000d440d4007078000c1c00704000100602c07080d035030391000d5036201d60420700128072a480a8203a0f84c0100b1104c510100054032117080400f2401c0c0110300c8031892308140d580e0350502c03d4250000355219518424940d000d80341c1c8800d405c40c0d0031001c1c045250005d82d0010f80b070b44c0b8000c03483c1607544d940e6102d5405000504180000c1001c160511070b101c0c445200200e0001e040e1100528420317441c904039030103940803203101036150740c05045002500081094440c2c00d95146454010301c82801c8004105034840d007140410030000841d02020741e5001815440d0042e100c80780d44003000010f12840d0800341c20000d460809859910001034105e100365000d030389910040c0382411540b0141d502d203000c0c05003d030700030803000c3c030041c0b03241d008000e01e5a008001264070035541d400074034250350003a00165040e12001080c00440411402143c0303015500000030000189000c40c0c030f01d0240d010801c001d0400301c002020070829a55030245460001d04102141001c01c207940c00540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 645518597 1250 645517347 645517349
    0x111204051216050f03211509161b02222712020c0102070b0a03110301121202070501080f04140f012301030c03020103110c1207021804031202181504 65
    0x1a0501c82d010511303409940c00b1080d51105035018440e8401d0185202c04040c00b404020700880001250030703518401c0b65900c950a501400c1c038200140031003018038100a1410040c0060b041c02c80455850600043e11a000c814088110f2480010020308410301ca100c080d21045030f40460700303074a6220f400e55a554010700102030340d220344103148004800b80300980e161500815494090307080150304000201c2c0030401054403080c2450006810101031214100a400c20380051002900e03000117a0104802d010008800000900041910a1a001c00205405001800d01e00c00181c12000300741005000c0481800c940c1c4914203450040301e810101c54002d081103071490030b0780074034040c4904014844070301e120f0603242c00c0200d2a07805410742c0c00542c0644284244181c50201c200200c46182e401032181071000c00410400507034803003541c01005803000e2114151050201100248400280c10405190003003c0c02d04001d0f8030743e0007401203005400c4024a00b60340005118071000d20800329400240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 645519847 1250 645518597 645518603
    0x70909080a090905040b01030206090418122d1d28050f010512070207050a080a1a0c1e040b0d0905070f0305030703080402030a1e03080703111204051216 67
    0xe85583d0b07900001001e541d01507078042c0213101000014409400c0030b1009003002400030b40041245c07031003004e840b034084007905019a06101c10b0b80c0d801802300c0d48480c142c8491540c0b9100300703c1600b0101041c41401c000080147c092220114803500000005001d10412030b0000b0000c5c40008409500064408036101c4030341c0e0300008021020802c0d240c03600c06040746080c180e681c00c1c141000340b66161480c0d80007414400542c8504c60001407240d60310300741c05002e840060085c02c1c0c4c00f00b641c64603116240000c51035180c41c1014004020400c402c0c90141c0d4040303100d85187c58685604555218100d22036600540481c801c0052100c5007081d580d040104c250f03100d03404550310103584100c0701c0b08085007400b008109410400c20040406d124071a820342040c0000e09940c1d0312280da6440b261224603245e1050848004084844203044e0055002a48800c05080a200903040051040154403410301c801500840d16404a014450100038040786c41c00b0440745142c1e5944140103403044034400c40421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 645521097 1250 645519847 645519857
    0x30606030706020a0303020310120305120f15010c150e01090201020f01090503120a020415030504030f0903051905070504020c010b030d05040b0d0f0209130c11031317070909080a 78
    0x86142030500186600032104968090041c207601660210040c0d0300c0503048400144046d000401c4400f02c560450a000d0300c40d4441c1d694030301c610005480700807401400300c102501c0720300030400562074040015a04a074240303801c00c1803d046150620407010500402030045180c144690543c2d1015803200c0b58a90007602105d0413204003030003190984020600040480c0c2051121000c45035100800d00e400201240d4017500341501e481703140f0182d078030480c1850002a10392007071005158114800106100241c608601414255194107580303c1150124450814460715884240078052181c0b1014000003402903645001414000f4040c103525154548a0301501019403a10383c06a801c036401c4940742d000f02c40c201411102c184c070041c030507000c1e4081400c0e02000f14903420780c0e0303e550b48000804052000115180c071400c000b051000020310b5920700da8400c12145402c0042000c10508540d0387c41003c001200c444041103061030200c0d0700501c1528100b0000004201148000d48812408c41e035803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 645522347 1250 645521097 645521101
    0xf05070e03011a10021009030c03030e0c1f0c050f0703030201061706040303020d0603020405040308091207020102030702040b040e07060804380912041805010806040309090902012c0306 81
    0x1c16080b41c103441c10000701a1051255000b10382001101c0802c0742c806801a500154a02441c5034140c4403003200440026414460b03040c10107816214103049650709600030040000481d0200b0641c0121886140f20350484400442203284540c441201c4603a0210603550020341e9610140e68462441c0812401755080130780105170004250034040b001d031036013802042103446984082c0d000754008841c04031340c00d031100d4010000d40c6482c0030f13043c09940300340c0c0d1f02c101c1840e241e00300c00e0400320420003106400708100f0000001d41c0c0e0000070ba59129804482c005800c07100d110009004114213000d5591038010f880c400550f042d0800005485540194410b400058030cc1d40001e0050226288003910740b07166094240c01c1c00414000035600c0b030890702c00c5819400f84d841004496070400d501c82e850a20b03410048481520243c040d0500401c01b090040440d0f08003076a0140c2611340d24020320140d02e646155031000e582c410142074007161000c100b00130001c80030340e0480764207000300903842d1302074810380300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 645523597 1250 645522347 645522349
    0xa170c1306120c020f07030f0203100227040506031f1b0503090d02061b031812040602010608010606050f0f1c060e091204060f030603150509070905090c10120f05070e 73
    0x80c400060788005e10150810f0741c21662907068013100040c2c10b0303800d842070103800c100140395840100450015849082d4482c2c011003420341c0c203a403101324000e0042e030500d401e12466807000560ba18441b8604000440a0020070121500812500c1452200a142291244c50311a0454011409038000509a54412100f00010381e46c8a606070303020398035010207000d0390400000c0400a550406090340034002c1d5032102d01262803500c4c82202c1414458400001c003080155024070401004090810007030080078640a00a40359015a40c100a014000001c11021903910901100c0c8400c02e0000b907000c0b070010705019480100030601800c030f000303102d031000304501c4100042e0680706c0c0e0251941c040c1c602030604200300c8580c6600c034104002c0c151036000100014103840c2c0c01a0040003180c0b40050313281350142c0c009181050682c04407450038a00b1051001201000c90f03038584800c82554400c0100d09090b4086070b24040c600040303030f056440c0c5100c00d600c3c0005034020034004d0400750745d04c104200004c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 645524847 1250 645523597 645523603
    0x305120a09080a0507081b240f040f1a07200102070525030206040b0c070b04080706081e04060903021c050318030910110d050a170c1306120c02 63
    0x312024014800500c90608420704c1038000300000c5100c2c514207070500700d04428402034002e00c04a02d0000d40c000220100c0c0f45101304441d85080c03c074030768041c4420304000c43c060700c0c004070191015140142c00c0c0040303028842900b2411542480c6c0c1a190000792801703150003072000d40c90684c0070040c104070b91201c40c1484c00c140243e40285030080041c154881d1301c1d00c1c0001486030302c5040b200307590360950360010241e950080580001c040940d050795494401c4c03640542070110030703004000440402d001c244448040000c1e2070054540a0800c540503807600c0350800511000d046120b100c1c00c1411041008105042e000050b40a02c80e4085540071aa400c010041004004041070b00080f018800902d4880b008064070f4092403c0b2820340380380000707040120300405821501400807a030f600d00510400a401c10003803050540e20315200b0700b001184c0d20700a00960811145070321403590500404c10000c02e240840303400007120310703000c12015613429010b4404044000c00d20031007481e002070130109a0000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 645526097 1250 645524847 645524861
    0x40b030a11071e11060a1805010305090a0b04210e0102070608070c0b04021206040308070e0d02010504140310021c06140f06030901150914060d0b070309051501030305120a 75
    0x50b141408419003c2c403d00340140b408000f0380e4a816020395004090b00c46030024004160180d4960102c000c0e0401d80700c0c0705d60300503409141098a05001c00243c0b050104088400c5030340320141001d0b0342c0359410a03481480311000d802c0c2c2c1c1c580e0035050204d681c0380c01c080d0091203040700780c00b52030f21a50342c1c40003961841c81c00c640450214240c1c1c920700000800c81650ba50303009100900c91840350006092a83c40c00c08100c5041300401e054405100e034071500300320360201d000c104951070040c00c0c20540c0020481c6c00b43c0d11840029020200e902d000680e0144201e60007084120f00454035440366141d201303aa1a0081c02d403001482c90540301180c0103500d11414083e00f980038200301709240e180c50030f1140690004007450a1795507129000000c080c06011400300410840f90003145c00a0b8144130007918800107008980b24501d80c2098400003102098001c2d03002196080c000350620f014103029052134007030361513075007126289400842055040009440402601003288078565070380141d1404031416 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 645527347 1250 645526097 645526103
    0x203070e01150305100b0a05040305030a030501050901082a010309150f0f11070b04080d0509060601090e07020c090c0c121b0f0309040203130204020313021009030b01120f0503040b030a1107 83
    0x100b55400c6c032030203280c0c40003041390a8040c5031061806a40303071030703060554100d0a20f400020303403140010051490500862405481d241c0c4c054403900c43c1c04400300200c4011403144150b103401e04036030460f01d6806a0b1200c411260050200c401983da408403c0d00100040e0580b00116490003000c503501015901c2002c20114a05400500d004c10b940c540080d13010004008803801c00041105610702003c90240368001e0144c0c2d00140028100380001500c180515009070b105142c0060400002c103034001040340480030180c030764100540300d8806e03580351780c41103048900c3c41d4441c1110109900c1a41c80040a03280416407050410515414a842e10354180c00030b05841544203018202c401c1c80c00347d00660f00220701120100420050380e02150aa82044406d10700c6c40c500758070030b0030070b42c1800c7c0d1110080d2103580c07501d40b069508559076141c840c24180926039100301c926821100300803e04a0725000107400804890729166280781d00000c0358030403100f03901043d041443d8900d00e00070b04015115103c0e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 645528597 1250 645527347 645527371
    0x40b06090301090609021c2415060f0201060e1e04020616080904050705070c0e07020c100809010b0105190c15090b0412030c0f05030604090b16080114060301210203070e01150305 78
    0x2010301080202129202401072109641c9c4088000090340d49040f203005100d1520781074001c0044100c00390845d1219881031011382561000c00c8040d8103484d446c019600c3c0c0c42c034440c60145c0c0300e80c008940c03603000e076104c3c40350348001100280050040ac50080d05840c80215814801591143c008807014041c4041c0100192914101031017094560b0b010185d012804d48100c62104a0410016525406424030704011809031414854040400c6c0281060481f0a003030140c90807910010b0200709202c05240e038020403141c048140d00b044515014041a00b4928605100f0a83c2c5800c04c600070030700c141d900b1507500e01c2e580e640307035001800307801070030501c0003d82c41c2c10800303901c8400195042e81c801031503140c0c0b1a603034150081c00501d014032400c1c014a2a8051400c013146800b82c05804080c1c1038100311801c50310340f102c5031099600e00c4101ca0541e03440c0480507420f124901900c41c2c051388040b20095060298000105402e0441c54405040701c6ca00b070b1002300c1031a4507207400e0b011102e00380c9440e10151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 645529847 1250 645528597 645528623
    0xf041a01050a03091203090506060d1211100218012307060c11100c09090b03100c050f0a120b06070201020d080601090b040b0c07050a060e040b06090301090609021c 72
    0x50300410180c06030382e01c0c2e4100400c14a2043d581d40c0d4055500160f400003180d03640d50300c441404020020703103500540c1642c030504c44404d00d0300d5083c40042c2040c0e005040010000505c0e60b088022312160044862081c000e544504615440c180319a82c0400000d0000d02c80f81109980f810030000d2401703201034803140061404801c1d44030340c03014044158085060010258144084000411103030205245258002071801c1c8114401005010305034003584a0034140080c0f40f2895401007540140c40e6100a0001240c685031102600c0c1401140c12240484c0008580c4000060b00411414211003291404100040411007080500c0c0100c0c20080e00503404000b0082000d80100c00c3e140e00170605043c5240c0040d44e84640c601c613a40301e50080403041c0c0000c00c2ea401c41c41c604100381c01c00742008690b40d130005810008024444281442c082d4403880d1101c00d210328035101d00003100c0d41c01101800030301005949003000005403006820803401040e04100a0704001074440b01304904c0355010000c1492030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 645531097 1250 645529847 645529849
    0x4030515061503191b0206010f0f030b0a05060d0804080705090c07120e210a0b0906091b0f0d0b06132018030703030c0b0903040b0a110a051b0f041a 65
    0x20703025442014000ba907407a40124030503811604945c0101038141e008213455810052013801c482e889501c25052040703031100900c00590519003050f400003029030002003568a07100000c81e000c44602c006400400001800f01c0d080d1004201e500c144d600947e0580035039282e5841041c510321403030350094642c0720040c044982140c8110300d40f410a080c020520801d00400c460782e8007494204070140421a44074041c25400c006420807900d60002c1c1500160945292401416444d0490161011000b01031f111801e1201daa46210403c60400003034200491011a441d040e0048030007a604580300e44400418882c0100d0345003d030000c1381c40c0140b81527840301280c1c1c41d69031640c1c10100c90381d841c1840d0f40240060380c2d102080b030040214005d984000300040365003400c00f103002d00038202e01615042040144403510ba4041103c041d4040c1d40783c0a4180d214446003681019140d040c01007141c000e60311100b0341001c003480442c1c6001130450704480d00b020301104010031110b28800042105614624041e00c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 645532347 1250 645531097 645531121
    0xa020f061501031e0501090207050613050613051f0c030f0c090501050a050702100c0b1008150606070b07020106061101050603100b0d06020d1406010c0510020a03020c0304030515061503 81
    0x404d0b4081c0d42c0e20201e5000c5180c82050319400d82001281035400f00d800030500004111154008001d1218061011869100c0c0d6449410080103041001900c5120700b0030400c040100321141c0790b255031745070074460414140030080d0a503060240c0002c4d092001d40e25110080743700da400c0894440d22249142c500e080015103483e0414610441400b0f41030000c440035880c0c2c40148000701155a66400880100340b034515071002003d40543e006a103400b009000714240001c00c0da40300840300324410169500d0100140c041e2050803001444058400d05001301a90150406c0301912166150b50690440e4448400d00300c440450b6038640c5a0300101c03104116203d16440350310400d02c0a03040800481c1552149004d981c00003aa1030403a95440d904000d500f4495201560046800d00c2d01003100e525a44405a452442c90b803901c00d40ca03030005446070b0031406503044030f40158041d010f4075140d55076810200e46400200050956514402c00091000d140c241c4483e400600c56440b01e5086407180909124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 645533597 1250 645532347 645532361
    0x50106170a0b241306050f03130204020f220815060d0503040509131502040b0d1a0d030e0901090501060f0c020f0d0b19020f091e150a020f06150103 65
    0x2400501d00e0280d002030001d02103803d1050034003050499901e110542c884004040d90f039003d4001c2010621003c080d411042c000c03079070400000001d510724501f032800050000d2062000021100742d00107013404c0001c0340e04401d19a02d54030480d0013041903640e07003004c0c2c1d11020360740c003185080340c0d00400040503450411140c092450064045a0a090325880420255401556920400c03000d1184100410003034222150b03101429042c15030030240307031031042c1c103542c010b01c0700300d00c060341e03c80e40280704c0c0c0760240c0c041c001d4515001381a5030000d2030130b080240081c0246200103020750010380c00070450014a010365030481d4071903a80e200c807a14100d1401c4604c0f00850104a912283c10004004242d6810b03a090381c2c614001c0c05050b19a0800290801d01c013100108401255801400203100700d50b00070042d074909000070782c1c1c401c02c808040c06442d1103001185039010781c80308200b041c1525421050700a46070f2000140c003110b0303098144c1410243d50f650210f64460f01d83c00181081040e030351180e08918 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 645534847 1250 645533597 645533599
    0x9031216030c032f120403050301080c0a030803010605030604090c060e030c04090c03030809010636091205070f02040606030e0618030327100b030c0612010504020705070801090b010504050106170a0b 87
    0x14200380301caa8411610320821b0300e0a0b00000e00c04070050055403010311410400c1c02d404c451008000380395960b87c3e40c0d06e020510803002440303808000900aa103960b0001c241c0640c1c803001c1207400301e803112806000e0080001581c4d00030301c118945100303241041d2003280051500000098001c9246a8007100c4500004029801954840c40c0004449000d00219a000900c4000140c40d06285440011868a1010380c90280d503041950b2580852903c5454030300c60112890300c0343c0d0f2988103041c20b0000b01c0010744001e402174a88100003581c02d6140c0e02105281008100343da860b40c44d01c0d81d0090b88044050b03010700c4181c100b0400b05101c0407a6103e051218000003408800c079464640c1b40600b010503511550b40503d0307c40d0900f944a01e82488072090280d001c40700e00341403201440c3d580043d484140207050040358001524414080c00308011002806480b00a015101151804681d0f400c020710401c2d0045003010300106909008140b803450720b110b010700000451303031040440c102425840750a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 645536097 1250 645534847 645534941
    0x115050c0c0621071e02010207031e05130b090117010609120204090227010b12060d0f051002040f0b31050d0303021b03040315020309031216030c03 65
    0x81d240c0f5841c445524403810050302c0e881005881c080c0900c0b0440170412180c411648100711200000f5005808080841100e2400c90f4000c11140401c0e03403503104410000d041d148030841c00040e807080325070082c40340c1c40080e6205003403100b06146c0720194040070300403103004c6124100c050104501c10190340504600040003c91031005c9138010500c0d0355416142d4203e4000c00d051074000310000c0c40300580c0108030701c400b0145400102410300d100b605024003480d205102e070213044c00c01c0c0012140034603003c135084029950384c480c1c164031042c0254814460020301c40206d01e030008405040c0000c2d00c00c0b0745400c40408403119094540001c44c1228150f1080710111500340100b069245c00c1c000300043da11948006035140d0340c41c8002c107240c1c10f0000d05640144c2c00bc000034400540f00542d000e1411410360000f50302e07501c607141d80c60300b0760003407100c80040c2c803000d1420007601c000700d0203808000045c2c6071010014111000390860a44942c4403120046003c0013851480440c603a001042c1980ba107090f032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 645537347 1250 645536097 645536137
    0x60801090b1303141c0b030c18041a010b030709060c0803010306021c051e09070303050403021e0d030e0111010504020a1202010302090301090c0825150c0f05060115050c0c06 76
    0x15070019030040ba001c01d64100548401c0c20b000701c050710038820001b50132401030080c0c0c1c4820000903041c0b8030303001d00121594100e10100f020020714021440c612602c1c0c01c5514010341e1200034150725034004585c00000114040341c00521107009104203034041f50094640b915627821a2170b84000780d4040400000014411043c1c00d80340d070854451113018411006007460b003141c500c580700c2c0300307410701815120980d04081c00420020340c00008843c100ca5042e00c02c43c10094000102510034825203419a4100510356000070070142e102850401e108801d8031044c04203409a03000c070707080700d074100e800a400c00200c40c0140302440309400c1c0d0f550410303c145000340ca0130f00c001d030219095a007641d40880707540603412420300c4000310901010134030300d0018075100010800d48000349010a003910a080b0950440090123103a00d10640800540355080429405600d1440ca003040c0d0303c11092241c44001c0c0c0c041d601092001c0c3c40751040b554416402001411035082a0341000240e84c0421034542c00381d010004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 645538597 1250 645537347 645537377
    0x501030b0f06030a020d05031e1305090618100501080a050907060e061608040801050f090d0302070f0803090f01060b040605090906031e010207060605040b0d060b0a081b04060801090b1303 82
    0x6c1d00150240c400e0300916111a401207400b0301055600d001d051004d507080c400c88030741300c06e413860781170469008641540703240c0c07109800709050412403860005843d000b0f01c104a0044580800c7d04101c507420b98a01110783e980c416503004450090b10301034501d400c080c104000c5d440c4500705184840034020310761440c00c080c00d075180c500c001c1c0603081100e201c8800704040050316070a1040702d601401c10603c4126a11740b8400c0341d510f441d0b280052000b403540c00700b0603106000b00d0b183c0c101c0040d81d11039500d40c0e990511a02040d03850110b14203d101640c01c120740031400d19241d0301a50300303c0e4219201c0b103050a404108100f8031001c003d200503014407d6240700803841c0140118481d0b66415840016504c3d0309504003e015142281c0121f40910b0406400c00700503282d1484040c5401d030070080010f041d2810380001042e00ca140d5110103454403441c03c01320001c00fa030240074140a901100c0401c2030035501d900b803030b00740d543c2c1210142c48114440c0008100c1d103881400705004911a00e40306d0b4084100007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645539847 1250 645538597 645538609
    0x80403030e07140a09020f04031707020904030e030708010e03071511031006110613021c080c01020405191a0f071203050a2009010f05130312120501030b0f06030a02 72
    0x43e012880491900307079000218103000c5514005000c22a03019440c049940280c80890310031440b005000000e50b180842880404005903000d13594014485002405d10381401410560742020a42c400e000e80342001805d0481482984d40c02410030340070318100002034543d20851034103a04000c1110742c480150203a42c1c054040207501c0350b244251070507942da0410b840244a0103400d0f041c0d48585c2e020000384081c8065a0005000c0154111403005070500030040030f25040d81184e4000340722141c0402c16111145041d0040c0c401e48006071a03400b00d0074103004030301d010020248030300d140e000c01c0c150700c2c601020a5a0700401000381c490b0391182c9040e079203580d11461074404c2d41c0f00300d001913a60400c0c00f202507040e0090194200f1651a29604801c0070000054988254030660b4140f040c4aa54402190701030002e545030890b1703d04041480c01d03540d0800300d48140b07041c403100c0d001401400d01d548092440d4440c2d2416039401801e01d14107940c80080202e031841c4068000350785880780341d88401c0165070300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645541097 1250 645539847 645539849
    0x809040c051902010b031207051908031f0b0f130815070f0302070335010e09070e1302040c17100608060301060e060402070c030c24091203080403030e07 67
    0x2070740d906076440605082c10003000320306642e808116414003112945503580003850800d6002007190055881e81c031860400c0c40c3c110000c0101721b110500d000b034401845032910142d0b10410b202c3d044218440c46903112040b501d0342c02e002e10700302c100081c0b000c50824842140680003004081182c404c0698562100601c0d14940180e1403414404071001c0240560340046825070741d49050405500b4550a0307a0045c0c401e80810300400c4004072141134840c034842c11100c8e02d21416803500d00003002543c41e148264000401210060200e11518100140d40240d04840c40d21840d0702240811969403181c4c00c00000d00203400ca400200a41c9000c0403000754034020750076000310070308814a0342d46480c0c400007916400008207214840d9241c203904100c46500010f00c603522807412a80140d4404d041e20700703008803240a40001d040d40b9002000425581d20700400401110042c18a4194542005000b1544c81215009011444005a440c0d600084c0140350081e0458400e0601050401070110158686545 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645542347 1250 645541097 645541121
    0x1707080601080a120807020d110102041511281e0812071107123c1a060a060f021c0221040803160c0312170f010e0c07080904 55
    0x211410f06410008142000d8454020034101a19240342c07241029403a18200605441402994800200040003c1d41120090458074400821101d0f030f41e0002050100c00c00420302081c4242d01e00c42c1c880010410f06814841000860f0b142c50020581e600c0c440c454420349048c2440508078001000130303104401400c8010a2031403155603038a040c4200030100700d81042e240c05c0c81d820068003800701310b410310380300ca4156400441142c0455861046880d4111140c1003440c803e0f813500a00e09126501075101906440c0184800ca0700c4805071030000061102c1600c030181e20003400041004170038010121540c4841003401940c420402e03040440300002c1980d00c144005800554800008214003031000300e13005809040c860400f030508810070f03500d109092862043c095020303e034a04108180000d07801840c1d200f49450344ac000820001742955286128100e412124580022545259201328a04a80e4060006030154031088420501680311400a0b00c1596080100e4005a03e60380110002480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645543597 1250 645542347 645542353
    0x501051c0606122003070e01171e07030e1903020102130329040206040306150f080d03050106170a0c14070b010806090304030c0b0306011e021c03020a0504170708060108 74
    0xc4804040304075031000d6039400010b00044c1512840f442c2c80b03000c3c0d07031340303c8480e00b4400401d544400043e100c3c8c0c0d20000911182000090410461102440c981c01e003c03910180b0913109501c07100c4040c9c05466030940000c107103070710076603240c051070b4440c0d000c00c081e1901900005140004401810600003095001500d81072894682c42110700b040004640304400d02d00d030b5545150401c0e0740001c40e80e200314840540655140ea85503132175402d00e110008020100b141181055a0b80d44005584440000b02250042841c1000005249002d44509850081c041c1003007030003a40c586140400070920f240c69a020011228441000c0da000310000301800e601031380640a8640c500758840d480c1140c0140030000d142c106110403c00955044200b1040d190304007505038a980d01c050040f41d0010916001c480342c010996105211141c000c1450400303680050006d4610007003040c4194103034371030980d001001410410041109000302d10b2560071060000080e1103144e6620305246140840a070007805c02c2e50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645544847 1250 645543597 645543617
    0x7030c0c0e0901140c09130207060e0a0c14180a110904020a02030706180807080904020f12040c170d0507080c0105160305060901030209011502010f15030312060f0501051c0606 77
    0x1401001130607600010710021180b9040511000c110a82c1c92080d080c520260042030313500411005801c002030b10000707142100c054602e5401c2c041101c43c100e201c3c150b03074203188100645403401d2941259000440314805c131007c03500c5500310301c030051a04400d0094906402c1c000e0b2a1540d40d98001404600c1039540199107030107c0d801d0020445844a031405c180316015420b400000b9061703000e44080c0c0303810031a49038075a050280487e003e80315402e08800712800000c0d02114194034406807500903401416010b00c0580c60f2030406e0540002e500e0441c0c0c1951004d10039041c8184200000d1042c684268a002d0502c81249450340c256141600c501c41490707003404e02c0700c01460b89481181e911040480d412006549560082038106806001310001c0d5100070706840801350003500044d440440c80303102008000d54502c46500e11580328042100002d1a000e2140b200b00840c5c0141801e55042e881d03008041441c0078015202540050b070b6001e0184134510b6040c52002d01c074400e40c03000300100d4441d01150303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645546097 1250 645544847 645544871
    0x8040b07060e0703030c02190e010308042405090415030609030305090d030204180c1b050c010f0206090705061b03040f051f0903030503060a2d061407030c0c0e0901 72
    0x303104250240a040d80c0f040c2000c00c082548481d920702d46540556516034528000c0c03015400d01c89050300b00409284030580004100880b8000601c00c458440c1c0c500b203180c0341d4905070144280c616a840314001a803c0c4456240c41c50180d10141c641c00120070401c40072603580d5a00016181c0e502402e4020071b80d100c0400084110901004c9040e0b511460118079142c2000c03134804194110000b8064201da603140144640d43c090305100c0d402a0301d141404110250380e00c1d1099030b9010701c405036400074800141422205000103041405101d4179030123045414200024450a904005a081040c002c4c4818207403d40906100030405403a882501c8981c050a140a00141600740f403850326540400410034000680d0000804094039414500300f680da44465000882c102003d41000c40c0301100c00c1101600c0c418001445460020642c5a071031507035035148404e40e42c141c5600b0741c1d2100000100040c00020b8420020048030301d1140124203010742e201d010901a07000c0840e0100300f660b541e60000d01d99 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645547347 1250 645546097 645546101
    0x90501020915030c0a03021305060c010e07050402090d080306010201021908040309050d0b07030b0102120406081e07020a0b041a01060e0a23040e1014250c0b1308040b0706 75
    0xa0b000005601460760070f1103003040c000340c0300d030420200c10168041246400c103807105140c8402000c00070400c07511085071618160003002c0000c220441c42c851002c0000e01c50506000341d0b4403640000b440c80ba0040680c5c3c894250a501c0104118119582004001903201c000c01d640145420f0035580d603100361505145c00382075482e1640186100301c00001b2030341c00049400051950141082c603020440510580041c0e14004a04243c60746076180442c0110b206544a40481d115003a80101d2220074490340950780701c00e003400d07103043e401070f0003040d8502c02040441e58404c0e00280f29010000240607440c00313060400a0a070040c40c0040c407030654100c2d061070710680c800c014000c908001e08880c2d000c8614070304101c210f0340001d030146450300b41030341c0380c1e84061204402c031007c5098140604000c0c3d2205000140081721640701180b104820219503680843c2c1c000741c24a040c1d11000000c0c100e580342d165100c403009100c068501000344a40c400102007030081e0000340306d2681ca494680703059140c2241 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645548597 1250 645547347 645547369
    0x4b061d18010207020a121b06020309150405010503010b070f0206030a0518010c0801180905010501060f11061302010e030c0d121d0913050f0706020d0305010806150915040905010209 79
    0x1034681c0180701d40743c0569100a0f0b0b080c100da142d0440080354109500d824132010402917440a500790000c1000204140c001c4001c10358018121042e15100d02c1c05040103c1030301450082c140010700c20720043c0b00d100248001440340c58003900000c408051194000b601d954012034604121a49408c1405040c5503414803088000072284005e101c1c261442000920380007051241500c078802c94481000141842c1c0d0040c41d072150860003d0105603101c0c0c01c06425501d217500d04200280c407100d400924a80003040c0c6a01408a00300c03103000c8110300e9001100c803810754022040c0d041c041c0034000e005958400c101c4d408043d102d000c0c040004d802c4d4220107480b00000907251742c4403080203450302c541c0c0c0c0c1e45c1110790384c1e004c00f0381d200034849440076040c054a02000d42d00150000d1046000124281c4d4001a070004a0f52807640c0074441070380c9407000d443c1c5661081d51030790207012000c104e043d0300d4503201903495403106840ba143e501caa03030400300090540c2c00c510700aa6003654000303486400750402d140e00ea2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645549847 1250 645548597 645548641
    0xf04060c0309140d08090d0503160c0f0b0a030518010e0a1b030507050d06020417210412030f051c0b030715080c07050c090a4b061d 58
    0x3c4070681c8400208010398450940188050000128804180e41e540c2c08600408d401034102da0f1540340c5004c0801c40240c18002c00e07621000c03582400550404409025025648a00300b258141542c00c00103802a00c0301410101881c3d17810f20b14a0071140c001d208101c0d1070300400300240030196580c2418a11b4580d6281c80c03003555102400b09002003540000e00c0c3c0c084844c1942c0c0b1180d00c7c01582009002030280b50040180d486c0000c1d4610000c04c0d0000c0c8040303052161101c406001140c1c1c00c0308101d0340c4114800c400f60b40300e0421150020a015000041c80d414131400c20510781845004d540b41151000940ea100c901ea4540309840e01c0d060400800016007644080c0700f00b41d8086500c081c068400c0108020728040001130f064040240500c11030749074480c05042d541b0b203402c001045d80c3c045c244200f00340f2400c1040310781d504510070344e031020041c0001c03500708014000205407605101c049a80341c1c2c800c0d00c1c01d0316000c1c00901c00000900c0340403c096840b440400d6401e0006190503c1c80c886484a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645551097 1250 645549847 645549869
    0xc030c020115140409120c1e020d02060304050a0c06120e06070203030f0a060b16050f010507200102040509040c05090702030301050f0d150c050a14041a0903030f04060c0309 76
    0x1440d1030402c2c406000d54003003510420301d410103240024090440c50704000e1502c0c2031108509002a04400c00135038052003450b01c4078800c00700c10100d03021050060406540501500201009403d111006542180c0110180c2c0d1159001e611703003403060003040c0e102c0b5001400c0c3c2d0124825030807240c1300d050f00b0901d024001c1d064074141a20b0082d80d9004c0a045442002d8414020810000d034550001d0010200d6600040d16100c40b146800d0841d00f0250041d1803c4c080d0f1507642d580d00310184251846182d542e20b030411600100341d0b20350080c20601700356104942d0708010105159813501a0a0310403486040c40c1038a09040c441480348510014048209560040c00140300c959030301c1c401040035890550304010074030000e00703050504100e503500c200e07190380c0303005004d0707402640c0800200007404940d01c070300605a00061100151b0721445c402c10800d8042c001c140b56280c00203c0090028000080c1100c0c208007400c03d4603031f582d5201741c3c40100802ca840f0b004d030041540141d48013000701142c8101e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645552347 1250 645551097 645551111
    0x7051c050709051009090605071202070b010611010612080c070e01290d02070b040c06020714040207140d0f0807050309030a080601030f0609021b03090307060f090302130c030c0201 79
    0x64a0380c0e049035000e818510b82c2c81d00d000411005a1a42000003002492024404c4054a00709032004200503602900043c101c50b514015100306802250b80300c65100860003116880c251044030040302c00071910307655548408001030290130381140d10a9507805404030076a0351205003016413400c1401e6026a0803540c1040042007509002100c2c0070703546055036a6581c10350403241007000700f48200c3c0c032420401480400e055091007090f03100b1034030561051080030500e90f203a640580c4c0d215200c1c441e5207040c4052000b0101241401d0f0003419078030b88036401c2c80e201c400c0e2000720706040100701c400b14000211003e80d600b9007142d110350111f13000b42003410250705d58100441010344a22800c050502402101e4012404a0b403080d40b109200032100d20b020042542c888071100040e42c06031020404040c01d810400141c2c1074084210765800d90002c005041451030040d05488100031150020144140e000c400000343c1c4514100002c3d5650b5400d0010740601c50210180c119100020f810085a150440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645553597 1250 645552347 645552353
    0x190c02010c0f02010c140607171003060207110d081206010c0c0306020c0c09150315060108130c12030c30120f06060203090a1a030a020d0f05010807051c 67
    0x401641c1080d00a400400704002c140010f03a0b40e2801c1c642c004100481003001e20f0075400c4003281060080060307a450840d00f0170300c400744210b0703164166089260800e0b540002c04c000f44003030340240426840f8114580c01404044002101d910340c440f02610600e000103601084080b80500031a8844002d0030310101100d456120300242e421240402445190300107202c0c0c503041c004224048840c10300501c241d0359850074801c40341254641d2500309000e441009a520b8101203900c1c40caa01c20700040c0c0d074841c1141d5600d050380c640c507100b10000340d910150b002400300702c2c90b06802039100001d020381c80311054902586041a038420300f03070004006218200000c88107010462882c0707503403000c152800100c1404104101c0b001489045813003243d40c0e00d0030350001142c40d0080f0151030440c80407030f9414101c540d0b50b4101548d0294452243c0c5600c401040003508401d0743e54061b00d80852000c100048000b0b46940c003d007141c0083c1c0054400b0741c40034408100900d410380e140e80c1180c0450134004180701c601d80e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645554847 1250 645553597 645553607
    0x1050a23040b0607061d150121020a0305010c18050102031908090c06040f170f15130b10030507080309030709050903070b01090e010b1002030a080624190c0201 70
    0x14401d201c1c50700c80b400115296151400e5420240e0802010070080802d81c032901814520010004102d028090032079200702820703010f03281210040d00c0003a0501c5244c0c0762940c4640c0d200d22040f070b4400000308021000c5542407290041c2c0000c3c4e0780354450340d01182c00124004202540c407081c110b500410070b880003880a040d02617080c0020303091180d529124000030301c3c00c10300c4000c0c40350740084000c100010600140302400c401c8580024101c42c0c0c1001a208407500d03105581018603161307001518203c503e11686419944c0b0913103002482c03e890354965244c4607036000c02e4403103d0514181c4039050080c080e0601c41c44004101e454000c5180054001c003013a25403009110300070003166203d0006403ca41c06000311081c0c540c0c0301850004030b60711110200002c08040301c0030300ca99880e2082c205154142134682c10809200c540085042001002044a02d180700501c020303045440c04070070340031140c43c5d04424000124203a100076240c0704a2528001d0788190003c000c000c01481c1000000940d03008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645556097 1250 645554847 645554909
    0xc0303190e0309130b040f0f050a09170d061502010b090a05070c260f0a03051f150c061a010e06190f141801110604120c0314030f01050a 60
    0x9990701d04d029465050707400d0060507080070381600a400c06c210400180b109a100d03102021603c1010803041d00c0d840800c41c00c4840c03800c0010002181c03245c0c62403107a42048090482d01c400300201040d09a158985020b1a2094511250150391100d40b41100c1e451700c20001c2d0341c0041c1f0044104050b14003d68020040c0c2c00081000c0c105a000c60701007146c10308004214a001c4a400221942d00e84601c0325071285070f40003540b071100282c5440c0102d0014001c5804a00780e0081e82d81e21104510b0405503003d101c054109a030f0310910041c074141c071001403000e00401d48062403c1e4560038081c6030030800034014100c801055481032031700b00038004400c1056001c055142d0840c1c0703800380c0000c082600c19200402c1071185a1180c8001050300e201942400c0e1600540c1d01003a65072a400269000e0282e5540e402514001c0c10800a03010766001c0601c01c00101051500030324000c141c98610410b1000550300550f00011803a003040c0040c009420303c0c00800005203c20011010015200280c14002c0050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645557347 1250 645556097 645556099
    0x120903050d020115090b04060807030c080706020714100e180a0f02031003140307140a1109150f01051204080406030c050f04031709120604060f06050a051002070b0c0303190e0309 78
    0x511b412840c07507622031768424000761020038200d40c0309a4890038520403080301d41c82441c0c6240701d001e00100c0e40500c0450494115140032440c05032090f003001c1006420a43c0910380f03001c001c10a49110000d55541c60142290020030b41503a00d2400c2c400c08900c00e4828260b0b4130250940100140a62100c0401c450760480e9000026680c3c014107103a075035429031042c442c001d840c0092014090300b004d00081034000d002442540300f00c04c0b0a000f0300901c902c07030340101c4150690003103080008102d0305003c00fa02c41040310514210b403800e503501180034004001940d080c2e5100310089414000035070544a140e2810f1041d040031814400718490005052285004c02848070b10001070b4500c04000c190142d400384c0c48018280000d011102060942e42c200c112401d80c0c00908010100f05407107401e12450007543c001030034400c03903282004144020980710384c46010461094160000d9614100400392216460410103140d0302e091403240003200c00d04121803040064a410305584080d40004100c917661a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645558597 1250 645557347 645557351
    0x261615090311102d0e062d010506072010031d0304030c06110c040c0201050f060603090307140c0405070c03090b03012709080307021609020a0e01080a09120903050d02011509 76
    0x690282c1310b00140c50700c1629069a4451402400407a904d41c0b11720300c90920b8074650141024501c2d0f2002c1d14200420300c1180d810000400041c00412503c0034840301000701c0c1c0554491026003d008580942e5005080e60006652400302c910b4151060802e090b0402d0204000d50406d8150303210b056121290b44511000d0060b000c0c0c00d104500801d01c510020100000d2041050340760b070303800103806000c0482d49044070300d40c2100000c0081c9008070070b5034095448400103508100040c2c1c0c4000c01100002c1d00f80f02c41d4404c0503240380d5942c0c0c80d40103141c412000769580007850704061402031701c4211a07070441c0c42400001e000501000d5444902410680080032450304090000340d6400b0041520f081c0240c041000041041401500010004080811030551084040c0d84080d40343c02c034050f10b6240d1001640ca00461681c0d9072255400300c6d00a078001a00180d43c01180d580c2107924038481c0c0c00c0d00c2c042221f000d002c00070300000303000c450b0b100482c500080c0b00e261a040385c43d4401c2c2d4114050805103503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645559847 1250 645558597 645558671
    0x3060105030907030c06051801020a1203020f2703070e040b0f070e0d050304260601030201080714072003030306180a020706021626161509031110 64
    0xb4200603080080d504000704c40d216039142c000042c10b075440108041340500c8180c240750b04a520000d0710101040d0400d00600c81c1940a08040340a54410074001e07417000d0040c407805c3c00d03200e441d00c10740300c107003036031811650400c00d11070f0600d8144601c9600458261225000700000b0504212680b68048451140e049141c1d8811030240d80b159010100540c016058000721702c100318001000f04156001e0382c04c44a0400e201c14007501c5c3d14041c3c1c01e440c010300e030062401080154054400e00d90003c200e81806510080c2c050602403031604018001e0710350a40c009560f410b8a40440c1c07600c0401c1006901561071484c0c070502140b8140044017070b0b80300480101000a10410065040c0d6481c00d41c001c00c02e56440e0103c0b4804441100054000c1c0c13001c0c4000400b04a041041041e0101e000c04844141c0c1d00b0680e0003400440010319226050b5080c281c084900705508090380709504401e0301c40e031101244142500304040c504030b00030400c180c0d00c619010500501c0c240071800c40911000040048041c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645561097 1250 645559847 645559861
    0x718060b0a09091d0a030f0e15120c0c0d080103020411030f070f0e10020a02030601050904120e060702041404060e0304081908120f090d024c0b03011109060306010503 73
    0x5005900340140c45e0040020305d4040690018a40900126641d9582c80d0000008100030380d0001486c210013196104200d1004400180320000d80e00960b80303694941015909446141402000c40c0400c0005644030018421480c15201d14032400200d41d2000d411840d0108100c600e502016105c2000e02020b104c04410b600e2040c495520700c6078001c0d04540c2c140c00c4219000e9039582c07a80001300d10901034400040303074504041402c0303031140750004640706c03a13000d652000380d07800f00e00302c82c01d0b030340103102084560050b0715071340248120fa03060a0950781052a15082a0341200d80398080d004240d00100803c0100ca2400200c03104054040c0e51103440300c1741549403230281485840304404030b00b006a800c020aa00d03080b02040d20880700403041d6110300d0500301c4203e07285e0460006190b9480e0f91080b904032150500c0b091032000d0b400c24000882c4c002040c0b244000d40d09002c800c00d14030583c58000d001c450341020702405a20b2603040400c0c0703044c05c0510700050380c00e02008140e6410840d01000284003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645562347 1250 645561097 645561131
    0x40c06021b130b0604080c011b03020c0907050f04240f081b040e010b03071115450c040e0709051003080f07020a1d1807080718060b0a0909 61
    0x100e201c01004035540746c0d40c4101c0340b9240c3e800d00310b1444c0859420404038003d038001482004190358146d0143c41c143c3c0c0355808102c00e0b204050840070070007100380205002002200010400307440703a40c0800c104101c1031f01441c40c600800c100300000300600c03082c58403401c0d43c004082a4010a41c1e450104c410344442c2201c1081c0d020301d90203030b9000c240b0300c00009000541c404c001d5006030a1a502c0313030404550044041d13038903025940c01d404081030b0313400058800000111000e20503201c1c1c80c0b13180a200b03022400240c1d5002041000307810075001c04017429548c081004840300c5240291400e12440d00303040e1841e519403007940f044054454403200011404004411007001640e0300c0700041e51038071b003c00448041c0e90044c0300200e0103420b10366004a0710151504d024100c851080840c001c1070380ea0960040d024006110343c44a01b8450600c02081452041c4007200103841203c80e40b05250500ba00c040d420780d446940f1000505100300b0000752031a0b4806c10380c01c140c4440d07000c003242041d0740d03881d5820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645563597 1250 645562347 645562361
    0xe061210020d1104121b0b0a140d0e0105013204050406022203061103010302090a11043c0608130f020418060c08090a150b0303040e040c06021b13 64
    0x750071400039003c50004600d05c8514940d40c02115000c070707122070606116441c0c070140c1c01016203030354050028090f000d10500320340d0784000c0032420325402c08400340100713025180291050005651120014000e59a5641c0303442034041c09104034510483c41c12141c08181038215480e20300564132900043c060110381d0b0110361480000200e0781c0d0403032030703108640c01e4501d8150104861842c01c085e2a0f49000b840f82055078162500106101c2460301c0c0c0c14421340007495048074503080d8820074440094955920301c41c0c4000a07070801d002d0b035030300c135102200e01e202640355103c6100060a580c0701400b02071380c02900300d584001c5004110340c000ca1903040040800e0446103009500506002c41b41c40c10002174280c40354102c1c4241d0061003151990030060f211038808443c500c41c2903100304803180200340d14610100c11500308400008282c844580440d003598881e0300191041815401400200a091038881c0001c00c00e038805424000120702800100c48241c4000030321070f0f103c030400c80e8070001c9070f607200b02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645564847 1250 645563597 645563621
    0x101b0503040b03190e0a080f1308030a030c081f05060304030504090c032933180109080111030106050a020c0406090b1005040b07080c100c090e061210020d 68
    0x19841c0e2504440f6039041d02103e5151303501c80b41c140041200550740000d010031580d640845a2410a140d21910b4a0301e50044020200e05c80400100000e00d05c200b0710050940d8405581c0101e40042c07840005081820042c1c1243c04d52408140c035540c6000d01d4414000c1a0741e000c4408950f280c459040031207007401079400041800b807500b004c5019183d007561201310080e19807540311304072060b140d18625921180800d080d03008500049003040b8659003800d8020448100c020f002c00d2141d110038201115000304c800080860b071604039aa00540c1c000c2d0a03000240003401c028099412405080c0859000600c5164140840400c07a0744101d80207111071450b911014008010595650b84200041c0c403a1101a40c051a214030800c41480d20480c2110241c0c4c1050241c11316103600c540d5180aa42d01507240f1401c18000d0703041c3c440302c1042c0d41c0221820800a40d445800140c2411242100302c0d4024248a100380800d01080b0001340d004aa0219500f00440c0010b0320340ca030030f16450300a4502c2e10390403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645566097 1250 645564847 645564869
    0x5040f0503030a061409070f030e01090c030c060905060432030604050706140f1603140f1305040c020a110a150302030109060905100b0904020f07061406101b050304 72
    0x405a54919841101262a500308000302480761700c081c441c014009a48039000203d070618841c00e41c030300913000044600340740c40000a404039161129000300003250000c441105005800b04181a130018004010380f43c1158828605460824683c0444ae80c118410514820b54000003024440d000c180d069841c130f000e020385000c0e1506161454507204540110400704000012080600d940300007a1103034542a07042e0186084040341600c489c403824910102d04105500c0c500c49441c910f010058000c520583d000ba83d1607204200f00f040b10341c0140d400841c0102d00e41120f00114550019010781e07542d0300504155021050301c03012808440c0e56170403000c002c0e441064051140c3d0307450b41c011030403600384081c2040800d40b07580101d000d480341034070461100034401d5414410290740310010103d80b10004d100502d08450500384150903004060f059924542e1503141254994102d9242607002c1c2003241c010101d42030080c8090321001130001000303034000c0b042c4219400c00c1000c0007141c01a042d40c40b85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645567347 1250 645566097 645566101
    0x14011704080703110f070b030a021b060108010c0203091e03070f060203070506090d170709090c0302040801051f0b0a0509030109052401030804060813230115051305040f050303 77
    0x141c159a002e420110001244086001e20150000c61405c0601c1c9080b00035010a900d005000e01d01c98001030b001e412100d90800108481c1101c0b0309601c01000050800b030f10312076240042c0503007181d103440b0042c3c06640040044140d0380d41c3e030340c1c038200a55014445ea454080c42c1600424644481c07508410755200c2400d40c082815a0000050f281451040048404c0c03903441204d641c0d164034070210210007040e0300460014010b80d03840a01075010072245401c041750355558440400f9101e2004200001c6540041c00b03002e00c50003802101e42c00301801340d80003a464155010240751351030038451520000f4011507112450381c4103204542e41200020000d1008a41c07600b043c40c0c5981c0100d4420320403551072440c961100650800b501d0403603801c503a4090800346041c00641c0c00200c014038506000040c00c40c0740300003503c965200d0203050b0010090120a40c0c04c10200c5007101c5a4405400700c92541003010042030f6940d11a08140720f2039201d001c1090b440d01d2814109440464a00800501000c42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645568597 1250 645567347 645567353
    0x60a170406020d0b04150902162001031109030601030213090209010b0c011803120b0f09090f0706020a11040c0c08030405060403080609070813020a0504020d020c0f1614011704 77
    0x35285000c11990100305012113803040104450001c416080c2e501c980c01020805d5100d030354081c00118100a15840c07100030107035180d260801104c220300c010003407610f84054455a061003800700e90084100070514100c2d070600080c1d0388800510000384242817055071100c100389a500040344540d80541200450b50315102d0841d01500050246101580303072100700306060354400780c001115030701520707003100d00030f90032100c040541f01070f00b46541c200c40348503d0380956803203040c641442042c00e4006050418030081d0058202151944000110340c45003564001154802e4180c0108403001c8800054140d180c10082c1c3d9504038542d8090500580030080100703000e0003054041c4690311a50b038040d11943ca402c2048503104003a681c0d18002800080002d0b01100e68101942e4140c1c00181804d10f02c941e100001000e0b0381c4042920001183c0201c0c03160f280b0142006161291100100a0482c1540b0480310b207988030420700c111180b40400e030803102c8180c0d01a2400d1511500031500740c13041490541 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645569847 1250 645568597 645568601
    0x3050a0b09100c031b0302090a1404090803040503071209141318030207030b0906010e06090702010905031909080a030c080f04031506080d0c12031119080105150c0309060a170406 78
    0xc2465021001740d50751000c140301e071088500500009003640794990611840d0204240d802050300d81041d503514050010134460009184218410300040d952000e051418460710b003072501805050041140c0d0520900d015010007004640301a1801d409551044403914041d1041c210303c0b00b10b0420726400481455030100b503079029030b8051000c17403150b9200c20707004603624982440344080410038032000c107074145425103069402030081d20000c183d100c2941c40740d80c10759002c80c00500f6000c01e02e50000052907002540c0d00e00400540020704100e801a403400b45c0841004030b80104201800501465402492804d0f2005143c001c2a28106e84600c20a21002840d560040d1030661140b020300001507849980c410791008d40c4120180c08102e010041a4081c00449109504544003400f54403500d1800f04881c4001d41035980e6140519450320051009101280b50320269501003041001c0450b08000100c920540c0c0039180266200c09213401280c0082600c403007801d10f520b1150510003405456 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645571097 1250 645569847 645569861
    0x30c0f070f032304080304051002210c010b0906092d0a0903030b060a0c020108310c05010f02250305030703031e06030302070306150e011d0f0103050a0b09100c03 71
    0x150441e0b03030f00681e2070b0f0007003029000380d1207440103591040005000c030341010b0500071076000d81801150043e41e403400f201003d40282400c06d881410010904680300402401078030030011041e5040c10b41406c01a0204541c060000c046507110309050101103040752000c4e51302d10103156904030042e07550401c0070072500903222086003500040d083c585094124903204d001c682c0e05840d02e450340c600000041c1d005495089006000420b107000001d8200b0021000c00a000a01400d030a41040190602d15019002c17007040c1e04a2410032201030160305e82c942e00066803448080a401600d4158103a10040902c040482d07040104a4040817800600301038041d00200c2c0c1c0344014006403040303480e410100300116200c1307120180042c0e0084404001154041e03015000c0c00c100407d076480810388814103500c0e0000c080c0e2100c1120041d95001c440c00501c0c003060642c0100da160040c0c00c5d2035145840302c95035002c441d80090088009207001c2128290100640c4d042c2c400d070b103a424090a021120050700030458 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645572347 1250 645571097 645571127
    0x50703060608060d03031a060f07050601080d1b05010b210705010503070906031a030d0807171303050c0c1332011211090f01050112060308030c0f070f03 67
    0x10030401050316801803040910820024080b50030300030142c0c400300c010305041608040403d406035080d80d4039480e9075008102003030215007202c0e40d400c2e2a2030030507e400c605900c01e461942005035a950010f51060115842c0f00d05054041d880d501e8504050307004107094001640d00c08603003910845603602c2e443d04030b0380450016081c0d40364565039800555031403004586000000d8000343c0e00b030041c3d5010754483c080c010b2507050710880f4282528082441c1c001d5810810380420041c500300807605604c1642c1c0d40d01c0d0011119842114104015002242076480c4d5001301072050100315010031007001c02400e211200000e03c0b1280424041c0d1461005184c049145c0c000e85d00480c50501e07000546000219800355103c5840c1001d03881d010034661401c00f4508122041d194854103103060359202501180100400820780c0055494080007500c1d0440001106201b1800e20404102040d1000c1c29640e100f6403405200f41e6031500040540c0c03d40c82141402000c01091000b00005e240e800b0802d0f06da02c80c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645573597 1250 645572347 645572351
    0x7080105130b100f021509030310060905010909020306010509150301060908010207021c140a080301050f0102191e0c0308070b0f04050c0f0411030f09070911070f14030d050703 77
    0x298070000d1015541c2021600350498200401404014800d809048458040f441551003c00304111290165441561396000962000c410b00c811602140c2004004107194240f4126084c6001c0018000e0b24507813003011000ca41c00b00000d02140d0240302100e5100000400d103441864400700119020b0f0000e00a210016051001c0464038000510032030302250340007015040c2c1c00c003201441d402c4902042e4003c8910b8114880301c03038002c0c0010081c10700002d2051807a81d1b1031f90b040400740b001c5002c0b604034a5045620a1910110104580d50ba80f08800c0d04800209014040c4454810b129042e400c401040407810354800401d1003240409000314a20078084070406440394031500f0800340c401d0b50b01404c0c5400000000010385000c41c1c945010403800780c404140166400b554201c160400c0310f6910316180c41c4030800042070b2003804000c02802c4d00200c00c0001c04090309001c1010f00660343c1c0200348500c03100f095400e10031041042d0482c4052981129500e80c64201400082e000030340d07007140030034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645574847 1250 645573597 645573619
    0xa090c12020d1202120f0a02010b0d0b180f070605031501030207020a091a04020c010c0807020714090c1e0a09050d020d02130b03011109150405300607080105 69
    0x112000c0620000c150000d040e6140024141c90b54030340115110301060540c852189410031061141c80500211550309040315151008183c020742564159240507200c0c484485007040000c01c66100071f40c00000034403054030100c10210007903161500ca411150300c0c0d031150940004034664041c0085109041c900b0040c243c0000040042d4141d000307142e00290301042c00d61041c80b02d09041d9028080c20031403011014101c944203004a002c0741d0081e14262901d94485820704113244e0003081460300690320b031004084007885d00b07025803020b440010001c2c1c41510100c000c41c550302c0b481010b4813001280d43c1040407a01c1440300316549198450140070021030b504030030020305460800900303601c80b6000b4020111540321356080095203010071030b81c0d6a2050382c5124804003500d0900c140030910051103015540c5482032410003010366204560030b503480034104001c3c0116107803503c20212148240c0300717184040c81040e030501005d22680000e44407500c80c100400c28402d5116403000e040f00c0003600c05003030032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645576097 1250 645574847 645574859
    0xa1b0602010e0307020102330c0a08240f06090604260f07090b19080c130e19330b0d0507030201120e1507030501050909060112080c060a090c 62
    0x28000d0b840c0186c00340c3c20822003113008102407200d00b00d03003001311340c4802c4d104117246c41700e5200900c0a5548000025000c81c42c50b07500c58000e11029000303d0741d51b003d5405100741c450b849400310000300ea070f03034082d1800034080f07042c41e00c90f4415138580400003040c242d101e070703101c2081c00d0f0001c1340a01118440e41190104422000780401c3c07004003c040700000d0000306061001c0100545a00130b004d0b50880d1845e440406d141c04440302000240c0303503440c00750603044012010044081036403181c1f020440d02e03145220320100000203408000c4000350007102d5540c9a036040554011a10344004100b01d04000d01c0309d907a145900c401040c1c118101042002044506400d00602c000d092400a055a0010905102642c040d1005401410f0107000100e811900200c41c41d007003400390006080d440c0842418400e515030140a00c1340504402d0721074641038545401c1c0141c1c1c80c00107100d0400340c5070709640b0b080e05101c0d101e4121109610428100c41d050300300303107103514003c007810101a101102001808124 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645577347 1250 645576097 645576103
    0x30106060f0203040b0a121b0306141f0c20030607090e0a05180304030803011706040201050a120b1e0307090e0a061e090f0b0f0c0a03020c0a1b0602010e 67
    0x80c07410325500450900b4145a00c0420703640c44401c6200911094903071405824005002c0c10406180e44043d0101290180b1005400e072566500000641c94204004c6401a00c13030300800e07215000504030342041d00d2041402914509240306010303100d02841e607655100808552403004001c882501280d0040d40c0d211011200640c4034045c8500c1840c1714000704119061036000759400942c50016101d40f1031040f010301e4a0365005a10032510b40001100400c103840550104402c0003420a018001a1030a90b0000b02076224490404080c403a0320780c84e00c4258495a40054800c640213000080c05112049a86440e40b10085009100384590380020503109502c1c000c038801c8030b034013800402082400f40d42d0303100602400e00f00f040d0310392690013940301042154054400100e000b2a1803050070b0403e030408915882005141e14866928001446803410311001203503e10311a9190050b12800c82c00303892410450440740180091100407400c0c86554a030440303050484400d40c00030001c0b0040e040b8102d031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645578597 1250 645577347 645577367
    0x90e0615030d0813150f1505152b0f0603060c02150c0714010c03020c0d05030f06041a10180906080a0602031801090501020a1b20010201090f1103010606 67
    0x7203020000c101c1041c030501134012014480c0c19051000352100441c1c0c01203031901c0300743c0d21090341c9540d002e0803078220000201d40074101c10b0303402002c800c0200c10783c80f80c140b0404564212004c40107244141d06c00240c000718462002c550000e10464141d54050006440280410f6810518103950225013b00000d031b900b020072800c0e1120030450380c07807a01041c0150040031050711408284514251204c0d000c1c070490120b900c603a200141c403194140e0b1424074240c0303041500c000307000781001403041402092003203d0317000350300701c030041140e1b8514603038072040e45042c42e0500d030003a14050100070039a4001c0c6c100d20100808001c0e84070703c03e1755186120251450341c4202d0076141c200c50031000c00300e0100d800a50b48402558000c6400300201c000c61421109060015106a507000c1104680c3d194020070300e030048804200002c0c0109410b132030ba60000c03032a4091103105982d8420200705264000c1d0030890310241c2200039124030284d64103000d009049040c904500c00e502c0d005000c9140d50103119400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645579847 1250 645578597 645578623
    0x340614070e0117271501030302060c0a09090f06050405190e07050d200904050304090501270f0605060d0519020705190f0206031801050702060705070b040c090e061503 73
    0x1400903155492140724040d068481c4d5481e07103000b400c890500002c10807020729411511840030b807031580365040c020f0410303802030701121154004014550350a1340c03024040c0b050b15481000000c40440007a98200102416402281c000d402c1001f017245602c0601c0700e900d60320a9502d0248100215440c05545034461030003880c0d409511000781c100801c0c3c42c41c071a49800d40c14402e400307036011440c200054030f0840c112012504c59100013801e114038030341c0b801381ca4010f0010754400c84515081c1e203810000c02001030301c4a085070340c6d41c1e40351780500d4541d608104001c00c40509140ea07500e6056100501400c01150040542d040f8006020441c02e001d208440c0020381003005400e07040d80c035142d145110b104102040c2c0d0b0f0046501c90110160769014002c40c01408180c43e40c0708c50442c684805800d48100600340300c195040f07181003203a1950071400315860258404a020306554803494898102001d9401540c0d0107440e01000c1011454000b032124018450822400c0d0080d10100406541d40182c2c110b00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645581097 1250 645579847 645579887
    0x10806190605030a090f08031902190e031f24080607050d0b03010204120b0a051b130f060c140714090a0902090405071703340614070e01 60
    0x10409144500043c54201c0c04245000c22078500c96215054013001d030b600240d6810318004280482000f43e010080c05040b00c07400d00750305200c1204000c6107500700a50402080c0510705050009a590600c40c00800c01d08119035003026140c00c005942c001d050035040d07880c41002c5001110700302d41d8101448000c0760b841200034a055074803e0303000c0303445800c81c0000b0481c0b1903e0720700c140c4a80d50203002600103801815140c4014540354184015009000390455549a251409000840c0c5074403120340d21140c20b50544a644e101c2e0864038000740c1c03980703270b10600d030f002d405038008508240e111281a0156000e0303051417040408000040b9214900b0788241c4045c0300301c104060003170741014194940d120041d024001410f40c590f0f0085984040300f224100c459420100013405412140750040c0e5220006e50000c5080600841506c581c0300c9442a00101142d04603d01c4441d100181100900d0190b10038014851007079008110151401c0030780e0440e0110740c4100300a100b40d44254071460f803d40440e194 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645582347 1250 645581097 645581099
    0x803040b0d0c0924170402010909020306030f2d070f03020f01090305030d0603140f0a0f0c05030a061b110c0909030f04031a01140108011e030c0b0901080619 69
    0x1c100090800c0c002500a00844200005000744600280100581030342c001d1601a450394100074514008540540503400a140a001c050303680400c80c401a21191107006940303489100000e4541540941462068131446ea004150401070000703604003424070142c0900708042c0303611500d0300c48201d8019420192205d00041015151038900d0f448814010b042c600d4105031642c880e40c0c203681c844410611240c3e140c80d0304104110f6004003041c41020300d0710140c02d42c2c50007014910348601400c0c0c00500a449001030f5181840b0036880400000c01001b02203c0d03207400d040c030380440603010700741400c0c48200c0d410010171001070043c42503070140911040900803100c0d0510403c101d0000c00391640d21a48000d0200d4107011a0880081c00594001c070a100039015008981000300c450503001028885c8442030b1454440e40c00100260544034000980c4080f000309007051400e2196541c03000d40301070505400050050000c0c001000148801e03039485901341e0b00d40040c040402a1016108200581608 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645583597 1250 645582347 645582367
    0xd03020613020402040e0c091e0a060c061b18080c010903020d0303060e09030706050603011a090405012a08070e150c0c0a0306140106030e030a14090a0e010f0803040b 73
    0x841c48086200510060800717465859845d41c1101c12903082c88034040006207044145000a0003e03420b5090a06021413001c0d1440815007001f642d03c030304070074400c18a144404101d00d58108100300c00025140c00d10190848100619081e00e00c042850019115280480d210202203484605140c068590665080c6150b00b0b20011403150070003a800c255441380c0c0460403041e042e9095028000c1d141c0115150340f42420400f04980e000342c00319110f07030301d04400d0040341c02c60104000c207518411500b2601680e01d80c14014054000803c2d40c44040b40c0340041200c0602035200408503c01c071b0b650b100d01701640e40d1401174408864100b100c503403216090304041092110340d8001c00d0b800440c00d007075551204111021545040c91a0811100350791202420801a0a6280c00c07500400d840e25040c0600c01032829002c0d141d01c07913080407008001907103222010702e80d40301c0c0c03c45800c10009440c2c442e003641e07102040f0a008001b80100e40d607100141200240000c400004d0b1019141005449850580d150f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645584847 1250 645583597 645583621
    0x6050901020a05060c09130608100b061213060501150c02300102120f130206070c0e040510050714160c05120105103c081b0f0d030206 59
    0x10840c1140b2419811400080e0244404e40c0240350b10441192140c2046081010708054204004d401340d24142c0200100d0390001403e514031030004100203038051030a00490501d1164954614181441c0c40500800d5031548503410900b07800741c441004643d80355000d80c00c2402c4e09131341c92000a8002044007001d40742940d2003445443c50760701c1d00c1c80c400e181d4090031034401c03e0011001c900b0f80d50201b03d2110036035a2101940d84840c1c0c6011641240c03500020016104840540c040d0050401084c43c3c420070018070081c0c0050700641c05081c00030702e002d00d440c3e6aa01140c0000444140c1084d0120312524016240b6907140850010300034140680d03000305001d030040c40c40b002d95090341d031001c0c0010301c3d0f01c0b0710080210080d1f2400000c10030380740070b8640c07030209019580705030700b580c103c4486900f45414040b44800d00b0a21f0002000110b9040200000c002c002a040090580107031788408180c084255001d8404400580301c50640c4a811000c101c01a09001e02c0540941c000000060041d1140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645586097 1250 645584847 645584857
    0xa0806030304090915050106260405100504050102310b0c010b0d0b0403031107021806190f0617010806010302060325210606090504090c0308030f010f0f0605040605 72
    0x5401c590800380e443c00c401041d02d41c00c45080e0b904030314074030700c001448400b8010103003d4082400c002000c00c01d43c201c400c080880c400344003150051003c01080c2001014040c18480c40c10840f8180407a04090900174000e41c08404403110035004446132803550049842e02124403070f4465201e10f0703c913103040c90042c0e0550200400c0384945d50786480114046d603d43c40d04e01442801456101114905460051304503001ca50f013880303d170507080c4996401a621f40c1b0141210b040000f8800c05c090302c801c00400d054030762005642c4000441c3d60400320b98001481e502404440442d41c0350b00c1fa110750a902c6130001d003000e0052140c00d420100c0180054240070000315080b00ca242001c3c218042c00384800004612a81880e00006400411401040c1e1084c0240f242d50003240104000071403408038054003000c101c1c82154003d684030701590092000040c02c01000b036803c00c003055500e10380120a1402180e09000b0310510b18101000440d5154042031680f0035916a503c8181c038150802c80d00351126081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645587347 1250 645586097 645586099
    0x130305060c0d0e121c0905030f2a0d030c031d030a12111813020310030c060206070f0f02031b0c0301110705070605180d0f052815020712090303030b060306060a0806 72
    0x161004d01b030024808000402118500d42040f0fa281c1e80300c80e0f03510340843e000740000401e40c007200d850302c911040c001c10400519011400c000400f420410001e40c040c040303459021490040c00d0103140307000700700480103000d22a01c3e42d944084403500d5003c1402121581d50720007881e43c0d01489101d4010502c62139440208000804400c1329102d510800c006990046500381821003000500700100a55016040040c0c05280090308541c640844010040b16044816604003d103141000089a0003070040b0341000c0342c21000617004110700d031000b030750300c8082c0400c041c060741c6041c2840200c6d000c40d409982c9540da21002900038249004000c560b01d40042d10002a000390321040350f0101c2e44c48822007000c051040350422811101414218281050118000d409550300032800f2001d4038012035030301191703034041da9044100c440320142c00c1c028065400c0040011f82ca0441d10442540c1003030042e001c0303901ca43e50a101402d48a03041c41228001a502c071030700543c003444a22807990083e042d403a40400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645588597 1250 645587347 645587351
    0x140a030801050625060606030c03110d0b060f07030306081506010c0b0c040b0c0639070f02032410140d03031e0b0a0504060317130305060c0d0e121c 65
    0x44404d81203189141c0c401c04a42d0365039500d50400140c1d80501414824441c40c0c20100200c0c01da5003504551441141105001c840d5204140900c43e520401520030306622100b901d0784604040c031340074004024500800d44548241c188448003802c040000e14851001a9030f51024903540340d45140d500080581200c007440306c00d11010441004500c05007030a2160302c802410241000103003c031b845001c00c0c12030010004e2079400b00d05c61028414062990b80128003000783d070303000c0f5410808100551000001c2d414025041e001800001c2400a403050360a41803803088203484001c0c0803100059240304d400c4400d0b9030301c0b410314003501e40500c4c10148a4001e041c0403d00081e0842d48043c1069900d001c0d01000d9a611012002410f0195208003e080e050300c007000060300b1500da181d603014000700e02c1c48030f0030800600098000703450710040c0000d6601604440701400c080d0345005503600001c1c21400d2240ca40300514440314000184040f0704401641c0741881d08907822951120101074030b00e010310041d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645589847 1250 645588597 645588637
    0xd0b090c16060e100614010311041514070803041203020c071a0c0f0d020705010507050705060307120903021509060f060120030f030103020301060605030c161406090a140a0308010506 80
    0x48003d000510000503096400611581003042544030104000c2c6e050381054a0500043d0360456000f084806440440320400d20710505500c00311440e20b0300c40200c11084c07002050990030002c0181c05140200d109506020300e050450500714128000c4401a044580c820700e400c01900380e0703051915100c10b08036034545140490704002c0601d07044510400e41c20346e90000740c882034415414040704010308024130706030b0b10302041e03612299612700c0700c1e01945100341000404101124040d042d04045003031011410300000d000c41c1000380d00c3d4100c00c000c0700c1d404a401c5000500400f408640d59201d0b050004400030240c03144001141c449008440030811030407506205080f2190400150940c2810f105039180e076981548141030030f55071180c0c001818440248140a5101d0b100c8041d80e040c400b41a01c4e000c4020340300e060194045407940c500018a029403014000300328004140001500c1c007920b062031128a040b4175240d038070144154050300040300a001403040d45081001400d00e21102a0640440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645591097 1250 645589847 645589871
    0xc02040f1b0206070f170f0c0c150603011401030503070303111308010506150403120507050c091f0e09071e0302030607020f0d080c09011b05120d0b090c1606 69
    0x400c07030025480002d81d10060802c500164080c071a00e07880e404601d45a01d03138011078500c64051041c082d10b140c031400140d80001d50041810360a8490284481c8100c810300040120764564030841920264001d500705505c816512401d6088241201d500100071807404080c1d0b00c0803001003180c2c4440c4404031204004403901810442e903404060802ca80002601d801c0c0802040030740e20130320792190781c4000c080c00704102080c1500d4210f40030140c03608020f56079403114901a41414402c00105500054540031f12030700740030a1058040c48003141003440c400b50f0715404242035845003140c1c84d500c5980019801e116040b207001040d90301e00402440c2c41d5089890781e001a003840400c40350701c1d00503071104420640001042207909200e0841c1d09000c0745d0f60038000a2100944100c0c500c1c18184000890f400c0d42c011044a82d40704029002010748a0184009041c0c480542c82402c49003266030400b00c0304101407a1010481e0b0280c7e6155075050b00d4640c80808103006103212900070307100159122040050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645592347 1250 645591097 645591131
    0x1903180e011404050f040f0b090a021809010b0f0f10031506350c220801050123060306010c02150d0b18090d08150307150f050a0c02040f 60
    0x80c2070b080744000030206a00c4144800c48a00a0180d040c42c42e0407028800859a61118900d405030448490840756480c03400140c40c0015000001390070032540741101000711072502e6000d0003600c12034000d10804a007801082000203007a19040da0005502c85005814070b0004801000ea40003400c0c042080d240440c980b100d40e81c070343d51200380800c07814034202c0d40c009d280b01d50801012414107100e9110b0007030300d201d400c2c1034030004003a034441c00c00000e20f034124240074512452a9540d21401c000e0a16210118207010f0705080c880d4290f0301d2010300b076a11007100301c815042461100030700528116075825004590300d0309800030580e0000d50511319401d200415000518a00c5200c2d0404105c1d000030b8800d12541c21810224000c400301a83c0600030440004180c0e4640302002c3c0c902480c1c141c40701e10034512500d0b41040ca540c0c1c148a00c80e0700081a030300102000700d40045d030f9242c20310120040c00c8151074501c40c81190b000010b0708000c0e040700500d8558082c81201e41409070000741140382d041c803101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645593597 1250 645592347 645592349
    0x81f0c020708100204032616210905240d0908090a090b0a051e0d030e04091407080304082806020f03040209060a06050d0e160303050309010605031903180e01 69
    0x1c14207400040600c10b2280c50010002e907800e10b000c1075202040700e803001e13030044c8c0203500b0301d503c482195100755000d114426204080c0e1540c61401040c60030340840c2c1c01350254100b441080c0c00303580140c0090115100c1c110700d542156113000021850b100301d100d40c4400804601108407601d12041c080140503848442080e006080340c0c0c80d00051111400040001d050f446900030740c45100030340005c6a401c4465003400041c1c504c1070716001a04c0f5440d10782610014008140190802d240804000901c4641c461458181c4c50400541b00c0340c648500403540c591040b80150317441c1d548184440701942103403144003884650040d1601002103011390390a42030364001e02e01d6100e251404420710056143c0506601d800242c00ca07009116140340040240450041400490038076a40348100c00300b100e4240032244946642101c0000150344901d005881c0e0707002614440040d610340540801d080c140003841c02d0103d0740048a00c10341f09141d5900700ca90070b2980c1007644422400150009150701c24080c10340c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645594847 1250 645593597 645593623
    0x270e0d200f031209012d06090510051507110d0309030c0b040918030e120712060c080f070207091d06090d03150f0e07091805060406081f0c020708 64
    0x160380e54103290310080986401402c4a445645001c1ca140a0a1101014290341c803401c11a80384d8820700b6803070014000c00e0141c3c00230205074204800c001c041101101c3c08400d40b04103c2c1c200008440c54002001c403401030b020020b260110350542c3ca4403500d086001203032058402d180610200ba00c175500d108a42125620400c0c00300d9001c0b070240a900094010305c2c074507005003540c03842c1520068034002d1031810101c6004cac0c01244c0c0d495021042080500c420809010180e8100d241e1141e90b2611030010722560b0203a00c00a0f440c0404a0060060800d1860141006500505081d402e0902900082c00c00b20b01c0c545400d10011901c6004020522010f4815803a4001078040800c1ca224081c054402c0815911103c146086060055030040c4050754240d0700142e0001f116aa90080c0a803980b082a4004d4800c01d07014102e001c0d0902000e80103035204850980f0184121644c8840d00b80e66048804e007111160103503040088092001a4090485c41c1030718411035070025581c6080b2420440c1c4a40d0310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645596097 1250 645594847 645594853
    0xb061207120308060402070c140105120c0d0b0d030e01050d0b0913020112020a02060a0b2b020a0e090a11211b0a0321021204270e0d200f 60
    0xd0741070540000c0032552180f000ea030b0562a2580554480e004500b00e40150001081812030302c440d141d20410649030040d40c4c65200d91107a080001d03d140a60b000380e03020000c0a8240310300e95a09040035407020b00915815141c0820300e001c24001501c1ca60455110f03034900b00d5840442184582d070395059140241c01c040c044415090b0701380001050700151420700e400300e41c010018a03840c69400102c0d40e40c4110b500030000340d9840b01c3e0001806200894291040c8502083c010348000303840300c0c00d070174915031088401030912655032003000d0400c44102d0b0540503d4000d51050740105540140300381c64408002c08071049040d0034001c629040c038101c08071130019808150701c0042d4144000525455003811603c8801c864a941d40744100703504580c089600380b4000c048d035188114020060f6200085001d8480c1d52030315250000e4411401085a041c58071101400707006c1c0304400795100d081c152200350b2001d49521590020207885c11005e42880e00102d041c0c41031190b000035400d00540c2d45055109c409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645597347 1250 645596097 645596129
    0xc1e07060f031803120b2403060a030c080709060e0f071d09130204060509040b070c050c090c0c15040c23040207050a0b16080106120e010f05090709060b03040b061207 73
    0x174000c104c80d0440f40d070714000d00940d140c1d107810348280460040d079001b107450300d15682d03900e20b80800d0041c41e6a0380001c04800d601040460592400325150f819548011420005141c1d00c0030107003410303001900c1880c1a4000440491540c5101315007110070744100303114041d4000e80703510219040300c004880344030701a50a06070100c1149040d010b41e60007858102d0342e800050a103922640c100c200b018048805100c0102c012030100a8284880e82c141c81008200c0010f03807401c401c40e0301855006507051640303030107880d4806101e10312940c9024011900901d03100c240c24140074400c55000080104201c280309510011450b42c2e8135400107108162040e0701401c508243c4e807500b2021110058800054031203044a812440c0ea400264a411030b805403800c0351510403040b45d08002070031640c034203240315420824004a0242030350001406580384100701c84825680705004400c07285c441c09044a11041040400c000c1884113002c541c000d10024402105100401c0f1181e00c0c01e019030703103e0b405da206055a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645598597 1250 645597347 645597377
    0xe0f06061b011d0703051c120908120106050a021002090d020405040c0305011b0806010804030306030b0906040b06030c0f10090f03061e0c0203030402010c14030c01020c1e07060f031803 81
    0x411006050f00540050a255081d0380e961901c40384002e4442503030054410b10646041d2081c004030a80d8116a407081124941c1814003c00a503c14200318200c2e4030380600004042c0d00c2082100c0302c84510754050071410095802080c0a54000c0c8051680010424090b42c0560303514490503000741e12a610880203240b5526109080d140d0107015422218030308502600c0980c1c119407010b91044003441d10710b26940c0d842c6001d0780184103503040601800d4105041000c25840010a079001d10b00401d000600742e52801c0c1015a80c000c1d8845650f0440000290482541044080c00a082001d410440d01c0399448460700707013000c1055401911065200c15001003803000000425103481000d4009001d01001035401035680d1101402c024104a2181501801d00014070404214541c09806490b9611558548a4084d4202c480752990074018410030580c004608a04441807814800c0038000c02842c00405540340416942c540080c11b490340710460300103402504800005200ea22629403a2183c85 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645599847 1250 645598597 645598631
    0x30f0606030b030c0a0b0f07020307240e04050709090e03090907120f0b1804051213050906060921010624020c0d0b06060f090406060819060e0f06061b01 67
    0x44c0c0120700603240d01100340103504408048034403107000240c0640d40c0d1403881c0f001c6454120164080c07844601c10340002440004070001320004070800b680c60740c6039003210b0010401164000d6803e80d01083c01c0e08402c101e00040f03038000c0700c000b110b00c80c01e99051003441004940117140840d4840002240c3c14030b0207090703c804e40f055028220400c20204120a20000410443e43e100350030304115814620000d41008400c000d8003c15401c10000d0036120009282104808030403400b50303034803400c003440000b000e03820301d441540d22108004045188044036030601001c600000581d1114030b540f51b2801207007001c50380710409013007410b80016549050300040000d05100c0366183d010f11030002c0c500c1030710200f0401c840298204e00308442040d500d103900b82d10800d41307205110940d0307006420b04100281080e00024220310450050710481446042c0e058000c003200c07010300919007041040008a414507900700f840305d500280150072030707150480030510000007026065500344242e4483c94030802101c059 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645601097 1250 645599847 645599863
    0x301381020030a0206220515090c0114030a0e0708031908010e1006030b031f0b091e150a03082a0f030f0a1817010513110907030f0606030b03 62
    0x19002441c03c201c00d10708003e4032001c001d02044d0040d41d0a44c40200c9007070b0018094901b03994880308035805c0321a02c00f03940c500041e0071900008140240e80c00407950794007619480a02a004003442031a659441892500400044220094520840b0340200b0041c9080005010040d0615000003800e0840000146500c2d41600208001001082070240c40441c9187c80e2081c1c50305420085606030b42c920100b441c16441282107606000d00380508807480c0700030741c04506600380a0301c40c24503540e079015100605000802090341d04000030800100d81e65500d4200d0469184014051240c4543e40c1d201c421341030308101c1c040844a1503400b00281d0324a000c4031682c040c1e601881c050603610800c0c000305d648901521400b620000000a948200d207446842c54031004202c0b45000140b494072030880c150500700400182046620b09004103141404000d040601d0540c4040c10360707100300d00301d000c0c0139900001030322500903d034450200c003460f104680200c0e40070302050b94000038014214001c26250045c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645602347 1250 645601097 645601157
    0x1060804050d0c0201170703020d15051c030c120903020d050d11060601020312060f03030a091a120105120f0303070e0a090606052d070c030201030b03013810 69
    0x103040301c0400141d8118070840c504400d0156002940e50710090b05030080d104006d1520689460503186002140448041400b84d33601a50550020007014681021410701200050040391030310030901c0c0000c140406c81c107a506020f03d01000d0341640c83d4003007250301404560072245a0007400c01928082ea202070000080000a40144010300303000b400030f51207104204100c008403940000207025a1a100e03201d44209502038202c82c1c0d03035041c00c41c0040ca031000d14016071f0221080881c640f00700c20342c10400c1c0c4102402c1c00c0500d03221646000708102e18810a50010b11007802280d05c2d0400407803080c0085d40c0303c4c500503180e1022410f0003c0400c54150040c0e002071340014940301c0c040c80b015078047c082d12001118003050315000a1840503100c0d84040f105400d01400300001a200d040150055290007240c2c403e0300c040c450901280201401c1c0e42119100c3c0e04205645c0c2c120f0042e100d4400540258002180c20b000c40b240780017000b080308401e064642002142043c01402c08045060b1f4500542d112 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645603597 1250 645602347 645602357
    0x5070b1b0c01080411010c020301110a05040618030809040504021309121419030c210b09070320131814060d030e24031f050a06050301030209040606080601060804050d 73
    0x2030103a40e1070017440850461141000a104000c0301152000d60007082c020031114807a176111000c055004000c1c0e405802180f001030800803045034100b24940d0440e0a4980c0507034854107290408003400010080100143ea001a0074641e800c1050394610403ea1590300403400031a40f076040345409403000345d041400569081041003d612000070344c0344c4030710109900d0f107404070b10507515080c1140c14000c64481e040903441d008110641c10f0701194051682c4407002c0c0c40c2c52a8a540d0010b0560807100440d14800010b24850718101031080c031400142a40c04503120903003410340d1500100c500f4050b000c030401c58a150f40d1002c2c4403003519500c1003164015800c59000140101c02c1da401001c0c0c504c00300415010303085580e23080d410205030041420304c4c01641281c880d2a4505103060180020408003003400d0402202c4020605003050302c0c1d48800d98505880300ca2440c1d10310350900c1102031b4000c006a903103650f1041d001c0740d83d050a20200c1c0c0201810380e50201c0905107030800381e003072285e83c01c002c0047c41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645604847 1250 645603597 645603601
    0x41104091b0b040f0b0c070527011d150a15020c030c0607120503071e0c0b0a020406093f0c080d08060108060102010b03190605090105100b0705070b1b0c0108 69
    0x1548111480782a12424402680c4514546c0340c9203140210981180390301001e0503204010aa0302c803840c00fa0a0152842d07811002e136681d085c0350714120456140184010b042d00e0005010850b10314640703010810161201c91100d6690942034250010049908016040140160341ca85410030852404d000101e07022403600b40c013951815901c141643c02107080c0b02c401f000190500c0c0c02828038114803003c03103081e6480da01ca0040020300600300c40004581d100d401c0780200d0f43c2c0d10500d109035010340e91a40c545e07100050501e06400310582000c0e405000b0443c182c20340401f0514040341c0031304640202208145045458601007030030100c144c02c030340e009074801c0a05640342c990200c5d00a41000013800c03c0c10682d140e102c0102e02504401164507050b202c2c8a000da80010980c0a0b20080c150041e0000c010301c0d10f07921122400e0b90029100e1505100a121043c0001c0701404028030309a8810811500401c2ea1303481462415040500301c513000070894454000000303c14090700e070360380000746441d08040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645606097 1250 645604847 645604859
    0x16140a0602031b070306090602072006030a090f300509030d051803011a010f051e031e0112020109060e0306010b13080304150e030706080f041104091b0b04 68
    0x383c0512000c0d45002410a4110040504244101005507402c5007041c0041011810140c020b0345c05100225900600400c0707114156010320840903041e0401002c6c1c0d032441d2241840320000e48914081600d401c104100c2c16000500d0203003500189625000f0b040b47e0008011804002e080e100301c0750303d020b01004000c54403180e80d01103500c0b000c901481c28003070349921419080b0706044001d0841c0704e030198a00300c0701d1700210010890144002c1e00907038030810281190303041202c5a00520350007000302e481040c9043c40c90003041c8060f41c1d018031884001000d149000c441c400b00501c0c00ea0128130b180488060100544d68032003a5038001e00340d00e0800040b01018040071076035601c01446010340e007034001f02c0c0c2014000d148035007200080104800301c0e61140d45404e41d1082014070124100301042c3c81305002c40c050305010480d0801c440c05500c03a524a40e0b42d845442803840001041214405143e01c074042103070f69140310b0b2010080c000e110800300d1204150886034032400c0340d0025544014180410088 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645607347 1250 645606097 645606103
    0xd150e040c0303140c030a03150b090a03021e03030a210207080909041407060e0a0e01030b0c09240703020d090f030f0501060b0f0c0c0f061b070816140a0602 69
    0x102c0354146000001c00c00c200b4542c3c0701030b0140c000c240c0043e0100184007605582c1c96080810f5003905150244140365881c1d40c15403e03031041c0709000350014100c000403c054500885010b619054400e0300781c8104e03907428000381c1154000102c9030b01040c000f200b010010600040005110746400004524112464507241c1c224011240f505228049600c0010100040a0303c00c07a081142401116500b40d207820001d020a80b192079541c5c01020742810002d01c000c3c1000d44941265000254100640c9800b40c0ca103c20b6401340d1055900260701da42c03541800d9145100303583c05404a91001a210081483c0007400c00348014000801c106410034103100d0560b8191500d801c480e442020403500c04030314508140541141ea104020740d02c330104104407600051402030004124070410f8512840c20300c0d08000316024400c1e030a40d002281403001700191aa00c0d180306201548500455040e60703500e600c490f260516074000d000407000304c64410014040d0580c800310904900319074104034075043c100000c2d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645608597 1250 645607347 645607349
    0x8010b0603070509120c03010516030e0c0901050d0614070512090601260a0b0916171009080c0d02011a030c060d051b0403030905010912111909020d150e040c 69
    0x2c0705d6600031280580d0b5410400c00c81e040341a01800a1100f0318122944181c190768012401000c607040c24840030010101050b0006001d1f4001c0c00049140d08100038000b07003030546001181c0e119a95480c10f0044411402203a208481035510702d542c8841c4900c00303808000d006800350442c0e62011005000101a1103001c1c1241a08402d40045d000c407124407103844c000c070100380503101c40c083d0030a00c98440000314015140c0241d000d0740384d500a0381c0d0703008014425520407010040d9004a5034281d0004182d802c000354440c00b40e04403604080c0518021400d061825034041c0250b03544104903240001c04005102240004502815420310b0420124074903205c0c009464003516507032400110740703140900781420301c9010900c40380d0310f50740c8034a000b40c9960740714051180401d607003c0000038a416444045201e25038849d5240031142604401e0041001291496800d007071a8a9008a003140580c405020803180600011031041c01c10b841e5240000f040e500041206040401080080360350851008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645609847 1250 645608597 645608599
    0x1e210304061b0213021c1d0c0306160f120c030b21060c0a02070e01061101052202130b060715060503030c06040f17030c0304060605032409030708030103080408010b0603070509 77
    0x750b5900006e510303030550320341c2c1079109210b420320b800d03c1030288807000f1450704131000d84e9508a0b40a5090b000402d5a105811035540e007507000c60b42101040c02740b05402c005400e8900e42007110002e101400c2030701c162142c2c07a031101d0011356620070f6902945405800050701503480302c000204188101e0b403d0ba1103683c001d0a400f07541c6400a4110040c41c42041407800410418400210558403844d00810b40c4000c1c2c01100340e55803c2401140603510141902606140c00310a000480802c0f0350902c413580c88070306514402a0b03a25207811074540c40d03540c0200052481040f68100c034030202c1a221044407055041540694018030507402e200000180c290b070032607000f21400ca1181303081c1c0350116001600c0700550714032000100622208042c000d003e03500580c401c803c28400741d625a030500d1341d1002c2d006004408101002d510300b040384007142e00c954100380300800f42d170310700002034032000c02d5a0b00030780c021601114002000c002185c003e104503491031800b162407600d10b05020800800314040d5241d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645611097 1250 645609847 645609851
    0xa1a0411040e07050304031404210201110106080a1a040b190f1a0301050a0908190306050402040b0c060108070605040e09101a0f0603061e210304061b0213 68
    0x3265440e095105441c01480000c01180b40da10381400010240e030410b4a0803800315041d0f907600340f01d081141082c3c4090320101d0034541031513095240c4000803d500400160b0601c4885d8080c050aa6002c0c06194050413800d002050f03910440c0c501304081480740d51140c502c1c46c3e080010b000c001480e000c41240c105240078207900102c01010030660080419940d0500c032a4544200600080011124000c0010302107008000954411941005641118200820f04181000b02080d20f106c102058000f168040c600081c0b9161560041030407a03000760803502c0c06481c04030301c0e0758900ca01000303440d025080007006400b41c203140000160a034001e90080c070041901c10390015094013020010051010400401444082020410042d00042c0303c2016030007100107026889940c2040001c40f8040c00300a0940c43c800390480c084566243c4026405680c040300c0740c070306030070f5806034403441080e911007071000ba51747d83d0b29260003c0d00726074030340700071400015481100d040580c0c2c94a0344064201c2d0b0803400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645612347 1250 645611097 645611111
    0x10206090d080408211909120503150405100e1e01060302090d1a0f130f0b09010612030207061b021c15021b06060303030c03040303090206070f030e04050a1a04 70
    0x100c403032140600410340006008203e80b00c4030300d0750004821409480403034601e100a08003024482c0c241c40a101001c1c00c230072680395041e40c00c3c501c100b00540d804100010300c140d180034110002010386070155612212100c60050502501c0d411070392158003c07103d45d001e5000d0010740c500c002c00c104014030800042c50790114200916842d10304540007041d80c0180c0880c5120090420b00b105c00c40203803117404903d105030002403118141f204042c00030340d411484000110740165100c00a0170001011010b07155260300c1b000400b441c1c510321402283e44242c000c1c0007140c0c240540280080c0f12507502d69034150890b1100d03c00350300c0c1d00c0c140040c10701d103c01500c07030008440c0c10482066402114ac0403421780c40010309008115540508150003540902070b551640c580300c080655a02007034038013401407070040002c500028003e0307100c2c065803403014000909020860b250300f8620088440c0540218802d9100310503d890170784500c0751700041e440c00400c58110032000359a042800c0c0945a401150388240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645613597 1250 645612347 645612353
    0x612190b04060603060c050304170426070e13030210050709090213050622090209090c0d09120f0f0804050303010b0c16030f050714061c020c0f0d0e010206090d0804 72
    0x400c05550000717810300c030b61000f405004100f80c0c81241c0641e80c020a1207038200d40d01e10300b201250203c1e554621035007052030717003941142011603460708203072907500c5103120000d6213111a5103003030b10401103146001c2e0700718003e0902074144403821007107884880c82c0004014920381c0141e03084095030803886005072204100302c182e410b640f056410680e44004046164200428500c4040c044084034040602c0045d951f42070319016801680710075603000002400042840d07024a005e424082803266000c0307400c007032070746652050008072540c100028002d0040b145032103800c0b624a41c0c80155130f1401d00303840d1a103912690789900060240e140105000104034500981c00c1200a00d002502d844070181c5987e0307460088400304604900f1681d034040c0070000101c2c5100c5502c11104c2034000352486103012045100d048180401d40103030007480c0c1d401d000b4500140001c000391408250f50380010682440700300d00152200040c940040d04541c1310380700304855803c022490b40c805a01034107125035541c403149 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645614847 1250 645613597 645613601
    0x190e061f15170f0928052508060c071202030d05040309090c1b030e04110c0604060e03190e0120060109050c070f02040e03041805160507050c0f120a0b0612190b0406 72
    0x15001400c5445000d414000a074054541004080900035400c1c2096035230341c12050f01c1b820300711942c580520301808507002041c4a0203415a1035116881524900440c18050504030355081c0c4080e000502000010b100000300c91141818452044c14500907048600000940c0c000725854003c08010400c2007901080e242c1d40c001886030640104c0407900d40e00300c0c0c06265a1010115026200d0034146000102c00380030100c01c0324088090031032801200c6810748020707141c0001c1c581005041003c0045108004055801c4050309001d92002600070313075240507500e100340c80b00070340b4200d00220f0401c0240c00103040c15a800c034030f540c0e045d200401d048800480c0281940600d5205d10f228011300445030946c0e0806ea400700740305a0100c20a078207821043c407021600d038004e007503000b81294840c407030b500d5452405408402c4400401030040b0068114104041e00b0f10400380c208071400d100000c00e00c00346141004403408031500c0c40c07000700b00c3c02803003803000d28001c0b0001c100130345034030040b902040a208842e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645616097 1250 645614847 645614923
    0x4020f060d1802030d03060b030f091c05071101030209012f010207120801060c020a180905010c050a02010605060f270612190e061f15170f09 62
    0x951810007a84034a04a410406402e10204a01c68003e12041d145030714000e1059200f40d981443c1c1603419640c1d084102c804042000d0089805031003110f04000d00940c12020802c001070743c0e0307a1081d40f00d80c882d25004d45e45103110104a0706250051001c644540d03070003501000142d8109501c100901e10b400084002d03044cc50b06100390700e5000055000c140308400740b0303500e402324032540c0e0170b402c03680c1e1408201c40604001000a5018150034010000f1416415900c00100520000001c942d03040303544590031a010030344140003148021980d102c0c60358084c400c00d00240401d2b03030304034a008803644070301d0220300c26241d200344013045440428500c110816005401054082d148543c1c680b1540501403800100f02d541c191120303643d0000e1345d0091b02d81d0007650003030214140101010384414160174a12507102c14410315a441e00b01c000990010180f0600440304030f07030b850f1f04100405400428105035001411880c1e0503100303400340820010300159006c484107a00c0d030822400045c072a0802300503446 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645617347 1250 645616097 645616117
    0x181519030c0b030612030a142a0d0e010504180509070902070602120703142d0f0a1803051c110310211e062903070902070b04020f06 58
    0xd496000ca1454002c1d8010750103401d0440b0119520803801040c1c3e95a4410122243d001a254104519004023044040d04010000700b9680c600c2d40c3c4046041c50901a02c040c885100741d11401641942681021812001010a00e0103514060802c4410340118200d00501040c01d5501e00004054410520512024004281c008d642c0d40c29a07080013406500310320400c0c4103840040c808280b0150183c8144010203e41d48080c13171896507100e400390028000310b803c80c11032203001300c801d0080f0b51100c40600c1c81088121406445400d040c0e0601c005c89074000b40803c118569842e004022030740060588186540d0948180c042515030340c0c1800c09003000550f4800112008000c0c40548040092818284c502001c8046101084031030450992011035038042c05d44102808021400340081c4860a1303403a00803040481c10303030138220700c4a02008102c0e085020302c44965010301c60900d028070600009285c092001d504110303464843c1401840080c1009100349210f1160401a455001c1540c0a10003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645618597 1250 645617347 645617363
    0x71208071a0903130504060e04120e0316030b060f030304090209030109081209100b1003110c062707180515040c090302040f06060816031b090518151903 67
    0x2042180d8968942019a501c0503100e101c15002c5101d00305441504108c41062060583c26100c903128516030800d9015200100182e000c49510701741c1b001c0114030b56813210301154607441381c95810715206508002e40414403498240c80281040d650000a6905540c5840c9006a88aa20200090041c4000c00000f40941c901040c41c1c000c0e04a2271300c0003442004843d05640142c440c8001c01001c0306c00c00700701207600c8106944c45c402624840e40c0520003007100c42065504d4004002050f52604004840d070040041900d0360801c0c0502d5651899400c41420800515401d4100490095540c4103010404011903075500021510031004427480e0140b4005441003103944080076005081d040c082c0003e9014604200ca10100d1541b5445a40101c80711551b6a0f1041c2d2105005044641d08078013601040540710170b01d00b241e81d03080d0115410064043d841d0800712030701c0c2c8001e02c130300c030340c090040d00c40d850a41004200300d030802090490040f01c012540e04540d98148050310074000c609401c0909601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645619847 1250 645618597 645618601
    0xf0b0a080601050d09050a030f020c0103060605340b011517012705040c050a0605040e13081201090b01080a0213031b0b16051e0316020f0301020a0305100503071208071a 74
    0x5401200c103270200f04241d401e442c1c040e9805801036054038418410b40002410400c440440560001c603107080c8041d078043c0f9041c000340300c0e0400c110160050b14007980c3c202c56100040080b00324400b0306201c00d8480e41420321000d4034204100702d031040c0520810f00000e03612078100b180c0f802042e048030000302000001b081503090504007101c4000c1c1c1ca015a81c090f81004001160490190040d13a042f030b4007030185c1c1181d40c0d940c003500d00304001c034450048413050024083c03c82941c0d6500e40e483d02821480c1000200154080001003401c04082c2107884602e1040146210300d0340e138042150700741d98108030302e907250102c44809a201d4000c551310144600d5004658074035203907076840810440790300500403107140c414510700c40341c003400064a4000786944100003c010700d0014000190040740020301c5190814a54008203003664000b803c0b040010780d4400c00c201d0b010300c03004a07400242009074000c00089040251407035401c00d00001c040c00c050804505070040040c443c040d003100c194000c070000494 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645621097 1250 645619847 645619853
    0x60f0f0403030605220e1516110d1d01110a14030d0f0e0709020406020706140d090503070212011e0f0e0a140607030c1407050c0402130f0b0a080601050d09050a 70
    0x100900703611003c8950400c900c0c402070001c005002d00c1f05460070301090380940c0325159050502d0440021000520106542071241d40c1d00621400b000010b01340c50b0050310094259108c0c1e41da9883c28499414882000303049811003000044c039005075076001b20802c048144c0030712001d186018122a03141c0090030441c6003081040ea43c0c0160594240c480215500592541914000d07805240600700046c0d0141c0010000c0d140305020602101c2040740005141440c1c1ea0860815610110415510707580005000c4085080c00c0c101c401d160100c06008000301800c00301c91001201050710b41c105502c3d1610986d03800c20308950b00141c2108a15400c66a1003080d61518880405451480901c10f018090010b1000b1b8024090701141c4070b415607541049442e04030040b851600038110130344040c440c100148000340c4503840200701020080c00c801e40941d04c0d00b10290b65104035900040c2c907500d401c0c010001c4081d000345ca00e40c1c01042c2400c0c04d035250540d0003d003000801100300086c100d031042d01601018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645622347 1250 645621097 645621139
    0xc0a120302070f060516050a29013f020a17060a0605010210150509010909050d02030307020d080c0c250b090d0311100f0f0c0c020102070302040e0102160c0512060f0f0403030605 78
    0x1c00880c0c5000c0d016030303840704504e8229060144074801c8c4652200210400c64040300502ea0b03807410320b0bd00e0785a034402c3c0e40200c0c21f400d00f03070f0300304a008100301902d0a00e0440100800e96001d2090340b4103208203410000001c4d224840f1525401046072284031940c0000c0a030000e05001d41005091a6020740e03560003002c0c090651403100365201d000746c0d0b1046450a2005c0308680c0f0548864004100000780010300302d48461004044142c008000d000220202c00f0510805022903074080078410038424590252000c0219680b00c403e04010403c170280640d01c0f02001300d104290182040c48421484110702810b1107181c003500b0400034030340320103030100c3d010f00c2c2d202ea000280c08210410451001d0342c0b05503a5071341d024201901503070000b9400c200619054226040c0f0240c1c2c2e03030003d414010010045503052640c403c040f04c0409641c0400e104504052208840300801d1000406950510100355000d407000a44622204810000020705042c0a40c200c0c0c00205006017080c0c6601c602241e00d002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645623597 1250 645622347 645622403
    0x90203030d0605150f0703261303180311090c090d0803100e0103210504050a030503030a0e03040b07060c090f1e06020f1b030c0a120302070f060516050a 67
    0x21103403102510080000045400340d030117100082618038504220394400350340402d81d82a070401d125044400506880a0340190f0038010125a400766140c038416240c040c05008100401d402c03064540a02040446c910703103004410068152054445910b600c1c1901500f8400e04007101c0c0c0100640d0010002c01010400541c07241400841318582c1039103078040a40420070070310015240e00900307141d50000f4441008001d03071000646c1401860716580c1c2010074030307c4460b075105554a82020007040a280b80d2805a0001d004200016610b030908000040502d03024900000d4a110b94554070a101d9901400d0324201a00b0041c0649004503640c001014090884107081c10121810240024419000044502c0b6542c00310015040240d081a9540000d210b25500b13998507201d1a000c1c90a9603ca05040b10090444a000c284400c041c0e820081d24101c1554450240502d403e241040800d5101040d603861099a802e10540030340e82d07041480c03400d216408081c00001380394103030355044105090304003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645624847 1250 645623597 645623599
    0x50f0106060f0e0406052815020f0c06160f03050d1503152f070b011203020708120904111b010213062303040f050105090313050f0a0b0c01090203030d0605 68
    0x200c8254480f0188000d0307986520034143c004c05154681a01d030206110394a07076040a00b6071b610070550341c03003190501500030b424103140544c002c400260300408052118005e06030054407040d207040442c0150b80760003c2c45c04400381107101c0e0700be070803030805103e50704440e031444400700144001c03050394542250b5003079a440211040902600c03031341c011000030f004061444404104501c902c151060701301c00508c00c40e24a460b00d507201000381d5000241102c40d07450180501d0403081310107001500c1e0182c83c140040c0c0001d071466003d150300d0b542000051007240c08507002968045001c154820048895014604545545003207140014060a10541c00307003149604001240380e907a030b6540c02c02d031841403c00d00300a1111981e6081d212404001500454000d0300c689980400381c6040e0b2903a6003114004d68004125070400900100003840c00c00344400a084112170a131000c0a58000003800c600c0284a0031814032800b046080b05d0800a510815031b480d006030580e559450f100c60244000c0c46540915 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645626097 1250 645624847 645624857
    0x1050712051905090703020612150603040803040201140d1b090b0f03010b0a020c091e0f0702060a050a2c061627090207050309030708060709050d050f0106060f 70
    0x3014118806001d001c1c018103030041c02e5410b2559881400000e007400038a4081107105124000005844400c0103000c0d0119150b6450303036900340041e00001d042c5849101a105a00600502020420300c400b00c0760000d509080407403c0801c108416012409121105001c413031800000081000206071b440420b5805641c85038402c3d602c030096110300380140d458654105800340f0042c054641080b001f4801207526004841c01b1641402c00140c854008413548030140001d01040b4000030652180241c020400960a40f8030703140a50000395260002002c8070100354851f0080303a5403c10079032040404080c6107244c00968000c084000001c0480c40d05031001622803d40000c20312101900c0103100400190303103c40c0300d00c1d1f00c1c500000c05980f06804100140035007000001d29915180b00a0403007504c910051074403003441ca4105030901a4a521901081e0403070020000030507401005c500c00e07030300c04480c130040c1c2000a080c4603203402207065010390650303c0e145011407120b40160140601021603611 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645627347 1250 645626097 645626117
    0xa090629040501060e12010e0111040f0902030f0c1b03030112050c0a08030f0a17070c02010f0c150207030309020405041a01080a0b0403050f07020312180108060a0621020309010507 79
    0x207110485409103c0c1c440020040000d880462070310a003544000b65100001042481d5001145401c41c1d21001c014440c80d04e0000e010494004044503580003002c06490850461030155001c00c0c40103c0107020f0084141c0014803083d20782a4101e0008070b560301c10088070344035a1680c1c900c10b448a04118145c885210b80c42c0c1000461500c2081c03034096510400145040c01c454000300c94081e00301c24201010300c0340f080203944100d000c190100e840350700c3e070781d8621020500c0d9000161003403580704140420410030f0061080070400c0c100c0040c00e04401030310f0069480d410340c202140108000c100096009040400744000d210010075070700c98056108036104581d90b40c1d00c0240d0b9a4011130a0014040c450000002d804280910f01a04c0b480b0b4000300c00728600101c40c0e0010782800c4402d240d00c5c10110000c1095809074966056400082d00c085c00c0c91718403410080001450110035205140030041c03181c0405e80681c180c00c0203c00d8041e0381040654590078180d220a029040031200040040d0507903003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645628597 1250 645627347 645627349
    0x7080402151c020a110d0e0a0e191d0109081b030a0c2d060b03060f040b0708070e090406050108060709030206120406180506070305060d110906011803110306090718050a090629 77
    0x81d82c0c010204034000220400010ac004030182c0448410f11110a440c0341c0e030000b00c0142030103100f0341c851141402d5959250005941313140d01d044036420300c07040e600503c00403072640d400c02c2c2000d03561078000d40041e8a44103002200b20080c039070320114810030801c6001c04410404690001d0b401b041c4101c05441d0695103413810400c52160869010742840749540c0440e041500510895400c2040351412602c4003111310f001c5241c605040c1c0d01159001d603290010050b035001072282981100702c80ca0101c10707961650700041c1050180b4803403203490096070004642000380382c5d8001d07450480d01d00c0000c1c40e202414103200d5110320044400c0e102080c14000090100e1525844241c503081d40042401d550040d03060074000ca0340002002141401556541008100e406060020045218441003007002038a8000c0c1800c08002425855180d4000c0c40705101440c0602d2424102401d408000203da5803040700345c3c006006400e5000e00424601810079481415040465511240301e1031350a0f2030000d050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645629847 1250 645628597 645628619
    0x8010f0b010c121805060c16060e01050403240504080c060606070b040f03110f101407080408030703090c1d070e100e1807080402151c020a110d0e0a 65
    0x20500070904600110414200da000c0d001c00d9a030114900341c40c00b2403170b071500e002c0f407040d521000c04241c00340d1002001c038694401e2498040080d0040c0e1412000d2824902c0018006025600004110100c13081140c2d0404030071907580d42d04c082e00400240117a04050821000d00d0f44202c508500714014100080c103181050307011500316590007208a5a5580c40d03440ea40c450b0084494200e08226640c0c14400032500204040840903020310050000182a04c030000d00321070348020408140741160041110868204035016403180d04070ba00143d5a5450a600b2001040d056000402c224055030b004510700d600320030000c1e95042c15072003004013521041d00c181c420049201d00c16038403243d013001c3d03e84210300c100046616444c024120110350103000c91401c0d6820b0049807580000f0300b200c410002545840d030001c14681c042590001d182c045450802c0345c0e1131a21480c0d2205d2660000750004003d1301c92451000c107810207000741c0f511000741a10007060410008400c904c01c0001d40c10200300041c0741c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645631097 1250 645629847 645629867
    0x10219121d01120e031201090605040605040501140603100308030c03190b10110106120b0f071407120903050d020105060301060611100c09050904030e040f020306030d20010608010f0b01 81
    0x5071110100c10a820f01c1003809070004040c0d0103a10301050020007218400240c125019241c0e100c40441c01e64240024802180c0072039200301d2056040100400074131581d46960142818196809039496031002c2621105a1180c1d000400e4a0303000010040709401140242d03006d0750078180c0f00d58a08c0f00040d004400d45114441281e40841e03104000410107000d10028009003d2003000480c542e5550008080d40f40328698090707c41c1cbe48290104016900c0c1202c0042d40045541400849130281c2c44040006000b1a140101050b0f0b024002203485d900881c2e0090040d070b800405c8999489140d00001c0c040c3c60280c400e140039600b0a0404134269004d4000300b607040c00070038002d004100540b0204000380c589040c0c3d1100740f1030020f00100d107a8851001c00744c420fa019031900b070065200c0380140b00407200085a000087c9105209101071a40c02050040e458400d85c501008480c1c904204a0703118001c9620f4884258a03000e000140c0301070640182600100348181049946a000019913450910b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645632347 1250 645631097 645631099
    0x7080601090213051f08180a08091009030f06020903011d0c1927061d0f130803360c010206060d0c0b0f120403030f0e0a050606040b010219121d 63
    0x28171100038a50034490102d007644190b081020800070300b2244a45424600341e10b00580d5000c0300010903801d1760070065a01040f030440ca14050342d54616603110018075052082d40141815000074030110301d96001d410424240411200091000f051409040c1d5100302000340b10f800f6014400180499148099820f4101c1d2100850b611003d8445980b04119603071740f0042240c01d5560385c401140c10300c0c200c0d1200040510361522500c0d5410280d0380850702d400014511a11560149001c0b0300044501c800e4a420803000d050060304954000848420394051610048007000c2d00054540320f07590010707070005035001c282c0a842042c1c440c8014041c00b5140d2020103000c00f21181e900300180031000e0002d18406100e080a0781c24040302c400003080d0780798203a4080d80041e4a0f4204000c0403000c91003144540307075240008000d9220b565507807540303c5500070070a910865580c2564a1540d0081c40218903005d405400801d00e0036852902d44640e40c400078414000071103c41a0304002809001c1d00b00d05954 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645633597 1250 645632347 645632389
    0x10509040e120c010501030b010b0304050c0103020c031e0319230403050705011a0406091b0503130506010f140612011511030a020604031412180708060109021305 71
    0x20020280005000c09949030035051203510591584603031810050509881400004511949035040c0b00d0503030601a049400038600800c184800070310b00180d1240c0072a82820050f844080852030182503003e5000031142c02011400c1c0350582c110340e034000314400d106c44492840708443c11919603049a007101f00c0000310100000c0d5100d060820304250690062291600b141f40040c2c9a840e0343c01d56004404a0440f0b00e0001e007050031501c0c01c1e000e0100902070b200410060441c030381c112030403480800843c0a0034400000085400400110350061080f6040b0084491030350f03507008450b41d600a1032042a4040c04140056034142c64100704540d040c2038851210b10081c2d0903ca0121501c050079142d04c0c2c24000c8c0c2103003c216202062000c1c08451429401910061510b420040c0401800d0402c07650411410000000074410b400c041640244a46808550100706001c50514140d030f190011080c900ca06000080c40c83d42c03a030000d12240d440c4044402c0d62030340e65010312a101a2014040711070103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645634847 1250 645633597 645633607
    0xc0903170904021b0105012306030f0702162405031014060912011b0201020406021b19032003010b0901030f150c052d0306120114011716050105 63
    0x1164000503003201c0030014801850880e688841e003080b02000240d0f642240d45440040202258101115060003036481a400b2040c0800c1c000949921009114650707100c411000700d00403a200b00801101c0201c0f200f4891081912049000170990600300c2e903221803008420040d80d598810015240100d4000743c103c43c40c47d04002c1d44441c403001750001d0b05c1d0481028451101d5a0780c41c01142d40c13580e910003000041d0b00b411844200c0c0008003200081c015a0f004002c20061140d000451529100034002e03151090941000000c00314112203032035000034148010040140404010400508003158241e070401c2e03080c404c20b060030b03104805401e9078042d080d40c00400200311000412011144942049002807841030314080c1210110005400040c0002c01c3c04180c0d802d078840c00c00d10901034175604a107468810307141034981d032000518690240f4541580f840303000e8003d421144100a1043e082c07025580c507548410401e0000c1d4540513164400c4901c00d807450802a480c0300207a54040e5112481c3c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645636097 1250 645634847 645634883
    0x4180f1112300a0c05010f110a080a2c03040503010501030503091c0201080403050f0c06040302010e3f070c063b1512010b1207110a02011404150207090c0903 69
    0x1c4c04000709079200d5498001030050020300c0c0c400c003803210840320303c03107901e03130710001d500900f00e0400a11000c1c100d80b405400040205c01c47d00315a401001c2018032401001c641400c103400c50156030700c501d400d90b08000010040000110280070041015110000122082c40c0b040d44a01040c1c84040c2c00b0070340482c0410007081c45580100f90094241800b1803501c00e041c444036140c80d40840302540140d565240c50822040c080c4400006180941e10aa00c0e900f0130701604d04004802c1070200d02c180841c1e001c000040003c40e0f00383c0b000d190f04580e01b080c54658031907024024660f800e02740801d010f03a1206840f00c1c200d03c031422080b101141d401c840c500c000c21b081400303503102a500c0401d98408052140d600a1403501080c01c0c00380007414141c5031079017101035407050505070240130b100900c1181d10040100b03500000e0b2440680c1c1c2c0920b003114030040310300c3e00820284159041580b52661f003506103544203800050300d008403803101004019034140240221800340701ca0200808000c2a81b0303184183c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645637347 1250 645636097 645636107
    0x151505030c0412030e0102011a0913020d020a24090320041104120c08070501020d03090c0302040908070521070609060e03041206050604180f1112300a 66
    0x407280401055900d019110b240403000152085002c60003c0c101d19501c20302541d0a01070180d441c00c1da600002000100140092900003004005940703a04035507800b80255640e8120100842e82c020b0711280c921a201c3c10050500308051840310481c81200312f00c080c602c0d20481402c0b0489400c5115a40241000c4100418a1151800081d40262508620b0b203c541203000100300418158031039494040f51450b0485502c0825070101c141508060800c200307903600400c8000c1c0c8018a4940044d42d0700e0145460204011650030182d0440d141042c0c110804c00e0308002003108602030802c98800d41014101c0810301501421850040c110600049002420075080300c03012074410540801c07180104400f15245070401e500c4610042140d00003042884880c0c41038603045601510f0500c00711080c070342c51072682075082c9002001d8200c0784031604280020003051070704240c001403c1e68580b40c0c00f00f26039541e034520604802803140072801c007000b00b4101c5040e0201c00210820800d130401440700c4090310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645638597 1250 645637347 645637351
    0x20d060513302304060e0a080a0f1b090507050319050403020714030a1406190204030b0f09030702040912090e010e04030804031206060507030e030c010e060a1b0f020415150503 77
    0x260066583d4036141e1000c0001e4060300181050745d0340c25195640d04020030600010796440f1140e0b9402442c02d0324003007000d0f0407000b9402078210420045a2080c0350b080d102607141f0754800e00b0320f140b03040d081c010007540c07080040d8082c8170000409425080c0346000705044500a40b40200980d1081d07804100391031241502404c03c403401010703552041c01c0f030b0715447e026101148207050365410041c20484441c034049008130b030303e1703010035021030400b401d5540e6003555120142070381502c1c05900b000600000780800889011301d5019109000c9904286840150340383d40101c08000301b4100c0c44042800c3c9480035001d8104c0f5101c0051856503100ca840c00d40b840d40024100741c1c00c01410142184144015020301002405035070f03502651a0030b40e00340244001204240c2511135080182c0c0d5040a81e40118039103100401210403c1e41d801e0000d070103895403506442400c1400400100c92010700c101b207d2a905014000d440c00c1c0f001c80c3c48803079401010070542c01080a84180c4031000986144101e000e15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645639847 1250 645638597 645638627
    0x608060429030c2806020610140616111f0909050408090a140118080d112806061d04060213030c12030e0108011203050304020d06051330 60
    0x50f040480c0e410100d2000001c80301c0008410032000c90a2109404a251010041046101600c41410320744440c0c2d40e44542445145144040070480c900c041d1345101c206d81008040d481005440c40079894442d6150008521080c4224500303520f042155880fa1180c60407180140c0d541d042c41410b00300c80c10000c000160080c1c0c1c0042c814401610551240d00f4041d000e421b000410f61003208126000402964503040700361441c41910108210420000901e9400082c903418034000c03641e440a03e2502d0010711a02c41082128510a0325021000e5240140003031406008184440d42e1075804a0400304003400a444076203e0500c0010081070b55075001d05088110300c012200c00c65500d449049a039100f6410020074201035150102c100342c3c00030a10441c0e240c003820005102d42c541401c2c2c20306030161100c0501403000001c0040c4c11503031805c000303984150340581d04000c2c07410b2568200c80c120080c1d181c00c0703886410412080d4024a03e4580000d00e803c80c1500304444440081c03c2180c1020002e80300b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 645641097 1250 645639847 645639853
    0x1b021b0a0e0c040b040e3c0403030e030a0e041802010f0810030209041208131101050a11190b0703020333090f060307060e0904060c0225060806042903 66
    0x860601c2c1c0d0313000140010207404401c490282054101501249440e0255070340c1103d00c50342c0c5e4070140c1c2c0f0803d444188080082d005012a035658241900030701341e012134000c02400005040884035170004280420460309440410914464604121074901c0d82c803800381c0171a8180404030b182d144140c030364684c0020341070030b012251562035020070104c0e14180e174100c403210960030503000381c03951248040390b04c48400d0441c800741c1165070303c0d00c1c10740303c03039100c1a11f040001c00102d90207518016404400740c101003400301d800d00050a4100d55009201a104803426826403010880f400d10030f0007034078000c007101e41080d41440e24051100310588005601a0442008006008240d907141d0340e21a10070000014488410300e4154101410b00e040d0740c0004051200500034120745494091803580d0050784080d0000d0651041042039180062030082401170781d106420017242055943d0118003100c071203480e500119243c2504004c20344445e04044828881c51300c0070140c4140480740d88001c031060103000d03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 645642347 1250 645641097 645641099
    0x6030408070b040c09050609100302040209030c0d0c06081e0127020304061a030d02060408130806010803041d01060c0303051009110306030717031902101b021b0a0e0c04 74
    0x42c0340d42c0250300315000e9a584098200401c45a9200d01803a54058400c032034142e41071600320007200c81842507000103401150b0100320144580c4041001d5040242d0060020740e404007986060703002d150440c000c1c00001130401c40030400460751100e0b151090030002200004507824107040103280c0b00751000ca941411581c800c0546501d203584004c5001d130380540d10100c1d601c0b28035034125803c1e0b610301e000f40f4082e40c806032420f54256404140190056072100c2099552800011903220ba80300e40d421020150141d04000981480000028002c5443c1904514a07104003407d180c1c80034a0300340300742c0340429001d84080002a110754400350388074600d000030f6940140c0f150311080c212459400109000c2c5000009d2240381d02e4104009001488501d0b280021030002c5400b00ea02e9002c0e2102d84e00803488000c071402ca42c02d009110720705145003a1001007045e84000c1c4407400308085c20b183c0560140c002c1400240d106015121200802500030300034510b400d00c0c100c2c030710701103041c02030400c0c110f2801800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 645643597 1250 645642347 645642353
    0x1a030a0f02040602010903090b0a020316140303250e060304260a050909060f0a03020d0503040b070809012d050c0109020a0617101511010b040905010606020c0904110603040807 77
    0x1c05800035200340da000142d1903080785030291100985400400c040d040c1400200078041d800421600c0a541c02700100258120310304c2c1c4840140c1e40c3c09007044280c00044204100380c413080e2039417000320b03041c0240101e000881d900255441e102e4000100d402c00d10800006001c01c801c041e2183c1260341c540401c84c1ca41801500c0b0310b0302500071500020020b400080e442c0d18500d00f4105850308070004859850b03039078041000151100c141440000d006004801003541840002d00c1940e00030808241e0f21540c0320921303d02400950f014581e4580450200407000c902c04040c207060041d03e42c1e400e40141d000d008034000030790303040d0442d041040b01903403502c08440058541019000007401141c4030101c030489110f40248070399100809403540703848141e50402400b40505110b035107001460818141d030102c40f8418901401a2100484e085030a000e001810864154030403801c86803550f0030b40707503028800d0b800c01015480030740300074010b850510300684503031500d40000c5070464803507042180381c0311481e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 645644847 1250 645643597 645643601
    0x11b0b070e030709110d090c0308031005120619020c0c030307230604110603100306150603060b0f180d14160501050f27040e010504060b0a1a030a0f 65
    0x12444400250900d80c1d54107181400c114040150041a20030701480300c0f07001441c00c55010b5120100c13070964880007104140074140c00080d000e1600400300d1a80c0e8038062080351030701001c0e031040c0c5000d400c800600300c0c641303040030803490f000341401c1001c1c01103d2051800d040117500032520303424840c01001c007510f0700c50783c0800c020550303580b05219070315040d03c01120032009682454085000c42e0410000c000000d0001e41d070001d1480000c440b107540302c0d19606a01002140950030081800d45090003d00b00e02c101810345e030048403410784c3e0500ca138503117504074682c1c20f00802d840381146035024092414044e15040f0008034120003d80601c60504164454a2160301803243d05061600b05052811401d00d0f03a409040151600b803c03c80e00e0038071076030038042540c40f540d0b00ba0818000e0407000c1d814045000c1107403c1c4d101d000107000b0711850410140090003080251011910189401c21940c51030810f00c2520b801c540d440341d1411040030001c580d44029500040c1945025076803003402c1201c3d07007030178 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 645646097 1250 645644847 645644851
    0x140c030312060906011724150c0d0906090504050402030c090c18011701060f0c051221060a030f03020a0b0414060f150609010315270515011b0b 63
    0x30905082081c20b18109004050700003400c400e041204001000100a641005594100c0440600880542440d00391086070703540043c241948410b102408000e400361400c05404e00c8001582501e2189251400c142c1d41d016061081601090010408200c2841c295104603401800642920091140d810000321400700481e001640d00c500030500b01c9049220a8500600910a091042c038503981c110003100100014400c40041152044490003e0380c481d8a88a409503442001c80307581c00c2c8000320107021904100442d0303e120342d1406141c0d80c1061040c441502459000c0c0c410741d1000d0564861241030002a81e058042d4403500008c04001a2500c0c2018459030082c0e55071504141c103101c0302802c108015003c5800025440e061100b8480c10340300b000e44201045880c159109d6400d00140c1c007402c1100d1401500c100030000004006180700713510326949050072009104c00d00a40e414a00311074041e25500080b074080e401d61803035540039004044180104204003812110b456507944035910b41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 645647347 1250 645646097 645646117
    0x190f060e0703021e030405060414010e0a05010f0c0305011203080c041707051003021201060f0e04110405090108121c1d010e0d0507110d06140106050301050f040c0c140c0303 76
    0x200044d800034150940d20741d24201610311328502c0c034504103504c8450f595003000d040500025811190300c1c15195096201941c0c20801e002955440007040c100107000342041044203240d0b40c01c1080b00c0d40c001d84a403282c68180d896421000450100d1501e0480d0440802451600050b0007000041510451014800c032055441d4008082250808080c0310104901243d90414903006210303010589441c450450706488982c03504414207103240c081203404004039810950000d00d4107003001c1c0c0d0542218001c00c00c0d00d005450084180c0da81e100c82d1542c3d0244801104000903050219105060402240f45221b11803160003080c0441c0301c0c0d81c0c0e42801c110f01000642143c0d5500c140c00c6103124280881020320049043c00b90404859071501c0d01e42d50a0414414400c00400c040702c002c000295010000030500d4601da2000b560f102c5038054102d0f4801c0c09454441c10048124000503d0507000d503541f00480c0d59140e610b0469556907200e8403980f50004550303140075012440b406e81d10304002a01e11415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 645648597 1250 645647347 645647351
    0x30c0417010b1c0f0f020307170a111005030f10030c08100609020310170307050102040e0106081320030a0b09010903080907030b1f1509031505190f060e0703 69
    0x9a80b508100c2c2c01d0581255002551242d102000c000c940d82500d503044a0384c0040002c2c180c044107200180c180760f0140c01881c501d45900b0220410402e0019042d03101c0d910519020081d03000740c904205020064a014000040003000080c07140404801204d40000030a105451001c4e1a903031158291031081d00003c1c05a8055014811182d089014440080c100c03402c0c01c61640c1400b81c4002403a0500d4000c5100b030880300d01903808690000c00231030301c6d1141c104008540b2640c440d03802e0b14a541c0203104100001c0c85040101e007501c20000036100751251702c070314504c40d2100450000c0c02d8192034040300360782c5400380b03441d000d02198051314501c0c071400c080000003c1c0c105c491300e809010904013400c0001c16502010040c4009014031101c60341100741d00b00c0c1001040141d440344072820007180c2024070142d601c3d08404808607040b5040c00240e030b1144004c00394241c1da80407090101d0743c00300c98030685d5504072034040b03444003100c7d8031500d07a1041682c3e002c5a56900c40e00f11000e070000955080c0f00203a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 645649847 1250 645648597 645648611
    0x6030f04030201150614070c091802030d020d0804020d050c0d0605011503060f060c0c0f060504050f06090906090a02071403040602070807080c04020906160f05010c0c17030c041701 79
    0x1550a1154030f03449400220700c07025117424020001e0120b84e075800301c0b14044c10001802428007000350040002840c0b00e10043c0450003c41c4100541c192000b681203000388550103441c0c09007030010071045181a9580d941c2281f0303540715000c11104222080d02a9150300070304030500d1076a00c44002945440b409120b0100e115454200084070425820140400301450554240141500c810392541124840e01d022141c48450381420b4650460941c04001c0a50803000f00142440c2c04ca009401101c8007254401000e00b00c01c401c0c0062032254003149a84454840c0000e5040d02d00000500d4200800401c010300b4156244d443c2c560384600c40802d20210b600c0424100322180c0c2c10840180907000c6440034014080c9080f102a076541070305042d01d4812130300414030081d103440b103406039903010401c2d003d000d5040c0308505142c0110840c070007069801d5420407542c41079450243d051000d19070b602407207090740e6031405000200590405842007001281c20013000502e8100c084a400707000010500000d800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 645651097 1250 645649847 645649853
    0x303020c0f072102060d1d0a0b07021603151a031e1e0d030203070e09041b0b0a0e010c05010f060e010e1501090605090a1e03050c06070f021c0206030f04 67
    0x1d2803108098160f0750040041c018010b845420945086050003400801c1ea0400f0324005818010280c44010300703441030080c7d0700700b8094030134003040c0140c2c030503000d480100514210700c6c0382c58440350002810011005c0300314440181d0551000c030302045500c006046200e816000030f42002a00901c0300080c542151003080000806d1050002441302504030100d24250394506035200ca0070b400d0410140359000c80010300281c002c402030440c03404010302c4882a480e203446d213050410560510703102c0d02626900085940d80c0200d007142c003c0e1a05413180b240e007454030ba004580524801074115102e54035042c2803004065280100c2d00504010313581c440300c035814942d401c40e00301c50051004000c42143c000440069170080c80c500180c0e1114902180c0d17441c800c1d00407940000255000fa84401c001102c41c002521030054100c0949104505075241c5080400411880d4000d000c00513141c040103000c100b00500d403003031a11903046414414551403100b20b40004038280c004640b001c040b126414104010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 645652347 1250 645651097 645651119
    0xf060c0a0501060b180108070504091103010801050723091c0f0201020f210703050c06010602031c090c05060c07080607020307020a0509072f1902040e0d08040f0303020c0f07 76
    0x82d020001d426410076500e05c401c00d00c0840ca54060506010b212808140b0700c074820030443e0701078800c40f4000d0090f4000b00054044030360007407045100035480c20020580092040300300c10f03029504441400c219142980d1034003001d0303222051059004001c0d5140040e00000801ca522003280a50014800c2040d1400007a09080c0f00030503802440d0402040703c2c40641502d0545c00e4880030b51452036403228210f01d01030710701e0301c0b5a0799080d00c0341c401c140001510a034004024000300303c050300b6060100d01440000e500740e541c030007402840c8083e800014003071810310201802c4580088411990210303a03c070020380c20040d007542c0b10401038000140f80b60035030400b212843c0060100766000d445500d00b120005003100c0c84801100f4001a40507801d12f01300f94140071210303010300c9034001e030384038207005c0300c1c3ea254400e040300c8040703008a04003002440c401801040c0b40c0b81c15501505c40e401280e5032591041a85510100d040b000d241c1c5c2402005410034080101d6071414803030b08000c000450501d070000310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 645653597 1250 645652347 645652349
    0x30e010e1206011d10151b050a0302120418020a03020f0408030306150301080316110406080709050702160911160b1920033d09290f060c0a050106 64
    0x95040e010314184660352289000c28006c90750800c2c80c0a88403c0a203204550040350400402c0b51ba80402096000307003c004180d0341c0c0b4040c800d40850f070032100202c0e04060319009502c00c0c02d0740320011850048100c0e84503002000481d074640760041c40c0c03610b991000151070f0056040040c4507800030040043d40d04100090742169200c030800141558500345003940c2d42e00c1084000141d080001e0300d107500f0801081d181c400c1c40030004001344900e5807603030034040daa4800c174400c0d9650641004041440a800803401141401006c44200401814079a00c1c1c00945060048090f03d83c00c108500320820201c10aa603500c0c2c0c0c0304030713004a80303800e04400c14404c1d64201b21164503071902d00b640c000c0861002841454049204105070394880e9540000c0c41230300590722103500305440324003409002107251050342c0c05144880f299618015a1100c1246048402401d002004c4103007041581c0481c01c0d902e5420000b58000800f0009070450f80d20100359075401c504021001c6078403140400082140c2806400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 645654847 1250 645653597 645653639
    0x50f03040b18150d0b120106080d0305060a15080405070b0a03050106030e01060b0405120a080c0a0b010905091e03161202010c05091f02070902070807030e0607020a03030e010e120601 80
    0x8181450220b008641c07442010452100d8507034881710000c0645440c0091002d080948000300a000d0366901c4203a00c59a003145407600091415000843c81d1511848000a40f100b040340d403040303a503000ca820740e1460000340041d9443c1c0710700310f0002911458000103124421199801060b1549413140140a40e058100001c00c0d0340d062500a05c80031a4401c00d07a004c5620444140300804520f002550604511000146c5900c1c1c0024080466190002e03600554510910005500c0ea81c0c4601d0b40f4110303182a10701c50030755048860344da02001c1d00304008111240101c81600c1c03a101c0b40c08114483c00d00c00c40b1084848912400094021135020f104040d07003165107050440c900146003001a4140d41049040095041c040000816280c420018140a0200d0300c40440d0360700c03d03034105140b60740c112003411000108800040325007424810207a07841180c7c023a0007200c03a80d080d594166414490300c40f91604200f440174020245964000b1002840e00d001409041382d941403450512031a054210f80c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 645656097 1250 645654847 645654859
    0x130509150106081510030605030601090533010302130806071e0512012309040b0f0604020a050702040b1c23010507050d05072d0915020c010804050f03040b18 69
    0x41d0300260031814144c016000c540c05c1c40b84002c00c0e2010381c0101011b0308410341520589002094003402c5900c040d0080d44540301e4001c1da03031455a40008001114070310100d0321181a0340c043c42d107500036000343c18080919013a000001d41c480404914102d42100c1c29400030786100c0310902d480500c501c0804c00d40e100d61420341d280000c1d0820700011030806124a030075100055412088030381400d101c485210a00803e103e4003414a810004010401034898800004040001c100a45043d20031611030904a45a03581401226020000200703504502203401c005900101c1606202c070580280c0c0c6180f0940406444c00c141f118148004003c1c840030380e203140e00d0481440240780d007003000d0301c0b8030303900c07030000170a940c1c0c0c1d009000c03036041d0452048942400c500c40100c56690b08400a030b0f241e4030b0415030350102066a91841c20b1020020074000101582020013484600e51040c4082e560190046044954481040740300d54515480380d0302408800001044510f80301c100000c4414603480d003201c203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 645657347 1250 645656097 645656101
    0x312050a0902011d15071a0108070305011109010e0f040b03030a02030a0201060e0709150909151707030305030c180907091e0509010b091c05010507090506070c031113050915010608 79
    0x40f43c000c05c1201842116280701054102c200050a2404841c6400d40e055098042d40c2d42e4842e10340d52011400304594a5003080314146111a4100c15560034400582d80d03500344070f0000c0140141003400c049095000b07a210160500305440400040668100650081d66a0f0710078182c02821a240c0d900b20a43c01c1c2800310500114580c0088910305031410807140a603010929042a00c41410071ba0180000034100f080c1d0010111288460704125aa42d100c00c6200e4000c8082040c0c4510040c040100460000d001213115418090054405400ca030120810544031300070000321000d400300c42030b10014440c1d0340306000789260b0300b117030890f43d5811465000501c1d0901c0000b690b00481409410300b49200400c02a410383e4882c2c05040228000100c2e0040350a800e00302213028080885d07002021481001c400200340c1400d000310340001d500669440d840508580c2ca0b003840c070440340d0140c0d0740b184c10700d6010744449155100c0c050003070500f1001803604103400d4030340041c00d4905070b1228003400100f1003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 645658597 1250 645657347 645657349
    0x161707080a02150d09120f020d08011a0c1002070c06020a0317280504050f0703020f06070f02120106080607260702030c0f0705120c0a0603090312050a0902011d 70
    0x40c6004880c2c0e04032034a003035842c078050b80079481e070299281e100c2415042c400c0010a200b003403d0380d46020741d001d589031030368294486401e990ba09008040c40e0000b0b10302500421a0100e0640300365200003502d02c88910b01406e0418080c0307408101242c01000603800030b6501c0402034110003420044c4014000343c5010f54440e200540840030240c1c981c2c994030b05090024032400000b010311910401d184111a10b081744050009005250882d0b040700c1c540718580f445200da000002d0884106ca50003069001d06048e008241700750398221200c00c441081729180c5103001030350b8124500041240d400300019095145c01d410900d401e90281004081c0010f100700103074810403610003050048400d40b07820300c2e43c0d269010102e00e1440740304010409806221005200c422000c64500126035040b00c8404240002035078107034849421201a960045a0400410141e07004c1e42103440098000d007806240c3e2400b145880703040d00c808440003140340307540b0302d000d00c111f40c2c029201910f000c1c9141d40b00308007115414 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 645659847 1250 645658597 645658603
    0x309020109061b0f05030a09060305060f130609020301081f0204060512060d02030303070f030e06011512090501060902070303051b090d081605061603090c0911070516170708 76
    0x101441c02040900f410018510000342c42050310a40c1c0006440f200d000a4140f4540300d0b008102540d001544042c0b0003c1c82901c240201401240000c201d4220084241c080168039423400c59681001074540c500021440701a101850003010070b8400703854100008007407113803050007042004058601c144000e00c08543c5c80b1055a0703070003081c0c4c0d01c800b0181d1a1040018020910104000d40c980b10000410048540c4100c04800043d410703203050115503100c071940740e100e41003400f800412518000e44100704a00c03801c040d0491410003d0006074080740b03912400d00351045500301c0107200341c00140c1c500c10550306124203a804521600c3e80602d1003540d1688003003522900540511591a1148420a21680327000319903620001003d4803d034400321b480c0c03c90b140c0400300c4411008100344d0700c144850034002e0003884204c69100404890351401e1510b00c1004029200d081d0b40700c1c01d41400386400150040200340138603581c10b0504243c0d03c0c03429001e96254901071100c4051604000410003142e0000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 645661097 1250 645659847 645659849
    0x102060109020c07050f04020d061403010c0504050f0409031103030403200a050a030e060f040e061c082205040e0105060f0d050303010e060d020907030c021216020f041112160309020109 81
    0x3c1713800c0c1d5a601c4040c00047c0181c0690350080c0b241c60710740200002e24011132101144103610a030300074030149140d038a003505d5500880c4503894200d009910b85446610302030b4081d19107070340b0904005180d010f1116480d803568100701c41c200d022403148030400421074a054003400c40d041c180d0000303040e108255a1901d0300c0300d1000300024280301e05640041702666404054417240010541120b131520368403165880c41c00810349003c2d001d080c0c140c0f0007000700401c03858603042e901e401212240c82c010108000c3e650040d901d0084461a1600716000b082c00c2d0740e14061003030000340320000840c1e581070040170071401e203010b20001c42c803441e01c50b40084001000801a00e044542c00300e60007003543e48031001306a61880c3c01200a521000302d5042010302a095404061841a59821201c101188120541481c459954000301c030b80e02c0408030400500d804442034000d804040d01c003055403401c401007829a41c00c0a0408410119000108028140d40c2103042154120921f0103010010464002034094401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 645662347 1250 645661097 645661099
    0x80105072d0c11060a05040e06010503061f03091505040303050711070303120b1f08060d0c0e040201020109050313031412035109061309021c05060103020102060109020c0705 76
    0x7010b07901e801030000910f0b2031900c0900150809a03105a48a8002c081d03a006000c0c01200c1c19100d004141d803548114140d9100b034101034500c0c0c111a8441c2084510007031155000304c10181c403121108001078440082d291042c40500d80490350f03081600c0c2c09410303030b507005040760304100c070900002009100000b100c000300c2c1d425040c02c001c0c007503d8100b8840039160b038142d10f642044810401010100c0240300d400001c0c00c80e99511015500e54000700424030391608030113170984007005c00c10b21070400c003513032215081841400006684816580c400382550401d00c1e100203400110300d0100280035140c51a581c85805110107842c0c22010800055083d00000c0c05418030074040441d9030303041201c0c4031004080114004e2400074854880c800090085401100700e10180038600c0310f21400f810140d8005005000c0101400b030715504403240c5d030000303007000c3e00c050783c1c0704000341a0355003004c0464189912060054002c0c204030b41c1140000383c0b8004069002403800f9104102e40e260302000403980741b0690f14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 645663597 1250 645662347 645662357
    0x50708071d0603010f080f0f070504020904180503090a0503060402061206010507061103011a070b04080d09020915010f0809060106050706110307081906060c1713080105072d 76
    0x765200c00d0110510032440e9900054000008985400c2c403598132021102031038225990400400c00c1035071654030701044126103074032405090016140036000f4201200c4050f000040b80d10759000303070802c5404050b105550710781001540c2c031050308241c0020000380009400509903400d01d940800d840340b0810345a05020b0310a0000b04145a02c0344085440594010206000540c00980b5011b200d50013071142c02c0c0601d605800d82180d80da1700700141d03144980c0000240b9140d40d02c0c0e485078040e0368418140c01048031744d141d5610380160b0340c408000b4002c2104c01002031040c0b45810000d440c1100307400c11a0140030f02001005105100050b18a055404520304280c42d00c000d1302c1e065003d000014066405414040100108194000e0510744030789130030780701103450800c56001d000448505000d4800041c04840d9040041004250f8080d5070006040a1924000f11140308040d0500160130601785651540c051080160788590030380341860b80c00303c4aa81c2440c1c0001c0104155907041803142c1486 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 645664847 1250 645663597 645663617
    0x15150e011e090b18041401470414090c0402030c0703051812010902011425020f1503040b010b090d021e041806050a1505010c0c0810091505070807 64
    0x51294410709210004142c540b44c9641040e2900a500c10307400a1541c1c065071034120b18058040030303e4442c0e4210701e180606c00c807005d03610a20710901140408210b07060002e039440b80d800252558031031040c0442d44110178400c64200010114206441e124403144205e00501c14003c84041c1d11084816030703681030130103980d500301c803842814040650000041c0d000d0045910303800305d200c0640000d00114401d980700d1440042c142c100300141c0c01441c2d44206140442e04010313142100c00700e41011740034001085c00044220b0b2900141a18120100c00100d070340c4080280010401c5c0d034466980504100101d00781040305c010b0103da0b54019040303000e071141c010200c0d182d060745c441e58044d070007031f10014109102000075000b069441d4034044104803102460080000d001180300e1240c05a02a142c200c40c0600a01e08070045441103690a001e8500300714032600080c0c80c100c104440c001c0045240b401088242440c244018500e9000041d00300f05818901000034242d44410400c4c0d1110705414074928503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 645666097 1250 645664847 645664849
    0x60118240b1303060911030d110717071205070812090907030f020c07091a040b09072001020c013206150706020708131d040f15150e011e090b 62
    0x3411039a40068025854042e024003403040c0c006d01583c007000194111070403100c61800071600e000000041c40340742d800c020424880920141e1503e0104d100340d400301c0b8000d42d1940b503144c4403415866011035465101c81020040a030041c401fa6030001e051002d0f990401d0554008100b44a0000f400b9104056480800c2e030804401d5034141e650b404005001c440c0c070151501e00d04c500901440040c8070040320b02c0503042011b460540070740c068201c3c001e49960060f40f01c00c80300350b800c1015400d80004281d540440421125004d04c06000c202003224000300b400c1d1380000049003141007100b000b0101030340d504c0c260003490071582c1d6100d1f004041540d02070642828144440c00601400740002c3c2003500002d00700003407080c00b00c040c102e660814840c4801941c0d494081d119003150031510908070303045060010300400e85070a1005103140c042c90001140300030948540e801c40e88101182c1e101c0000c3d00b1001e00000403a0000503014111060003404070715000c010f501800c03069807141841040d1907900e0300e901 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 645667347 1250 645666097 645666127
    0x206060a03080d05061f03060305160b040306180812040b070504081c0201060f090603021e030604080c070509010e0406050a05010803071e1217100308030720060118240b 74
    0x40c620640b202001081c42400010302420b040d100c01d42cac051040d0700340342c501107510b07214900460300c510445c14542480c503030725000a41105214000040003c0da2000003040b5180300400d2510604c200249203842d161800210720000600780d0020003c0a000070b00c001400011002c1c00200c10500c808840100d0400c2280503103819001000901000400028a207506401c40420303603100310b580c16002e2460342c482c00b050300414411103500d540303c44003050215423a10002c204509051003030b9024692100b02061481c2820703448840d41e0124402000140140c0e841224ac0020030007506106a515099483c5c0c3d0709d004458026001d840f1099414503004006040d440341a0741c030142c2c45054034117000024008003464240320507061040c40018541d4405070400c0c4055036400300b24242151109601100c284030040c0c100040d1428103925030009681c2000098020403086900a0300c03004146c00050070340304440c0c0d00304100c0c2c0c4003220b4102c00640c0307800f0100a58201c0e48505444001d200c1e0308560b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 645668597 1250 645667347 645667369
    0x20f060d0b040605030c03061306062c07020c090601050d020c010606030b12030702060d020304051603050c210601061412131403030411040b03070b190206060a03080d0506 75
    0x2500940019500403a5415508a1030000d181240c0c1008030550f19401d064941351000242581600042c0009080c1c0640c20040ca0402d40190703c00079159451f82c002010648d01d040c1d078280c2d0f10b000c44581c02040401030800540c40340b6544090002c01005101140020402425a5040c0700780800c02401c0d00000750b05a4107190110802880140da54100140061441800182c0100d4151050002c2e5080010031160721b0355010340450310781142284c81e10025007010300111080e00644002c039950000440310000510301a101420640d5210400c020200304802d05100ea60791440c003100034000d5007c905241100c0041c01c02d40460503205008040c0c074800c42c400308091004407410300c0040d03141100300010f42031080502e040c440050300c50b001c0e981d0004441c02840006400c0c6894424142031b00400b6802e44080c0848032007948462400011313030050307a104100c825016658600041d410409150451001c0e40c09105090447d2201407003481a03646100364161540c001c0b0306541c5420400c54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 645669847 1250 645668597 645668599
    0x18060c15012310090b09010c02040c020c01120b03060a0f0b030a030210050f060607060c230310051804110f0604060503090c04230a0621050d03022104020f 68
    0x640305686501c40728544030909405402c0b0079502c400702c07000300d0070030000001a541c0c0b00d884810340c131480c00c60002c40717a500403c1114100300c2d200c3c41e90030068440d07002c0c0c45000c0d5030325000340c2148803610000500f84185140103c0b1042d04050300004980c030301146454011000300400701c5d00000542c902c1c03014011182040d0340500c22009800c06241e408100c00c10500007514090003ea2141e1902c00900030041d0f070700684c486010810030000a8080d403240c58024214203004060110404079850030b50940c02c1c0d4000c0c0c0340300000802080e40880c9003002d0141c0811204440c2000c50080c008490202c0100001c14942e0302089a8605036913040100500c00401010b0310360301c0b40c945c0707801021a0010b4501c0603807072051500d80c8009103001d004c1c0703407126a850aa102c1140c030b49030b0034070740d0a4900540380030f903000d17500c130400300b146440300aa200b00300e0865607203a240014140b600b07514100b95400084105032061054032254a5074030b2942d07201d50340080d4181c1050700c660000540b1825100089 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 645671097 1250 645669847 645669883
    0x904030203090108090c241e1c0c0e0d0c0e101d22050304050402180102100c0e2b03050c06090d1e02010e0d0815090c0703050a0912030207090c030218060c 68
    0x138840a40c42000a012449c01c100e4101045103003504014282c03000c400003074011503001d003400581410242c00b000301043c00382c07911800c0d090769050300c10b80c07000c1c00303031405450000c1d02002886801c0000c40030800881c1041c580e440c05242002200002c0c3c03039400714503210702c901c40030640203000e070030015680a070100034801c5590342c001c09160000d500d40c1700c1d170075400350085e00c0060042e14800e104000c000d44090700c0782c05c0100c00050810a070350440030031126401070040c4030350700989c1300210202c0d080d6200c2e440b00c40d610201200c55a1519100a044c40001d42c000402c0e022415408140000109008450051510307100201a40584020700010800c0d10900801420f403e5204c11054054a80d42c42c4280da103001e14014462404000c55051801090030004040024410001058103070040d01d072000740207443d0521000084004c007001c0e0016808080c003403000080506c1002c02c200340324141145400500880451145110100c0b01d100301e0010502c44c1d0458001d0000c00c4412400d4203007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 645672347 1250 645671097 645671137
    0x301261e03030106140306090114011b0c030201021213091505031603020a090b0102031603020c030a060915060510080a0605061b060f07080f13020904030203090108090c24 75
    0x105030740e6a0400d00c0303032100241c5411000c0745010614000c8a02134800035003150381c039a09040001c54440c0c000d13001141007090b0000c00062842d09100d00c850340da441940402c2255103940002454040d107036060340744602c2c4c1080304460b0540e981c034500003110b001c2038000c02c0a641c1c4041e070b039080e10002d5100c241c141c0601068001c0b81960404e090083ea84201c0e440500c1c3da0300c1c0e41a241c02c40d0601c10790503025a004114004031803a1940700411454824411600d90144403004241003101d44801100c400b0780b00c8003c1400c220f0b10700c040707a418074448141048035610b1b22000942201e104034a0109000b411404600c903002b194100381301420300500065039440508900d0809044005400c4000e8010000401c070894040c680d4203000303041d180d1b00c10869407550401c2d030680340805007100d03c0c400146148000180c8401c0351043c072860107a00039540b11100e440014100900080c48080f441d0080300c8050b040755a060141d0038104415401030300c49100c001c10702d600d00d11522480c440c054060002e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 645673597 1250 645672347 645672403
    0x11180a020d060803040f0308091f1d04050f040b1015020c0f040605060915071b050f0f10030c020a08040b03100b0f0a05070510061712030126 62
    0x7007445100302401040842d40d035865450300d0303028070302038240d07034400c9034900304041000d01c030261109403c024504012100e1100612442c940302c000030f0130114a441500641905866a0002b91103505807000d01443c42c02074544854108000c00080c00d00c800c080100b607201188401501c040e001c10541036010fa141c001010f5a00d2030400003040c030504003d581c6000b14100f40c080c10046440c0940118240000e8000300903803100c1d0800d080ea5014818421000845e4800a0081d003c102d415440d030480c1e410103041c044401c642c0c01c03246026040444140406031500e1450340303410502c80c40c001030f0404400004038100240544007600580c0007280114290352580c00960054840008030307070741141d49034140c296a00072001080d603c09001c0c04071000243c007440052102d50b00c00d40a4845080402074900300715121a00250301203080110b4410601c181003040f4044e580702034031654111740c07408040c0807074100280450000605134980c0c01e440c0c01420008060541e01640081c0030720300d0b01c22 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 645674847 1250 645673597 645673601
    0x4022d040503012a05070f080d0f050702060f070513030f050f06220b0a11031005040b041a0f03030c030c010b190b09040522060603170309060411180a 66
    0x802264465440d0100660001300300e038801180310004254030300394000060701e0a840540001c00d095648012000354a800230b40060000c010602018070001000002c048081d421100c006001700203540c008070500080346241540c00703501c64964980140e80b1041c4412081090041d540028010110b00c201d0004100700400c099072160404001c41d40aa601e07442490030300910340180340c14040070b8200100c04614100c4a19a20000512011030a402ca051281c01c080e40304031143e0000c2103500005107c64034084c0078840004a04031000c0c48003030b2080381ca03207954520200c0317400c2c4940c40500c04400291402d0054078a01d91820094a8642d08046180d80c06815041c0b40c0c03c0c03141081c220051810704000d00d450043c0ca1080b42c1c00c170f04022440080c4801404064070140760400391110f10600111002d29609070f90f481400d001c1b07210b03451890030000d000354a07844921901c1c024030802054034400141e1b2544260050380441001d5800c4d0b01045214035102000f10603881a04100701440c1c40c65 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 645676097 1250 645674847 645674849
    0x1b060a05150f0904060f1d062e0e04050c1507050601051905061c0504140d0503130318051c03080604110a05070609080706060305060a0e033703050f01080307020a0504022d04 76
    0x4404040c130400e01d18222a40c00700c00c0042c0389c00c801c1c6600509104146644800a40c454400c00880380500004030010380300303180c0c3c2200005000f10004034801004024402c6038018070095600482100b5030780c114100c200030038060203002d900085001f0303d1300d0886c607191100f0340a050504000380c0c24039042401d5082c0e402850380e001441401c0e0800041132080d000c60740b181203154042c18091480e039030200c4040709401c0780b040003180450070116241d41c0d4409481c20300c5101c0c044a601081a52401506a410041c003482c0315924040b20340045a240008840030b5201b246040d030340d10b8034680340850080440c1c800180171101c02042140c1001803645c800300649000d007084441c16522103c810041d610602d140106503041440120031408004d264440d4001d13400300460009130342501c0146041c1000c0c0c400034002901c0da03041c00300703c107402c14545004d400c441d0065441c3c001d039038020411000561203410301503540050003c015500403d01641100466411241148600203980400b5002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 645677347 1250 645676097 645676111
    0x6020307170c070807060b010c1403031014180613020c010227010903020f180c09010f0c05030a0c0819020d030506040606141b060a05150f0904060f1d06 67
    0x2401c021840074071919050740c4120364012811460010986d840c00d0150404c7c6400505122088000c1800540c1d1544604030f4611020000c64882c40d05210130b0003017440551108088403456070300e003500f40e1102c4c071442c10500240244003095486006c041030301d45880c00c41101e9000c2c0702003000f4400704410b400405d080606d07450804144552a103000b125070512070002e6012658206003040142051070031680101d1009040c0f40c9104552800d242050804492090500200203440c0742c5540e00249520713205c0c0070624010040c440d103591030940d41d20072480d40905021480580c8030403c0107070801c40700d03030b440d60b550b0a01004912010203940d9600e46010130380402e003418005a8a400c080c400d000c201c4556565010940d510074414041c6036000ca010488400b82e0818090f082d60700410140c1d001d2680f0b41e80000e000e28140d07101d0b903061520751808600c1498645104000c030383c0d03454052a045a0801800580340c2c0082540000502c07403070081040391207103a03581c8030811402040852080003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 645678597 1250 645677347 645677387
    0x5030303090102040f0f050f040509120d05010914100605091f03020c01050601031e0203090c0405130b070f0509011b02100504030c1a040b0c0a0f0f03020d0306081f0906020307 77
    0x2481721042e0b1b203051091301465800c040d0701c2140c103110b441c15800440e00f25402070b00f03842c1000411442118142d102e28461901756031120f004100c082d0041c8508050700381303c80d001690f64144502c0d480b00301003031881003504015011541c002681c0c0ca1038205005802ca0b07c0c80d030001881c54402c007070003a4114001c3e80030a9440c04c0b0014031036500038060304084c6510600a41040204540e0071b00c02900041c140b29030318461011007006079101e42c81428040d1269815103e50141d0718900011240c100030300050401c080003902c02c2c40540c010b400c1d40c03c800000d0034840c0700c11000241208400c070410303c001e940841c0360100c19000c1d503089001802603c0c02420451511900d4142240301c0044031055000c205908004c01c000a402c0c4402800e0540c06c10b105450340030480d92034207061000340300800da811100c8580343c1001c00d501040140d1503818142410b0011030328002d501c07a220301d89088050304100780d2900034603101d02654080804960304c000c0454484c02d0080009012801c60030441c04811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 645679847 1250 645678597 645678599
    0x60a211b03060f051002100f090507150504031e050d05191412040c090608100e0d0f080a020705060f04061805071206020f0304120807030905121305030303090102040f 73
    0x1e100b07000d000c00f0b564031800404241d41c42c0a080c05540c0c03492441030401c501030080d50714a1881c85014003185044032490104001500e03062482c1000810380c050580060354860b1b4003402a08172041d17400b03c3c1d401403103080401414a0119205440c6a01c0041041c02100c1008268903006001b500920540c060300c1d0880d40305201c030903191000e00c00c0d40d2102c02d8006010800700b0849000305241c1c8144a4445a60030701c5d034a00c81d0f00c0580c2c01039005155130390441450880000400d101b1502c041c04070600404055072410405071a49184007c52820001e580d000607032010582d0301101d05050b44507089442601e0520350280440d801030314111b940c0742c00d01e504010181150003079000684c1d0040d000d0301181e403400340b00c1000030303000e10001c4440b25024030181047d0285070020354810b03405101a08806075200000074044c45004083c041811703d0b01221720007041001031241a101c400e011066a200e0300174101030900c5603158083ea615202c00410845411019000303003003210130007031f03e0032242d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 645681097 1250 645679847 645679901
    0x40b1501090b19020316050705030c0103050f0a0906180b0f0705120f151002061f0f0909110d0c06020708010c0f030f091707020901081209060a21 64
    0x829510848036860ba0520103282c0300d8180540c0341000101c0c43c012a803030000803106602a003580d0a6058401e40c0144104004c00e080a00013111422000d00c5c0420003464050307442c4030103a102914070381d9081e0351401a43c0800c0080e500c8524003000980741110103010528240608520071103a05207014001000716a01d5402001512400c4102d6880900340b9961b44850101307219000380b500300315000c0680000c02c107840b60203014240103600d5018068074070341011404078100d01c031803590007000c045403c01c00401079403041010a59002e40701c041313000c0d03100e404c100001100d10f0b05102d90000044121030108010308005070119a0660260340699640d0002c1a0880f0846405c1201158421400405e000c0c481d52080007020701c3e840d000194050f054540d08003040ca082441e0426182c0003d07070304207500c0c001c11154010960b1400814107840013640c00c0045005009859005078004541920424001c0384800200c01c0e0b0300c011307511000410f1012402802d81038a145600314031a100c00c42d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 645682347 1250 645681097 645681107
    0x5070918090224071205090405040b1501111209180108010605030f150f040203030c0f160b030405030f0c03280314090c091506030a02040503060115090b030a0212040b1501 75
    0x1140c0e101805190502c0050b44805174044007600064003001010403006100ba44c0d144201c03400360b07020b88800d40700e62801845064201081c0030034a03050003c80015a40a680c0004810500406200d10f081e105d0300f0500100700030044681d107145503002094004902c1960543c809422504102c041322006424118150344030110440a149448bd101c000907843e0740d003105000c0c0d00b142c40a03080341c0c41e112410a4540c01c250741c0c0130a17500180c110b242d450340488401006100982550a070b013600d142003994406907a4840c039035040c0b80301000405c132490070791400e0040e203500701c510a8040c1c000c11000d00402c0600402c83d1403a00c0420702c3d141c020103084000990480c4180d000d44010180c0b20411400c01c413074040d0040c80700c03000e05d40d0040c5c403080588610003e58000d0141900141e141c1d424001010b0030041d050b005441c80e6465024680d6400c2c1c0e004031414100c40058803500e64a482d9036030100080d00c6107a516600c0c400c125828041003029030192944103245018603440080302107001150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 645683453 1106 645682347 645682399
    0x31303080105180109090807020603010f0f120201170406020c010e0a14010e06040305070317070c060b0f060a0e0d1e1122050709180902 60
    0x4205604410600d0160000b240d085070320044840a06051950511034040165110f154460a00610f0401c9400c040c0d00600000e540750384510306c1c00c28904040c400d0842e43d00c8100800034411130b507204800320320380d0305039203008810b200f10b04100403040003c0c00030749066a08102004001c8070900c00c0c030f08900101e8026001c1e40e4402e0412035100b1600310010f055a9040564003294040301181c0117502540c1804c2c0951100745a04040340d0192411595080c100c2d00c460030301c90503030f030001d000a00d2140304150502c00403c42e503090000039100f182c421174010409010035100b207030065a6400c03003003030050603023172000c080e40d1241c162103a0050450800d0610b501000c03024042c4030382c180c40c0800020f440c5041090000c6070b1072440c6610031204641e070b2603904c50109949034400c0ca102d60042100083c1000c4014402c260a0b00611420101300d102d0844007800c5a8150070354541c0f55 = true := by decide +kernel

theorem cover : BRFrame.Cov 645503597 645683453 := by
  have h0 := BRFrame.cov_init 645503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 645503597 ≤ n) (h2 : n < 645683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
