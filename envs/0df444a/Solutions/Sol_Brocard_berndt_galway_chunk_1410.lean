-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:51:06.841711+00:00
-- url     : https://prove2.me/submissions/ad8196af-1821-4ce4-a1f1-462d9b65ca7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253417266 ≤ n < 253597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253418516 1250 253417266 253417271
    0x1506050f16020d05010f2306060415140406080a050a0207050a030f0e2d0109080c09060103020904050702070f15021902031c0c06050109060e061009050a1206050703 72
    0x20040810415445003614007202801c59111801c115107692200160f00761380038000f40010341c14104914014844020210182c02800501590840030350501500800d0083d0240d0301c1c050600500e240e540f00310710013a00801038501c060a08007600c081c042d1002c1e024594502002d0301b8003460000541d03070b000d440c010640344100a4140010f10000d07562100540c541004544030100e44010781d62030281080d090340200301c0c0140280d08048811007406064100b5420040c40c803440d500441d541d1a06e405106215407200c5145001e40c03601c0030b2034039406041450003600c0c0480041c0402c003070312802d039002c10150b0b014503028000364040003224006021000181158070550f640700941e0b03003001c406a0446104070300e8020302952000d0003000c900307403403207501600000c0c5000340041c50f0381107403007042d00c00c18900b01c004a04004c0c1402450300700c0c0c240c2403c281c21511850100440200140d00d00c8051243d80d140018183d110440d2000007064200b00f01200f5000a0034580c0c151140100005c0400d41f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253419766 1250 253418516 253418527
    0x90204150306120b060a052205010b030f01091a0402390d030203040c0e010f0e09030313080307120608010c0306050607020108070c060e100f0b040506100f0909090303150605 76
    0x103c008601c0c403000c0e00008400500e440303007004556a0f02c11900601d400c1200c0c88004100d0400100804000c144031a20401c00c903a40c82081d51000c0c002078502040e14076140707004001c046096085440d4850680c0d0300036031420300c2803002608a03032001030323075405020740c031840c4001084480034603004100c903a10284c08c50203840e841994031802101148428143e01101180a10030300c500300c0400303400e02d616500000c0d611110050b45000043c0f0039024480100d00010f00848000300a43e802503404490f044407240c40c0c2e6446811581004051200300310190b003a2009480030b034001c0c00e00034692040000341000031024000c060755a40c0c0c01042c0501000c00a40700181d070700c02c151681c0b084d00c525086c1030004151070700c01c0180c1007130402801c440c42039103244c0c00c081a0940c41200400b92110040000704091000e103c10340d1021500f60350b00c01c400103007010340c0a020340d112941d00300107842c0c540500ea40711a088401c40e80d2038407042d00001c0c1c2d551507010244803003002c403074041c18031400c1c0350f0b0609 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253421016 1250 253419766 253419779
    0x80723040b0c010e030703020a050706180603050c0d0501060e2403070822050102030f01050d03090303080613090c05090f0f0604020d06031a0a0501060903020f060307090807090204150306 82
    0x91045124041ca080c10020781610315010a51060180700510130540b59a40c605e070400030760b44c10302c7e610203071070f0350258440005102c3e004043c6000c0006110079060b134140d140c242d0541c0100b00042c407241d08140100407001001071140714030f50291181351600311106c0c0c0500d040c403900c8650803003500741d5448100795644a01e0071000580e5405003042c41d20240306d6440200d801d401d4020000c5905070501e0440c810010018190041c0d4810310581c004111240c0e0303100e0400005203040800940490050a0700707201091145501641c1f0500142c24050310b1003150920004032144854281d0311a01a00400d02080c500088110b41005148144000074100309840300038010015006502c10307a80020001d01001c0c2d540c210701c000307540042c4405c001e01044200601000c030122210040c0343d150800204205001c2e600300c0054a0700a054000c08545820034844298409001007051011814002601d20b0301000301c1c40241104680158440346411030030322001c4012102001414100740301030024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253422266 1250 253421016 253421087
    0x1d0313050d02010e0303030a05190908030a0c110f010b09070314010e0a0908040801050402040606030c0f080603010207060203010308070b13030e01051b0105091501080c010e090c12070807 82
    0x399102120801082941440103807400352452000742d40500001c004c1200b103000c240d010074412103001c01d10038076904520211204440150f80000c00306038042c03001c1801c01550b640504000c800c40c2c2001620301260b0309010f844e00001c0d2000403490780d15a81d010103541000300d070480d004550341c1028400307800e00028110b02d04c1014000d0700c010b0b1b00c0240000707107043c00781d42014014a400c0008140e5664039841c040c0e0191504a03000da0085d41421000200130384244074a02540c00c1e00d641d506030080c2000021103090360040e003460741c199000c0c00000d0200b045480103500030361181d00c03001c0d41c1e20039500d410504010020b0030364150314500c402c0c1c030b0046134002c0c140c40c0007088246084d5a0b210103507820207030844402d5000d1a4150300c0c2108101048000040c1510b0768000043c010040740c0e0b0f2078000c0c3c0d40e9802d0580c032050001e150700c40b0000c694103142000302d400003c03101109080c000c44596140c0c110340101c40d10400903001900f40a0100e030003403062600c510301280600324175086001e10030003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253423516 1250 253422266 253422269
    0xf07061112042607062f030c071b081f0b0904080a0c0605090c01030608030c07050d140a0809090f06090f0721020301060f0f0c020409061409011d0313 66
    0x24003140c10f034649810200c200e6405014010200c15880700000c0c104000240206884031004520783d240640405055000a005142500c85024659510325466100c0380d00410b03002c403400f942070300b8104842003140c0311940140c41340f2002843c66030791207240c0f4070450341000004403170316103031104e25012074580b00c41d00c542c41900300101d40d60301c4505241c00c644d10f50103d600680042e01d05020720420610201d43e410440354242c1e003d1104a88480e042070304ca110780c0c5a52001075010f0201003049060400011a5450044108020120118000c2c03418034403030480032600000e0026000d40c3c24981492560340010728402042900d03e0600049425918040d02e0000103080303c2c1e0020711500c0c4a0f000400b1101e100c4c0311103c2041d4094044070010350000c0c081c04002c140e2040135030004502c90710700c0c3d018503400c0e0b60310f203041e81e10303107800740001401c2540c2d080c0d681988075880e40c528518100340d854014000103000040c591540b91a41c075004c0c4000000c81c000381c004020040142c241c05442d00c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253424766 1250 253423516 253423523
    0x10501050613060302090d060c03090624050913051203010501021501060512190e0f100905030301030f111f020c040204122325060207030c0b0a090b0f0706111204 71
    0x594a511600014008980d0341c0c0b001004141031a05160024ad0b240d040154980d10540701031220080c05160400d541e0300b50b030820b4208404041c400c0000d45044100c03607401501c44040018a0707295a00c58504203448960b040c0f407407400000040181d540c2c100604800d0084080c9042c07402e505051004010b44294a00e0501e02010103010480c0c20100400c0c0311644a988002000452040700f0100d8603400e440401c2c08440c09003a58450170001c1c00e029600400d40d000e400b8514582c01d517980c6c54003058581c03c081d42c1c0e5249150103280705848030f55100d5590405014101d40c1502104002481c1c166018410b13401a80140301c00c025200104e151180d10035405010004070514803810302500a03c011405880d80c0b0400d000790000b4001c40300d050b5034180400d8121100c950701c901042c0ea41c0d070071605c0010241980d00300c0802115540f400540550380305440c0006625035203803551082c41d007194481008034500092030008102140c49281d03c8410b041d09141d08003140780519503c281c20003840038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253426016 1250 253424766 253424771
    0x5010507050705030d0c060b06030103020325050411031911090d03020a1704080d0924020c030706020601080c030105040c06030507090306140103030f02011503260403140105010506130603 82
    0x8010040180002c00c050700c4007404640501044080c000c141805d036034030584540d0b00c1c10841d141c05090090031207060701d802070001c1480f24404840414100703c80d012360801d4580301ca4000c610b13655130f8000c480c40582d41d070010301d4803402c1010052a004105044010f0003616007003001d03096820010aa860303000f004c640c003a81700720319400c0070790600ea00448010042e01d181881400350380800d401500a070b540b801d0407039144210b0b054044d984000d081c01001e4103040c0c4410702101c1d13100700c1204004030a080d0b20507142e60040c0704010a01e0411550841405070b00f114006110301032081100c03c82082040b00240402d080c1601e6038001280c0e2801000109a107920008410302d001c2c0000c48000c582c808810402101d0034480ca0500401c00c0c0001c80004480407030307200105205018840f990003200410381070103461a0349802d0702000c21002d02c0548001c0d0074507000c0c045422400383c00118083c0c00d01c80500660401500e0031204142c000728890b907400c3c000b801500d140555030106032411800d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253427266 1250 253426016 253426027
    0xa03090b090a09020310031b06050d0b04180b18012c0f0a080d0b090106080609150303070308160c24060506210c160609061404050706080a0501030804050105 69
    0x45244120340760403052590340000706004100702d06c05480c44c11a40161100b2000e003551a01e0003400c00301c2803240c480028003d0242507038003103041c0c0c403084401c107006000103040e140c82c0c10813500ae107814103400c0c0d4021030b9400030404402442d6404c00401031401d4020410310510b43c61040c00c000d00c13045079044400c040c416a1340002400c020b65003130287d1610803030314010b0f49071400700c0c40c0380d0040750a42d03c1142032000c0c0102a050495040d416581d081e12661810782e5200240700380100c0082030310358035580000d55075200d920244002d1401702d000e070742d50070400d191401c18807402c1030b81c0740700ca041006520b90484001c6849034084035100c0200141180c0040f2640d26594081d01032500802e510620001c0e4603c0c8c0d00c1c0d00004041042400d2800c1d111380c03690741e100c0e07e1a40c4d000711b808800502c8811500500002c03056840001101d105d03000004a002001480310079200007100c00300c8079984160024001c41e600461400e5004003500313400d20680d0304640e505000d0740a10b01c12107040c000c01041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253428516 1250 253427266 253427269
    0x6030b040b1f020d091401030b280302030c0a0302062703030a050a0e24070c09060906080f01050702032b0c0e120307050a30050405120a03090b09 64
    0x844144074200820b500380751107407504401c409800121205003d40311344108422070f82d01540095080350030000055001c1d000d01401540034010b5100215802040851500c00926040010302000d20207620000951402d51041c10b14155513114581d1080c10110f100b0401170381c80d003044038820000303200800f0140c6404030510a40340803071300015030725000c0030842014059010002d440301840c5950345e4040011202c0901566680da55440c094202186440c810f080c2c0b80f501c01040b542d1311600c0072400155030303114203c0884006811003c0180c0c2c903441c1c1000b180c03e042020650300000100200114206450003030741c0c4c1e2180c4050b10031103032a0b484100404283d9070004e400c400300d0183c41030000c003202800090518001e07aa0852107000c0041203458103c2c000800d8960141c0c5c4100284407811441d100e044101d8038078440c01003e5822543c050001004101e070300c2544244075102c0319150b90401081180c58180203c0c015420780c403258226001c6944544420211610a104c00360349500210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253429766 1250 253428516 253428521
    0x50a14030d02040b070201031a03060c1804020c2b052d120603070b0702221107030c0308180a1424090d0503240301020d090605060a0f0f06030b04 64
    0x30700790300351203101160000700070b50184c1c01049401c3c401d90b8100000104500c200d250900481121500756002000140380c04132254000c140b0042c444d50325040a410710400581681e0100d401840950030200a00310b504000f04001e1440c000d00742951204c40e403100c1402000e60290703403442c02a0481c0c06803200802c820300078481298903044130545964513030b644c58102d0060015900c1134000d00c5100d80004901c12000255095603900401c948805850b15419040c0122507000540c8060f50340d054080840442000801119200342c5441ba4258140d05000d4011080100345030035804014501980810010500d1511250b01ca00200301440e9040c90440c586440e81a10340704101441d01100c1c8010030801c4a0f510603040c1e1803c646c1c442e12154411034243c00b003910600312094040d07803014039136a650756445002c1c0c500500010b00f4800d0000660080c2c0707030040e0043d9001584e4005005060a00e181c50101402020320070b980f070307103241800490543c00507216890400d5500c107240c4805a40384d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253431016 1250 253429766 253429777
    0x90c0904121202040306021305031c080604060e090604051002030601120f060302060c03120c07030203030708090f060a0b0102010c020a0302191728080f16020f0d0801090b0a03050a1403 81
    0x90b0045403101d40300d00e05040290302615800ca8420360301d40b00064145800108180b02ca080320f51651401c0c1e203802419100040e01a11460b0700c02d40302d80012400c260711060082c805d41c1d020000300164242410300b141070144481000e03030918010000c104090760030a0191029540d00d00b80050801100c0784243e009210070380000758800c10025000501c0030000000d0b017185012525101c40740c0d155481041d80d14802c0c43d10003005a04107000240d01c0710301503080e83e40c0c0910f40200380c9043c5842013503d24200181107503900d100f10f6803a1b0798050f0301c2d6424402c21108905500041220340c0340ba41f0081d64441c16109200a25442d41d00f1607000c11080381041d102c4216191103140d16105081040001d007000036101c0303410314841c207245192152213503120724000c014080d0000d54681302c010300302d0007484003d200c0105510072036007803805c2840b04005c601d0a0800d56900d004081d418000fa0b50700343c540540c912072003007019003002d00103d00041040408950710484c0c03240e079484102d84260860065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253432266 1250 253431016 253431047
    0x100807170406152903010f09090302030f0c06180a0f0b070c02031002030a2406051b0a050f06010503030a080606090f0a0306140606030c030a0f061505040e090c090412 73
    0x40f4000100300c00660307120b07040c00c0c00c192440c0c600151080c240e004580824410f41c0804101a1410082c80420360300071602e0034001d10542740742c0b42603524450082c0d4084014480309500130020800014080c0000700c8040e0f20b800042e15082c101e81d1a0110481903100d009030115030702401080b02e16009038a100c3c08964041c044d40e07402000514a000250012a0303504121030901403200034440c400c3d9441040c0b81a4082410b40c03182c10182c08507466006131002c03c0d420a413210b0140c00c103000c20056510854803e8008140d510741a51600c1e05029040e0b01140c0264028000d210f1800d1b00812080e501850994040e603c54031580000f8001010740319400d42c12035100300011050000c03e40080d880081280701403451303500c42d0800d000d000d10085511582c005002c0c000300e880c0e5012a000003824840881c4042504d50300e4a803a44008820f414419010510010302000041a20383e445584003105401503c41c80299002040e01510010402406a1760b40e03041040b00c0c42c058078094004480d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253433516 1250 253432266 253432301
    0x1002010b0a03050601081608150a0f05011202101404032012070806090d1d12010507020109170301080607050a090f06030605010e0a060f030902030c120c100807170406 73
    0x55034140591120701c00c0c02242d09502604288807910300300d1480c0702003140c242d1401003030411541d010104141c3e82c05030ad50b001103078958428000e007a060b0700a490103072071912030441c4c20844c540304200c4e03a80c4d0144442024069004540101c00b0303440030a80e001c80760802800300c40500c044098104665482c0d070800da10418a40725840d0702c140008681c0d0aa40001044603019103640c000a61f44e1740010f603000740000d030840c44582801d00c6e5014541c505010161035024441e01c20f1441390f01350364080f20312000603959000000c090080b4a4426603100102c41e40c03052035541890882d40e03d0301c000402007018440001905903860740303e049076000810000302c84a0705981c80d060000c019001900c9402d000800040003a40d0501d03140b0f00704007c855558540c8081d84901e05000e4001d403500480503a41401180710001c3d045c0c40350140703000c056104030701821203c4400000c1048445a2121210800c821101000242070304441d054505010b085641c002d680e0f243d28000020b00180d0f45840d01084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253434766 1250 253433516 253433519
    0x5040f0f050a0506091005090c0a1e031e11160503070503030901060e0115080106031a0306040c0e01080303010b1606230405120f031b071e060c0c03020c1002010b0a 72
    0x2040e43c815030250300201c8103c0c581d03880d0744180c1940b541e182c0c01400c0d070050160001ca00d9411090300181009015401c000c12001d0340d41c107140d0042c000c10b010b10404643c40da0054120b20700720412125042d0320580e4100910b404a10703d500d41401144610348aa0380207412941c10301c0307020000d0700e0045a0120491390380389451310a05000e010288588518043c030b910011411a00300000114090165500c0300101d80c6000c2048015019140c1240c2406214401e42c0189440511080f8400c42c012020b402070b0600c2c0040d115108401644800c4058000340010710445015004907080301203c80080503910382581032410041030002d90a40c0d80710a507281240481c0e45803d4024400c0d070150044e01d0084144101501242c07050072030880c09000200001403540c501501000d80c80d8030580782c8030381040e00c2a1784000307440140303070082c01aa2141c180e104d400c0221038055000d00790210300c0d06240a04d0550740c040e540754018101d180c8520300003400529483d100358441d038626680203040e4507146 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253436016 1250 253434766 253434781
    0x20a140a020a0c140a0b09030a020f220b030f3409061202010e0a050a121b0806040c15094a09060c0412030504120602040513090b0105040f0f05 63
    0xc44615807840c5c000c0503c3c41c40003c5d81c0c0036a40076542c4c0300d000078010307210400c3c01350308000d0010031182e902688500b150300504682c02d42440042045518080005a120002c80800d454003250401700402d40c6e2003544500c00380d03003101a50240f040c05506400d0761096601c5c1d03806120600c250071405085103050000a10740aa108000a89074003e80310910605408414001080c016020700b82d000001380d202004440003054104003100d000d0440b0740c150003008100368003401070f82c0e800181c2560100092000b80640120508001d0401004024000401001c0a0711408903403149903c10b04240c002200040d01d0011608040300140c10342e5110f044082202544802440d02c2c400918920b0a0001c0c051070b00003e0030a0141c0c0b6403134411030500d45002d9020312400d41003041102003040c1030000084610709103440c0945680704060150300c4070b0420080c85400e0100a0542d00e00f44c2c2440151000b15030484100b40c1951170503075010401e40d1134008681d01514405074148051460b040402002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253437266 1250 253436016 253436039
    0x3011a0f073804081902010b0d03021f020403030f030c05070c09020406230d090f06390c120e031b090709150e0a08030a020f010b04020a140a020a0c 65
    0x48410441c0419078007419411000b8140b0080310014200030041080c030300301d0560789450889034880c910010030170a404501007002d401d110b1108030003592200306d02800c80c00400510f01c0d032651040e0811410980b5645004248003218481c0b213050642e00c070800c86c4514411802c960090b0740181240c10b50581d07408020000354494400e400c0020641c00c016181c02003041221004001d52003102410b000c0841c200100030b0460003804c0381e4828440424a0008819021790203041c000000101d8184007070808014404e8401d4190ba01001d01c500d0007582c413141c02606211070f4582080448090809110003038030300c2c0c03034584101030349403141d201c00c44880640603c031107944000c141d80b0680541c5880d401950f403914a8007980c14601d200d04c0095005601c6079070040c080c264000e03c001d0683d0380d00c00c0103600b150700000001005030400030f044949100c0134000c2141c0704074240c81c2140f400300d02c04801403007804c038041355848442c0009202c02100d8400c10204071100d400220850201d903517400160350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253438516 1250 253437266 253437323
    0x30f1b040b01081f05090a060302010f0512180102211005030d0503070804050c0604060c0501050f100504051f0609080105010f0506090f040f05151503011a0f07 70
    0x400000410444103050600518400981c1a15080441e86800840d413503895040c0e04a080118001c0800054540e43e01240c540030704008940003803200d0450000400000f41e040d00d860600804020f103840000c0000c500e10350160b030f88812030b99549011250035003e0304c101c003004c1c118100c2c030403542c1d00d0a803580482680034600c2d024080001d02c0d40c0e0800d058032802105098130118005000290100d8080c92031260310600c64010386da200d141c500c0000e144c5801c2600030340d0020f22401155001c200c0709126594000c000d542a00c1c00a207044070008804807240d004e40341c05070b5160004103a445001e0003284486843c1c5441d510f0704151500c600a00880c01c51080c460701d50b082c44c0c0001140e9490000704420b80c0d401408807031030101ca43c020700c0040403148a20a40140e0b86680801000c801407203524003401286250701e40c01c4075050208210400f5000c0c4032000c050040004224000c0d1010301c8003ca51204101d59813a0640d002c5480011300883e100a003400b202c00e00074421a080030344d1881c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253439766 1250 253438516 253438543
    0x2071502130815071e1e090e130203070506070302030d0c0c03080109020f0a0c081c15080303010e150d080c0106090f0207030e040f150e0912030709120f02030f 70
    0x100c101c070f1840302c0c41d0840300080d00c04e0000b05003c80b01c100400401002d04040c140b005060190034028901e0800c58000d01100c00304000403540001803025001904015800c2044c21408048802d003030b0b00041e841d25021312405100c0c5c5800222072007014002d00a031201c03002605820488407010004c00b0303000c8012800b0440c0040d11100011a84018034825a004032003024010f505242200c1c4090702c00e006a000151400c0f4000c0c098500940c00b0603821178455540c1050101c1c140035108010380c00358485810520b40c039001400140110888500629842100443c804c450702c80f020b000300700440b1800101030290304c4001241d641d0030038150002022107486d40d908010540c0340e20aa04128001c0860040000f5101859200710b803505030040b035034141d84070100165422141d0801c10701c0a45035800910207020078004c01c44200014002820407508180e8058610701d00070b0001071100b800c90207001281044801d19070144001d908503240d0090307019044501809050f4401a9a0240c1143c078a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253441016 1250 253439766 253439773
    0xa050f0a3506010303090b09040905010f0c020705030d02030d18020d0b04030e091e100803070f0c090902010816030207080f0304060c110709051305012a050319020715021308 76
    0x8004081c03000500c981220742541d66052401d00785a04501039600199407103074000d85580c02000400ca0a01c10f007800c0c120380ea0000121a400007002a0800325030b41e01c020310941001d03141003402600841218400da602080004e42d510001c8803c0c00100b0341210080c0d081102c0c101c50300100a40c44000900541c0240c940c11111b086540420807401b00c221811084020b050442c9171114542c4016141c105c1c20901003180500e440f501003e01d1a0001d44007900c103284e115200c0401d02240300800350140400c00020700424a4179000a80341e40405010204491041850702225038466419100000c1e031000c07140381d44002241d001c0207640c00c03d46054513030b64601106814800d028100808500c0704c1d5102900d0070901d4014068000c1200409030301c02c0b550307500303e0003001841c01c0c072442c82401c01000c6031040411031440c1100f286590481d0042c1030100c10000c3c810001120700c0c0303108a40c0712244000d65030302064503204072080111701103c1c0b5894000701e540704c503208025541d0310a441c10b0f032044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253442266 1250 253441016 253441109
    0x3040507151d06040f03020409032a03080a0e061f030803040c0311041422050f03040303020f01050603030f070503120901052d040b060307080601060201051605090a050f0a 75
    0x30451a4843e07486405e00d803440040041005043c0350704843d2809001e170920b40c2642c072200d15440e05903090380b00d035a00c800500032082e604168200c2070082c0c020442c41c608100e0a00b822400c1c60780c8100180256201c0301709203043d0084020f40d542c6240145500c085829104e04280c41d11078242c000da4002292072400600b407a48860030544540600078808481c804803d0302c40030b0807031459403180f518181d24410321006200110f8410080c440c009100d81e00219a01c91031428000d0900600070a05a16641400c0034820b440e80d00000340d0300c10040d404500381e0340710310174a800c40c0383d80b242c0d109401e4102c6500d41040402441981b049100c5c10036000309000410006984440c1402d0390142c90010712041c41c0801c001c551186034561f0310040240413501242d8403070386035a242c503a00f684501c0050307440700304202d82c4054002100f074104c019814540d00b04040080040c610b1080d5029503030080001b0f20110744560313a90b44200e0002e2810076610b401540700d01d0000d514902c28034414190380c2621800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253443516 1250 253442266 253442269
    0x102070c05031605011115011503050906100e27070303020d0c0317040c030b040804090b0f060d050c040f290712120b040218030c09010f06030203040507151d 69
    0x1500e00c01044248140c1011070708100040d03459454030310710181b042c4a40340d03551a5090b15020510702900500a012110034800b00000f02a90401010390388070703810410501104c141c1b40700540d001c2e0380544402c0880c60f9101711240001441d1162101550120b800d1035600001021441800340c902076403e4501d50717400140c0c1503943d04200300d03000300020301d01040b0114490b100034801382c1040c421049100745035070303944501c0c1c50000c0a8a0503944840c002404000001c13030b5210b00c1544007000c1d01d103078500c0e04600300011114010f00c100402c00c1d03a00c40e40041d04003040c04080303802800c1410072007201d45443d000306209200800031840925120305802d18088405481034030a2168440916045110f1f43c070804c96585450100341c40d00aa101c024000c4a0f640341d0001d05408600904407030f140321070b00340400d850f01a450010900401081c40148400c20000c80f208050707500c1400d0140c0d8903182c1d440d2851412400c3e900030b228645080145001d540e50040c8442d00c0080302c840ea042c081d0b0307030200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253444766 1250 253443516 253443523
    0x1e1e0405011b020d02090c0c0f01180206180306101809210201021612080f04050c04090302030c07030b0106141312021206070906030e0a0b0f1b0a020102070c0503 71
    0x160303a01280030441c4640c1c0032401e0500002e420b40c03018014100301000ca81c0458000b100648030755080400210300c0c906c41c0c560030002c1e07200c100701318070090104007a00c400e540504913404074042e0180c00e00003038014198040014124071124083c0071108180b803c0d040c0005540311a0261b940825408006030b0002d400718000c0030599a00801445031f40c1403a4401030a050b2813040c4107400707554091000c01c188034072560549007030500a41d00300d24031826000008050940040c1280003140801003880b0211b41c0c00280c0c4110143e003a0703000181c05c03a050400380e185000c2c9142c8070304035100704400032040100640d5401d040b6001e544400400000c0007007071040c0c030b0080180c200c00b03d00f01d0800070490540b0310f8038807c21250018014528440a040d0424241141221103001190700e4000411a59600d8411900580f044a028224441792556100d0f01060060314824505402d038010413480d03400025644440510810001d5860204160180c00303500408029a031040c00102c2c00034050a010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253446016 1250 253444766 253444769
    0x314060f0907090f030303090201110604200f091005030d02150c0306040f1503030e150405090a020f0301061e03050c0d0e010e0102120105041a061e1e1e04 68
    0x40161140416500c180301503520000c0c446020465102c3d40001e500c0c00030411180650302130303900800c0c4003102c0e00024001801c46440c410841e401207040102148101c22190038041002c11081c000441d00760019201c0032461610640c45082e11060080c40e00c81300e160001103400580c01e0300c81d2031080c0007099031502c404082599100e903130b200000307001c65118002117502000081001400034141062081101c009151506103003907801418014036411a04400380d514046078240304003201d100590985001d82c0c880c1c80c1c001c00086000c01c0d505543c0303130141d80c2c01d03400740411652290307541c880c02481d041240c82e40e905504103150340030381c000d07110b8041d562094801010307041c607003509071110400500e05003070b900216550350f43c514401160280010144003803504101b040f19410542080101d80c915200103030002e10420352029141c86000c1600d203a50b01000318030042c420190407400c586d01c00c050f01446111124804100c0300000354019200c1c843c011a55101031040e02200e0301014841d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253447266 1250 253446016 253446019
    0x6030203071e0c080f0d050907050f0613210c080d08010e1005030706020c0f0d020109051c060501060c0b0603060417071a0108010b011103040f0303030f0209090108030307031406 78
    0x14495071400d1040b040b103a02c0780b0800e00d4549100c00c01401e4813139108a41042d6030005500f00c0018481c001e5501d07500489801c07402010140104518207030020304050500e078100d80c042c40e000300388503040380c0802030300e40000e0143c00d014940c9090320311807401040c100e000c400c071203155280c000404e034400b0008050380003140c25150f05003143d007018000080d81d0401016801076400b401008612034405000700710042040d50000d0590800e801c04000810845c40080c41c01040300d5006507001d03030b038071a401c841190300599401c0e2010401c2142c4003404c0d4203480005c0d003c01d042000001ea0300780c0c8041c01d408210301440e120b42281d21171000301915107a082c0c40c013800f206030b0b0300004141008588010301d62107200ccc25210124480e903c01e0007065002c26070049880741d6458007038200c1c0707581000d64940c1c0102204040c6141c82d0810883c26004880707804040c0405682d920b600c0380081080e03040713134000b800060803580345681d03a098403a038a6004840544c002410111600c1074183c21110f0140135020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253448516 1250 253447266 253447277
    0x60506030402040b2101050702071a0a110708030a0f090b070f200a0801050105010e0306100b03040f020612040318050105071e0b130204150602060406090213060b0403050105010603020307 82
    0x1074540030800504548507165a002c806040d4600390003c8000b4004200409040081050726298401a00300b01d55984045440c924041c62034070442c40d5101200c445545600b0104941110711068030328180640c4c00c022034501c000681d01e54031603000240d0010f4138080b56034101015845e40400c522900030701c1e40c0100b059010700500c00006d5541c101400004414160002ca40100d110016051380440e50010b18942d41d100b00600c62941d000c1c19544107490180e0080849042a800580a0b40580c1c842c07001900c5002c4040b80800c82d14494140f015600144616210151441c1e1521101001d5800300d000c02c815040c01014070044044040c12594140c40c0c641c24411071340c5842803080000e8603076030180c18200080c00c000404001c41035008082c1402461108502441444112800e50f20045440201aa000c210495002454540c0b240c0d010f400441d859010380b01241f1400c1d001001110b80034200719000c40e01c40c400c507000e0000c8034041d4000307105d2a43c0c0c1d420194200e100c20303602080004c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253449766 1250 253448516 253448521
    0x60708090c0f030d142b06210b071202121609060509010c0f020301060602030d0e0a120e031501080a060b06040806010e1009060e0403021501050a150e090903190306050603 75
    0x240100f03a04082403090481e407501c3c3c05c18030188101b01c0c450344034002500c103038004074804070b141061007164090501200c030b81c078028004446100800c01d01100092140c50b4450000340020710603080181d0403891070501b5910ba605045650f52426021902c502e090303158091500300b12841210305030126000e40d00c0c0c191401c0941e40044403100b40b1b1f854140c0b6098010200c404c01a00d00b44903d60007030041e64051500c3d40094041001541c06104002420f9448007491801281e413100d181640c4014030f0601c500b00700c421401082c1010701c115000600b05186100000b1a5440851400c0c40ba030704c209803c100100030102005042c2c000e134050240c060b0b00940040c01410251800b4135003041c0642c04000d80716a9406018055403044d0f00304001c2c0c2c140c0e00050004151701004800715004216400390010b40c1040041800c14801c2d104504140d1450459503480b94042c0300c8162f1000c50140c45040b0078940088810750320352040c0003014141c030f41760807845540c5102e03100f00320607111300400c19032846c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253451016 1250 253449766 253449793
    0x90c130f0902060f0408061e151215101a09041806021909080303060d080f120412080702060f0103020d02010509030a03120e010b010203071b0503060708090c0f03 71
    0x30100e0245000249640d03000650140c1e40f00d6002c2c000d0216180b207501d64841c01c02d0340d018100748014152140400500007031704441c40c840300007540d0100302c031821050030580200019140c0a881c4594201a00490081d0051030a180c2d2585102e2076680c2c0408080d00e0303544805402603100819003200000c0c060001002c5403070150030154028849241c0c94105214075120802260f20520341070022104000002c40c1007504556000000d0080c00090340c00c610b840004140d40602055005021190000b41c0d43c04a144039400c2d15848500c4c2440b42d070944c5031501d80009806140080b030b42c041140c130000914094030010b1000c0c803944810016640c2070f441d59007400108002c0410480c18020144a40a400c1d1420024000154001d0ba506980c244e01d040d4500304490010f202c01c0c0030345e41004400c0200342d800008690301d0350380c4516402440c0410020b110700b6512590015540b5000b414144810280e000800600460b00c60044d1010103600d07104004d07807540c0e030300070158140d0800c02c2c282400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253452266 1250 253451016 253451021
    0x30604020d0f120206090d0c110405100f03060b130506010207060f09180b1009050d080f090d050a150605010e010c05010b030d090e0123060d060504050f040605090c13 73
    0x28510600300c680003829980c0e507a02030f908610030508010b03030050081100452040011040c41c006c07a080048180d0b0b0151034a00801101900076805140c0314000f092040e00500c000c2c41c000c0030001850303507038240c07203103401c001904007108428030030f8403020583c00130b08115116840c00351205030018000d080c03802e0790648940310005640d000384040340300002581c07031a1030030b80320040004a01c0021070f02110030800442d00720702c402a404000f103002c02408140c80300e4900d5400c0507004442c0640724544d00442d100e581c42229000f13030f000803106401004110b40040c070441010700ca0819000b42c0d41c0c1c203441d41007c64910b1702c10940000e595840c64901540214246801180208008944108440701107460300d03042040341400940440340c10050208903e10490142c843c502141c000524900105082c07014605070b050310071140001c240180300401d500020003020003400601c0305203003422a80c0e0318084222803e9a22034108000500091000b0400d02c003150b80062268009000d8501510300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253453516 1250 253452266 253452289
    0x62b030327050d02073204060617090309010c120527030d03060b0a0f020f01090309031202190803060a05091305160602150628030b060d0203060402 65
    0x3855030301d80c024400a503004864030001c40c00041c080324a41d80700c0c40c000d4a0400ea5814001c1150440c1000303109990b61120f03104461981d121039003003d5001c40307601d091301560b480310459005190160008072203070058229121200c5900c401455640d0700c00000e0703141c4c860315048500007010303614400300080075214140244800c0780752031418003140703041003c0b24180980030300035041d07805540b03904070345010006000ca500c1d80745014400c0c030f03150030b07165441c6001e40c0d402081170100d03549806401c3c51081110302148048403009100d00300450801514904103800203594210720014903000150000518400c1d09442104280c081201e540310703c40b59030030203807070280e1010b802100011990f99000340640140c10013800010202c0c01c03890014a810a0115880540c1c00ba18104000481c2c010404241c0030032680c032511044d9403242c0006030305030502c0c401030018005400001006c01c4c43c0705440000d0300e20903480e01c54503842d010104450b400050304c000354981e02000c001401070400003d07401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253454766 1250 253453516 253453523
    0xa081207030e130515010e0a0b0c0123040507060903030f200d020c0a0909080403030c2f04060801020f040b0f0702031903090e1015020f03040909020306062b 69
    0x2410340101000103603900306005001000d40c1d03214000e000c00071171501d01c0502c4860090030452560300e4060042034015100c0d1090304488440400c240c000380a0a401c50030141c042a220060f103840340d400d006001c40e5054400303542c144600b1a020a40034005e075103040a40340c16495004038040710240c115590100014613100034401c030504201c0f0604100142e4142c1011a0003900403621624140301d9603032215130004500745e0828503100302080342c0ca0200c8040d01e805240074181c02c861820501c41e03401905614080340c00301c1118030303044030341c2c084407404000c40c0458060101e50303036030010142030780502c00c010400150104020000d80c40e00c2c0d030003404401100b42206050501c42e400082c14101002e1100210b400105004c604255000a046000e0b08004050085900b0f16442c11141c1c80c260340503903c1c54020b80007408602d640200840b005424010342100d582e03984641403800a040c41c0d4404030301174031130b03000070444c2441c0105200302c8035a071344040c1d617152001000a20102d0364280c403098 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253456016 1250 253454766 253454777
    0xc090a0902040603020406080f1003030c0303021603050306130507050d0905070902120f0109141305011b1107050f1323161d01120c090801090b0702010b0a08120703 72
    0x1525503807800a0801444162030050b01e903891b110018068400007000c030950450480d0401071071541c0c2d11100b03002c1d280c151801c51140011440c0c2a40288555201840084650452001010b07401388c001c5102e04400c0e03590700300d001d00d100c001c802a100f09544070004910300b4000c0c031a028046031300c01d81800340503108940c0300303075070364010502240c0c0501d0509092284c075008000c0c026080c40032142c01806282700030031000c040004080da5140000e080c00e030b40da640d045035440600500750041111000300900b2412090600e81000c0c2000c40e8801001c00c9034051403000091914046104503d19980946489035000c10b80350701314000e00c640039091511414104a1040341a0300c00f420030b10800220b581c80258140c00716000d0014140c002e00343c043d21413440201e5820380d03400301110946020201000c01c5581102c1800d403045000c68101041c1d40d840c00d40300400b03014401d844d80e4080d50307035a00208000400c410034041075038214018920181d00c0350303880c1020700c200320008091990107443c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253457266 1250 253456016 253456019
    0x601020312010f1d090a02092508040b07020a150e030c06070320040b090904020f15070c150906111c030203090c04051605030a090804030b07080105040c080c090a 71
    0x100700307402070280c0040d03100d642406010301080194004800700c40400d89007150013860035400721541d030b421146009025145040205201c000049a0f1418400b5540050286602c52143c000d20ba00c400300e8080d0b86681080000c218024008982c4100c0c50380c1080036002c0d803803450400b04015021b11075124041d0720041000f46160803040c00601d024070030f20344d80890580c9090200c44088039034490410700d0480304010070400c02109104641c50480207903242c54032641c55000144600141c0c06140307812100d0a2000d15001e1000d1005055070740c40380e0ba030350404d01d46611482c1c1a002401c2e07004d50105040950500c04180150314003800300070004111640022894107049d0140c5030b400001001c41d4012040c0311400006009400220030103440401036803800c51340d0036444040a4540348280000000410206c40d42c0b90803010080d90002c00c0e00c2c3c0e40f50b5aa14265446610483d009000111628000314030762a15000740410002203568594080d10b03174030034881059001d108040c0e400403213030341d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253458516 1250 253457266 253457287
    0xb0406151d090c0d05061603050c09010309050106091a090109020702101b17030115031104061b0f05150901140601030b06071202250b0a0804030504030b010e041401050f07050306010203 81
    0x1c1d56140988148042c1000d400e07c02001041c1100c030300b004505150511003002080340b079910a80310415003d2034045010145414114010300bc1a001281c00700d00308007004661180031680380701ca000050769810000e0780e80300294001c900540800a5006011340344003102d0074400c00501c000c808145200041c03c0b1003645d00c8460000440740c0c054200c9101100411110419180c0c555002400d810280720f003046402900f40f01c3d100314080d00d01401140c0102c010b81400f6442c5da20010703a4005403a03e403a032610700384140d444182003d00703108401110001070b214101030007105041b10104c46001d0240e2910300041d8085d0002425582d00300710705010010100d112002100b94002558020b041f41d101840c00300001d1001041c800c0c9c08039152444100010300403042160341c0e0489a181c4500c45444601d001c40316441540d00c080c00052617071001103000e841d0041e1441c0618450740c5400d0308241e01c003403510b090314001c54825201d07071100c8000440c0203001c0e000030740d40050144140c0c6e241084800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253459766 1250 253458516 253458529
    0x30224040303120b10080103120203040807080102040828022e0804060c0509060d0b0402040b0a02060907090e061503011508010b100c05030f0a0c06090b0406151d090c 73
    0x140240c1c0041e01c2c00f421141d040c5100c0c0300311800640140c1d14a0f860155045020700300580c103200042006d540000d58021803882402550080d003000030540c1c0c0419920702440c3d01035082806010280e0240d46c42d20361030888034101111081e100140d00c011303c1d210703030340801146c2d41403200b402d21810201001512880312034400c0102441c015100c1400c2d606007810444221040b0610715170901508108042046d0707980c900380c4d20300d440005400b20b404080d00300403802a014a82c0150b00f42107006c103580c0621500425010710400c0391034101d901443d620703644007054034401c250841e40341c0c0113200410100114814a601410400740c008100c3c891a003519500040e0554000300c80743c2d41d0b0300f07207220103407a01001160b4909524645284400e8540d100d0b1500c0344580c4d0b15031403c0340000101284401d01820442200da038000800700701112031030800c03580c4520112000c891451a018100c10300103840c010030b4054550201800d0154050240102c06558000d8202070041c440c4060741d903516503619 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 253461016 1250 253459766 253459769
    0x6050d050703022b1514010303170f1b1315050406020606010e010f08040221070302150a09060818010c03062405030105130204170309010f030204081528050117030c0703022404 77
    0xe50350101c0c00c1c0e4aca414800e0050780003404000c1d820030854144004809a0100501c440c00a20b240c60780d10308581010181000e5664051840c1c1d54554101889a54003c0c0160080301c1803030302521041d0341c4000045170001d421210706404030f041c01400c8108103100e070005a900c1480034201d0107165010030003040010024054545040d07000180500843c00c0103607a0700000346210186500700035005c00081d181c041d01d0b0052100b00821403000031240440d102c1e4030600c41c6031001c002c201c030354407000b8010b000d080680903403e401c8070005100403070340c406280141001640c0e1343e40d603411079081c4800c10000140e42c916007c8015024403001c2460800c820412107130604510085a03510001d10014060910360902c090038503205200402c82c0210120b100070761040042002c0c6010742e1452550002e220724034241c01d040c1642d00050f50f128068950000d41030341d4001c0e201a5407a15568071090340d034410300180c142d46030000303041040142400030312001c03c444504003c0c6019210501c0201182d00075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 253462266 1250 253461016 253461023
    0xf06020d09110f0109050609040513081602090108060f190e0f0604022103030604020f0708030a0e06131505071b06320402100306050d050703022b15140103 68
    0x3903450710150f142048080d080210f00f801c0c0712450500d0700300050700c3c0b40a0088c045008a41364000602882c2c0c0078094103500d16800407082d5201c0009402407899040d081304220b01070352081001181210740001c07454410305042c01c2e050300741d03036a00300b00403080350803e04141c45054440442d01c400c0c0300c06101d1002c5040828005018601d00f83c0108100c1c61902d28146400340c1c00e0500e41c03181440c010007200d5010405440240e503481c91302d4102580c0380310b00c0d030002c2d1090764080b040c4504108290400c002013540c3d0400c032000d43d11100c02d414000080300b000102884011500341c424004030740c12459004905080041c170313002e81e07141400c0e00d01e01d0142c41207c16170b6440c26070310944511514442551000390f4a00c400a0924032940744a400e40030b0f002078032510001ca04d0030b100503c40d82110000d400090000748402d44980740031580c0d045540422840b406100030181c020384400307000e52090006450200507904895155081c1c04c585030615804240d85500c07003016074052a50000e0300035440f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 253463516 1250 253462266 253462283
    0x3122d0c0512090102100b06090d050606010201050105030309130b0d0501050f0702070801060b040e0406060801020d092109060809010905011a011106010302091f080d0305040210020d0207030f06020d09 88
    0x5403480c00758141800b409009450a0080c40501400c0e40d0004d41501c40c0c0c1c0c202c1c54001010042440010000c0c020702c4540c0c0e500c81c070044a0042000340100e113082c05041c080c0c000f031103d0390302d5004051702da024a00126400041404074680d049450b40c0203425407040c0a0045244510f103131321003a00b526421600700d207140459030f0902481940c1082035070000c103210380003002041e003480e1071070401c1d10403407041da103034400d804000c6414080c4962001d00242a070340000c55890110350310500251500b0704c0240c4903440c0b2543e06281084e091481c070842100c45070380d100e0502c0d0070988180c800200c040d01142e45990383e091a140051424859030001902c2d0101c126045982c01e400101980540b44100030035820500040005840c1c444600d13030404007200140310258102e00d003036501000c980d8002c100501c200b0119114582d01a801503020714002d69035003418000c41035090382d070f90b1181c80d448801644909810004a0700b440c1713914034010310410303015107414810074110040d1020b45106079903e0340f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 253464766 1250 253463516 253463537
    0x1050c060903190206010b07060c02160e06010f110a0602280306030c0b070c0e07020f19210c120309140f100606090504150b04030c0e010501050403122d 67
    0x10f002d41881e442109407000f044158144030138403009010b40c1e030f40144503a84603d48005000c0c000d00071450190301d8911502d0466946810b20300381d10f1401d03500c95010640c1c000342450320740d114012000d0408035003c01803844134400e50392080258080e221030090903092a07503403d81411b0000301d100c0609429903010500c58103505007580b06a00075400742c20581c508101000000300f98080c244e0454109074514500d80e510003a050341170250490f4200e0a40c000c400c141c101daa8880f84a40c100c0500030030215200c0201102c181041c540014070b4800070680b800a00400188d200051070790200451034003245039000755492003c41481ca00d0119142d400c80f2610410845041004c01010508100c05003d8980f0b003d0003d0f03e6680c041c050180100d80b81e414406800d8885101c4800230214a4000c0307039165600d00b01a00c900d981c60207150748140804000203440d610803001c3d9400c0c2e0341c000b250901c3d02d01c100f40040d42c3d0403e1003100410314040d03014404500c500000044a440c4055464458036017 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 253466016 1250 253464766 253464787
    0xd0806040c020a021005090d051f0207080409111b030306130513081e130f05010c031d150412111c0210030216060e060a05011404020901050c060903 65
    0x51005010601880c5444544149954009140e000080e0181c90811650a00040032038103442490541ca41190598140d001004030004a0604102e001068420525801c680020a900c160403000d40149804e00052214020540c0804510103030100e6071807815084051160314000c100c150500319401c0401001901d04200c00310200e24401c107501000146025902092503c80340000681080b10100d03040d8052511150b1098400150740304450f106d1044a05e01c10484019014903858202500c0c00092154002c040085409500d512041480d48654509142040180e007906a00c107020a03514201002250000c0002d07040ba58543c014042d1141014482400294601401903038041001b441d5204050300c0c24141c16412111031007030585030f070001c80c00307800ba4000c890000154982080708004c410381c40749501400c0002525005d6071007161141c21507100344102c081e0502c4004101d5001d12700341d40101403004e01414840c0c00d02c044109002d01d042c00842e40c107044c0c1d030300018134801c61 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 253467266 1250 253466016 253466027
    0xf0204031101140a0c081209010509120f0a2109050c01110309130e030c120a0f030b01080103021201020c061503071703070f17131e080a0212011503050d 67
    0x341c181c2030918070441d0041c40501c81103071203500b10103801c10151101c0d0004000130442114003a99100514030300f01c0c284550781d28004c04059a4140b164419442110210025101900e080c8516801042e08180c0e9003002964689000710703232251030042d005011a0508502c0c0700c0c4103403090040000340700407000c5000250100b0700aa01b4010103030b10070300c8600c9065494800c0d06422110355040410800804140c0c5482e5004410203040381d400b03100740142201c51684064425058166589607141c05600e074280d08680382480031600082c1c0c414014805402d205000c1042c0700c40b010001071910001c10f00140c10702d407095036414180e0918449c2c2880902c2c081000700003030551448220580c4903500221a030f41e2065003802806002c0400110051021205030002142c0c20800600d81d40c0090501105801606004064466401e00c03250041c0c80700010350b9205884011006003551406a0200426403650301d010300c6982d92500898204104140c0c07220001310302ca1401044c072003d6a1502805 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 253468516 1250 253467266 253467293
    0xf0105040c0302270f03030f0c0c0405060d0308070224150609090406090c0302060f030a1b0c0f0606090c0504080c1008040f020312030709080c030d08071409040f020403 74
    0xb01070041c4850001a00341030b5400c030460015140d00308030421800b0214146880210100754180000724044c151041400000c00400c00554255038010310884100021200151390030343e081220440010001b80c0186400341d04078416004440e41440d40311500c45085400000f03402130380031a1018007202011100455140c00011a038250a00441b03c004c80c1400d50f001348050f12043c2c5440e200418800b0b0100c124004d1070300503207200e9443c0c0b80c0f0f00c5480100d60013036030302000c1d080ca0407a044245500842d88000341d4a6290f4071110018055184c601402610071000d0b20107d55904000071000c6051054510040031b5448846c0c07100c1ca000112420500f2002190340504041803150080940c421034450784964001d0b500300710660305001207032030182c800900c40c600603800030a000d00c0d40e40043d00001258803690485600d04020750605407145410b05189000c1747c95207010a4006000f4406041404000c90090341402d08400000381655580145850300342d6000605200344190030705d0341503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 253469766 1250 253468516 253468541
    0x705090a060b0f1b060a020319050702030d2301060e030d050307080c0c100507120c0c020f0405061903120806010e1e04091703090d14090d020609090f010504 69
    0x40036602c2c1c00c0c0d0049082c0301d01d240a20320600000381204480b400319001c00c4880c01d80008480040c500300240030025401034603e040510000b00310340e20008840c0c058a40300311001c1d4050f5060010300000040034210100e07980c1504524008034401400c03d08c1d210340e00030031031540d0704600840120305043c104041c81d03d104d17081140c1013040084d0b19410030030b00b54001140300d084070b81d40e255083c246c03030804004c1c11100e40c40a0500051040c002c0d0b04c56209051015561000c1000700b0b03d140741500c12454031400250000384100d20034041b0302d05940034550010300a050b542d1003054140004a40721580d07001103551a842c2c003071803542c0c03e50140c00c01c1d60180c000e08000070b00c106260300107111801a03d44403030030424021040c1c0115151600700d011501c0d407040c2c1520008940502280d2070303410449840e201d5114400d00c9000051064103400c410300c1c401a103a0b0303d0310752060b040c02070b21422058240d8001c0c1e0b040109010300d48070310b581c4500c00c140c14940004503504000400050702c01514021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 253471016 1250 253469766 253469771
    0x30b100f0b1317060109180c0515042112090513050405010b15070b0a090c09150b03070f020705030f0d110f070b030f0709030b0c0c011407020705090a 66
    0x384400410009114141e40c5458001c03500c0300c5000e80e00b2803120740365800040900d00d02c0c0001c02c0b004030002912905907a0b40d100709000c44104d52400b096500c4118102038008079068201304014241200c1d03c2911101252005181980318081d1024501c43c090009155016082d9a80117001d441a500005900c2d54175181842d17914020000d1303610039964000c44611503989000c101001401d61000c0c140e20000390469075599614600c41c4491f40040f2415122040c419000800781e00c1c00380700300921150300100c4c844429092615440040400034450008284030060114201003108081c40c81483c040e501c03903559a514450007406e0280729841540a81d111141040c0c82c200d022600314030b0007c040c9089607407080021042c512309001d059401000380516030001c22401222802180306500300414145282c880440844508240340b102900f03101c0202d020414082034440104a81580100049400541d40d11403114441c0244c4940780941d104000800190a29000c0254020404d01d0304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 253472266 1250 253471016 253471019
    0xf0f06030c071e0807021002210a02060c0f030c0a0c0c14040b010201060509071b020604060801030506010e06011b2405060102010e03071509230601060905060c0a0602250507030b10 79
    0x5484c0140101c140c024424141c00381d2041c102d5100700710700d542010000c09980040c3c009890105c1c91940191400780060040000140d49103d02c0000c64040034100396801d4070710340d26082120340e9900300c0c0961904102d50005100301081d042c2c0341c4880035200e121038015a440e0220100012202520200d605590500c04200300980d0f81490030780e8006881c2c02c05101a508401c0000b1050f03001c44030095120750049008281544c0c415100e6050f68424002c9484a90705c4088804c61298115400c0d03001640b66020704200c650b11040c1441050300c00c0c2404890340d02c0f070040490300792441c41e44410003a035035803042040d650307424024890340d07900e9100034500c5c10380a03449803240030b181c2c41c021150302ca40303900007402049804003c10005041005a41a0303400c04075030b103d601c80200303125840c0000c41d0044042090300c0c050040b100444c400c0001030007540c400c0c0e0f4502c000b0b034216a01c0c0601c0000070045058901426041d4806000e2040e0082c040c29400c6d803421944100000d04021086404400e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 253473516 1250 253472266 253472273
    0xf0c03050403020a03080a02040f080c010201060816030206180301020a030b0301061221051b01050a0b100519090510080109110705060703180c08160503060c090f0f06030c071e 77
    0x10300135512070f0146041011036466454440c044d21455100406013485031800044404001c201d082441c5d01c00d07030003407203150f0360741010582c0d8900c5040b040380c0590503a0410001890b1400090680e003a10081c015090030342e040000f400c982210441d000072a844a41031551807500b032140300f001d4010250070800785512a00c902c191b000000c501c140d4079855203c92070516501507000d0300c05c001f009914139102c500803511441d0103080169030301c01c00c89050907108000c500c3c240b42409002c07012030380c802d030070308840b600c04081e81442c0d90501020311031a14030100d501c0e156041d41180c03031440b644483c12154940b0081c00200c03400c82c00d00d0b808041c002d10076207000481c080341854000c040382c80d012a00d9001400307800000c2c0060003004207049880c400c0010b81d00310200d010b844165923000f030545181d903200309045c2c85282c1154100c203081c80070130203840036107021000c00443e02000382840345c801034030401251641d481690f11483c54040440d016003049961101b682a42d0f201d558a4101c02e000782d903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 253474766 1250 253473516 253473523
    0x1401120303051021150513050f0304061409010932031603020d110405040606030209090607020303010527010b120c07030530070302030105180103050606060c1f0f0c0305040302 77
    0x5610742a05800d03842d80020b0022500380c886000121a108001174180411144d047c401288011500c6001c1d904080c1e00c651004402c0d9402c07500c09d902d440a51400c0d508103001940e0015940c1814441603080200c3c1000c2098043c060018040d050850708044103502007690070b0310081054400da0050000c41100340001d07118a044960544402418010514111151003290b01360a42c1191400040005001440d0052012a0700030344107010b00e07440d0f0703004444e00da0404641c2d100150b4010001000107007400c83c0010042c551503800315000d012103c80c21001490207a0180456490210342c84007101c0c04500a40c3c1c10191100c4043c0c079080e069680a0020b0203001246241c04501508965102060390811b80045a626141d03030198640190003038029002030045600900428500c03400307a041d900411416250050000c0c40c0681d1644204282c40d480b4030030043c07603401a0030001080480b104046104d54031002804200342d00d62024100403140d00c001e10390100b508001c2800003013074010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 253476016 1250 253474766 253474799
    0x27061d03090f03060105030c121024060302130e0a02070f080705011515030203190e0a110406080a060f241a1c0c03060503030f07020a08010b060d0f14011203030510 72
    0x3649c0502070010010141c50800e0320500110040714240080403c1c0c0050700700c6c04500048403035a803003030b005413102000c0782280500c400000104135400c0007440034004040c03020f0303030000300c03a40c0140c540703101c5654802141000c0003080742c1c601c2c40031a4000402c4003e000d80b071824800c10380780003c00c900c0c101c1c585041c036a283d81100c060542c000003140c0c0c46c000d4000c132400c203051544014490035404103503c2e96507a0f410041510000d421504026244c5858000c5208445401c0b005040426090715030300006c000079100c007011240c0d2240a4610200003c2d8807000c0c00740c0c44640f40090340d14000070040350344010751001301300c3c82d8208100c2c0034881084041c0150044d005030005000c825199069008042c5c5400040e403511020408900c0e00707134500000d02035076209682190400d580c0740c0040e07098a81101c09243e014200307010f403160100c4940c1c025006000031404c086281c010305c0b10494103000081c0c0000780741d10900f031524003d040d0503008998002441e02c6050403058034102d241c045542d043c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 253477266 1250 253476016 253476019
    0x10225020a0602010c080f040f140a05010c1103040b030a061d1602011103070c0302160801020a230702090411090f07030e060702060c0a0c05190c0927061d03090f03060105030c 77
    0x1440007007000c0c00341c02700310007560b02c0c1e100c011140404103080305203076225a100d0701114598244031001d12050321400c025101c2e021900001d5040c1420200c1c5186603400042001ca02c2c640e85580c0024181e800322140341140e012012510791a007066024201000282d42104096a041680342a44504000122944481c0074640988582050300c0c0407804c002d1480200c1403104d41c2454045840803040d4024250b08281b604da1400580001c4180084040d00700405142a242406110050306008441030392040c807414200d4600402240001c902da4802d8030043d840241900820224640601c0fa9103a41c0c01040e00500d901d00e06640001d641e4a4000c110306817000d07000c50403200c454054500d820842d03074080c068810840e400c0701000c0d00494802400e603500e40d807101d0001a8110701d0700c521008139035001c0e003c2c545440500c1801c15050002401161416900d00c490b6404200c0518000c1900540700c010b141d036241f51070100a030340c002c0402d040c0e210741c202c200100900e80d00022000080c510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 253478516 1250 253477266 253477291
    0x12090d0f0203011b091d0f0106030203090f010e0a0309050607020901140103090609060b0f06070b01060507110d050729031b130f08010c0f0206040212010225020a0602010c08 76
    0x8031440420301505003540d070312400c0350314458408803131900324101406581d80550010305060300c1c000008640c00c01034540c8000e0141700030062003128429001550b0164200c802c903034000d00c89210b0242100d80780400709140307030020300500d010141d0291450000b4002101c503581020701940001c2c5007000c041c4105a2410a100340186c402d1340aa001a4040b81e0058010030910045043c8503000c0e25240303100a200d079a1082c2118200d24150301916907281d00700c0500c085070780c01e000090340c0c0c6510400b0155140030004924202c01c2d6940c081c410b000da032251026000071441c1c07089106158806960706901074800c0c6082c0118842101c003a40c1d40200001ca443d0300c0604540317125000e034410a84801e90f00a4408404159440003000c20400c0f900c092000700400c141c1c6080c211070b070140b01a40d480044c0c11103000b2501501c1c200000030050500d0741c000500e8120040300c2414140d050884080d0380841c002100001c0d0701d40b12034200d00602150000348850078001a0042404800404400e00c580307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 253479766 1250 253478516 253478543
    0x120b030c10020c04090602040f05120d0f12050108150604060501020d030b21030403110d1a18010501060f02070b041a0309010b0303030414010f0e030301090f020c01050103110312090d 80
    0xb4801c1110700700030040070b8410841e00c8005e0410001039401401060005101a900043c0b103041a1280381c840ac001000545201000440201d41c401c0c0180c2d06081003204009200d0b11002407441520f0080c0840380050050064040c607015521400401c41d600c030b5840c048007006142d801080001d9a50756501e00041e04051368400115602000b40901d10100340c0380f00c3c15132040000100500a4034020400804000101400c20110070700302d4000070003036080702051410703402e100311081d038001c50403041c40d0403150b464210750350846009a01c0380c0000b4501c0340d0102420380d014002c02001e0902c840d42d0310306d400d007401090303400007203d40c1130200452000000206441c5080d80f0105a5003002015a80d80f4141414100f0025a03010302101043d440d1413400c8040c41820302c6044034514200000d07505681c40d000c0d0810041c141004580071a0390208018500c0120078420240030b580b0680300d00f030700d40c4c040e0070505151181640148c03000d10410007034040b5940d04c4000800c401daa2040c202504007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 253481016 1250 253479766 253479799
    0x16060e04060305030408010c1b020303090111030d240f1514190203030615030f0c0c0703020909061b0a021f02040b1b0c030102040303171008030408030406120b030c 72
    0x2030820b81d2020b01030f80070210303010071052019005660b14213015034403906820008142840b00d1456054000c0d410780c81040120901d50280542081c3e00119005680c00c040c8407001c508180c80100f040c4442ca178203401d02c003405c800d15010502015041c0071821004a50811000b1450007120080a00c24005024244003817605000104e40180c48600741140c410600303100301941c0c03600f0940313500340b00301d15200c20710030040000d006072849030401d840c0b106c40036141c41c01300802e660b000709044c4005010f05c40300440542c6071288203d006070450002400c43c0d14007111100e900c2c220120201d51004d00c10404903007030b141e0005106c2030b0480ca07044828416510403011078020300c0b403030340044100c000104020400446004079a48000348407016078460300c0008081608038481c41c000100810111072647c0d071a4280d0f0740309150f21040b14043c60070306c603440306009031454105620402081e40000740500c0560f80c8400c0c11001d24440290500c041360004d8002502c440c03100c0c8459000c1c400343c00d07512015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 253482266 1250 253481016 253481021
    0xa02030d1122090b0d11040507110106180b010c0506010303110a15020a02010b0405010b07081602060f0a09050a060e0405040317090102040e060a030b1305070315061716060e04 77
    0x30340000d81c0b07540b14415a40e180d03049004a407007205409494145826010704196564142641d802800200c0310020344c800c00004010152020080203003c10820071244824862000071b00f60b610443d5144180084104007921454480c007410041d0708800600018000910641501c0c0e15040400c4124449442135107025030005001d010769040c1c130500400c0d424568000c01108a0307960003485881c504d0b83c00e000a5810a00c100c0228040030060f0401007a00c2c000038007000065a0310b28140b1920640000d1019005100c44042500340003680070784880d04003a2000090000b55502800c503441c0100240c890300070030100c980180c3e00d480010381014030034008031480d001040030001503814a940045c0c000d4000d80104194000d080011171602c0c40d0003861401142e9200d060550581c0c0c44101c982c01d44000004211640d00ca111804400916030b00220741000c21362440000c1c845e46064080480001c04002c4480300342c101d10001241c50550104e8401a00d040d401d14406550410021400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 253483516 1250 253482266 253482277
    0x31608070b070305071e14010e03030705071b1d0a05041205070201050d1401090e06010807030f0305040e0c03040209061806190f0b12010503030301150309170c0c0112020a02030d11 79
    0xd8034403007240c000400c0c00d45500201455010b40340c1d01c20b47d04012601282211582481d48195500500019200038403c00061030400e2040c0100e101c0420301611412103402150451030029001c3d0000c0014402e1210070705a0005400509002c01c0c10a507d03803540d200184900340c420030200103444010f40e401501241c0e81d18413000e00c1005043e5003410301808440c2c0030b00403040c0b81410070400121032503000a803d8140c645e19805000000d01c0d540d01d00ca88034200c1001241801000c1c0400106122224030b264402c0150780c40140d0303070b46043c4c81042200b41000f010301f40314203800e040300310000d00141802c503404441a207e00450103a4148000f2004070180c1c0501c181160400021a200d580031014003c4d1322040c0c044480c150b604c46c420562240024000d880c10904035101c80c51845129801000742c55001c0c0402401c01c0c4003c545071042c83c0e114107659107840e0301c0190f500420b541e0100ca956241055500c0440c10a144100d000b5140d10854941d152080d45885001aa83c20b44000f281c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 253484766 1250 253483516 253483523
    0x1509020a0b0a08070f0c0201081f15111e0a03030504060b040f0f180203101e020315010906020304060923030a0b09190f081b0714031608070b07030507 66
    0x50b122942c280000348410800c8540b140000e18044104145501a03050201c0c402c1d0305844005070b9603030f034016040030f891002554030441d02c98642c00281a00806a031400c5200306583e41c2d1110303504031240586402c2d07000c0b070400401d408190740000129404901c141500d5814500401c26803510b0800c2c80103000d840c403405a100d860014440b40d41d0500358002c1803900011002801000c02004600b8021b0803800c40c003070b405800505294132000a10b6200c1c10303401084825204c9415804000c3c1d0381260411204401c0846880c001c0668940e04025684010642c510042d4038040c180350009081040d207100300700030030f1114044105074080614411210780b402070110394045c401d03802e11540c5044140c4245945000d0107031640c43c8141f25026104245410607148000c94019503203108031540300c1c8895001c0c0416000150076600c00910200340140848581c5c090701801d54400c0500b00080242c03030303028155610904004200d07010542808072400f0b005590b85441850405171041e1040300b0004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 253486016 1250 253484766 253484789
    0x61e04020409200901090902060703050706020c07060507030305090705100e03030405090705031e010302010e09040303090b040c170109121116030c0f060305190b060c150a0b030a1509020a 82
    0xd1050b07002c1c6052010b61000c1c01c844c01c0485907a5040143d0484c0c4a4800c040d400440801c4a4000300c1e002c2c1c40102710440c0700d5103005181c0303d510780c40c0300e040c80ca00350020300025100181100605500d401010707000114031001e0a034151401000505204d02c60341700e0000c2c0140c1c2e110b848850707036051090310000c040103060520b840c44c001d54010501d0b441213601205030080c0c04019000d43c8100c3c400641078980c1a103c504dd03c0e0310f24020400640d1005000300d040588444440d40001c0c1102e0302e00380a50b20404241c41007030300380102d184200c60f0610a10b082c5a00d0f04100c0e9001c20994032500304001c1e07440c2842226071880e40e41c5a42040c0d511010240c856018000010030841a2542e002c101e80c2c2040c00306081546404044054030760949461050034244041305104c07a8099010b5105820001d258034071304599001c1090401c009083d8a10042c062076040140b212214002c48140c090103e0181181400320ba079610101d140340e03040074492981d00d220120841d00c1d0350b120300d40a84601c9800303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 253487266 1250 253486016 253486043
    0x15040f050907060f17061905060c0c03061605070204020304060e030313110105090f13230405010c08060109060e010219050102070c0b0315010e132a02061e04020409 72
    0x185076842e0310501c01c2100048044004498440c85506820490007080c601480c5545681c0108000c1a50005a0b02005d8080c5600014170fa80c65078010080c0201c00b0014214001c480d500301801d02c10010080b00094001400202c040c030b5000c02100e0f07116a044800513200d41311030030030000070610b2580e080040e100010501c001c100c3c849000602d80c5109817190403101c0c201c07000454003401290b009a0300400c0c141220b082c01e10f40143c10b51030028040800140c0c84c4e002c0101d070704007480c03c41390584d410a5110305200c03c0c0701080c002c0f0001c2e0031450501358a01e00300540000c0000200d84070b01010080a6500094540e01c207001c0d6481c0f103030441d141003441c1c1c545420528001d50004030100c0f084800c0100000d1401d62030340039244103000341d006190a440710f4500660728502308800e45075018070301c00042080c03a826889034034401c210003022a105204c601c82145050800ca100c40403c0d07500110402010001400d401d02e0211551107041c08151100c2c40801c01900351002d000701080c010407070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 253488516 1250 253487266 253487281
    0x6030f1202010b06030703090f1b031b03021012090f0309140906011d01030603020409080c070b0c1b030a0210030e0d0302070f08090a08010e010f0506120615040f05 72
    0x605008050203481000201010100140d089030300d08400300790002c409000040070300d4003030761011552900800d1040c42100140e580ea6488a0b54224006244840048207005000216090342e07540c071801e0015075842825500041d640b50643c60400e0100100100c03d0700c915081038101d1846541d00c903101021889903403501500c80c650328080e98050a00064402c183c0c2d142042809001d0700c010703120243c810481c0f20b4244403048540c04194145900c0b1200000161228030540c905240100500c0b600c4070020728900c0e080194a40c018895040c0c01e10220310103003030200e500e4261050303003888a2045499000800cbc04c1502c0070380083c1d80710254140b14080c1541580180c006101c1100550300400581d8a05030200e02503050040c3c01072026040b0107001800102c020291510010320543c1034940c2e90081c1400d444607100045060394580c60091551510750040235044034048402d0384c040515602031640e80d4400800703149817020344140302a0161181e0303000100d02c0c3c1503080c0c10300c072501d030050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 253489766 1250 253488516 253488533
    0xc0309120307050a06091401150323330c0d1509090b01050f010516080309010612060b040507110c010e150c010b1c240f021603030b060a0e060c0a05010603 68
    0x81542d00002880036107d4002040c82410562100c0540141c84c19042d038540000180d4000880c001031151018081c0060404100506a003c284064884078401c031400c0c5001c010810442003041c4440c0105000e1207a9440e0700342d46d00784c401c250700001c501c10901d1028141c1c05140d030084554928080381d040900c181035902e64140d41c81500c503a00c482501c3c200446d840d110704003d10595505c05060f400001c3c80a40003150042880400030600f1074a4034003100811915002c1115078694450390035206003464001c46e03510491380d060131901032000111441d10381c0038922086040062901d40021640ea80d0361840c055040101100c0380c42d10305241c0070034020680740f582c00c0c3c841c4241408420070030117100140080f4907800040c0f12200d011404d40007200c4455101090003250301d40c524809140b06a01c05041043d0005c42070307440b861070909001d41100c0c0540d4486c0d0086504008074840640c0160000c1c404070000c0c3c4d030f05039958012088242c18036809603402030141d400c0c04400001c7c0010710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253491016 1250 253489766 253489781
    0x3161b05041406180910090218010f090e01020a090b03071205091501050402030421090b030c03190b010207051309020303030a2705060105010c0201050705010e07090f020c0309120307050a06 83
    0x143c6281d0040d01503851104c0074200b08468440e4180d209540c0c03146014030b190420460240f024101d001e0860000124021051098100c5082481c0e4401d0810402c4850b00581751420f0340100210303e003e01b1301034024070310442401a5400c406000001c92030300e61003203001c01550f09003c00104410b051122800d900e84410340c031803649040d0603000114a1389802e00c216801680e100c00c00401c00407040300040c0000351000040014803000010000d0380138910301c0154868031b11503820031340da07150481030022a40e6440340000790841c903081d80e808690f60001002d101b5100e040318029168005101100041c02c0c40c05402505400080184842282590450101c06420b8064807102009007044221000c030086405081503010000411555010b00d490005250040c0b51545c0303030031180d445043c01d50314850101c920719401040c0402480343c26128610700030920310810351601c2c8601d078401e0750724094400158464a4100d084000c1c6000c200100e521031075008050341c90002480c2132400040000c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 253492266 1250 253491016 253491019
    0xd050309030c0103050f040209070203070b0702031b2109042a021e120d090f0f02010801060c080f131205071e080d0c0c0503011d0f03161b05041406 65
    0x622005100b550b020340546885a00f40b0103820760942d495408102d035840000d0103090a600040002d40d0114041a041c0c52241c0080c0d00215130343c450903940e00700500d0070290041c0160f00300100f500680400d01001d036011401607800300d611540000006401054204090f00d81c2010186040804014010100f00044030340c0d001d5410418078440040e40c4061030364801400b039004422983d4070a101203001d0700040c00612000242110f6540e11400c2c001215401a42c0d1203003029020021581e01c144640d0240c21180307410341e80440030b6074072042a400b0340c1c1c2208500c40c1d0041a89154101c0c54101c100090203440011200c0030f4581c180a500e94404e40900e80322150710700340c0a0800f2201c4503d01c000c80d614513004181420400c10304031914081400100c03905160b40d18009229602401032800c5103002d05180c00c3c03c403500740c02c02480c5c1b98030b02c03049000a82041c07040c200151001c1c8628241190021f11482a404802c6d8138a07000700d41d01d4009580c17040c580007103e1030407140044401d108a20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 253493516 1250 253492266 253492273
    0xa0b10111e03120910020f070b0c0f04060806030f0717010513030509040b0109091d0c0907020a03140f12041109040209010b160b070809150c040501050a0e0d05030903 73
    0x900c05146030703010728640d114656903004009169207161114401039000320300e10140e80d070411204556500366400f40c080c4035118000402e0040a1214003400250002400d407030341441d22040c0c0303411304c1d618081c501c500420303c194140010401d0718240b110b069000408401d80c0e170001d0711000e0700880c0030514040c00c0c403a580303810300051100c121304500d00a21074042c2c4625040c030341e00c042044040d10301e10940c01e04000703028500040c0c0745040d00550304d2810380100c3c21041d00745854542e038504529418002e1181c600b48051240c1260007061112806815180054007030f80004c0900d8440d200c0d2001c02c099a0b4400113005820000401e800c40c016440f420311480d24180074010001d00e100c080c4ca010390700034074050040205110b5100280742d2010403804003051034030582c40d900d0000c20211400004900105c04001d03c40c1001e11840d15981c502c04204151814096540900340c0154003400c2d052040c006008610345024140144100200429140460400740b50154590304103154007800f910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 253494766 1250 253493516 253493533
    0x80114030a02152d030c09040b0a080d0e04051909020d0c06020d11010912050c0a0c080c010e0603150906010e030610090f06051f03020f030c030f0601110c01080a0b1011 74
    0x2900100f061003010b8804c803150864548141160060b40326200e125400366a488044140c4d40700d008401004120010140088282e81070014210402185045105519180400598a00c2e6081c5c0440380c008a034800102c001c02407000c0380000c820003d015280ca42441000501a5030001c5c1030080900295036041d101041c81413001d080e20f400810040010aa584040c0b408501c600041c014021b83c400403108014016243c101000400c1e4000303900d603030401e2160328065600308110420460040da113144c91864440e4420002d4828220344030f00c6116601d02050302a845014964001d903001410f070703202c0d81040002c01c440b403100c40c45851318050808950b0b88210085d8440c1d0812124040d06020b030b2004044926010102c0c7c0300072180a043d428444d000400c942c14000d180320780a1081515902d0610640312054080700a003507504100b030f1f546d924003020b000032445107260982030030300b85019183c2d440f6500161100f003130180e400031612a40070030b8451340a14044a45c4001c9815a4400c0c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 253496016 1250 253494766 253494817
    0x31b140603130206090a0603020d051612020a050d1404120302030702070b21070804031b021e18090a031706060405060a092106050a0507080114030a0215 67
    0x215210542a400396003400000e02000d007028240030110b00c010f0002d440c00c1160740018178890500e420400010b54082004030040b0940d128607a04035251400022015800c003074000c125240c0580c42800c005d4021882003410350150f0300707580110404240c00d001c1e0002c04211000074020486054981319003445030000800e01900c2128020603655000d03080c0c071802c240042c220350b03010300d50342250241c030030602c43d40b49403040700d019006100c165650403641c01c01d03040c000d00d0821107a03800d01400740803480080040e542c4800800c0c00d500c1c1030244000f100f51110005008002d142c100036100c1301e0fa8020000411004a90541c0f0144203403203c03e0507000350740d41804611000c403a0650070903010042130202d032505d00060003180c402403501c00941038884e1850b102d28030300070600c0c44502a00c00c55001c00c000301da008840c1e0005a1500030841c1c0e26010a00808070300c01841640203650310090500719980b0107126800b1040e030040c1500705040d071b482807480d070310390f20103603400c02006c1c001050356000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 253497266 1250 253496016 253496039
    0x41103090c01080103050613170c0601050307060801080309040b1914191208030405070f1d010b0c06011e050303040b09040c0f020c01050a030e0a05010e01060609052b0b01031b 77
    0x145c9401000500345030341c1d82d56401c00c0e460741c0d2000544142d0b9450b003040000014510060005c118420007600d89940f400c03007814601001078110100707000c08c001c01446500c400105561120300221004511604c0030804107000210410803140c09075042070b0003043c0e881100400082c01d0006869042407400c500c40180481800c90144900c859000c220101c0460307004000745030880e0295060750012039131280005d0f02c2c00c5003640004c0f16150000d1185a050801200d401e0040c01e100107010310705103006006e1500c40b001400340104000c0044824900c055149038484003400c4040c0440e03950b1a00e03030f1019103c41e00030306101481241481c1420200074400c0d95100c004c2c1044d07070010520f43d403142d001500c268218920600400d984c0781c08045810780d041155811450144000040c003a4070b04516a0a541c040c0c0c02c80824860010f504000755220300749100c0d90400c1c110808583e441c40075000101e00c40d980c40011b4442011103002200740070a040050741e20b00142d040d1b000c038540c1d403131205039036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 253498516 1250 253497266 253497269
    0x515090a0509060c360901030b010518040515100f1716030302060118090f0602090a050312041707120c0603140c030a0203070e03010e150f060603180c041103090c010801 74
    0x82d452040e4005502400440c5120b00c0c9a0118804c200ca403c5102c10204041b02e03802d900641c0d060303602c200100960304020040e591407540040c10003401d40f07440d86425a543c0744003615400c50401c2e00e000103103400d0b103050403a800f80840c0c010b070f0003900b0b540d100071210380702a004202c0316a0050105610740130722400c49003070440c0d80c90b4001d00f6442e031811031180380c0500d00e109603454440c0c0382d21100000400041400038514815440103883d05103020a021900d6110b80010780a5030203c2061981c01501c001942e040b92a20000039403890070100710f0904001c126030002d43e48014000141040014200d00ea40c01d8407071030f580c00c00071540d19608819100b0400e8601544501c0200041001ca180a400840d400b5982d420540386a0705524082400c4a1182c40c454460783c1011a003004a03080404c040e0f03801002e10b140040e41400d09000003a810311000d8490340c00c1c0114071054030901c01090002d080748100040c01000504407404908806500496002d0b069000e0381e0144061903008500450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 253499766 1250 253498516 253498537
    0x306120f02120c06040f0f290f0c01051608061801090e030d11070b090d0c0305070302160e090111030c180a1503150801020c0d0e0d080f0406020d0f0807030515090a0509060c 76
    0x203207c500a00f13048c00b09a071100c42d92854040c010015040319003024040c03a402071880000303282e00c000c10300200412981000e0903192040907584901002280701c51482415079080c9440000d810020082d401c0c034521400b448075921a0030a01d02200241e14500031b00101c902070300414107181d132400e94494407046050303085000315100318200c501091207000900070040c0701c1c3c0122113030b403a244030701101c0032800c03036100c0441401490100701003c0c00078082e82c100051340b40c4500d400e60404502c0c84000e801452000c2141d40720b07111392442075030740e9901c1910051080d10f2403c54406810400100a07000500d01620484014103001031825814400c58501407a0000600460b000268040b10071080b02c0300780e1076105061464200106e40c0e01d10003088040c8000342042d544034034111000e401c0c074101414210500078003860501200e41c010160a9000b8014500050a41e44030030800045c1150440e04940042c1c0c42e204110b010049035201c58010b0380b1180485600b41d07a059641240c503c60303040c40300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 253501016 1250 253499766 253499819
    0xd0b060406141c02030906040302010e0c360703090c060804120f0918090c080601050a03080706110304030806010e060a020a1401020c0a030507030306120f02120c06040f0f 75
    0x1215054000d034042d02d0032400a45420510f4072021107004280d030816140e0f06c0e8160402018881010340900c40e00781d10403284805002081601030005031481000d070b00c0300d003418800094214a90803090105200301c0415040c4248600f03010400a00170441c00324101e4140e030300c51601040e414010313070000e407141e0ba0220140340440062401194102c401088640901c000d9540c0442e083c407142903040294641140001003400c01410444850590755010980c607801c4400107003c1520360f401031030292a005140159100450302d0000000c0c103c16402240e01800071040c0030825a100e041326000d06801d0313850711052040c060810030f0a11400940c400075034003044101d07000a6600f50828004580c0c00001405e018140c1000d60030300c010300070100d00007240041c0304820507400d4440c460240c101d44100b14198401e540d29003020304001c00000c0d11420300b0304440340800004000200c50140301030441500c80d69501c06070380e480340260140c280983c924000202e9403404109090f0010300c601c1c0c01c2c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 253502266 1250 253501016 253501037
    0x503030f10052b060606050904050a05060109270606030204090c17130f14060906070503010b090f240c370c120803060103180f020105030a0b03060108030d0b060406 72
    0x20310003406643c0300c10340d00031154404070012030b181d841200020300f460b841d02e43c0e80342c00a078100703c11200e009110420882c42c040610207541d80c03006080090300ca900200d40f4042d45144420030501c40303020b1494002604101000c1021075064019008845071031000380041d00e035054040d540145191406942e241e03054000604042200c03501c002034078000c69440b00144001d840e40e454035410034000d034501e07901c202c0030b004201a0412640754810f059150042c00c65050a0b0009103a2003802c10305441056580a90805692141c0005142e0710f800c0c00300c8001c9522403802030031290001c541380c0055010315110400004444103200450b00030214a9480012501d808410364149200003659400559000401d01c544031440d40400b031406031280544070301d000c01c00101038070413000d402d400b10340f0842c14a1000407034070748141c4549a4242489510380d501c03c00300310000c0140280344d5906204400000402c040080000c03c030840f0410b070144090040b032014409648107038855000001c03003a082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 253503516 1250 253502266 253502299
    0xd150b1c0b0f030a060c0e0a0f030213140a0b011d010c080a110a050a0605130b07141608070b0601050403080a050304110409060b120d090e0a020c07030503030f1005 72
    0x712103440d0000344440440d4940c0c9010031310307044450100300c1e88265654003100c2e1090b000300806810800850309190118200449611240300703620000740900c01209840c0d010860b5a041031180703d005550354551842d144111038042c0510030380c2140402c10041d2058420700c03d4103010781d00f02c0780607100e8901c040c005030345120659000c83c5004040048100690038407020034801c1002d668003074001041b402d0b48600b0414229030024002c040c641c03142400150006030285403260307000246042ca0121400d40006286c55403184140c003494100314801900200302c44040601783e03441c001c0ba0040d0040d550342c00192103600c0351340030142405070180035000200b4441c0d0003e5900ca841030f1000340403048001d0204050b107110020480303816440b241411003d0402c500c115298446283c010450100c443d0800350104119009094600b0601800a440b0380c1541d0102c40400400c0001c035000150703682022522604141c9a07011941101400b04400300400302e03402c01528401001100c15200720507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 253504766 1250 253503516 253503521
    0x20c0105090111070b030103151415060a03060812040f050405010f0509070201230604050601030515010c050307050a03020c01020f0102040501050f031510030f0c020312010308031801020d150b1c 85
    0x1403407a806482031400200d1205da41901031030086200b00032803c8108041183c0c038059904c9090044a0304010303004110a40121010180f00f500c802e607069940c42d4550042200035191035004120030b4403a504888004c03c104000903c125140c0080100c1c0590702e0f4010030040c4d540c00c0c03181d0701d003402c0c110301c0034011441c0a00c2e10b1034000605000005880120b214134001750020308012545000c840401c0048504160041e180e2054091a00f00f01d18600054540d103440442c40f001c03410400760807168000c1100800c121281c10343c1060842c0d40c00c191078038009695035400c042ca10300500420705401030500f414000c1e00d068900c161035040c20904540c240302000d400c0140010300e40c80740d5000b5041503844551041c040d1030f10329540440c1e407030940c1d00c691054498a0002c10210b6004000101110780403003e45030542e0781c0036840c907980e40c44600341d84514a07640480b1120a51000034612000e10f003c0d031084845c405901000c00045580d04125092400791001c031003c103c0d0681e00c1c80c1006030469 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 253506016 1250 253504766 253504787
    0x160609080d030c020f0f0703140a2111060408040504060b0304080304062c061f030215030a140f0601090b03040803060d02011e0206010f0506030103020102030f0f19020d0f020c01050901 81
    0x1031048440381454505c841389840504240c1c1511b68020000074010703c586440d812941d90360701d50007881079440c56540ca400e03404103608603441c00540420402d100603c200100340e480c0411204940712401c027410205041d51007442100d01c0307a441c0c0030340060030700034030400c0da88220b81201c11039083d0360b1241c852801410aa03542e0761404070b0402205100308040c480004051420079000388075130b1620322020909180380d44019400040c1101c0204016031b112466100b841e1101b500301c68803500c03003500800207404c20620250400d40c40004202140841001d0b45220305400d0361107101c0c0301e64a8030360b0081c40c40b0540d400381180004000040300760501c0003401ca5640c2c41803505442d841c14075541a031b0801c503001c4003440180c002e40010800341c441020700348003a040840301c03503156525650004c3e56034403400a450b8000d002c0440d60304060800081903030b80c03040101c2d40141801101d01c3c8000d448845001c0040c0c0070880c10001c0c0b00311b141c4001120b001581c01030310b50178585005000190341c4d50340c45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 253507266 1250 253506016 253506041
    0x6120201120b040b0a0b0a0e01050c0c010c3f08040201080112031710050906061201060c0809030a0b070206070207030b1b041508061003090c0e0621160609080d03 71
    0x644d07621810035145e07018510002c3c03440410b41070b16031a1079080146000900000c01d81003000a0082e4698003001080d111000704c0242440101e01d011850724080503840c119400403001580d090242c040041c040d10412202100da11854800e08400c00950b920744054030044c0c00031384a84018000f4180550341c1c0386a0394064203200565507540d0707550291504045803001e2038010196010000c0307050040c1c0464002030704440c1a81082044804007007164014810641003003402c05c000414090410b00301c0e00c4400f000380c140c6a429040e410098145d45050b11240c0040c8039010014400071301c0441c03040c080d05e07423240500701a03444000d0b503c03042d45240c015084400ca81000000742d208404041e602c44c280540d00d41c0c20030b03441d0905c10410031002d209c081e00141800d082c1d150307000071507000a05064a03410700702c41c40d03140c84460114201080100100180000080c240c00502800041e92a490003000032040641a29580100c90740c1c245407140c0e0010350b02013a850143c0500031781050595004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 253508516 1250 253507266 253507271
    0x723040e0307061d0708120a030c0c0501090602040f0b090a05010e01020321090f06042402040306090309090f0b0d0b0a02070b01270506010c030f181806120201120b04 73
    0x2e154440d1401c5a41010265102e280036580e03903410000188514402000740a001d0000343c0404044199584103000b5048101a91075900b0544580184070307130860142c0040c0204030b042041e140280095001d40118901d080d40c02c400020038990180469040d1000a00441103051404006442c541140e40c0781c141076000a200a0185c4408848a207440c1e480e1180190500e0620b20949810081104046441604000f0070040403170142c1d08040000e5250040c59155002c000c0c00c660020300860b00001c1025003400358040905501032601c10a41e06e10103010010380307480704801c4040b940b000342d0090300302901040007804035842503c4154403074a4200007502c6c1141c11394a14540c400c09070480700d00e0000e080c44504243c00c04028150210b000c04c141003240e070903c41c0c00a0700c1a00180d800400b042480d1119040c190311804045000c0d4103010444d400554980300d5890000640c00b0441c900365140020024800000b130b0b400001300307034060711440d104507169994a000790900f05281130708142c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 253509766 1250 253508516 253508527
    0xa03030908040b1204140102090a0611100e1608010605030c090c07081b01180f1506180b03150c07031b0c0303080621120a0908030d0c020723040e03 65
    0x44400f402403040e004641d541c04914902440c1100c0c000c1001d0480e0f164682c414485041c42e41c40c3d40c007200003980d0b100d0405407405c01c0c0740c0b80c03010320345403405020ac884242054801c10761341c0c9002400b10981c9620410000340c054441e041c5a088904030700c11160706070b100c01032404140c10700082c681c0c1c00c1007540040501c1c103071183d207070107805502028074200a90f94140c1a40100c013402c1c85035104082c0e90036030319040c14034980c881c2400305501c500040e1022400c140010f8003045154450b6004180c0c03414031000e54201d4682401c014410300703490034001d010b628980a030741c07030344400308900c1408032611141c14000e29032001c5884141e0b0941c418041d040043c04030f004940c2c100c038403a00540c0b203a51b0700ca440d0324000d0f00b80a0550002c0040e034074003a1141119500840000c101820045440b49045440b400c6d03030141102e01001c43e038000041c90000080f51601d041040c0c011488141c1c141c4c08951050b0358505040807040c4000f80d00c0c0d60290840080590705103441d40084052102450440341400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 253511016 1250 253509766 253509779
    0x3010e0f03190e0a08150109110307030519060f0f0f1d09030408010e1b100f030e0a061b02070b0a0503010303050f07081c0f020703020a023312060d050a0303090804 72
    0x7041320b0300200d64542c4610001040a006441a00d0260001d200305100803542c03003d0390034242c00050f10040c18141c940c40014802802c44540c200318000381076081c001d040e6143d001440034101c500444d25a50003403280420b11a00f885804022100320600c0038003910030301c80c10030301ca4201c00303415018a40010040024612000d002c0c0415100003a00500003c1140d07010346418600c0d0200c555004c1d000503a1040e00d01c5030440d010006210050501280b021218501141402c42444000781410b18220000401070b001e481021001c0089400b03c501c5c1903141d42c4081c4050080018000006004100600000b44144d0190062090110145082460700d0f5200e003500e03005104ca610300c001c181011521480301c039000f00f254501e0008030840c83c1000300c0c1c4000b9140c2c251000064060004589006070400c2810411140c0e840701d0450380614601c00e00440c66654803051018400ca0b056002240091600038030301d41115600c0030052140c10600e907000e4024120f8031000361a104001d10000cd0392 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 253512266 1250 253511016 253511029
    0x2060f2203030203070912051015090e07080f01021204080913020c100b010503070c0f110a060807111204150e040e0106050915092710060503010e0f03190e 68
    0x61074070035140580c070f0b4a0b120b0740c01001840c069010554407240d80d0b031908046840490901c2215034294400b04480c400040d2581c84a8859400240310fa480c2091074600d00da004100442501e044409403005050b0400e001800d07070051602054101a101300840c00144001c0006d020140000d803580c02004620490b5108a80120589000f039410100150910310014807400402c0082403d000c0e045003848500103201d01c8040d000240140d240caa15107052140300940500400b0000b003800140a444000040070344a09490400100c0d00d2031f24142c50701500460340794910300c01e2800160a062402c400c0262040d48266201c0a201458606c100280c45a008a640c031844003000851418a04824804600801400c0d4244000e0b48d1103a40c1f12513441d01d50041c3c100641c107180c600d92070f522200100c403402d03410502110500c2007900c02050301c0407a800031380448004500803c040c0103501600781d12040078444000c55030304200824410860703513040c2100e00c5000e900d452050070b903426011900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 253513516 1250 253512266 253512331
    0x50903091e03011805061015030b0f1302040e01080102040303020606061b06090c130501080318270609070c0b0c0a0207080328020703030e06070618121e02060f 70
    0x280301440030f06a00512174200b1905420141000740d4041091501045c00011603142d0702c030000301601d03040c1d07a420350750300c2d514080b44426009188805000c81001c0e100000e520511540104c2203280000248158040c400c0e0350859401d50003500c1196165020032640b6401521080b058050510011080000400420340709054000c01418416000010030900d442660001c01d0307244d05000050104260210507a045003820030140c2266019001c0082e0300f544114400701020400040b50f02000100c0c0300b219800784030b041d960000c0c9030300e61480441c5d4426000d01e01030800c5207101c02003240c2900e010020688510b0510641d50303c0d03a10742140a00710383c0b11111840030382041c0340140c2e44000314005940c04170016030000700002451a940a4110885440701c18454207000c1691424011540c102c1c1c026549911030500c0b500c20b80c3d14248264801121040c00004c440046400d41d0b00c920108405408008d90001c004681c0da035025221f06540080071203101e040c480d49000e449111140d007122 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 253514766 1250 253513516 253513541
    0x30803041103160609140a0e070c02010306061718121204120309231216030e060a09091d030c030d0b03030a05030a0f1e0915050903091e0301 62
    0x4001c25005800c15180040c100003005080c1000c0008010f81604010540110340300c581d001c00c241c60102000442d64015a442480280002000c1051b000d0b40b000c0601c90145c400d0b281040b100d5151201180c0c0032501101c0001a1082c08003c10702d60140004806940d405d0001150306000c00603c40201d0f6400860585103810b0800003400200004113124150481c064982000380380002d444412003500c51050744036000070f8800e050b00720000240704d085410f182d1520311907a0cc4e0001103e0303046104440c101900060048888020f10380b501034126564683ca039584c1008960401e010b10f4007e0004404080760804c03101034100a1403420f1004c1c119107103011010b9502d80560010780c0b03003540c0701844810f110703800402552410540101c1500d400480c08507000415101903103604000b04940034100303140030105a4003051412603a004860540d205107c0c15242c900b02c10500e1040d660140c0304294150810f00000314242055501c40c80c07002c0c45600301b0f00c0c3c040120b00c046400c4400c0701c81e2a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 253516016 1250 253514766 253514783
    0x11040b03250203091203030405060610090510112401171c0908070f03080a0c02030a050a0503033403091505090109170705060114010e131506090807150903080304 71
    0x345020314045d00010100c01160010710b141d40b900307680321911250000c01451141700307601c0c0d203070441c6481106180043d0801401102a440703401c1e030007815030f8449402c011501c1c0f16400703e514005201d070034414041d40010015122507420160061800c0710303d0b0100354a00e1007802110190044913159056030750800780c440204550030b018903642041d032641c000300e02404818400300002400e40c03040741d4400c541d500c1c00001038521880001d00741a0144c1010304244034003605107092050210045000f10601221321107115010400c501c11401c01401d41c00c280e20a09068203103044c000e410114940744903410b071111111424044c44119001a00d80e000c19079500c820300d504001e00154200790002c408000141042c010f030349c03420b9483e6814081c8034191f802c081c2d1100b940703900544019058500040118006c0d03080303c00d050008001c612a910380c00c00c60031100140e034a020b42d20020648089401400606007042c442541c0025a254801300f0810312280000120700508081c1d406a840340102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 253517266 1250 253516016 253516027
    0x10020d150501090e07080c09031b0325230a06020d0212042402010e0a0605040507060c05060708090313080c0f040515010c0501090501150e0a11040b03250203 69
    0x3564500840d00704906200c12040c0030711002000d0546168405c07418a04002151355000c01d24800307005441c4100c0e094442e0030410760170741d00b00122100003070f0381c01d804448002c8142d10780300000c0c07601d050941c005000b107454103004102c2080f510b078540045829502c8003511000000c1441541d0981c0a10010303007095501038000b590501206000c480c5240c60f103402d080c06d04020002c900b0b804154252030103074101c5001c0c0c0b203900070340008507405e01a03025111102d400d800c000e805130000f203034111224060700e44040f510f035019451a09071182c00c04000c0401c1da95a41d400c2c0c80d01100a092480076100511041c002c503200700440002074503c203c0038007156542d1a0521100c1d0b000d407212030b44917604280821080480e821501c4a100310301b4030f0300e500c4446480c02e250303006000c956030140071542881c44041c03090840301903880880350344407030b40140c9644240701e81003114120f011400041504001c10040d109515001e180c201810040c0c2c1030b0800c0101d07100d0b020710401e03440b82c8400350b04080340c3c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 253518516 1250 253517266 253517291
    0x3070b0f0f100f050f0a090501121518031d0307090c030e0c060904200315120105040c0303260108060106020f0c090112032601331110020d 61
    0x281690040e200d4100b60340194101580025030314441c0c018a8041c8543d09000c840c69681c0c04c03a40340c010304e41800c0030415540c40303400e5108540070324501699410140d016802010b006803041081622070581041780803c919a41201c00001801c03144410120000b81680f03070340c0d01406117100501e8144000101340306202d00c054243c50030b002c004201900800440031481d1030f40d004480040408590009000d2742c81d4211a10988405000c468482004010019001c03c8824002511201141d494452040d100c501c1400e0380d008a80082c202651300e481000081d0080c0200060700303009030304080144454086d240c0b0701b0b00b0243d1007010154405801040016014045800c0b04280c41015081d0003003d10082035019506215190074008810144410700d44984058441d504001400c2c900110902c00014014034080c000d81c2e084100c40f10880c51995841d0307840c01c0c101b1000300e040c1ca04c010400002030b984411340d80762001090144602106610075248010a4465912040002d075100e8460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 253519766 1250 253518516 253518541
    0x140a0e0105070e1002010f050103060b01030b0910030b0c0c0a06051b07020102071a09030304060206010302040c3b040207062307050409020703021014040615150e0303070b0f 76
    0x1655120692404080c01405a80000c1c50f44140600355001820309060300310890040c66101040c0c00000e02d1b0100100c104030349500131081e402c6090303805100e22003021082008144041d514011150400d17142040003d51507218250310400201c02d281c202a0500c1502d070400b0f1b207486040f40d20665071820400d00c2008200501d840c50500e4240f1803c1c045541d00103555204240100d164481d0b1090710400c0e10089a812a91241d10290541e41c50720342d101c002030b544010a0204a100d24241200d01c010b061041450081d8003101d200c0102c040c0b100ca5800010810b1000c0044042d01002c4103e0705290b2118001840c4652154200061501291800303901600d14414032b140d03501106014006250b0b803000c02d450607104429001a6a400740d441d09904d001e0000b04140c21440c1030228001c4a03035001b4680301e00c110301600301030145444507030713481640034814050354510904540311140310901c66103200c6604103002c0e00300c82c50101d19031100d0700340420446a01c0c1c22110b05104001d070b54240407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 253521016 1250 253519766 253519781
    0x13050a0f050606071e021f11030315040504050a02042f090a05190510050a020f0106060225030b1003031803051207020301090c0807080c0604180207080409140a 70
    0x110410071541c24003000142003031151003805803102e01c00d407454480d0b034000d52000c2c841860f801041f0868580c5841c002c01d10307850040c031040c00840d8004d0b1a0070000180801100c0c401d6080f0303100f448003414000100b2006050180c000e60b05403140c80c0148006848038846c9120390407103c110000307100c119142040e45486203124120f8510414070000c09642c0f6200801c00031b40b04101c8000c8200c0c40800c003860188107040c1e200a50000c02c01c403d404c802500036005129540295090318101661000c400d402d0f2000c500c80c001c0182c0c000703941308403480012000b9104000401483c07038982c40d926260010101c60640c1c1d060000c41e4881010001c254004481080205000481229542c0303192a9103840d080319680c18994030100045900440d6020751000c0c0c445680190101c801c1904d607a20341d541c4540d20b02031040390780300d40300d9060700e00d24001702641d00b142d0581c009140e07961101c5a061010b904420000c45803000d05001c00f1420f0340c014040e510340c018240030400d1071454507840d5601500c0c0c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 253522266 1250 253521016 253521041
    0x2418090206071113090f0b09030309060f0a090510020405040b0a181a030d02150106031a2707051305120a1b05120f010608070e0103030c0f0213050a 65
    0x18884018016214031096070082d642002d00d41c0310900c0c248000c00c440030051118070205070300e42035588003006180440036801d07501600021045a48807803140d5503910040d9155812036202e4000030300d840501000159000691a102151100c982e9549524104c0f0f0040b0f0015016000b103014800d90900c0c1c403440c030040004407542540607162402400201868030302e81e100842c0c4911205114650280840c0c02c0c021004c0c089400411007007800a403204075412591001100c3d08000198040c4a80a5051600c0701e42c201200799680400070440b4134204035100d1401e49901000b400490094020b4852054400f0f8a42598908803040d02a14907041030300024440c0850044a4100840000d5810f00c2c6036800030011b958101c42088050001e65694032a9500120740100c098070114003040288001c902c4600900249445000d62070300c482c5c01e80191403034414840010404640b003601c51a40480c041e03203242d001c2c50302c0c54010809019103414012030103a00d610030302805a40354803414451124 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 253523516 1250 253522266 253522271
    0x61a030103120c02010c0602031e1608093c0307051b01020307151a0307080102040303021218010f03020c0318030c0d03080c090f040509010504120305060906010507062418 75
    0xf0070750001e81410fa4041000d8040740c3d000c400184004600c1210203185035981c01c4000c00d07850b0080944450203020480040000c80e00c401003214035400040c90030701c0150082144440c82c0c101e01d83d82424540703454850041500c0c070804c0c0d02030042c040c4001d1903618000d9000c1d1400108281400d00d10b8419140000d04542c01040f00001080384440710081098001c400401c54101411010000d00b281c22890b542c10301070810009510703401540200102ea00c290250f4291829104261000d40503510400d8038801c115070503210251320900c42ca01542101d4100141411a0990658036580141c0043c0006055030f8080d10100d1a0411062640040c1150881428103166030000c1c400480602000800f480103c1c400f074042e5a03200c1600000100076108000501d00445414040c01081d030381500c0382c510003a00380780035902c40c0c0140c502c119005002d14007641c0b101001107071140d100242c280c800f15a036403240d02d03040880907844028500404094421a8144950014400074400c0c002101b1403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 253524766 1250 253523516 253523537
    0xa1e080105090a1d010c02030a02011107020a09090201050706241e14030a050a0809190b160c1e05010f110c100912030908061012060e01061a03010312 66
    0x41d074002c00700c0d5100307907202000b0500030041c1c90280003c1014285001c541d500340180640520740c000b015000d1090a03500902c00403c840442002520032040d0182d00800302c84814030004002d600641000d03403042c034000c1e103400600d440324011640106074940d08c45104e0840b0940c039991103035001000d42924180280d90003445080305500440504c1019080718081d40b0a860701e42e0203025a0b05059045000d0707842134441c03407912881c2940b003500c140b0306c54407540a90a10301182c0d000c3c482c0030fa030316016601d442c0c40c031104d4030302c10310400030b84044030240c801840c049116144110090140c068440c8501c009600707000016040f4a0503d4064080040810501c40c2841001038001680341c4282c9100b0f80160b0215070849414280350890040e41008175910420954864212004c68900005881c0c407130312000c1c5411000807076480381822144541000304007144480d4450f03140811110000a407965940300d060090b00d0000d1281e4403240700120041090101081e10b001c0b000350745107810300401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 253526016 1250 253524766 253524769
    0xb0a050306010e030309060c010219030c0c0b0c0702130e0606032409010603050303010803040f05040b10051317010c0305060d0c17011104091b0e0a05040b060d020a1e080105 76
    0x5010007054103040210300701d22945151030a00403940d010304042d000603581d0b031040750068080c0d8010601ca4081840d0f03445086c00130741c82032007030506191541e5550221071001d41c940318801740f0003a10055120300100132103030059030380409003000b0f01c40070352002c0740303940c40e000202c3d08080c0010802d0f8041d030003249005e07090f140d40c0201410040f1064502c2c1e40b181d100d05005500514907504010002d2000000100d9410400406002107650100e0083e007901d40383e0b02440141c82100018903045500320100800d00781c01440070303103818885c00010714031856880c40100c5110152454190303080e55076210006085a0500516a10210a980103900601980d83e000d45140c100d20680c0a04d4808910400c91540b080d00400351a40324132003600d445035110b0804200401d1169464a80c0c4600f01c0300641c99180184001680b854000f0050482203180000317001c00307040c8c42d04440d41c0c065020084140d5019062000e05091003050755102c60b0107007072850382005c0c07a6134009200203005a040041006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 253527266 1250 253526016 253526027
    0xc100c12110a0f0e090a140106110c090705090a0b03060406090b100507030210050f1801201c050a0506120a08161406070809070f03050a02060903190f0605010b0a 71
    0x20034a1502405004151504035150000700b88840d50120444041c0481c06a098000720300101507002d000000341d2703031082d0a56150740100303001030a5400c02c9616203403500e001d400d035903030244c807904002d0300d083c2c07801000070028413054100702d5100310040203105484c14584506400342025034030400c0034205c401c00290303a1014446001041201c0001c0070801c02d07200340036030700d8682c16a00c4e0a0200f800c2001209054030411940e4401300702211540080c1d00005014411001420035010100142c020207021155408851a00f000c507201043e0750000b24001e00c1540c0c850929440005903505080003001030450038140045d55039131010040f82e0220f0700c0d0904440704003500c03012240c1d502180d49008201107076208032822550080104001c2c240f0740002000c0d11410810b800d0300c15503610362a00b0007030340d041c17804040d00c2940101e080341c00600740200100141d42000382200c28490403102c8038045121617182c1168000c40d61142c0341c04015039805034501404030741c2001c908250300703807000516 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 253528516 1250 253527266 253527277
    0x216030602071b0f0503010c0801150f02012c071a030112020406230414010b070f050c1012050f0402090c090a09020f0c070f050303120c0c100c1211 65
    0x25035640024200d040012800701c01096200a1070b0200d2255620440780c02002402d2081501950030000c9140c1414031414503541666901c00c20720102110402c42280c0c400345500030141035650301d0701c0020740f002e00000c0e0484084170003044400e40f041101e410138140741840e40070f041000066059010030010715019030b81507070130395050450306500c01e0000a000c4c1440e58440d12005500e01c1d40140e0340ca008104429022100340d5042c0188401c90545a00a900c00d100e04030701d681040c00b240d00092007e5030000003046c09901240c050040d00340000e1040c10441c43c8500105036484102c4511070802d003d1785600c151b204144007401d141c1600807071005000200980501c44000840c0e0034035a071400e9800c8090324065070215254540b690f003080d903503480003407542003a105001c8000340c0c145a80e100401a500040e02030350402c0041028440148000351038102842d2007032182514444080190390140b03a40303803801080741510310501800c800b0594480d22452820040c0035a070022105003140c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 253529766 1250 253528516 253528523
    0x1110703111002120301351e0705090f010609080d0f120219031e1802091003050a08070b0105060306011d01050714100e030c07060807090308030a051006021603 70
    0x80041c0082c0d4101e080c0ba180b00903000001340040300110744031200000340034408002e0007540e904202803c14804800340d22010400069100f020b008015984440c24000c01103c650125240a0780f0303140000c3c90510111040c40009092000400c603590788800b21034010200305010300081d03145148000e2514661990310750a0000c40101610004840e03030440d003022920415941a680c0b001740010b0107070100c00c1d00601c1c03219041c03401203529249403242e0240641c1e101c4144000701510fa090260b0f0040041a1141340c0360f40b008004049842071103103800680c419883c0a5503030450f8548106040010380005008071030038420420566008103044c0011800300c034098070f08898210049540e8401c2e210010040c50b1140340c15178a0040001d0802506038040009021007203c0003412540c0e402140701c02c404507802071130208440760040002c603803c40c14610703010076280d88a842e1000f5030785c03003961100764960350307541004040b07503c2d2803080c8054003e91010303211507034841003c5004800d1602014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 253531016 1250 253529766 253529779
    0x20d05070c170f07051005102c060406050a080a0506070c03081f05040f020d0e010b06070b060409020402160b22060506060c0a0c080c04060b030720030310050111070311 74
    0x1003903a0f211400a4420841d8007004541c10791740c0d0350712403902504042d11185000042c80a001c0390683c1d45803905124040c00c120503070309070040c90818070f6013024054213454100b90790700004135541e02c50540c40e4028100c2c1c840104070407101854507500d07112004101d0720804c420742c0410000203500448040d08400340041e034424562079200c0c40d0065100d04d45c0301903030062402d0301c003408610054001e0402d0103101c1d1000c10090196220b45400d84640c001c20a41c894010401100007a014454494000401910009100085034082000c0fa0301c035100c05080c085520a84004000c0c046950a03071100c0b46408121403c072030b60b1660a40040d40640041c50641c071032000444540b2204155402c514002007242c071007103024184103d50600034000c80071035010301036500040e428680106821160b1101c2100c1c61759907544011a4401003101c580c03142039000c12040d103961f0f50104003031400345001d1101917096514200004d88261220b0b920281141c001013810030100d0f00d84c003400d91143d034099820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 253532266 1250 253531016 253531027
    0xa0c0c05040b0d0f061b0c0b010b0406050405060a030213030311010c021b0d0519140f07031a0403031e051006080c040905130605010b0406080c130618090f020d05070c17 74
    0x3030303000d0401d4a4205001c51b0094450781d1010f80c2c0a80503103130071400340d80ca9001c50b07620f4032a40440d40c4168007038031004c610104000c03c0340d800c0101c0201210081880c00504200c02c6120000c410485580180c00040001120442e005002c2c461300ca8083c0c7e01d40000c200d0100181007015000e400001444d20441c0445113982c00d1240600552a8407005040e103410a810301d40f5092040e012540c01c83d102e00d2041100098007608000341590a40341c00c250304d83e004602c54075001d2a4020010000c030b04040e125451000001c0725001c5c0f06c000d07950005004505440c0550100300807c803554440c0040001042c14006403480c054111002d5487c24039000c111039440c0c00319401c01521003400188506d00e402c00010b4a12148030103081a01c80a58440026031244021101070380910a007460090020b20010031029000d20350f20000d007a090040c691205685141d039808542d140c18894980710340019450141c080d00c0d1151a500c04001d081c160000c0807140c4902c980d018096501d1007220700001103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 253533516 1250 253532266 253532273
    0x90b18010e091203010e0a06210f0312020310050118030c1502010e0d020a050105060d0201050d1e020d0b090711060106050d020f070f05060117030a050f040302060a0c0c05040b0d0f 79
    0x2000f800005102d110581c0c0b945c0d01d600980201100701c800c01061460600045048600340c40b0300e45400300b80030540000c0c603c0715141d01c1c1e00b00060140031018000340080d1050060114005113105070f885041c18910769180c400094610350041d0952200006c0e1200c00f03000081e000c00004040d14842c40d13000c2e407007642c1c2d100107900600800f40380c4000d610884010310706560780020383c2010188920001e1110f07885190030f0000100b43c20390b000b404910148104144a09a64000c00b4442041d0721421800c0c000018000202d1340001c60740e429064031012445142c2c205402c255030440702a1412804902803c50000e45500c4107006220401a0004005ca0182c11030b4043d6091580328a01c8070f80e59884a1134041c0244500d40300031641d40c095000005400883c44174118000500303500910b250007250002210300b540a0030866111042c00d20001c00962980000b43c1a10100d513110307850040002d06007a2002c4405900c22840b60382000288041502c4001c4500b00c000d501102e0001500703600d14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 253534766 1250 253533516 253533523
    0x30d08091b0604050a1806060201020f0a0f0c0b0702011a0a0b1b03040302041104050306071d04090f05060406150f0621090b040302030a030c02030306030c1005071704090b18010e09 79
    0x5124680c041e10008020a44c40e0810340c80c1c0d040c01b000d50104000d0250b440340c09070700344e015040691803418014800d61041c1c5000c0c0e0341e07a54070240d035880c0207403400007507070340380900c0d40400d481100050b95111201e021020113091030800401c0120740840e8024a400e000424074400c0900d0441030f404105141d9810140810a4034091030b8001e00500c08101140281012500144201071091164501250b5180d00403070720030444820000000081415580034040544880c2c01e044520b00800944240450320522485004921880740402e60302c0c3c07003c01503902203001d41c0052a40d407000310000c1190703c1c2c00c07080c826200d103160100d800d00d0044400241e401020111000b030524020340042008060707000c80140100386458908101182c10765800b240c2c1c80c001101c2c202e4141c0e0044115058602c2d000e100c91000890520b0550f160128542d148030220385411001c2c000310b24041005c1c45061100e01640c40c0d0314106460f50f103046554401e40d40e052039018828035120041d840c011074407400060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 253536016 1250 253534766 253534769
    0xf2401030314040b0c1606051201030b0702070b0f09030d050406020718180b01050a0f18110702190609050603040b070e0415030c09060509100308090109050a03050c030d08091b0604 79
    0x20a0380390480303408070301e4840904a80c03070011400c9091007c10300e41d00480c00e644400c80815000380560307003550b540f211181030142148056202e80c26001a80364005801420b07511047d015454a6103280c2082c985485500d202042c20f00070144014065a07500142100854105070301d42090750390361a0b40000181400c0454a9101c1d400a00d500d041c8210300c0422412a40d0680310740c1c8500b0340e5a00c8503204651607005003211283d145807044d41440d429005600c0065401e646540761906035400203c0442c1c0089a0640101d1034600800490f500803d00e4001844261421440c500d07060f076441201c468000d180d6014840201900203064450b175100c44000860404c8407242c2c941c5901b40702d920001c1c079100d10070009050000108250500405040c040d41044140b0821541165904102500180d000c0740c10040300c410002240d82e20307103000c003000750301810241030340038140024141040d11025130901401540f01c28488004000158110b618264125202036840480d00189151156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 253537266 1250 253536016 253536029
    0x40201082a03090d0f020607090b0d0204050a0e1e06010e1027090b100903030f050d0f0504060b0306010302030c1c050d0203041e0506030705180d050f240103031404 72
    0x4010843c040c140050380002c6010151107100544a680108a0751030300121410300c001138045c5810030038804600003800300700b20840000350070203031650003141c03080d91103034000903410f8000d501340100c039501306400c1800000b800804001c1ea2902d071700080c0010300b6480020380241c001c840345120180c8119040c0c030071200c5004120402c10440e16003681d11f00e02900400e89128a0091040d0191929900507020038030984c880b01c0c0102d00d1a14151031201094100c841400810005461200c40600c00d608240c00f85a00c006a6800d281c240380e021142c102c4041802035100e1001823015070303400a2018810383d41101c1c90360000c2c10741d0105104100092100528078803c03603805003c0c00c1d0b00030010b44255200881031961100900c2c4070740104040c1c030311400d90010300c00c2021440c0d032403107500240110441c0140403205104c100000c14904800510103440d43d4001401d40b00c42903030300b8030040c0050180c031a07982c42c80b07610000d00c0c55004c66040c80000c00340050511501c00340100300c41520003c019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 253538516 1250 253537266 253537351
    0xc150e1c0b0a020a020d020a021e030307060c09060f0516230109050109021c120c060e0a0f0605010f050f04090507050d0308010504060e15010e03010e030a11010e010504020108 77
    0x10b0800208019400202c251000360092030300d04c1180c1803000540e1084650000c02c681c10007401c110501040b542001300c85500b50004100384008035680d406000900d80007a518060031038500180201112060b80e03c4400304241000f10600d003603002a42100303456001115869401380c0980c0441d5010382480030322903554288148442888019802049040d001f968104100003180000e000c400322000c070b00802c43d510360a90107030490f115100c8009800d00c26000081c110b0851495546000d451410448a4010848080e000c100c0d01d801024010720300e0340141c1007640d00b80000280d018400c07880460081c0e646c0e220050510800708251001800041c0a40703400c000d05080040102d0400d0242902403420503400003070b41180c1a0b150341c0b065247d070134003814810321800112000c039405c2803090390564070350b0452014040207100034100a01c42d40c0383c030f50746100314000260a4805844600c0e0299140000b04000340c1d80000600350300c904c54041e41019003111503e000701c1c040180091952119 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253539766 1250 253538516 253538521
    0x81b010318140c01030e100b01090509190c0f02190f1703090c030303060a05130f020301090207111903020616080a0f2c0d030207050402160c150e1c0b 66
    0x10b58800d110382031800010a68881c102e0440065059440e07101c0e07006941e81c40700145214024481d4020140540145400ea0213280d5510009807440415140d0280b1800700130322500b40040344c1c1c461b0040d002013070709204850041080001c1d454201d004403007148500200c01d00d1080003803294400709150b6008202e500c4000203001082143e130800c852800c000e10a03181e900c04d1614000080c1c0748504001454541d00e0350502d014840342501c2c15600946943e11420348160204444c005540603101d050300060b119491420285d410b032100d6032a20f0302440c01a1898030400300c00741e48078420b030703501502c24036510041c540d0713115040340280c84040c0c40400c2c00b040c0c5211441d4025051102c4440302d0752411044400c4d015113a0700801101c04417680080c600d10098514202000e841451b20300a00541c0d101c0c956440200342a6402051b03402a86c01d0720340c080ba0100302598400c200230300038812086d81c10941e882005015040c024140511408540c52688029002040d550031140d600414085160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253541016 1250 253539766 253539773
    0x90302031e060f1b1c0608060610080103080406030c17100e220201081005090f0601111c0302070606030602120415020a200a05060c0c0c0a081b010318 66
    0x40d2520301240c16103000e040d0104081003680c4030418004c40c0c060780042c40e001c4082d5080c004c6940080032043c1c400c80682002c443c1c072030142c0b140320014402c003400340078645001300401046822400742c0d40240252900107002059040042e41c0580380d8a080c00940d81c030700c03498141d6050104420003e8042d50300c20070031155403200d041c0c000407601400d000d162161503d102c01c481c0e00602e949140c020700702800c010700c0558490500345812440c1248a06082c13500e58010456210084810090400301082841940d50703111808a460300a54405486824420710542044007a85200d500c2019008035048090003001d03808480150f5001108640d607000641a0109007030040f0750a031344803103031030407005992401402100d00c0703850300740d0714004660080705121070409034000003d40d140c401d555007540001c004001190203040c01e040000c2e15406102005131034581c0c040810f0f800340b490f0640801010000141800340610a5a014a054503440c0700403401801c18046081000400c0b640b01c0c01030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253542266 1250 253541016 253541053
    0x503040b0f09030d050403030203070605060616060b1504031a19020c0115060905060409020c15010b0c0d0207050604030201111f09020f040603030e0907030b1807020d08010b1909030203 81
    0x1d5420035400d61300ca0b48009a000d8940b80038601c4040d0144c3c008100c00d10004045903c03103584002c000304000d08050f5100d1042810540c0f45404482150751582d1030440d901e408030100b900c00c2c0161000601c2c250850382c4e40c41080755002d04103801c1801500c080341c106064071a440c4e0008900c0b000864446802c0c900040c00303064810346001c05480316031000f04105114018601c195180609910b10b82860404203100030340c000b0001403000c1c000c0010111420800300c5410740205071038901241c490319440c4189051144c800c45441c00e551221408010b1500c0b900c0944040b00c1c0c090030801703205d21a00c80740c5410182801614100b8000036007032005810078a500150310b0a00030340d100c184490f002002d00003140c1b120700000c1c022883d40402d0307050610706200c030964481e4540c640800e16141c204d01080404580d40a81200a141e036010050700c1941000786c0740d1700d1042464018401e524115000c4880c1c802d074429412543c00c0d0400d032003615409401d80000441d0b0282c121000801d000d41e01961 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253543516 1250 253542266 253542277
    0x1205030f07061406011130190809010506010c03030209061b1c0e0f06071a010f051305070c021e0a030b0106030501050a140f0117040506060103062705040503040b0f 72
    0x101c191012500795403240110b61009401d210081403810300507464000e201d07c41001e00d90900100503129090b4a00590103844203034032a681e1400c0c0d5174000100544650f0006240d02841c3e890882008550ba030701c014071381c204617050304005980d262054040341c1244203208101004401000c82c074058a0400221081c0f404100e001c10401c6100c4aa41210881d401c0100310340d020000303900e050054a00f000050424034410100300c046076800500d8085000c009a10070440c0d40d240703035410003840c1880c0035040404c850283c02008113241c01c0c98040c1240090b81400b034010a46807216610080c0c00e20b0400b00c802e06d00400c5820720664074030700000c8050007405544000b80c101400060b1a050580040c401d85400100000d850742c0c011061108255045030032504000c004107045568194440d0000d005600034000343c21680782a5002606031401940600717405c0c0000c0c4c410649039124070284c5070101da14080045401c0d00e40d82000342c91401580c12a0082d0750001421902c1e9103035103030003000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253544766 1250 253543516 253543541
    0x503160e0703020901081f080d050d0b0108040503160c0924050415060f0201060e0403020a02030610140d02040e15070836120c031c0e071205030f0706 66
    0x44a41d59080d004609902404c068240840c000e0004118111003288400515545202d07d10884594414401c0d26040b601030124002c00d000052540700883c0f10b00914032079039428207041509080c0b0307503501540c038802c061580d0800c2282c02180307001c110302c4020721001426928003c0c0582110514003144615014020fa482402c00c00741c0082c03141003600401030791505014241148070300e00401500c00000d031801a2045560740c880104001c090070450f14003845c025802455000414414145010b40c06494401054480c00d0200035600240c00c41045025081d5040342c0b40280e144080381c0540200711007021640180808408a0030365001003d10420b016514040d89403078000c192200d0079a00c5200390213a0f4210400d0010350103428400b0306400c41e1a00488040b241404184405500001d12030391064200281d100310400c1d01e0b0300d41406400115004225422807e840303035a841003540f02c1d001111900e00c0405003404400d005a90814045545496861206160050082480ca50f888 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253546016 1250 253544766 253544789
    0xa1104180f09020f010c060e12030a0c211505100e13020705060f09241005042a02030706060305010207020108010e0708041704080f160b070804061404050316 69
    0x1d44041c145005180585801a2020300318502600c01110001d15088013034603072980302c5e41d2400210a040081d40507980c0b0003e4060b4807070404080c00740545800203015404c10821854440520b110b40001010310f0709081c0d030000300034140c00c3c1d201e0b00c04001c1c1da2010790b00c0540034944004d1660490b80c0c4014001003254010031805042404908034002c444c4045d0a640c40280051064801080714940205070710b82111005400d001000ca0810303110301c80454206c003c4014890004c41c0c45030b883c0058082181c09009000445041090341e0b600711240c0302c400c2003125000d40c60309000340200d40100b60007038070034001e42d51a82003981c040d6010b80412400034010600028204805802c1180241504e07a604d494948854844260000c01001c00c1580580d04000000c0c42402c10041c1142c0c1045800c0900031202c01da508000300401583d00490442c4030421000e00003486880440e405c7e1211800c142800c803241e5401d055583c091030b0001c3e0303018494000862400381560511718115400fa0492 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253547266 1250 253546016 253546031
    0x106181a0d06080607050d0b060409020c0f07061103030c070c0806071e0f052a1f060602120a050a02100612051006050a0302090408090d14060c03041a0a110418 70
    0x83c0e541d90f54088132000002141070210304001603540c0c02042200b17000410441c1001d03218021101264091000401c09901402401c83c50340420f10943c801000705003030528080380d1808a0584030f100040005140b0302000420504100400041002902e8100d04480350352421000c0a030040340030381c5603901e10714100c99070640d005101c1c1c0303400b0321051915035840b41006ca50b0078841040d00e401c202e5251080480c0b40806800041c05c104500582c0300216075800000364406082040b2003654108100b1500410175070320814050008a80d0620905d180c0165280026802241840554144404000d0a04400041c5020000c01c1341040300e00407403d0300c01ca0004803800ca8225849d42c8600b0b40c01c80080b040800c007504e030020580385c0c040c0c0100f80040c0381c000c2c0755000402880b900b04046400d4195106040c4030a4000c02c001684100d01062562450409869048500c0e0341c1d4860312400b0302c001030004807030f40c1058100500680700d8405c01c80c1c44d20b0700d60003414a41f0b20040c40540303d8600d00040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253548516 1250 253547266 253547279
    0x30f09050d17310201091e1a040503150717130302060f150f01091a03070f0309030203030a0509030903010c120c020a110f06040b04090603020108090d02060106181a0d06 74
    0x11007000001d81c840e4044074001d98803c68a003110f0034840240e050000903240000c5221066240700c0e03c824038171140343c50340c505011110b010068415528014a181480184401c0d1000202000000007c0072100803a070390b078a5003110400c003010080d072004003a4000b448541010300c5060b6000034480e409035800c0c1c0c0c1d10480c1081c040d200c211100d50041e146005201ca0b18100b43da2812b00008040c5003158240392199000000e440211000626640c0008104010240d1101c40d546101c2c0305440d003030003404040d4400075541c0c00050700088044e9900c4000c10701c1c1200400c21038804401c05002442039a0b51014060014104502100c0600d4202380b24651164400b161008003540c0c40140710380c00d00d09a4007400312184c6807444442d04070008000200d0380c5072222001c1c00c02850000c070041440350851000406c0c001014102140c21340c000d0601d071020503000300e0b0300d0307042d161107250816603402601c0c01c85200d071174140c2c00349031010183c00403504803142a81c003c0c02041c0414406110312581d4a2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253549766 1250 253548516 253548541
    0x90c06020604030e1e1207140307030c090f0209040c0201060e1602030d0e07050d050a03030b0a03120804021c030801030c0b190f02150109092001050a030f09050d17 72
    0x5074000c0003d0f18040103070106103045c07080c00e180b048090210307651180c0040081000c00352092403d0b40158001c000c01c0050440c4180089034008058010307000d441c5c40c0d070b640d540b010b003014003070312a000e500e4410021a10649505079075022800802c00d01c0210050380e0040e00801c49802610540c0000c240000d02c06c0a1001c5240748000b525402145410200884040186030900910180f4050400005202e50ba9101c21340c500ca0300a102070910718541e0301e0301404943c032000c120390040d4480340f401c00221b925201541c014544a0501100315910391000818001005200c602000603445c2041c0a01d80c0c4060260705032449928501361081c5c0302c0705207201c907000341d103a1020340b2601c01301454480c0c1e114200307a40c03291001c1d00440d000d01e40c02071454840d1080036004800341c0b903030714994001800103844032546042d1300e0300c020030105940100000c0c00c52143d0480c1006068a904060f010041d050740f0a44519030007006450726070b1007240000f0301550315211494020711122010800410340c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253551016 1250 253549766 253549771
    0x15180406170c01050d110307080708010e01030206070609050c041505010207050f1c081204201005300106030c0f0219020d02030a0c0b09040c080105060706110f040801090c060206 78
    0x201e0041405554010044446603c00002e115845403100c022404580300c010145024441c1521030405030b2070000b00c01010034605a00204d5280400c0e8010805601c81408032072025130080c0010800807242d05100e03140031054141da81d085441d080045800702e070031a0444054900903030076123043e2581d500422001d404107044403507100c8040300e00006c180c1012501c001e605880b801e015818030314030000810464000f11000d41d200710303d0802c070b4400c200b00d540383c041010034119004c0112100f02c500051440c0145d504180c1ca9420440c0c2141c100712807220400090398071100036000320741e100d140003009040e0701c041040110727041ca1400e0004900224026000161582a03148400125020002e0306043e046060f80c0500440c070600700490950040800034124004243d503840e2869400d000448860304198010440001c005214550f18401103800c0141c0005000c26a1415684243c00c0d6215000c44000010000100020050019080132010601684004000d03035039861080c2e031948803c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253552266 1250 253551016 253551059
    0x6020f0c060f210405010b0406050108070c06020f0c03070510110f090f01110109060b27062701031b0504050603030d05270a0501050a02041206020915180406 69
    0x240b00e1095a50002d1000d0240440c1d8036840a5900d401c0703061141d025403040e01c05461030303516101c00d080c8a003894052a401800d0a2910107502d10744041d00074a05011010013702646d00029200e40154a1401342c840d40a0f1071800d0303035900c08061a1203562900340f581410119810a026900c82024107025200501107442405103022001010450001100500a8180601054001c4130103c09210b42c0c20054030a24002030420101010400000040c048030244020b40e442129885e90750a5012900f151007501c090104032002105411094000e1164002007001a0000418032080b55a04800030040e20346442c481030311030f8113120545a0486403035030164001c100700d0b0210416540050f6101404a00030321282c000352106160201441c1d10103803442d40828032031000d00000b84503c80e04582043e408616252806144200c04800018003620031035021a444001703448110b81c15009003070102041d070340e820010b500e200e811100e922516015600e002c074003140d9091000c1160465000e0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253553516 1250 253552266 253552279
    0x405010513051b0409020a0207080f1b130507090f1d0402060703030905010c020a02040e010c0c0209071707091409040816060b09071e0903020a030201200f010606020f0c 74
    0x20307440e66032014007009004849504149840b00f01c010340e40901800103850b560348090390b90a40094000d14112040d00012800e40012580c0c0802040000e031078a03003907866030916200841007200003001901c0350350441c03030036505041c208061282d01c000301d80d003a1510044003541c255218441c81c101540444030300580c1c0449900494090314002c009440c6151007440c0100714160255941b81c00c2d41d2480c603510003d0380c402c9028208514050081412030180e460080200d601d140800918a0500b0100a40200034220200b084244900e4480312680d60300d007081a41070420210041807011a44038125050148541e03640075890961483d50103a0340003000e0ba8102400d501c41001c000594030f4049a440d03a0798ac49000c075503140e208071144202d034540c8415050a0b10306001644a070185a10342c800c11112132014001039a0b803038101415290280f8010611804483d005288000c003c2c01d00d1b60503214420400401d23010540164068404035070030f490401ca200c84401d039076000900d1055500c043e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253554766 1250 253553516 253553539
    0x521031303080a1e060501090b07020f040c02031207021e0327040f0509011a09010b1608040305011a030106060e010207090f0b13050105040612080304020d03021c05030405010b04050105 81
    0xb4411442140c0048829400007078009402d4040540c281008030b62000c1c594850004021035038110b8451401018101c400d070740340548690000303042c410344440c0c2d03c3c07149076661042d40002e442002905c0c0032401c1600540d10714100b405000e0740e06d03c00c00307a2030350b6a083e07603a002404ca90070202c140d5a01190006020403444440c550080204c0e20002a107a00f15554104080c1c400c820790040c2d50180050b1400002d140905190381c8052040140000d07004d0420070b001048003d1101e0211586220b901e00d40c840341c44c00b1894461110310490784081c00d41d60a0080907012000c41c0d0301040529201100200f1006035202c1c01552003090502c030340e0b40960885d14040140c1e00b6a50415080c0300d60340780c00080c008441d400003400220b0792400000314140d6810052040303040600c260805400ca20155034000c110b20781d26401107120081c8002d00415940c81d03030904042c006c11449d0902081c2c01c81510076480484802800c503042103d00b51815800c0c1006050141001d00c1041e040c0c48c8040c0c0007135401d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253556016 1250 253554766 253554773
    0x60c0f011a030a0605060126010f050d03020a0602030a02090406030501020909060f010207060c02120d11010c051215130f0b015a050a0e040b1309150905210313 70
    0x4020050046d810322007140c540a591209525001c0485512094200c4165051004e030940d21542034005a0003a0710700e49912021031340004a51140684c400c0c030250340c0c2e6561a43d8040070340191075129400c54202036003c0204901900602000d6034140e94101190340c5c1e000c10040545c0b0020ba07030a016800500c0d081c80454880c0c601421414000f918890341010001825071070810300c900d081000031400b1500c10f0f00c01e2400e0085c0c0c3c07500c00542ca0908d0410b020f00c11109103910003c0c00000e6802c11040e0690015220801081c0e100504c502c4100403103441c041505010b010b040c01c42074002581c00c2c0110400c505440c1c44007148043c3ea400030010780704600d512005400c0310a9542040c0741f64152698070b09070110075030020201061760f80756203c40744484060155503510005511071410803101600c143c0b0303000d010702418900810003107100310b1907043c541d1030b140d1140d42c5002c40604080b01329081c4500054504643c40000048a4651503600302c000014001034801d840211030044154000c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253557266 1250 253556016 253556021
    0x50103050f0c03180a0c03060b030d03090507060e0f090a02041a03010f06030c050c0601060e01080919110d06141b0c0319110f0f0d030204120b04060605060c0f011a030a06 75
    0x100344c80b03c0304803100b46506455480d046081d503801250343c192187d0f0084102d00f010310640300c4001142c11700303009482040d51529107542d441c1c0120700c01c000e00c00300c051800342d940b11801381c9040005820007501341003214410000e503001e80581031021406200030390518058501f10b03070482c0e106100500c0501e0404130f08401401e031454241080200c02d2181540040741807118500a01c0940c44250070000403400140c201140200406100c1c4c200c2d940701e081144c8180c0e01c10303e52365401354118603020f600c0800030b01c48030b07541c4078082c0015180100f41c1055001a8107000d000758440442d41041603000c1801c1282441400c82c075641d103403c02e0024400c281d5804100d00d010300140c0c10402c00c03c400741c1e6107640c0307005044118a0800d601c0b241107450040c40600011a1081c99460305518050400c0401d0038070303081030300f0000e003950107080004081c0181b84d40858003a040c024907a40d41d6440d0910f0440d03560356100030003003243d480c082ca01c1301019800d050a805c0b40310050302600c162086078945000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253558516 1250 253557266 253557301
    0xc0e04060212150114031303121104080618010b0105040306090c0504050901021801110d0c11031f0b030304031a07022104090e160e100b1201050103050f0c03 69
    0x300e060702031041c50540c00011400e1071003a440d8481c102c07480b880c048001003444000c1c0160010480040003444405400d59442644040d050304200c0e207074018185084000340a44082010b600b40081000316603204041425401182c0100711044403030740c0640141e00303c03400e2201290109404120030400520b540d00041d44842c0136840705988240e690011a0507504101d560b2034050754000b54120055008501100c9454000c0c40d14182a003440c0e14040c0d034800c0541e4489082c8800740c5480c2003082174141600140c00384c05820340d000803400320f00060588030510025144141812020591401c001050320101c2c1c1e084a00c400010700052404122400013030b05440c00c40c020315000d8210308101c04000c40310000400c82c034540d83e515045880045a0104400e400d440d04020071381481e1080d0003003241c0070340d25240b0102e182611075001840c0183d429034011428440041144003058980c00c0348203048450a1324107003c182da43c0c0340f40c01e6422200f120888071442c0140007007021700059501034403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253559766 1250 253558516 253558523
    0x50306120a020d1a1503060712061a040611060f1302010e09040b2a0318150f010e0c0306010903031b17070201091203080f151206090d020a0c0e04 64
    0x81d6031440580100b120707000c1c4100141d0b40951801c01d0200010484002c0e251301041030080c4140c07020841d00000d4545101030800400c000441c0c2e042003c15105601620090004030701c1d18502601c03540c907030065500703c3d00c00c400100d1118130304280f4036070000c40c00307501c03c4d81041001d01c1c80d0f64400652000c2030349580c500b80c0c10084105085a201e486e01c50310940164010f00c1111498641a40c100b102c1e00d4500203050414501440004110401035054a8209401420a41c001400003c105107003a042625801c10100381a0030302c030104200f01d04041c160b5040d142400790070b41e901440303500248001d41e0751a0000f40700e80320400c042403003071040c135011111400000314501d007280c80d01c01c010041c400d111103900c440000c01600f15038010502c0001040c2c503114540c00c1140c0707901c0143c08110024205900110068000744a5181d200800b03046040d0003007609003003003c6080c3e4551b1b50341c0119500c510511500c11038441c01400080e48404a80c2e000202c0072016082a5501003010b0010704101c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253561016 1250 253559766 253559773
    0x1204170403120210060819080903010e030301030b04110a080a03030c02030d021c0506010f0909050403050f0c0a02120606061b0703020301020f12010603050411060912071202030c0405010605030612 86
    0x1100040c1d644250307442c440203540c01081315070340c00c010b560b0032a411940f00e0095a0310060313103684032942c14050440800c1e08008020380b902c2460020a014000f00f5021201342d000c00000441001200e040513030140303000c0e02c0c24140b84509030017484980102c600642000354010100540024426000b503005d00310305106a030705210182040c40d0591308103400e46505003111190040c0c0c0c04280d8030030564016405d1134080b41d08681020003500310802e50040c001050748646c0000d06041c041e0040320fa4800001c180195115509001191200303c022000c9210380030001a164a140b00010070501a10006101620f400001c2d01c1c00796080500d1607039810a030041410000140e902880585403100b115213010366103001c1480b50820702001600030300d09051038841440007098042026114a28041c2c0c0c203103560303580e0b0a001a181d221074851480c1c80741b082503004900f8000030040106800c0c0309a04a50601c00450100070a4034024054080060014070000305c052600b981420600030b61641039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253562266 1250 253561016 253561019
    0xc0708040510030938060603010b0c120a17070306060e0d02041808250309060f05132603030906060f01140f040608070309021f0509040615030b0612041704 68
    0x100f0905016804050000007528002a8642440704141c0e050b210151105d00000b482c1900001b0704501041c0100e00401d200030440740c81c000020002460504a000c400c80d89030328080380020308140ca1904401803a0307454801160105001b406041d0503541142c480c040c11103100800d0100728132000d0010380e030140e120300340c000c0c101c0700740c9000403055809145150364850540049100c50310341100c1052403140c1405050010030383c440482020784249190442803440401c1d001c552500070010310850040030f03620b00041c4440000300e54100e604020304c0c0071110081130060291640012036905940c1d40040340001c0c890b180486151422039014185030000c42144071403083c4c6a000b103200700034a40c0b0001028005641c00150047d401074142c5030512096035a44d020480c07101d4507a0101011030268000340003918080c00c25214040c40c082c00400c200c50b503030480060f1880c0083c0003203021900c0c020703802c0c5203824010b0031129410074407040110951119079411000700d0560b003284045050030f000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253563516 1250 253562266 253562273
    0x9080f210d060b030403030506010807080a110909070c1e030e060a0207180b1806060a08070e040f05010306180206030f0405120403060c0f0906020d050c0708060408030f0c07080405100309 82
    0x444002d44030401c0d40f60303120f160921b0003038111180500258140310241c2d00300300409030301c00400c90344000440c0c0c010404800040300112240140c000c3d00b0381c0541d10707404200301c2ea0341c8125940c00e12805202560031807584006034040e9408508000780000e480503142c0d52650401e68003c050400041c411540803030f50365480c01041d0b06012080103065511000c3d400560300d0040d042c1d415400400356500c0c400d0500340300040051054030b80355028840c07244005103899000f0464241c84a80142c03040c0080003403185901c000340004d02044038501d1a024040c6d000204001030950000e03030140c94603142d031311003071900300058800401c219024440c402c00701121602c0c04014000451060802044c400c5851740080d00a07003c402c0e00404108001c14200800b6a0000740f0340d8811941d420301c1030b0349100c510282c40c10100c254104000302d1060b1800c0c8400c100344000154816001d5840c01e60150701e49191806940c8034081001e001c4450a1200740020328280d038080380b00c1c03965401d0002d81c1008580c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253564766 1250 253563516 253563521
    0x21c020a060c0501050604020f0a03090201110304171e031606020d020d06080f1f0b010908030304031e0f020636060105030f060f0f040c0b040b0301050109080f210d 72
    0x81104000a60a40b011000c000302400b42a4004000300c600390308042c205003801115000e01d01101d810552100440815a40200c1e0344032000c3c0410001d40e5078907030722107402101513501382038100c0c440d01c1901964202a47c0d2015100356440c1628049e40c6041c3c1842c106000c81240002c0a452280e802c0003004814031040c40108a0214210030100c1d450780b0b13200c104c606145d5409425240340e00000c0400d1207448400c03140b5889265400c40000e40c45d09108012a481102c42d00b10740300b28030001040c030003816042002101007011580650014031050304088600c042c2202644025900c81008100c084001d01c102c626030048106801d02d42103030ba1400256981c0d91082c00703180382e410620040c0041c0c203052102e201444100ca000f880c2d28100394401110307441c0e0050510581840302008603080002003401e940051446002481d19191a243c01d0b0095500c2071050a01041c1c248a0000700c20310040740e20908038103c131014080010701001031001e8550300e81c6c0c04061030f020400c01001a2030b80da1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253566016 1250 253564766 253564769
    0x31103280803041a041a0a02070b04020907030f0f0510050303070b07030203180a03090503011107020d02060d0b120c1908030a0309020109050a0b03040b0f0112240e0c03060a0e0a021c020a 82
    0x80c01c6c86120b1802e1803d4001c80c4100c050006480c9034010400000401d04002d1826003099050343c50090aa030b5820040f03004149402103072180e5420104000300d829000d8000700d005240a00008044030349e05c0c4109545c0780308104000301040c05040000350701a000ba03018507031120380c088003c4113001090080c0c030b040640c0c070a01240400c0b0345e86001c1c0000d0400340300c2c503406010300c50711061602d062500003614402000400034403d01000070111082010394210b5000c80d000900b0320269922030380c8034540c5540003040101e00031a40409540b941e4940f103242c00301224440c101840c58001d6540c1300300c01816800324240c0c1800750f8100001002d0b1034806c40b16000304210b015141e12828240303840b007226a8041c0903030000070312140052040002c0091140c407865403000205a07030b00c002030b600b890000c10702c2044140c0c1c40e1401214560840020039042c24072841101074414503503614003440111030300e41d501500c65078803009047c801420503060b618020300003032140d180584603e500060034080e19 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253567266 1250 253566016 253566023
    0x12130201021c1106010512030702060906040504060e2d010330030e16050105030c03070c1704030311010e0c0f010c120c02031b0609010302030402040b030601031103280803041a04 78
    0xc46a01c3d0408001441a1405407400700d91242c0000340e5243c05550300c0c0118000607100301000607000545946120448008020240007441807641d1000c4101c10303801d0441c3e80c50740e503103a00559116943d010341c2e4a28104107102c1d4040304543d0840e20703060f035001e449000b0070404400038902202c7e52a0100d1403135603005250358011401200c00c0080720704240040000c82c01d030050201c0c0070701c25607802002b40c9a114a0304641c5035145da545180c101c950003103140002c0d00070071012059418407803010000f070058901035126100c4020902c41454200c9800003141006900200c510803124a0040e0744001a0703541450a241d0000c05a12070a0a4400420245001c200c50100754070460506014150700402480412442c4d0107258009c90514841da2024604040d0300000142c00c6503260350005001903009011181c2d690b84914002042c2d1008000700c601c24424004244e20103031003548540c4042068800541450788255141041070700060404c48034448044903560000c81c102101500c40d900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253568516 1250 253567266 253567277
    0xc060b061209030408011d07030822030804050f27090a05030d0501030210050307020d0c0c0305030304030906030f06081b010e1512160c0210020102130902090406050612130201021c 79
    0x41c04c2c017802d08650006131004180300102c4501d40800d040442c512045a400000c55992120403c1b0382d819140208603405d0f21440c8051800300c1403054180140040d207a046d10f604010300503440030400340c9011000444400d80812410350442d5201400301c0d50040080d90449041c2a02552120300f1604426008081c0b566524010000c0d49084015a80790100071f0401c2845c40c02d01010080d1902d148020480c103111078581c1c00810011040b251800860300700c2c054039280c0c107051030300906240c85071042c540080d08195150303403462075078401c140481c1e00c40c03001004e042c020015107032001d010011540d4141700c850844006191508618039012840f050701c895611a4414000210381402404403114910101c204c60401034000300307500450340c1c04803101c18000d0b4221604901900c40c418501001420340d1100240f0540640c010b801079450440303091084944540031f000e1503000d80400135418903105000b0907102000d0481c051201401881a40ca1121071101012243d0186d00080000034a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253569766 1250 253568516 253568519
    0x330705060a0614030a1b12031d0103020c07050d02060408030301151101061d130c060e1302180d0c08030f030610090501051e0c070f17030a0c060b0612090304 69
    0x1503030b21402024000c0c4084000071411540b01081c2d84401d01c2d94000d0030078003103400c0500c4a50741c0701c44000040c115003010302e0386c1d0b8055150060849002c2902c1d0b56500e07201400101d5198001c0c020748869911b030f44000c2280c18500010080742184041e07040e03030050420403011408990501c020740c0a410407041c5d10100085421000b40150b5021030b5002c00d5034500041030018040020994924400c0080007003555104c80d8085040d04880080c024005994058001082e582042160f0500c1c1d00803201a510b0392180b221620580c45a49250700e40d081000b01060300614001d6052000b5034082c1c0c440c60707203580e00c0e031356058515408084446044813000c01000424641050003440518840c0781402c1c5003031801c1c0000c0c116008060000030b4441003443d6405035480440c0c180d62a00c2d904000303ca4140741e964444060030404c0703020b60151040e0510100c1d600c03a90010407540032414640d0b0301d841c0a1000d480d214020400c0703200729648898104161024a50601054ad000781c82c0900a1075840307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253571016 1250 253569766 253569781
    0x230a1109120708070902031005040902011110150f08060105040518060a050a0b030a02130b04090204060b090307060504060c02010e1203030a05060a080d0c060209040905061305010b0103020933070506 87
    0x24413a030301c800707501c0340100100490158580301080403608151030209100700140300507100d07074050260049a0f8454070011244a1429404c4040b4280080140340b5001d92124898005030409018620255205000400140c18154083c0d0b034441c0d0480b5404a41e500e200000c10b06001056400311150341c1c8800034040240c5480c030a03110f011204400030461082c00f40c2c049a208440360f5645a45243e88440600668a864106144559000f0420004140c50f812014040d42003550164064480d0707030070218625014074200c034181ca6103034642a00a141950046680c011078440c3c0c55000307807801410740d41d01c100c01c001840c021200e205010134145081414002e160328030307600451050b417009146206942d00318094203006604044056512651640413401516445030b004225100d004100640740c80d1401180c6207a911032002400013100c0500114241c2c05071f074160701c0d0700002603100c007600c100130b65a964210302c0c2050707140495030651001c804160f400024045d00e0507001344003000400b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253572266 1250 253571016 253571023
    0x7022b020a081f1802011d1c050d050304051903022803020d020102040b0409050402150a080708010e042411162a12110913030201230a1109120708 64
    0x183e25420300400428000c007411005658600b400030b414080c030010500c9082c10341110300d81d50988081c01869203002c8260f0508800d69080380b06a0340c1d0700030043e1a01419225030700706c0340115000710082001107000106207158145040301201035200d90a100440b803c9018a5946445540031010318081c40d1414081d0804000c1d0041c801103900c10042030003101061000e03a02500d0b1450000902c654443c80881d500410181e00c026620310b0100310028010b40c08081a071184e00c0d25a1508550f0340c7c0d84400510340c600948005101c00364000d02420840c0803407030701581f800416100030035442203c00c8013201d1584240600d059140c1207840701c030203100e22000d43e141c4a0b011010307400a0260010841101d0001d14010340d5072040b02c00c4041070a00c000d000130400c4590000307142035014203140781001a925498802140903508250a419040b44c1d000c2d101091810048450a40781c1e4511860000804075100d9680380403c00740108030103900e070500c011f030320012081e008003d881d003081081480c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253573516 1250 253572266 253572313
    0x1d0108091903050405060301080c190308090906031005011707080f0304140105040306062606061003020a18080f0609030c0a0f0f0f0507030c080307022b020a08 70
    0x180201501401041000000c1c070465030029400341818203059490212800d00c6a0351180d50302480110020a080001045c01c1202c0d40c003c4640c00240d002c0700301241d898884500c000707058a0005c1c081c1044500b401e8a0f4250f0058004055844a110304100075048600030303002501e845030000503000e80c00500304071001c00b070400d140041c0000d1404248895592050b40628614078241800b0307070b0043c2c5d0280b400c0d240070710b600c42c40520166840e0855201011035600700404000400e50600c240000b011982030f02914014061005100b403c1405402940c0007000e09402c0100c04403025810313001c585644400340a07008041d00c034501000210900c0c001c4058660020f5410422114a821a0000e8405025030f8041c2010b03042e010301c3d09107003004540f04900545115240b81443c003c0042c0401d40b042a40e2048500303480e59a00c60003043c3d681d01460304003d400c003400d07440700c55481aa04070038000000740f07915201c442c4121079010840c6843d03554011b030b503540e00c0099110003c0d50808441030f03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253574766 1250 253573516 253573519
    0x806070c02101704020d02011709060702160303050d051512010e0601090501240504051c0212031305040207020a031e11010509010807120e12070b01050d0f12021c1d 72
    0x25401c0c0c18043d8544a24540944024418000c07040b1000869003d07001f601030301d41746490009024502600507a4444808480c0d100041c000c040703221101005d820000b03000e40b0b800d0307560303181041041203510380289006048803d00b00036511540d0116581d0b82141000c9902940c008100403c1641c4864a44141a00b049034200e05010050003803409030b81407030107880d5804418107c0d1450f41c0406440a11441c1c01240d0006d18200c40c1d100000d10f400c0d4503e01192094409000000b09058001c2e103d004010a5442c1d12200840401c01480d050700540300c4d050004040c01c011a03a0780d40c6072500380c0950140500201e541d960410240070740c07054080320180c02802e1582c9000c1050000801c0407200410079401d2005199203040c81c007515030701941c4400840c408450b402c80e41c240518006d41c0050600b22000034155002248904040b070269a0507944540c20100b041030ba0707510b41040041202a182c00c5100e0380076001e60412644542c6005602c80f52141c04d84003011002c0170b00c100d106040c66a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253576016 1250 253574766 253574777
    0x4270b090a090201031514060f040f060801080d0212030109090302010b030a060b030607050c1207050f0a140f01150e04032703061d0a03030c11030706050609061c1101090806070c0210 80
    0x10031281f00320b04c041440c03041c0116021552415201c07046c40301c90040342c10000100912090203e080b0f0f0b04902c82605807111402150828508210203d0352101c00f00400d060b00101880108401d080d03682148860701d21a0002045003102100440d01d0a1107454003a10f8003034480707a002c2110709060000c241c00034050710b0171501e440541015180c1d00c0742c24007489003d941c000a20281403140a00114050160312030035544111042d0038141d4050b140c0080c1410103000d040c1008890040520441c3d1541c05603003c401881c500e01a050b041e0f5142c0148103138240841d407081d100180c14000e03145d031400650314803944075003819407e091044408500404900801b581292640e10600140f80c16403a03905280110320001c4002c4201c6001c40030082c5d4403140c1c030004c25050100a07072900130621446080e142403855075111020482044075004941c10008a16007841021940d9410f01e40180d00e0103061111045a84082c502e203030810407a44035000400a0762000214a00588202ca612400d85040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253577266 1250 253576016 253576019
    0x11a0102070b0a0507021507030e0306060418020d08090d03050c010c030504030e091b12180a020d1707020a0b0307020106170309060c0a0f0f0507060504270b090a0902010315 76
    0x100b010782c403650416000b40400411428215a90800340d0080a0420341e1134940f100d416150150680b04021a1584603014a10014400b401e092040e60081c0d021416690817841807030f002c1c00302006440000f60b910300020040c0035620746480c501ca540d110f10940d034159a410500000d1400c41d030019051b03d0406003450140000300342d215040d4402d866044450b2121916603100204441000c064402c44070703007000c6240403020704002c18075131240400c03d81d11307510461a07803e29a100c40514000940c41742508804101040301c0c48008180071014002581c81d2007030a0b000540c495100c1c0c1d00590502800008200045074207015a40007050b06080c60500c800b0400902034a90081001c480c0c040e180c04500b041c1082020801d1190058000d5008403d012507800c001a4011a041007914148107400000454070700c100112421501c0c54844540007880610001d030150803240c000e41c88441d156000c005035503482107517045c0543c012060000b1030124510002d0b0540b203100103c900b80d220a1030f030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253578516 1250 253577266 253577279
    0xb0115050a030b03010608011d06150d0308040611040906031115041e09180302060f07080402120a0b15010e01180e130b04031d0301150e07120e011a010207 68
    0x25034107604498180480da85640300301190041c205035100401c10360038000c0010310b04810250000300ca00200081d200d40d540d85c00d5400d000500c0b10f0101c50341140c08040003001291240241a803c14880c1c0d10103c1d0512110750310121b0340c0c006801030046a42c0c0d030042002003000b8400144035150043c0c45004034420b1f69404814503000d62322030400203c444030101030b20410f800c0c0c810f9010340031004080140c0c6080b6039411100c4106984205e0142c0b01d15000701d00031038941e00c0309622855440d0390b00308440d6a20350a020006450760740909142c482c22090100040400d440607100e00c001010b545d10340164000018034401412541c141400414043c1d4556081090400300c159440755400a041c2d40307605a5107680001d0994000c0c011a1420f8140010140d01800e508811440340a074280300c0c400603001c06080365039003610031600a903280810419040d04c01e8140e980710340c003030500e081140d81e548905003da500300343c420241ca95642d00d003480c3c004610724020148010a1000300319803800c2c1130 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253579766 1250 253578516 253578527
    0x506010804080c0708030408010b010f1d100905030118030e12060414070815041a0603210c011d100509061b0f0a020618030a02150a090605010b0301030b0115 69
    0x20700140c8100030000703e440f0014000c02c003981c001c19030881180d603034a0f076483d9207074004c06518010720f00052103131000100740740c42035000070504104100c2007032000140104100b2011000f000b101c0902c0580c8000003200e035401c0c8240c040240c0c00030b1070301d000302c00790303250060000300c030820b400f88501c980750f0078812512030000b5041d6000d0b07800500c8000c850350360804d6a00e4980d890380a400300744100c0500100950781c0740f1b8414043d074401c045c9408550300f0610040750410b0112b135003681551102c8289456807600c1d0307000aa41c60b07042417596161500702054a82510220100050120304d24102c2140310f240400a0100119400c08200004d0414860b410b441da07001070440c4904a5140c004015000d4141d4219038001d103c1c000f8140d40d818a46038080d40b9400d003103c030402011481c00000c44080000b204039224841c5590142411100501044203603c8000d02014425a668003255000950710300c5001e01801034107020585941c9149422404040d0581010a40c0760541c84851820350700b20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253581016 1250 253579766 253579771
    0x19090803120a060b040f1509120209100302040f140f04020102070303080907050d0311011a0a120c05060703022a010e09060409150501091107021c050703080a081905060108 75
    0x10032103000703900c1e4040c0ca680500400d0b08800d001c0301c00060300240c0e010b000d00400044030082c1c44d50b80d550705554001502c030056030388500b4520400140c40100140750608146602c40c8180809150040d1250045000c1341c0300c00c007201450903501c402101c84070300c41400460b40400002c6642c125494241e0000791039103024070004051150507008160440000d2160402070140a04040e80742203071400d004116103500224405d49528007840c25102149412006e0050a000303440121014645a101d00d08001c2250083d900d1214511002c12aa500d51000305011070203580141180b04100c0c0c101044000101c0c00609056440150140700f81d03044014034140240450b40018541e4501005c00c0c003801800c2c41c010000c21000b02100e0241c1d08941c0010f0680d2a013500c10031503000803c40c2188a4032038620b001c2d501000c02e06150f640b2078a04580a0b411a2264013602e240d6036503540c83c0041c40d0444906440400c6225041000c90340690b0543c03090423030452001d0000f0b003410b41c0040c0048074003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253582266 1250 253581016 253581037
    0x1202030411091008031314030303040f030e03010213140a0b030103120c0303020904020c0a0c080d08010b070503040b0403050c0108100e0403030518070605040302040c020f25030204060b19090803 85
    0xb0b0000098801c03c5a03601100100003a00c15240d0301c02d0001c03074141402c1d44a001d041a40000210f00c51581e040000581e803159911002c6031004049944080c0c5a008020307003c642d140d9000c02c03211040c550042c1d9070000510302c404011000b6108241004000e0341c0c160045d0014440620041000c80c2100201421001444c10b100d481a09681401c07006172003055a500c2d0024000101289c03260400508400d234a401042d040ba1415207030407207603440f04400c2c039801000400311001840a40c50000040130036500c83d9003100e280c40d99544002c443c2c1c0e0025401a120b503040405040601d58210401c1c40d4094220101c8840032410207543d80000c01024101504041d550b90016808036200f04280c1c000800f41011610510313501c05000341261300034002240600e05108120b80f0242c00040c090450002c2400903081e40324002d1446445150300b010000b03040d01c5420000000360305c80f0301c42d030405854030702c1141d6a1006c0d21002d00240850000b024810000e050208110700d080c0030081d103004640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253583516 1250 253582266 253582279
    0x121119140f030c0318060c0a1103070203010e100509010b01050a0f1110021b03070309030b07030f02130602190b01090f020c0105090309010f0906080c0c010212161202030411 76
    0x462144280380c6020340c0010315041c00c03000052005540c03055004d54810340c1948101c5540540c980300da01e0312640f0540d5030311010344080c4640249a4010b2807100c0c203261140d412a4200411a0002030940301c82e03107055a0141c010f000c1088084005002e0f0a92000c1007100034019503204400003005441484205800c100c801c0d00c007414200d1240d80807040713158403001140e00150400c10b85400961042c17242c084070071200b00c0c87c48075410001c0180d81c920740e016103580c0c00303c038503540b00e048189100074540c20815603641d40c0c650742a01148094441c0c161a4455a07522034140301c4080d140c80d0441f5628080c2c441200144400205620301090559401150118aa581c64070f5520301a0143c42c03540000c55007000201321442000101500d8024402da85030400000024001c0e1844111800782ca1b0015010200103459180c14a009042c01c2c007024000514020711884400c02c048402c0da040f51100380356590258015a0203215040e40424500003141303076003010b54408006140c1d4280b10303802140d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253584766 1250 253583516 253583537
    0xe100b04350705010e0a030b04020405061302040801090b0123060903010b0a0306090615080c04051008011a01030f0c0206130501110a08060a06050301050102030d0914070303121119 79
    0x4128074440e16804036010451003400400007841600c40c68140203050000341c3e0507851400341c0c0b4007401441c08894000c60454019142d60f0280000342600808640d0440d0950140520b003203031034401440104550400040c8005580c9082e91100704182c0c49001d05402d0318080c1c003005011410801d501300c0c41180c41c203558405100c007090142a0101074a41d02104619000050044070707000030b1101c80c0b080004200035055421041c949258900a00e0703555400b00b41c0103400c27414183c0c01190400e0301da006c0d80c88115900d0352100e094035155000214900c8052002110650b014060400b15020545083c081c0f000040c1000303581c1d110041162000c2002c180110091102c203501126042c1011032600790340c7c22200c01e010700540ca0590701d250085452100004100e8031400540707051b100141e002e1840c050320140744038040d00703603080103658590480d02c1c140041501000500001c620a40b80d03a0350314401750001c2c9080301d40407130704250f2905042107001c031040000130106400d0750b0681440c00825 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253586016 1250 253584766 253584809
    0x3060601030c1d150c010b0f010f021903050906070609021206130201050318030a0504030c0e01030c0306090516090c0801091107030503220809030631080c060a060e100b04 75
    0x145139900f0800c07107407800240c101d000711040d0070078080d40e0720540724080c03000c030130000440b55545401505001030f002143c441e0302600700342c44441c0c0418004c1c0307421810720743c0c0c00002400b203620107e0111007042d614498007003142408000c3e0380d10b428450014002c01d1410441c0801406209680241080340000000f10340d64051101148140070306000c032504c0318602c0001800560140c041a182088440c0300091920459402c0c40e0590303610610f40402c8514542e22031340940311700c12048485018081c2110f800103243ca20711001880d012401241f41d2811100241900e803043c1c001100c15406c0c0944919100b840c901103940060307040c03501c40d560b9a6078a0701e0381084412901601c0d60400012043c009100404000c0c100112040302540c0041e15425604d500f0245c03c007841e03140f00000783c1e007000b00c0312556140c110b40250003180824a05550030303044508160046031808442d80c1d50b0b00d0103003c2e03554800042640240501030004000b800c203003071804c65014034810440455480300042449 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253587266 1250 253586016 253586029
    0xf060320010c08031f08060c0904110d050c03010501090905060315040804090603240b0d080a0c1b080105090a1a07110604060515030a020d0615030f0503070203060601030c1d 76
    0xd450308403483c261642029985904105010b8000700d50117028014007142c40d040c080b41481c0644241200c00345041110405c2c04007404403c500542c00c15018801428040040e00406100700d80b0034141507907030340c1050009445003806811029a242c030749400c0000c0c603140005d20070303906060b140c03501a4940e03d51a040c0164420350b008503003032a051500000c100560f0300103405101e0580000e05e800d00c00b1a46050003100d0b40403010690004500c0b43c200c000c95081c0d030051040b4002403401070081d40c01074807441c1d13081e50000340f920f900f240c0e6154100640e10081c032640e41c1040c9000d0185c99940b4064585000c000e04004400010140d0480410222400380000307100204508080c0c0c1c10900d01401c00c0303c02000100c070302003000b041052a03050b8034075022a10020310b81d40101034105180b21511440020100d002da0a40305050400740803021440d02c1c04403541688c030039402141d4900e6240b042c14104034002d0403084c10705d0f0a002640c81e406400450045010003d680108a41d80303410001415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253588516 1250 253587266 253587287
    0x50d0e1002070b0d0908190801060e010e0117090304090608060103020a08030f0f0c0a0b0708090c2b050f031308100b1804171b060c0a170709081e010f06032001 70
    0x480c030fa0540f07c0e60625812040c62812070716a13443e1049051780c80d50065540c00079080d0418006170b541070070215101140c1303807801d4022200c0d0302180d09003919210304400b10354254001c1c090b1540300e44010001c51410012400c003030100d40000e94104006080c06600c0350040b26485c592121020800c14041c1c0410803000d0310f400d8000c0700d901040d040202026081250658080742d0b6030107006503e004a003001006950b800940790590044401c00042c18440941200001c44160050030310b14529002e00300003512000380802d9071b01003641c2c682038820b8985a400b01041e03400505180103802165502481412070034400440a00c0b039903521314180742c0904a0326010301e40d00d10702203075004109075003003112210088008111100c0791210050a0518040c0c00c0300000042c69501d1140c400d8114810455000221400d01d4003042d40c50b40140b0742040341c0e151800b210075607058011a0500340901175101001034107501080f0403030442c0c40b00c8101040121500c4402c03500030047e07560f140d1003090180c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253589766 1250 253588516 253588537
    0x403020f0303010b07150c05040b0f0c07060806120f03041802190909180203120c1603050307031b05210f03040b010f05091e0c07050d0e1002070b0d0908 67
    0x2d580c0d40c2c540780c0640241d04484015911202150000000d402280c802c0d850714401c2900c8450034646040300c1d20300c081d440b000d400540201e0922507507000f03080420020000c1d02481d290380009190100c2480400200c03001d622801d41c0c4200d0070002204404400c4400b926404043e410032581c0d0400000f010340b0401000c20041c0300d01c0210080300990148010b4165071100405000c0b145982d10000c04110301100081e42c1900018580c0641480c250010403050f24100b0980744113040d4515003000700d4085600548058100044480402d07600044038401c9082070203542420b1030058407503a589544042c0c810401020311668000310042000a41d10503da078005143e40e24600741c07800094525080c883c00800400d1450041407618160384942d102e01001640064101d071020412004c03400041c0c03101c144504200310080c00305070140601043c14095403100c96910030708070240301ca540c107504c60b104219002080b050060143c490211355884542d24001b003018001410700c007022384190f6503280d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253591016 1250 253589766 253589773
    0x11a0711062b150902181c020a06050703021501030b07080a0b060c0c040c02031c05060418050616090f03060b130204080a05060c1603031e150305071d010e0403020f 72
    0x102400d01c9103411401400b030020000c03e22155844956030f05a018014207162400805000111281020781020b19410121029802124550b40200e07440f0496034005000040c0000f03414000e0540411800d070152024034146d401541c950b03160802035240290241c000c02001d00080350609015400c4050758010080c003c0307a039070580c089441c0c2d40c0c01028507124019030900c1c0d0b51140d014004000d41e0308100180010b003c100c91a40c02ca0401010028102640580d94004a55100600c003410001c450706c50030090849041c080e65050181c01a6030021b003c02481240c00e0007007100d40a03c24003202ea2106002c02c007022050300207507121090300c5800d1825403002c03070001103c000004110f11040d0180080c1d0b95142c5481e010039903107210380080c17003c407202202c1c204c00009100e54041e200512001c002c0101c1e07c00c80e00580c00c143c440200d00c8011200d00104140309100c03043c81806c0040075043c2c41c0c2c1104052044403100020014401d1a0074042510006001d16000b4040d404c000301442094 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253592266 1250 253591016 253591087
    0xa08060301060807080a030201060b0c0303011e08060411040f0509030906070623010e010603020702010c020f03011d06060102100e07170a05030d1a040e060f0601090b070605011a071106 81
    0x5e0566594242c0e90a500647c00d0400000790350340350200310385210030f085000e5842d683c02c00d2802c080781c0078040c0307404070007101c40c00000074624424071259000710301c10300120f142112080c0404c07055451501c0e03006451440c1c80b0134441843c0000045030511003003940c0c46c5441e40d5032802c0540007000f04c202c41c810188002071034143d149400c031508505035040203503403015907600c071751044080b07000d04800240030401ca00e045d2005403800490040303164100a00200301045100002040d00c81035190269643c0c0c00072083c8070666805000341182e00031849810400d40038003d0120356546c00c0da01c210940205108441303410300400f0f1040000c0a50030000710381e65601e1031820b10005141a004aa1888800c41141c10440c0780501418612691044c014844d60301c3d00030440c002d01c0300240c01103060100f130000009600c150040075108003405400300081962420130612241000003546400c42201084000300245c080c5114160039413040c2c401035142c4480081041e507002101c1030420861104988 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253593516 1250 253592266 253592279
    0x30c0705090c090904140706020609030d050c091c050c0301111605010603240c0512070f02070f030309050f06040513020307051606091b061416080a0906090f05060a08060301060807 79
    0x44e4544001b04030032200c6903541e84104a80340c1006658001c5150820041c00001c0406034000c1600000400141e5142003c10000114866a18404517401140c008108018000280035010760800b00390002d100c080389000d5104000c1c0714451038091520b414200c0c0c4000e0080035400344016582c814888000300008942c030081803070300344100d4040141050b4503040c8035440381c000d684c1c0c0d00301d11005a02c1c4030746541405035003101c81520520210f00c80e040c1d0000d4132404502041c00214020b4940e1841e440c18081404620981755601070f0140f20100401c000984410012840610752503074010b86944802000b20741a201d00d401000c00302e203040c070b148018402135600c40c41010748201404018204056003044007451b071840703048042515501e02c07101d0140c0607001403607a02501ca0b01c0800707154042d42d0b040b10a0b0440c0554000140c2d20901c00c0c4082500306440401401c03c0040e28184280781c00700240c25445900f84000801a140c00421150707142508550f0181c00090152a1559100c2c1b9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253594766 1250 253593516 253593533
    0xd02030408040e0709030b04020915060319060906140603040305040905010311031009080910051303050312010609050306190207060e0d0f03020403110f010c05070608100602030c0705090c090904 85
    0x1001c3d0f100b210b160118030458011681c12044960056900c411a034440c3c08019003600c0c024187c280c0c54014071101400b031365501300158411a2000c03e40c3c10341428050b01a003c4481640104448a150010500003100800c100042d0aa400c481941c0d4039900c3d49021101030040e40c1c0104c140b58140342c004010495100417400c40303000e0503001c544000c031100d04100141c1c1c0c00258054120b00c1c04200c0d00200f410042500e15110362942819464545010031400f010034681c0d0084d223554001051119100300401c02d00e50050103e480c1035020182028002a1260000303031540e400c4d008108120780b00c0405a806440c0b0058100c6000c00411901043c4980c41d00d0840100d8000a88100040041e0074024800d032020703a600b00d02010b011145442c00c1c4583d5207415940981071001810047d40050010099030b4044c000c15914414a0b042801c51100c181426410810642d00244044206e4040010313000e011210708440c40c1c4c480b602c0c1c0f800c6001440c8100c1c5e144a4214040d0b0082000b80700303039076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253596016 1250 253594766 253594769
    0x2100906330506030c07140303060a060c0b011401122d060f0b0904150312080606040303080708070908010603080301031a0606030a090615082d1906020d0203040804 72
    0x40856000d141208110300820300d24901c0410010101050a00541c1070060203541d12a9000312040c0c43e00c0c400d0b4488004109400b040c011641e0f00c0001000700d98184102c03600014642c904050061204a96845803c1c2605008541c0800308128200710301741e00c20500c2004a50b107070f290800071012400c1c0f0100b8403160001e800b05c818a242ca0801001c10103600c030b14822107001011510343e03141021107641907036100c1d80d02c2c15803268841c15441c02d052400102000214800c022103440301008540203042d20707100510040c800c602c24407040000c40e4211603400d40c0254070b854900d59544d100a0250740c403240341e4210703800c80d61815001000704285000114140d0340554131926006403503a42d01c00000f10100c412607000700041c0089800c1c43c806d5003255880c1032144c680400c5268003544203000e11a081d0f40480e1440e40071185110808100605850440801e221070300f40f4032240701455555140300c8a88810305c01210945078051040e43c0d4103942c40c800c2074090070366030b0341410700301808a50400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253597122 1106 253596016 253596041
    0x12060301090222111201060c020d0606060207170118121b0f02040c02060709050f1203041502070b0301030f06050606160311070509060d06020a02100906 67
    0x124548400000f400c0c00001011084110980c030070340c1c02c1c13501d040c1d8025008004001066441c805880e041d290705060400c065006403000c01d54a00341050003a003003a24154001c186203030b000c10610104c600d00621810344140c0001e0441c01c81e200c0b400c81c01c0c1c80c5c5025100c10f100256001090454030840d9080c0342e1b408041c41c1020010049411008540c0c54600200030300c21444c00f4424540304081910007010355182805001d0103800381c0b4050305100342e00340031440d903d583c1e5202d04003901d00044420389480700d591f500d10310100b4801b0001750015000302d0401107000207900d8144c904a9402c1840451803d5541c2c45000c001d10016000702c0d0415400c000078020090860301d224815442603850411a070314054620b41480a184c00691041d5070704000d00c840740c0e46e0400b40c4024590420b1300160303207114402e401c1e4a401c4840611810712030400441d4020303c40107500c8604070301d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 253417266 253597122 := by
  have h0 := BRFrame.cov_init 253417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253417266 ≤ n) (h2 : n < 253597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
