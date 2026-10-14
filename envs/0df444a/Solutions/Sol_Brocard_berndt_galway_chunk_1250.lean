-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:59:08.925103+00:00
-- url     : https://prove2.me/submissions/d149de10-e07d-40fc-abb2-b8f65a18604d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 224640287 ≤ n < 224820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 224641537 1250 224640287 224640337
    0x8010c0801120c03060c050705010b010e0303120901020c1c030f02040e01090207140d0201090314030103050d1202070209070504051e090105060a1b031718060c0d090506240303 77
    0x1030540c030b60b007142d4018a4200c0400014894401c03841d081e56030744d0f603507903c0341341900e0200e00b100c0605041c1c505101d00c41d20400c0e81660b000041325a90b50036900f4a2040b0788401400c41c0c064041d6540447e0180508400f080414140748905001e526469809118002d004a004412842540140c02d04150603c0050102c01019002410600d03ca42012003000325a60105c60a03c4560f441c8100180d4587c1c03685014150310500e80302003008408041031855255a641130342e101c07000358061042c41a20850701011a0700c2c1d0f070548004d25006420040c0034500184e0040c03007607029009003486a00d031480720b840d0826105102c040480c1e0080e040000c07590030801004156001403001c00f04000170792525040800c26000415400e0b8441d46076603500c00c1c09850400300d000e60040100790080e41c01081d034500038900090240c0c0000368a001d007959220700c501e141c2d000c2e0061132400740c400d103d18014425841214020001e041c03481e072070707441c0704400c3c44810103840348600b481d103c0080341000a043d441d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 224642787 1250 224641537 224641559
    0x1217161202070f0f050105010807050f03030406080c0c0601030606150c03020d1d0a08151f030209070504030b390403110d0b01090b030d0e1327050f0708010c0801 71
    0x41d9000d1003100c0c901d2909039a13072443c0003008010031a0700d6515540100204001044050301030102155421707903e0300002c010a617a806280300e01030412445001254011403c00e00321802102110150344803580c6078200500a4003203807061030810805a488500001e1207022485461641680500032404034a0001c8842d0744100210048040d100c0008040e65666401c105c001004242c001d0240c0e100035000c0c02a91000080a40c542181840410361a40003035080d0a016258120340d450751079100d210080300c40e0300a540004145a2a0100b484802d03031251381d210403414184141024140c00820b030120362101341603240000f1500034001403000075400d90007100100c80c050007100301c00711180c5440d25031a200307a110001880d6074110798175250070180171441f042602d504102c24020b10450100c0c0c0000c0c41c2c4405d0341800c83d0340d000c100314404280b4401c01d03041119040a07640d03440396400c006803114480b8041c08a9441543e100080320302c0103014084141002e0340b24080c07039138602840b40700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 224644037 1250 224642787 224642797
    0x106120c02010219110c09090601210605070825140702132906070308060607030c06060602030909010801050708040312020c030d0506090928030c1217161202 69
    0x410765409001c1c0708403400c04101c0320b4801205030750314100c00100088030315080c19440074280d8040c0d48441c0400c51901c00000e450b90441350341901d143e80e01c180c0c0c2003401207141c00c004001803030b060801003840384450f40300201728041c44071446005104264003040c5140484404100783c00b0038418411000010a104080e0458130300140440c210205900800000c456480500d0900301e2450080091140c000e5064945100c0c1c090320b0152500b803844d20b01412407030000300742d0342c0b0070f81c00015698101842115826035581d0b2000040c41110348601740651281c022a000c81e0081034088000142c0b0388050080a000c1d60580d21703408480c0c0c455440031600840384507140d8090503003c004060071268100f00a000d216500b1400040c20300b0036904100c11410081c02411041d0302240d00b210340c3c101c84040341d2502d0760602450301c0030740130140b41c1a83c0c04082400c0140120380501d00019407170f0b1b08448407440c030800b642060003a0b561342c958482441c40e200801d1000040c9800300c03980c00542283d000385 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 224645287 1250 224644037 224644061
    0x30a05160e03101508010e01270308061003020702030105090706020f0601050f06030702030c06011511030a0f0320030901020c010c091202100306080a0c03050f2e06150216060503010612 81
    0x400320b940c44102150075921170b1f81001a0726907582d81d40c242e45036a480802c800d02100540d034400c1404a54400421511000c2c100502c151525100b50444c240603a045036242036000e4000c0c0f04915143c0d1010341c8646182c41002d003d4020000c031a905181d0105165041e140001c1c6903c044221110610156810040034102544030400c460600c400c01009401c1c0200785030844900c0c0d07156410802800320b91010503400c404c0d4801d0150305003640c2c1007910b000b80b8076800d1a000503401b5070440004c1e5481c0780603030082d001640000500c0007041040d00240302c03030160b5038020b01103600d400508030740c60750b400c0c031541d404075044102660040c85c01c2c4109115420851501061440e190f41c500350078544040004c440c00310080e141082002003c0c812000c00c212418054108274071903940c003903000c41e03149140c90400c0d1070503030328070880300f4280d8445070103031440e40d0034070019407e0440e02039902c09183c48003038450f00301d20000040040c072800c103e0b07040c0e48099170346028080c410b0840ca00546115a203034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 224646537 1250 224645287 224645321
    0xa0914161706041713290a080a050402130609050f011410050c0312010b07021801080d03180b130c090b13090204060b030a02130f0609030206031308030a05160e0310 72
    0x203145800a517005d01d0701401e8175400035403059040c2d80b0810021a07240070070f8100c030203040c0000f26070300390411255544074000c07130b002040c1542c0307e20000300c11a0460f1440f04809180c00004113101e049980180d200f11114480b030502641c0700d0100c40c144504005100c0e6000503c19040d03110f851003a0050b2240e00c905030220380c10041141c01e800f24144090300418082c0b1004268031080d803401400ba0060f10083c42c2d0489250350500c811075440c1c008100c01e9109258594201a40d030020b03503602182c1150304100c40914a040c81404240c1402c4814030607503186003140da0100314144c0c144940c480b400d500402c814480c00a115407003029100942003070f6405650740c02c000074401e10302d80003035100b41d0152a0044e030301c010584842c0151106500000c00703e461030380c0c050044507040f0590b1401e0300d0f0103c0c2e80076240d0307407440c0c00c502007030060b0b05000301070500c040140300840030107405c02e42c007481e4014030000a01800020840303000d81d6001d54030358180d014142400303842059a00c0105114a01568 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 224647787 1250 224646537 224646547
    0x80903031902061006020d14041806051503130b0402040e01090b060109080610060c14070803040501110c010e04020a05070f1104140403170a09141617060417 69
    0x2410354001c1c0c800010040700310648454900d03414010180d10041e91354044503200d0030500002d42e030f00c0c045642039050002200540e42c60305800c809490040a00100040105124001101c05400309114103801004a245865091b11151007a24403586a0588504e000100f41d10394400c01c0c48040c1007a84c020b66184801290001c0a000d43d8803e140503200c0d44580f41000c000040844040e40c0c00640e140c1c01542c2440741e10344a24400d80201c4800340780034508143d803810144461090000c10704042d21440c0b400041c04030f0080003410883e03000341c0700d00710644071b0703c1d00ca00e80350a441200345000911038015003400c2d1070581e0280046420611340f0a05003a500d6a070004546858801566081c0311500040050710b400d01071090015030000f25014241460b9a029009100554818a04910b0034000420134000c9a200350011a041220110700320503a80c2c0194903101c1c80e80d20f214940d03034105008510054496101c0c0c0084a201000301030a40d078517143c4803d41803012070308004c03110741042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 224649037 1250 224647787 224647789
    0xc082d100312020105073b0a1508190203010e06010c050c030316110a050d0b0406150b13060306081f060317030f010603090b070c020a090c050d0608010b0306040f0809 73
    0x95140b4074907415400020742400c1901020f00500040b440310151a52054403952102180ea081250b1512000441010b025140c03800501503003040d4202038000d00380d90000600840d0701030212801880890741d1000681510001c0c1d41c241d100900401c401200041c012543d00d52152208080c00383c0940c0c180d0340c0200c07482c0e00003070a40d8040ba206481300d4656521441c14080745107052400c040301250300e12661854071011410224842102401d0014404005003c0c001d1a4110b001c0c4a25809001c01e402e64444585815030740002c100a045e071080c1050109005020340300e210180d83c42c900c010102d080c006010000291045c000210681c3d07181e650010018812940c58224881c1c0030304100d48034503100040880c000c40581c03003501010304040b03d103008075034400407583d0050b040d8036207028080c085001184200f03401d644001002c520b084105003109034464003070065400c0041061042941e0b51061a098803480d090040d810340040e00071400040d002500b0b8103141d84501001810848418 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 224650287 1250 224649037 224649053
    0x2040e0102040b09040b1009030807051501032301050c04090e0102040e07050a080a09030c0209130b0705040f08060c040e0601120f02030406050f04110114070803010305010c082d1003 80
    0x58410f0980e202d0200c3d400040749464000c0c104040700685105c0000007000500a0903a0540e01c0041c180280c00680b0406020040c0015024104000c1e0070803401d50752458004181000c02c9010324070004800380c1e05081c4074060042501500c80c1c208103504280c201441e0000514000d481c1801c0c4ed0750801c00000c5084102c420984900b9003600c030b060b2078442400703002e84004401002200010f2900f81c80e040081d420481e01c0e8410354060341c508415544588000300412203841c8080d2a01075600f0800410990160003081544c090f01170500c000f070ba44002e5980e45442c00ea44424008400340414416245c0c032000d03080c1c0c0650149005c070007802d016500b00003110040001d1414081d0000204418002e8034003440ba044010400c241c40d0518285c0c680301640c140641000c0d040114440445100d20050000c1e52046900941c100e560703540c1d240750150003411203290b554045400880003803003507044028011095403001a1844604030b045055000d200320042c84425070a9a401e40480416061 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 224651537 1250 224650287 224650289
    0x10e210a0b0a050705031603020a030902030307210201020a0c0b060a0f09060f061d04050406150b090a0602030f160203160b090306160e011202160f06150f050d02040e010204 76
    0x141d0082809040002541054a0000340500c0601000b00184140c0860005031442e850055280058503801010002c0b0082c02075950040d5241c400030440c2c4003444031402d0f80307460000c000e034060160604109000d900381d000d40d021500108401c40b000390081050803031010340c0200020540f24082d500c0c0c1c1c140c10410201d54101c540310640d103800901c0111480f85050010b02070301e080030407000b20701514000031aa118920a401240c480c0b000c502003003c2074120504503085c80b02641041d945452402c4043d03086081010f1040390702c043c00041250006c4111480e40c0c8101c100d42c0d1070045034a0020a41444c00b5030203e130540319610714140e0b600e1180e040900a0050f240c2c10a580b6442c6c0010185008405841c0c04c4901c400c51028000c03180d0000c01825010500707003010016882d0031170309c440090282549011100d518882214204070f02514000240d0707201d00d0040040030501d501500e840043c500521221b110720440a112714035010500f90030f0584010804500c0388040c039503044c2aa005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 224652787 1250 224651537 224651543
    0x18040b030a05031c0b330a0302070c050a06091a0c01020708030105031b060d0e10020c1609090b04080c0c0a150e01030e0304090e0f19061a010e210a 65
    0x201107005040042c0d07081d007100440d1203130320040c40042c0c551400146078840c10140c0f6032042609400800021b42c1040070121105020f441031a03d80c842c200e03018000e07501c50b02d01140e5040c400040400c00e4039104040c0025908503a03618464141000002414070001d50000040c03000c060200343d04811090000f003844c80e109540c001d440c0d5140000b80f5290102c80042b00d144101c03044814400c80d00e0b840d05882c80440d00d82008500031a40d19001c5080ca880c5505040342503000254060007000c1c000744008800d0300412902d003943da55204071400700c03400c1f030380000c020b805031001040120740c034200584006182e078000d5540095428000034841112540020707020303d0103200310b80d1003642240540003580d0081c2414400111750881c207036101c0c4640c0c001c03030b05482c1e42c84201012400f400c224107048070b511752045801503110104c0329402c0c41944202100c01e1707424400482c03002c1a8011020300300f0750060b11003480080c460f10800200100a10312154843c4144030042c10042d030820a0101e4140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 224654037 1250 224652787 224652793
    0xf0b1b0604110f1e10030b060d06080d0c0f1b09450f08070c061e0906020a12050f0406080906160f0c0c0e091b01080601020318040b030a05 61
    0x68803106000d004810700c2d41e554460b5144039000045210310078a0910000c0c4105c81016071002d090310300ba801010a8105950800000f151030502410b15601203010380d450882107072040701045004556104000030f00a1210241d20002c5000808540f5100c50082da14045482000d4641c500481140d80583d019031a0f0070042d04440f10080c80c40c074564465906101c121078000c0d88800c0300e010340104002c00144030a00600c04c030800d21200105032032200354006030301b0304c00c140e444400804107142050040c0100344200080f65046010b1050300046804a402510b0412250b440f28140040915030b035000f80142082009400c12644000308007600854507216a1400c0481d41c041c0317440401000c00d1109001001c00000c07098002c0e0754211520712501e81808103000525114002805d5030b40b164001c1c000100074042c05540110f030322112440c409100d5856a4200c1d4011034910000b40c40050158100b008800d52801d045106810141c4014001265003003508022a10740104000c0036141a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 224655287 1250 224654037 224654063
    0x1003020d110f07150b011d0307030b09030c06010503070e070516060c0c0c0b0306060f0c011104030303062c2a0f040609170717011404050303061005040f0b1b0604 71
    0x80701c00034810300e1200082114820300000031f004000311040d1001900c50070700b40801c4070399003040340c64095503008d032864005081001560381d80360490b07809203036507010b102d0010a4030f04001403414102c4140fa0003102c56501c40e80c1050345d079070b84010704181880c6540d0114001050b09402081810703090380c2d0303501400c2d00c000d08283e01e41818980191001c5002003080c00500d03034450003907614003a8290030f900e5440c0e084041c5940181000e840b41d0486103c04540001496059400344c2c0c01c07518801c40222007604040340c030441c40c1144503c00c9400341c9000000c03802140e44440f007a0400803e010495101c9100e02400d18800d8100740302d00003d81d0070004082c0301c000e40c03004c6094003e048aa0720308008061011a003510307105103014030029141f420041000c0c0744025000a488201100c0804000c0c0c01c1604107580c0702e501c1140d44a0227800e0001d01c0183c0140700d0401c440c203e0b0007500199042c0b074201000c82d040d50344507104140c410300d1401608003081c3c0040c003046000341d1041c1034040c102c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 224656537 1250 224655287 224655293
    0x60b031f06050411070201110a060603050d08010b2109160b0d1104030308040809010509130c020c01020c181305190c05040608060a0905071a07150b1003020d110f07 72
    0x5101580c0140f03001c3c50a20b038410800301d00900c1500c014581c2401d03d4415000700342080c514008205402400c2e160500e1000004e00c000443c1051113540349c0d5071850026a03c07500c81d100c1910402070040c400303000988ac2101d0f041d00503040c02d038010120a00383c0d400c0014122459903a101140c00c410740780040060300b2400c3e00e50a1243c0700821f03e5010328142007a2650705c0150045070001c201405100c8000344484103603200760100d410036400181640e0801e01d986000300c00400c070500e40f400240c42070f41d0542409600000700c18500640060114225651040a40045400c0a04410708200040b49075400103407081c0710007095141c0907034510000340c0060130300883e030145603401035016614040c1c042c04603503c04a2035550080d411000490007050a02c0c103a031401c0110b07804080705038040d0481e00f81c0400c007000200b00d000d00418003000064800b24440c0101c030510041b0a6000a2080f1040245402038000c1c040c0b43e400f03076000003954900c0c1c0f4420382059014000160b81018000358000030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 224657787 1250 224656537 224656541
    0x3020f0f18090103020915042d2f0d0906020406180f24020c12070314030301060503130503090405100e100503071419030320190609060b031f 62
    0x181c41c0403a05011294510340100d01451405400725045069420b03c0040b6511903030803e15104c03d40c10310140940000e10850081341d004a440d4a140e14105040034440301c0c119151000c4060031000168414060004205070640c00034084001c41512015a040410340500c05007008203459140c0c0c842c6c102401c51151407098041e0003c2c400940744041c140a2001c030655070503400d04007000c030b00c25070045001c4107914000c04195850380c41019a1580c903204080855140c00701c900c50010981042c2e03c44803044c0c1c99000034041c02c400a1818000a8a100b0510040ca840301c1c0c00364041d6480d01507150041801d40300700711420388400070324501c00c00c21007030764070b01181d072210210441440f007a08140000e500d5840e10300c100c0308019080320070391909030b40701c443d220380c00c100e0188042260342e078924000d003410794030b500c0555400000f040c20030700200d0049030410194018402d40c400000c62543c6100040c500c481d800d544c01941c81b1210300c01038900f0449141c0c40c044402c42806443d0346058040e003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 224659037 1250 224657787 224657827
    0x80309010f0f020c10051201081c0201020906090405100315020304020108091b190e01090902040605010503090a17070f150b010215040605090309190f050d081903020f0f 74
    0x1003108100e294109560701142609070701508680d02035141e801c1705c0048403180a042440c895000703000700000307000100001c3c0f200010710002501108103ca034081603080b03020307e188040d0000300800694000d841c0c03a901c0785601c2200c429030750b0307602d540703a46480300114480031052485903400828170040d9030300000481c0e40441040d004180050f40c10802804908030701d201035001e11003101e01070904440506600002e8000346030000295030f540c05c401801f030086024143c0c0224903004000c556544100101d92003844250001c1c44100103d0f80c07020b5000b2885050380306500c2c014041d050001e800c41130000e00c020302509842c0e00101c01c42c100d820032070300300d015000e0641d88050b6a2400103003007030404a81c016040710b40090309955661000b401c521800c580598000c0ca140c00455a5000340302000c000da800d041d100c2c0c8006a1190140443c1000c20180034140c072a06001061283c454004103d04c03905640c6030140c1481840d600d0340c4502e130000b030000e1b020000046008459520510301c504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 224660287 1250 224659037 224659067
    0xd02070e0423100c230c1207020d020d0602030a110a0f0c1406070809060114010903020f12030301062606010806130b03060c030717070509010507110402030108030901 73
    0xc0641801d030b82e401e00841490100c0c64084001c8503404400702000d11880344050710b01e001c24805504802c80003040c011000c50180103580a0702260310001c100d060075260794000010050400c0300005900440a4019100c101da0040148a1200052300c441c000342d11381c1751140c2c0300540c130790800000500c10f0318241001c80b00284800d02481c01900d0340402d5100243c900303410701004c4031219041981c0680f20031004244103200315028001c0c4180d000d1613070380c403d40341d84003071300c5290762590300e94900142d0003292207002403038241003030000d03103494008000e80e034100800402203140e400484070706540099200001042d02c0d0840003440504c101201204c000d1009081c45084c604a0700180090343d0140c01d442c040c0140071003a400840b02c3d50301204032030000500b00d07483d911b1301042441e200c0e40b0442d4003000140b000c2c4c80b2010042e4603142014011031003070300da99082481000045400b6008030b45c0c240c500c0c0300d00c01c184940a4a5510045020302691405565203a032802c00142103046860002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 224661537 1250 224660287 224660309
    0x1109030105311e08040317030618130b190e01060b0412020604080307060207062403140c040501030c14090106080c03060f10080105030115080312090a050f0d0207 71
    0x40001501104048080c9403405030340301d20b084401c0c201011911480c042c2c1002503000c2800000900c84020060001c4034407411000e071105801c005102c44a02094501d81d0700055001220b200e1011a0001c295001c500c9a80c1070094043c1c0b42c461820448081c0e80c005141e404542180306403190600545854190340802404218074182600400384158840c000030b8110741d0004400315a140c500300c6000f08210b40880380c4640341030404000a40c008403040312154034210a91a80d1034000c40001d01d454410388010317001c4c07450b40d141e00b8092408a01c0800b031034051000180490341d920b01c108c0b8040c6024050306125641080d8241c0b00e07071101503009030b209100d42c2004014180d40076400f079a00c580c42500381600c84c3c40380c1000c9071400036400105540b0407200001d445d03040e81d101d40c55038100ca20840080c4003805450455025144440c00799583c1c94004209021546030038a003899000700b6201c045403461012500d0b00d50801c40110160111500180d44d03c812041c0d04201410103040301e1120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 224662787 1250 224661537 224661571
    0x40e1311041a0f0a0b030a020304020a05061801180302100e19170f03030f0a0c051c0203040204141504090c0302120a030e01080105060a0e0d0c08100f0507020c010c151109030105 78
    0x21762411030100900249503d03400100107400c6407104030030a00240406011146c4402040f04803440c14500c1307000c1140001c41e109010312080080447c8441100d0b00070701400d04140c00b1410440b8002c044400b200e4101c0d41ca2114a5505801100c40700010a07603008601100110100a64102107000c80a0225a070042c400c3c0046000b841e41000d40010072800d0003c1c510059007020340b590700415007205e5400c480004c25038048082da800a5102d544226000c102451500d40a4010a58251800580c2d80460800d0140301e0815074080180d1500a403403c4d500d040e42c0c0c0d80060b040c0303280c0c90800c10684d0811800700b42010b0304141e040b12014000d0030810040e60411300461440e008a903001d10400c60100c940c1d502a071130f40307800081d41607005000e4249060300c0d4000c0b0f03030b07031458154602080907203040e84101c00044075101d0207000f0310741580a0451100800700450740c02ca118101901d1182140420b86114080c41c4955a04884402c045075100e680c0134040500b114070060081c1c20900c26801c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 224664037 1250 224662787 224662799
    0x30c030f0f081c05060d03140d1e1a040608030d0b0a0302090a0e0709060602030313060f0c1107140d110a12110a08030304030909020307030605030f0102030108070b040e1311041a0f0a 80
    0x744054452210500c040e072600c0400704010058a0112b40f402c14580c0d0324041600301449a42042c0e643c10b2403580c041c000c01d50220140300c00c842181c070803890150011b1102d05558001a08040c28210000700318070b1805440e900010322107102503035040f1415941d0707003802030411020301650b4001c104080c02003007154074040e40030303480f40710052580d82051034078600402007002c60f42c07011124208003001040100b10165025040740709001c0c03103030b08511988900044000042c55044058a40513240394130700d2069507159005071780f04911050b802151080045030000302010940c03a014050030b005081e61a450042c003004200070381000089402c200108000302e60000541001c6800c61340005030390396a0303400308600610341908980d40c1030003000101e200502054002d50f069411950030780e12942e40c0c3c1c500600451285200305010024074800254000183c580f129185500800390500c1111882000808650b014030046c4001085100030740c0090500c12100680740900b84c5a400c070b0242040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 224665287 1250 224664037 224664047
    0x313080d09170324120604030903061514040c050f0d050a060501110a0f05010b1003051504150909020102010b120f010b040e03090d1412041509030c030f0f081c05060d03 74
    0x36410012101c00e9540703041e0b417078403000d0541d10b6440ea0b80c4143c4040d8102441e004081c8000343c070090b21006d0502c0c11500070315101040140803a11110b0116444118402c148400f80004070705900034403105100452815944030020301d0300440384d4400245600c1c0130a030302000c842d0301d0b4201c5410071510800540d56510000355400c09903400900012044040d0b01d400c0c0c1c00f4081048034103410190f1242543c01c00d5405070007440c0215141c205415514414005102c00c6403061740042124403c4520200420050350784503104860043c0700118541d002007001c1601e010aa48646c88694000140443d64031800e00c502c0c000521304440c14411416080c46042e1340340552501c0910464240c3e03072320410041d04655200c24000c4401c2038540d02d1105440103c4944c20a200f51030006e101e03100c0d210310f028850b001080c1542d5104140301d1159007551501003c00a5010341200c0040c0780c4000d980100340c020f40502941101c0d1081c11000303440e031a8030300042e1400035000d04d01a0b0404030390031000035041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 224666537 1250 224665287 224665321
    0x102306030601031508030a0e030705030a05190302010e2b020a172d040e25082d010f0603050603280606030c050f0102210313080d091703 60
    0x2441c3c0490301103042d03099944d000c034113a40442410301c000104842c011f504400c0c240101c0c541102650005541d90040c180c9039480050014556003014080f81c1664010b050000b145c140648000218650700d052800c2c5400180681200d86417100c1100060a1401c0c0303908102d403598510181104c107555656030036030320b442c1c0821050038550125070510200b01a0b64030b0864003c2c9100494840f18031903061aa135640203000301210038040308001450b40d29031400013415085190398a5942d007500c008200c0e4295400341c0342c2d10101c105440d05581405500009a8080d581c00062480c1540b401110400010315680f1203020b050400781008995540858128142c11070700031115284800c50042102c1c41030060320062141c2d28000001c0b00b8031008141040541d04140e4900e14030000c10401a07076a000112045010b000c54510501c42507000d01d8007540d0050b02c001100c00c0415130f01c0c1d444400c60740243d1086003280f070381c0300662018051045951085044400401d500e5400c220201d08107640758 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 224667787 1250 224666537 224666539
    0xc1a190509030a06050a0509210a0e0a0e0403080906010510020a1101030b060408030408240a0e07050409110406141008070e090f0a0e0102040f0e1308031023060306 72
    0x102007164a1661400e00031115120b078415400c0000d807420001070402841d01717884070300b094800c9102801c1d2070807010200307120802491086d2400c140e11351104845d4a4642c26032641c018031621b82c00a061080300c1d07040780c0079921a0301d42088501d403160406240040c16480705102d03a060740000041d0300d802142601841e508050350b6a0801000c00040c1c000c6c20b03d504046400c88000140019000c50201c013034015030b01c021060300c00010250140312480f21020340035101036032961020849480e05644581081820041501c1d903003a55840001c00b2503184200603a40082c030605100014a070601c52840030304016002c0c49801c4154102041061703c117141a00c042c0308180001c10900c43c0140000c005400d8010529040307450b003a180002044c60a588404a507410035403100d48485043c000c1d107055900300c040d041c150714a8459203441203c1c0140c460308010a80300c80607808070b0402002148518140807600e440603141c407100c490700804c155005080000000c8680039940d881a08494204038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 224669037 1250 224667787 224667797
    0x3070e011418061c1703090a0507050f06030c0306120d0306170d050f1b01090c06020c0a0312051605060906040b010b0307051602061b010c09090203010317070515040c1a19 75
    0x4e440c01440340ca484a200141211022081020501000400714103440c07150055540443d5100d06103c0410b00b01008142d100c207080c80011502c4140e03030003171580040e00405500e21071040200c4a0f0030301407200c960500182e1144028007201c040328921004000c0300308000c1c180b602610308014014050505002d2108100144210840c0506004c11084a210b00004c010301217103031a011141c4090f6106140241c040e150f003182d440d01e000f6150904980d000303401c5410700704440d07070102c031103510020103d07681000d4041d103140841c1d4100a00b41c46030612000074069400c1c542001c01d0400016805207078080c20420800c5510782d482000d8840c00e03078460091800e019500e20009070700c2c4c0201015541c42c5c403020202050382aa0540161820140c25110040c0e0a0b0b241e440f44000e91109000c0035000780c0749505c0308226242010003c0c40d0b881d00820a40b01114214008400200310a550075504400068000d00250301502c84454a07480711310b800c1d601d024003100d40c00e40b01040801d080010300c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 224670287 1250 224669037 224669089
    0xa0f02042003090607030f09050d0f0201180503070605060306251110060e060d0305031302060403140706030c030501060e0906150a05031509010308120603070e01141806 74
    0x11075454407892009445001c80354503460070100302541c8031002c440f0074000904020001314001814420105420341107400f51200200d046400e0b10594a5040e900086650701e03503141485052007004101882d22a0001d16503038140c500b050380c00c3d100d003d456940300f0740140080c0708030214200120003425040d9000c6030b011301c12150050f280c01d035040581d17800034051201003007031a144590010050700c0760803d154031151902414440c0902c08001c0003000b00b001080416100f40c60360005058062005212a181c207880c2d40d00c8a032700d09101440d006950303101030320030701541e5054081c8800310403051030100010340c544900209145540076102e80186a41c1c8041180b50f02c0d924016401d20402c08501a0b485043d107800910316842103c04840e8220080502403162403c950000d040701c0d00800201d0a16a9040c14001c00036000b600e001e80c14420510700003001490914454020250703c500d5032019904c0c802882011108084c00204103c21601046030507a0307013084800034000a00c0700b1541070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 224671537 1250 224670287 224670311
    0x801022d040e07020a060e030c070306270b040b220206091914010e150a12021c0203040b1003080f0d06080717070801020a09030809040b0a060e0f01020a0f0204 70
    0x24031442e044580050601c004000d40d103034001542c429054440d03d020003095010a44d1075489008585441703289030403615003000842e031241c0202c07010040154850040c4000080d090304110b258540071900b20396440204014007620038041548801e40c2d10292070b03010000e44980c080492820f40c0284190001f00701c51840c0e450301001d17003801ca00140045910b040e211192044c00d0b00142e2483c40c0020403000d080350f52030401d00c40e000d02202c084e0705140d0610112440548805240d82c015207080f942c02d0200c40145c01c040b035402221044061030040ea00d04240c2448004004002c20400c0510b144035000c0000600f9035080341d030403070750381c0420a44884881000e00058981c03580070300c0ea248585540814180708601e482000f440012040f64060b55942d14894281d005408014000c681c0452040000c01d01c4140200041400103100180900403c00003544081d160b03005100040c01d40c40941c07006041644080604100900007891000c4507665420702ea103112a030000d0080f51903060b00040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 224672787 1250 224671537 224671627
    0x70b0c03130314010b03030f04150c0b040b15010e03070501030b0a260c0a0311060921160605040e0406020f09030303010303030e011a21100e070e01080102 68
    0x51281c211401e0490703503960b82401e041034942e11188032030725440c10103100b6040c9400001c030b80049058224241c10145408028210714a481c92040300f070200446106001404d28014544107a00c1005542000e0500781c60100ca0342c0450300c00c2605100c0d05201c40f202d20780e400980355040354000d10700801c5100c0c0002c00700b480d0300c1481d8044008950000e0340c02142d02940840e400243d1002e004603031a482c48007007007240e00c055600c070161004e440c0c0c1051000ca0f0400d01c00404010a026041a001c0182c11956500c0b00540e001c030384403035405c0000c0d042003010449401c00d00800a40c50440e04003424001e602c03040000c06440141042d9001402c1c071030101c1c00c1f0003a6034003050010266030300c2c0d41e5039050107806004600d003251095440c1007954001c62100d8901c00c0e2140714080c10a401280e507050b03130348280720700e0900009418403582081102e44011070203118207649054015121641c40e0004068a480e010b0700f1020701350f401440860a110080340b1408201010100c1140b41516015060a9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 224674037 1250 224672787 224672797
    0xc030123063705090f040603080409051e0a091110020309130b04060f18051608040212060c09120705060a0f0302071506180506090718150801030b18070b0c03 69
    0x1024110340da00c01c0b0540d503041030103400c041d00283c505044440c03041c0d0401048501a001c0140044070500060016486030f42c403056000140801007500c40303001c82d000c1040e800c82181c0442c03c4586402c1410100000d1034014042e0708801c1c3c0d4109420740c1c191401039144d00604e80014003503008400118896145908108103a100182003008260b85524605d42000e1030341c0140c0080c3c4010910600071840766103d40c0e0310130f5041459000c2c20f84d0320907104442d40000908141ea10200d03d06841750740300070610103d0701950540520b15910440e90003406030ba542074120106940e08400d208119a8a4040c225008080f0b10f141841e0007444096007940240070b6150f02929000c2c50302e00344a0000582da004800b6510401c0c0c00d035001c40b50111035542680c04c00c507007060b000000140810003580c0034604000303000381c011241d1000d85440e205000d41c0702000c900c4500c005a0b0500041042c4012800700a4100c4103080b800000d0612480300f00c2e64460183c4a11064004001480f00300010140180d813 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 224675287 1250 224674037 224674117
    0x15150302150c06010f08060402010f0e1806040b0406080c0f0307030c1514180118080a050312010f0305060f0a06120606030b0604020406080103110d08030c03012306 72
    0x20000c1c011440089003607421000d04a0305a10840c000440c40b540c1c41c0300224101c4c1d07214030082c21980c2d102e81c01102c0808160b0040014405c0300d9180c07070032507903030b10354400a0041640030b5001103142003404c00081e01d0060192034010b0b0f2400c481031042d030b0f00101d14441810010365016611102c00d0000c40d24010300ca40c4040d0035191104008a01c0146480105050500f40c0e62901805180c20f0b8a40005200e00d01050031a50040100580c180d4042c1e88080380f10b04044030752070705090b0340349034990a044280c1e02c00c0320301d60000104580040940c045450240c103101c00054203a030304641e5100c1d0b460034003612185d0006902c4001030300c1400740342c1080016181e00c0103c0840304882c0e03e460000382001e40002c445208007180010140d040510a8030100c03100b950711826075900c2c5450300f41280c0903410b8042d030401c0e0b040f1181c10215101e080294000c2c0c058607280c51b0f807589000e14881c05800803170b02c1c210022040c5100e0b00280d607a00300c25640c405407494a1003440c00705001407094048401c803049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 224676537 1250 224675287 224675299
    0xc020a02130905330c0c07121a060102060406180c031208010e07121a06030f0a0c0206010501050f0c0f0601060207030308060d0309060f0e04060906080f010915150302 73
    0x45101d036040840100d22801c2154180034541290342601c0468102d0b200404011a00c02032103844002c80030360304541c003440b4661030a4880e030105800c00348541c10062004c614a00e1010030464020410b4101403c4030005021506000d80000d49a000c00390010b0080c680310030400c0724200220f01100f03c8113920003d50b0b070030203a5034508190030f00907021340007000c18901d1000003103400313520002c0b61050402d40c2d1400c00e040e00ea001d00900400580c20074602c241031001f00d1100c0e40d140c10b4003c500178404100100c00902d44851128181c031100240b000454200e030b0010422640c00a0949200c803140b03903200340c1c40d0710440e107030185000c000303000000c07062160703034000140c40381c0110b51302d0b056034001d41e5030310501e80c0d500f418006402c0447d68024001414000100021489080c8032401d135155441c110086480c1d210000d41035800e180c0090040c03540d60042008221010400c01035140c403040300038800c0c80015100d0407c000700d9600d084401e1921845c1c1c00c8040c107204118580995030050403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 224677787 1250 224676537 224676559
    0x20708040510050f040e0a1b080c2109010b1002031312141b03070501020f0706030c1b111c0308040611090409050d0801120b0c090103020f0c0a05071703030105040c020a02 75
    0x50342c0181e1a040c0d0740300d4201c0d490500304c0c40e448c1c251020380c0405844203403108002500c0b040504016a8440030302280c1c0c0111a00c0c11041c02c04400d01c069025065050002c1004129402001800900c506800c0c0c195441000380064500f1400c0724101203a0081000e05d100042505180d4007440d084d40079105140202200c421615152070b01000b201c0078147c040b26030311760302c8031700580e5540d4004110342c9442c0d000480800c0040c0c425045082c11341c05510307084041008585c04505400c6204000310b40105801612006504040303032000b0402040b00300c242d050000c01e841c00341140304060805000c054940810020405c5040f04a8061140280c0304000390348031400d0060b214003244a0020000c0c1d5240000076900e01481100341c2c40769080050030600383c40d51003107851140d00c12510181455000e210b0780d00c10b100c2d080044c00700180c408006c0c000628091601c0c60401025070040d41c084203817028482403000303000003039a041d600150340000e00c4c40c00d0018240d244c040c141c2c4000390700c480349182e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 224679037 1250 224677787 224677799
    0x601120504150509010b010e1302071a0405210712180e04120201020304200a0b070302030d05010b04080309091b071a060f01050306010309031e170a020708040510050f04 74
    0x101c101c10300c507403050422091301c0b031654042c2a1101c0ca0403140c0040c08030b91640ca80c92070020348010b00700c0c0c0f2961006203806103da0300c600304550900c507074500113102c0311308101c20300c80f052100d041404c44503882160480b20740038003c0c0d0075000d0700314050000c800b18400448001d000b0038501e041751700b85940b00d03015a60748042c0c58680c6002154100c0d0082c0684803106000c038014001e41e2702aa905c9490700721065440c2140d03000c01c200c2009441e6011070580d00002d40043e4810003810800d000c0d901458bd00e010b00400301054801c181e10002c2c0f040000c01080001d041f020003030341d0b9440c204980f42c4006490b074a610030213a1307080280c40d6150074000617500301008007241d503078940c60540c400f00b581a075030f071030040084228203883c8003404554100700041542d84a640403011541c400c2c1401c54100505940d980342008001e00b55101203003541030341c15108145000061307400344900b0030561403c0c4160356900c60701e010328490301d8090300544442c03040c03481c06042074814000a0f12101903e55a42d04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 224680287 1250 224679037 224679053
    0x708040f032619110304030c0b0c0702041b030507110c060705010605031c08070503010e0f07210b1507051b010212180103060e090a170c060426040303020709050601120504 75
    0x10503240c0320755103403080000004075404c050701d20950301a10782a089100d944c07948944098000c03c0052540d108010305401a615403007100b014012440140045440c280405012140302528101c00e00c00b002d181556031040010300c10442c1c0320700f0365407113840310701528100d805404103810450b4980540c0180c2c4400c007101c4102898020410383d0f8030109515500380170b582c0d0b440203008002c0048440000158480648880a5004099440d01c100f0120120750102e060340c081042000c10740380c03240403821242c60301001c1d944000706c22440b07143c9030120a548023592910324a0240242800c400042c18942e0700a01c05140200106c803019030391001d0700c000b03d015140c2d14002072404203241c1000410444145907003603116a280c1c000408644019480f05c80440305210f6944100d24010402251008001d111150190b8407441400107403120642c0501e0341100034401411101d0390610081011a500040032400c0354100070000420b0740b60403004803540624020000129801d080a100400001c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 224681537 1250 224680287 224680321
    0x304020a0b030c09010c0f0219050a210b06011107030303140a0b060d050c09060d02030115050f04060315050604030b060301061a09060904090b0405150708040f0326 72
    0x21608005000d07110a41c280450005580401c3c40c2041030060360b0565020710915040c0b00c0c0104c880b5880c10f011903001504070385410300080070705555040e040180d400e000e0300c0e5101a0400c6d2213180780c9198903e00b071841c19201c420303025080d1010100490401d0740202c420407040518101900c107008d40724100a80503010310408030403403090010001d00003000c5807140700c1c000500200060f2a140958812a01412010b07000030800103007004403600503501c200c01030201100380040580c980d850440e803d140464544007440501800b00414506200391804582c01d45680d41000200131020707030120600314241c0d400140e04914005004418030984044041c81400c00320020710803161078800e84e49900400f254010503041051286c40c0041c5004805480845d10203480001d04101c030341c4803122420020398042e202500405203402e082144621050380c03111040c2000000c0d404c0942e9068240c5252400c0941002405007a03000c403440003020b031a403240040c00303820381b040c1054883c0c00005504 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 224682787 1250 224681537 224681539
    0xc060e010606050c0706081302010f02010e0613020901090c090308030a110a0c060b120d0e01020a06060b12100302060a0302030a091407050102070f150302031008010507020732131d03030402 83
    0x18245c00041452141c00c0b168403642c5020200030001565500641c0e0398107a200b030307560a554030380300c007104015803c0008a11030b100480d0849141c0701c150051010034941a00102030440c00c24050405540d040300c0c9040c00ca81e441451583c0e80d641c0c4480b280020010061b0101ca03c40313000400d400102e5001c224111418000c480804c40c401303045080000344658181001525004480407103005d5004004c1c9155010b410300607aa01c01d00b140e03551000716400742d0400301d0611004180c8100704420642c00c40d0f408013814041910f41800d640024406001d0000c80707604164000000803607242c0c1ca81c11011049901106842d8a10140b803401a200d140c3d5001b820300501c9031400000b26074164000c1318084640942c0007010303040c94054110042c0d0310003006000801001080090404400d1081501c50a0147e024141c0b69040c2030086891000307283e0742014150901100c4a14440d0740034110b003c0000807101100304e418004600c0c0b0150905142009805852074140c010b00300e4040019441144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 224684037 1250 224682787 224682793
    0x50712060212010501020604050616030e1005071e09091104030803040b180a0c141c03030609050105040b030319030b0d03020c1507050619150b0a02071a09010c060e010606050c 77
    0x130b02d5100485c0d43d0481160041e206601c01d5020a945850390582030003065176901d00410500000c03d04a8600b034480c40103a80d02650304d004120100b41d010481c7c900c0803100e03000340a080c3d4650300e401003010340603010f03039021503036207640e90300e90f1104d420202c034011544800341a4982c9018103103017510701000c4490001c0d50661801448048002090358100e180e40710101103400c0d810441d200e590740b5650740c0015001400c9a65500a295000440e5400304c0d1217a580403404a0800e50341106844069008502039070174180442e10760f80e804402c2e50207035100300c00001c070a40b41c4504120301400b080006290000d4020003400c052540c082015560003c003a601c5062000c448991307000c02d846080000750198009030007082a40e41540041380e03040480900204a0384950240016005403d5004034120341c0c00181200b41c0c0c1b80c0500a500052003203450740601d101001d07400348954840c0c4444141001141c204440030852241d010041c1c00407040000c01031241c45903005482070703000d03c1d02d0500c070384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224685287 1250 224684037 224684039
    0x3031b121302120d1d03030d051009140708070e0102010908040810110301030203070302132a0f020105150d0618060902011d0f090403020120040618120f05071206021201 74
    0xc0d40000300c1d04000d150345d503100011402203c0503640c215090721641c5501d8081008400440a03442c01040c1c09001503042c902415032a00c2c034007a04844040b2190502c4540e240c0c03c05c1120380e008a60140d00c4503140c1400c0c0b06000b24280102c1c010803110800a1000201182c041600403000440c0d1401110320441040712105030107441031180401d120007549580405011b00050908500c5800000403801d80030880f1421410400d5200703501006400b0032440240180c200c5981c84664101707109154002001030342040d0024000c8601c4103030f680c1c0e0107490320b07503030b43d604000c01680108090040100d034451000c00600d4000050b10054606030700140b02b0700e5104c400a4040d60407505403560080495034440044000c0c45040e15009000780c09555903504074588020700d000e004400c0035210f184042e5954200070001d031500880c0310b0f034000b4025143c0424030921180c1040e82d40b040e50007040c030080300d13052450907904c1c00400e9007045c3c0b2001122a140400c04c40160040d11340c81410400c83c0890b030f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 224686537 1250 224685287 224685319
    0xf0312030118020327030d0608010b04050f090703030e030f060c09090c0f0702011209140109030807031a06131707031505060306070e040204050406030506090f010c0203031b121302 79
    0x213400f0594000801c02400e0150031a014011a08002c800748400162802c04003000700b21003c49103a83e0110005075103440360030110303240a1054907400700c0040001d100c1400e00000c05941d0700350502004051080100d0b001c5000d560800c0080c4405103100e08071100c501d050346000000b50071400d03500340035040000100748041c1d0345100396680e040754245200d080c51001d8004680712000403004000c0960785d00c10b0000813a507002c0050780030902c1140049105080c924005203903410081038642007516049403180d21804c460002070a102d000c41d029625095090b010303000406141e070081d4152045003804800d00000894542c04a0340682c0302c0c10f003001003d03032102007030700c40c100c40031903058100750001a5080d0003418031001c1140c0280c80181002d0722100070508841e156041a140d40e40403d04014405408201c105581f03051000240000c10600f0b20282d6a4040608030204001c07400c080c5d51510b18181094810919400c05000b0f40d505103003070110404c0510390426405008000080180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 224687787 1250 224686537 224686541
    0xd170c0c03030714040f0e0f010b03150105090f1f020d0503150d061e020405040e03070f150216142407050d0605030618060f04110d020f0312030118 65
    0x2120404502862460f0f5522100321108007242c80c03440304445090101160810984400c4c4c8040e1800d4210010300741010b045402034041d05900440e402d000400c00c10010450714403010707008110030308145440e180420f00207400d5680260b100c0360400c600030104a8040400015481c0c0441280c00f5603000040b10a42101d1500c021194085c0b41c0010f00c5079916079090448400c04294080c00e0000340703903110006035100400c9109081000340350041414400d504d0700e0f00c41c168031207a28000031850400c181d9110000e403907103844050200c2c0c0b12040d03858040d079020780480300e000703d1151000c0e403014414500040762036030304801c0e2000340c4520079200300074071001c600401280701c000c07045c07482c00d5a40d4078040780c2c030754003807007071100b801d0380701c550000703141d03c007007040303600941400f459140703501c034141c1096285c40d400038080800b203211103081c0001704e40e81511a035140c00c4161549021050742d800400e10b1000ea0803c0315405102c0d00047d94200c02c0c401020b107050f14220300d00c41e10b00301c8010000d581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 224689037 1250 224687787 224687797
    0x161d0303040501081e0703020a0219020a05010309020a0312020624030604080a11010509071e030b130c0b03090a031805010e061305060c0d18180c020f0d170c 69
    0x24255104010500032913009143c015440140c01107400c040100703141e120035003900190384030000b02e500030841c038007456014030603d50507a0180280c0103a0303240603000a09014100e110f001c0c14190342d01e403e10255203d294400001c0c40d00205910340e18a00f0400003076644000b2210103c045071850024003601b07480c0036207100e0200004005044940761b607100c81e9040d07441404424140840c1280038400750740700380070b05446800c0142c0901030301c900e0a101400008940b951105030700313044007001d00000d10040300044c3c00c0030440f00700c1031600e0210b00d404c183c610025004010103542c04001c0001590002035048100d920941d0350402c100c401d0a90005901c0039801040e002c1010116003001600308100a841400b010400311129565540045071913548034168203445500000c9080741e0381504240c1d07a040040756a88101c0344540741400c0c480703400641455240c00180c8611811404074400c0009801c203030a002d0503a08840c0c4c6000020303000d403c111189143ca070440000140c004001207090755 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 224690287 1250 224689037 224689039
    0x50a270e06060f0619030b0f12070e100e01031b0512070506070203011508060109050f01050f010c06201c09080708070507080a03120b030604051e0102070209161d 71
    0x700854551004000909404000054101c103007400300590740e90300d0304c2501441820b01d440000340e81c2441424041e41491030746d4050b01950505244245011000541c82c1c00c94032035005010440c1c907803c0300c065045032030740d00096a00071188008030511034078050071000f000130707400f0349581d03256aa8140f01c0400b50540307800300d0a17005010108002d003881c178010450944020000036201d03402402100e0b845800c1d82012403244d010303000600c003c128501c5669005506150850700c40e46c036007000074400b82071000c1024100318491000f2010046c041c1c00400301c0300c100c1e281d0480c0d544c001c080d401c81e15810003180f0741d8800c00300e000703c1c0d00445d1013407142031082038120072607030b28107040e64980c00000d600c2000e0071a4075204005000902134814010316482078881e0f507810708615441c08601055035444e1451034441d410280a10000400c005100c10750046c2003401042120b20b05400300d40280a00c0354060b400c2a200d07800c01c0040d030b1004040c400f21031219140e440030700d80c440c1c2201080b200d86511203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 224691537 1250 224690287 224690293
    0x501171b151b011104080d1b24050114010f0c0f020d020d0b090105040624170705030f010b01110a0f0b100504020c212b06050a270e 58
    0x701040490300801010000007121100c200c907041c03444001d08580381a02c0340d045184011505004140c2c060061706070950640c54031204d039440c0700c46680645032000400401c151a26030444140d2210666030003001581c1c5402000250394903400c107054000c05018090010740e1400304140d2481c06240c0490886420000fa410048070307075800d2101042c8448426644501c0c201079110020b000c4ca5401c80c4605031041c0040b4080c14186080c01c2540c0070744412203491102e140c0d0000b0540c01c2884d00c02c040f00c080008080d8011180d50040f41000046c2d0032694150017007860140c1c20302415000340d06481001e9882a05000248040d030b40c954a007500c008003904081c00c094004218405030035500840c00107443e9900c10764600004d0101e034051480a420742c0c0104070100e8196820314001d80707180e408c070700d045860f00700d4000840c102c2c01455031030507000411a00c4118a4810690301c0100a040d010381041541743d146c90301103010a0b4501030170304403020b82c00341440c070308030a50240b150000290801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 224692787 1250 224691537 224691559
    0x801080c10080f1e07230f0a08063d0801060c030309080d0203041506060504060212030a06030c03080309160501090302100e09270609031e09040501171b 67
    0x10b10300c42e4060700c00303902034a110442640c40b001e0f41141d240641440c0e2503546c590031031441804080b00b818450015441000d000c509403114030380d070440348400d21601d40f103500c40e5176100020358084a8100410070314a8032000b030304c0d5024491070b9080400208504025603480d01c2d003a003190070a00c00d004100004031015a010006070098201c5010301e845460b01030304245d01414054100d0304100c0d0180c451f2400501d81405020041c407500c401b510345c62406500d00b50500760080e40e1101f0b41850448580000400142e280c03001e45d0011000c0c0d6442000304e02002d5690803d00c0540c1c0003503030424228090f8006042b0501c1c2c0c0d00030803d0880e501a115003c00703070318680805c072401d000242400180161071030301c44150f95910000038483c010541030b55128007090003d42400c00300c0100b00b80030551180c424400d04100000c16103404a20f03207003800b0300d8240bc0c5490401140909034545400c94101000862000c1101c111868030620b00021249155042c1c03c0381c940f000e25503d40d4a80001175804 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 224694037 1250 224692787 224692801
    0x21201180311071d0610030b060417010e10050702060f160c061814240f0402060d020703090306050f16080a02040302060c01090b07170c160f030801080c1008 69
    0x9074544182c80b048042c2c481d0b103640c51a8240d003282010341e00b20000c42c240b1080040070f01d014603001b0608069498208400080724000c40e070a4402d60007500c0388000c1d80c43e11009a40403d4102e650f10801000170784142d45000b0750b190740070b0700381550500054000c40d0002038440024032101c03840f0f03002c803119445030769024039019561240017480030382d24240c031005000000314a60b4000c50202d841500513041071070041c0c90340d50400c464010021000146128401d02d1032540c3c1401d69040032041c159043c03941c5a0b440060308610802941c0e130038090000c04c1035418150403020074005c4030b0042c0c8050115030342d025105242000c04503142844010304ca82c818101610038600a0391007149480300615180e142d400061042c1c00001852403540c1d103c0511004002240320311780d800c6842d50034120242080c00440c1a208100141a2509110086001540c0381d4000b881311420540000c2100b542c00786509005008030004d009503101d0313201c2c0d424481804e0822040c441e030001c2d050381e074507111511099 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 224695287 1250 224694037 224694047
    0xb010504050a06080d021609060e161112030405120702010813051f0207060f380603160f050a1d0307080f0f0607030605060307030513080a0504030212011803 69
    0x6800c5403180303a41c8001c041344980080041d02581001138005016500b1810600210391501c2c1d000705010030304080c010800f4507285007510340c00c91401205e03490450b81041089600355040b0b5450300c8180300303071290883c442c03d10100542c0a1400360302502e9100d840c0841850f954450340364002d0000780740400180b00b140e00c14031400800d5104006840407000c05003588411000c403400c4119080307500040344000c0000c0c40c420b568061000400034400144002034102c1e101e96142040d03407200304c003001507001d201c00e04040c0000702c02008010f243c49003400c0c0d034040c118100b1071103181c010030302d041d07152400341e802201912000d07041903440041380d00e08182610012290032501d0354040c0300e80d83c000704144030180b00c061429981c44006024940884148500d400c002424000516140c42801e1003181c44041c2142d60000041c14041115143c0c80c0050241004821020b8403030400840c00c50b01c1c05d584000100101ca001f210307074102c5100140c5015080b44c1039400c0e51000e0002144002d80068015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 224696537 1250 224695287 224695291
    0x30f021204060e0a020301110a1e02030403080304051c0e03010b0f0603010b0904020409020c1606110a1101020a0c0b191b060507170406060f29181c0b010e040b01050405 74
    0xf2005072521688150b005c01e01b0764411411011010b00c0108d40003a42070790000c070356129100c0d40310030785d06911100d0002030b44910403808060660400000000c1c14031030104151600154070100b8540e8000340000010117040e0041802842035080500c560028a03141c0d8034465000d00040c030040c030b96460030380400d540364000b04001e03812035020301002410785242d01c040c00d201100a005030446080d10405608040441c0d04028280206803001c030400d9100066150700340c5a0004c020640c000c2800c0040c2c0c5004d41108008012640315500421095260310103040102100d1910304c04161a5031016a154070000c201240c6c2100c1c1040b040300411141d400c60742c0c004601381040d1046603128000d0740000c15048800360349203611100100100c2a0b0404c4043c010b0a00c11030030075000b040707860300e640c0c0c3c40c1e883c008800c004e10000c1344c1c50003500d015048000c00103c0042082c0700c1c00904180c0f6414818207103009440c106020b00001461002402c0024841d552218284c544c036030a2104000c010640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 224697787 1250 224696537 224696561
    0x1409060a0f06030605010b13050a08030304030503040c1203030603150e12030703020403200312090105070201080601090f030b06090603150f04151d1b0f060903030c1c030f02120406 79
    0x840b1400400329076640b16050180c520303604550768a42041506003512126580a940107207000c8c2c00c04c020845020040c1d80c0c021358140343c0290780380c555042503642d0000c550400e6510140b1000410101901070340081c080343d20541d414070903140240b200104031110795005055540011074480d1581c080c0343c0056a02c803129040c01802d0a407251107110324800101c00c454404800513448070000d10b01004204540e80401c84e000d4036040582000030503600035424024103010741000440c6d03050f80900480c03070203486100b111070052a9641032502c1803800035100300e4010102344c00490b64034200450710342070341020740f100720302c0300d032103403910500302090040050b82d82c1e05c4401c141180c04003241c06000840b46055004103200030358180e546082c80040620b43c0061412503110201c0c94030307504034200322644122040e030744450381400420300714401c482100d1814005c103004124911505200d00300841d5443c1e404100c1031000813800c0d412407054044140c001000140040e00103442c0ba0403058480740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 224699037 1250 224697787 224697791
    0x21e0c010c023313050303040b180a1502010b0406050a290705070608040201080a05010e180307050f0d110303040309050d02030a05060c0315180103230f0604061409060a0f 75
    0x3001500d20841000c030042d00b203143c070200241c0910104210000d4002502045010314507091070031060701803522a102c181414070303042981a8030296111800040105138180320b5800b0031005210090080c81c1a0202911032031900c0008100b40c203040e10a1000c3c0c420001d00880424018050740034800403c0c569807103a1601000404000ba9050141c1002011151540b581da810144005003006030300501c625820b500c0c02d401000441885140e40d0f400070f89603441070040721300d40c1a0035401c500c6138100141c03540c0b0a4001c4102c1c40140080e00c0150014199100a00c82030035100c484d85901c02501d001e000a150002c0c1440705241203030288540d0343c401000c6032900c00c00c56494605081c000c46501c4a40c40340482001481c80518030701400021080743c59403502406441040b9400750706000240100881103d01c28008030705013030f03401c030030210f581c21644000e52005040759030365801c0790b003202c00768207010301e810140014100007402000f000b8090b0442d561540003c40007019181d01c6c0c1400b0903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 224700287 1250 224699037 224699089
    0x2040e0a050d120f0e1b030a1406090c01080f040b060a05040c03140901150b09120307050604150501030b0403121104080102040f05010c030f03021c020406021e0c010c02 74
    0x52070411200c40410310030789940041c94140d5079030808944012511011540c20909600c070030700404100c8100300b49a600c5a003901405040100345003400111006021504c0b294140c0354403000041d401307114070500000c0b1640880e92800440720150706840038a5950209404240010503400203180d1004016200c25607556480000509440f003d034189000300e552205856070700200c82c0780c1d407507102007608024040501141b400043d099030a11a45002000200b6242282d46e0f070384940e5900c8480b09000c5079240c0c001c6042c50749d1107520a03901116204111001e8047c0350507540100383c1201e802030700303c031400d03030b0b0399182610b4000c0c03501ca451410f50395403da00820010050040c002801800000685450520302e0011401e10360750002410300c07030402d0f00f500c000f036442000b044120a613881c0140c0c41d01510280c4000c600390705e0f484040c441e0f002040c049035083c4e000400700300008a4400d00c140d0060305400710740e100c89810006a0005608400080140c1007070109800d000700210480c100c08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 224701537 1250 224700287 224700293
    0xf060114070602070c050114071707120210050604063503040830031303020109050703121e0f0c0312060303020604020a0b0c060a0b0d0b1f09021602040e0a 68
    0x2030384299000c82e1055800300300c800c00d020350804182d0103048203080483c0e04080380d0005054500a04500900380442c030303401010202c00708000e4580060b4820300307003540e005503440065105c040444420440b01d207401c002407402e103014092201201c3c100f190f0024540161452401011071070b00c5600000e0786141c00c9124040340800c002c2008152070800340490a500100c45500c011038111388a480b000d0701410410440031100c1120340241040d94403d5135842036283c140d026250148019013503000d610400001c1c0403a083c68603170a00240d03510405112403400c1301d4810b82c81d200400f44e00117007603400b02c61035290142c0f056980680c000d0810b12984401c0072214000c1c0d50441e001140182c110205010450420790108400340c03103049c8902d400c140007100800d0380c90900a08800e50f841e207583c03000790140ca440340a096181d400c92441b40c074500e480c4500781149074480212003c60304425000064154443c429500c007520018841220030040d502000060f04032440e0441d10790042c10020800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 224702787 1250 224701537 224701577
    0x4050a18062012130c080d0314180c0609120115060e01020a0b060d0303140906061003020405030c360a050f0903070f030908030d0609060f050105030f0601 68
    0x14030030640841d241541c00a000c0e00c5a501c0402c40102d000288010810544025800c5030300080c80d13018101620002d06000806500c3c540c400c050b00c0c080d0245408500d80d0603040209040d0b140004001503031184890310045c6040701d81c19a1403a040b00c000312650b80380980050004582c024081c0a44401070b43c0c0003401c654050f0400b2100c44108402040101d81150111516180c00d0024100c0040c882c1c03a1103503c070500520b46440f50701c4240c0313282c0c02c05009500c0190703030224850b44001c6525040103a9544e0301019503110740710b06038a12100c20181e100f4000c54090b42d2000d070140c80f403843c040e024031290001c0f121100ca5a0030343c04c40b41901c11903c001034240e1440c81c0e11000816410101d180720215031025200000c1c0c083c40c0400c1118050b000004c484445901c42d4141401c8001403d00f2148103c098010341064000050116604403041d00305005903810b410082148981d144200f000c80d0585e03201d038502142d0280002003c501100d10469803221043c100070041d5040b03013514050b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 224704037 1250 224702787 224702831
    0x3020d0204080c0a0504020310090506040213030b060f04060b04060503061201050c0301060e0603060108061207170706031a28120803090607020a2301060302060408030301150306050f04050a 83
    0x2c1c1d511041c0129034928000c0404002044155401c51450901515482540d40d140c0100080292507501140b50740c3c4690b81103884000d40000058007540d100e00e064105800f040d60b01a1060008400201081c6441e02c6014104c4512007000d600d0245081c0c3c0c00d99041d0002000254081e00943c60220380382c4003030241c1ca120301c8602c412299a50b0400c0c2c0042c008001c9c0d02d44c020b009450a0040003140c5e6048404190401001c84240b59276541040c640c42c540005030b0001c0180a036080c0c0600030b4600002000b0040c7c0342c40d500c0500c40900b91212049401c1a42d0084650251051a005680d8a0400020402c0c42883d81031004400c2d110606003060012001085035229070010400501c882c081c0011500f0400c1072003d4114140700e500c8410b510500050300d141b0821000c411401c2101c800d60000000315409040039880300d80d140c031502c1d00c1e41c0007441f0303010243ca0110307100c03100e080c400d10604080d0b41004080c0c00900c030300c89082c44001c0000030140c0b1107840e40c580382000030031800c0130740038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 224705287 1250 224704037 224704049
    0x41e090e0f0601090204060f120f0c11190f1106070c0807030606050616030e0402271809030304120318060b01020706090b07080d060e09030d050c0702090a0b0103020d0204 75
    0x10007503941c000c15140c0361010582c0403050080c030501041c0706055100910000c814410300d03040d4170848040c6c91850080004403c1e0408003031908c01c1c107c240603040b1420701082e400305019610b074104191802c40040c0340745d210081000c040c0b69140e000003440c00c0038920781100003810341ca0404245654050710640c154001c55515800b102c41001040000c0c02004060041501d0403420101c0381c10030700c02c1c015021407005050081890620049031110f034156900c4000b0742125002c801580c400501da820804a5014041c00000c921070714400d0344030382d0080c0201c01c20340c0154519038858995000d070080e40d103a00c104050300e880704540007480780300f2030344400c40c014080050181c103410700281c900709682e8480010f00000c174001300700c04c05456040c7c401054025102955035180c00034448010080fa41100020328030403001d102c039040c800405085d5100034500304000c43c1e00c40035400c1c4240d0050680080d8000308800029181d036010341c12403041200181009401d110010703903041c0680e001178200d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 224706537 1250 224705287 224705293
    0x506040308090606010302070b072007030c090608070b0a081510020606130605010c170f040f170109020916092d140102030f1305130926041e090e 64
    0x20000c00b41d014007400390010002d080c11803601c000c82d51910784010004002d4000e02040710880480c05545082000709403001005585e0010b440c1d00c0c3c850168680c0c0e000c0c10300003914101c40130440f20b8000402e41c00303035546c14400504281c040c40f811140550014404007800c021040c9180380c07a00c603450703c03c01c0c0905a401610b22458048148280d0300c42c411030340c0d4652820680304220704d90700020009000c035044241c40d046d003804125210f02c00c1c0720b0071214080d195400a000245c807959141e55105580071341c54003d00c03880040c049142620b080440295015600c0000300721817074500e514a55002842c1d0420018a03607a0301104980c2c0644074507005036016142c5500040114a0100640a028441420200c0c00c0003100000d541c0d0203845000f00014200180681e60892044c1d1000002d2500400312150b81101c0b0883c0c1c4045c0c00c866030102c0e00c184031095071820f1202d03071580d0303140401030080f0790350709092800307600903902038a0041414022480d844c2c0801c0001d2580a800c0244130203c2c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 224707787 1250 224706537 224706541
    0xf0605311103090c090403081303050c06070201090c0801060b034201031415010f0504090c0e1e1302161505010e010f0303170601030e19050c01030b06040b0a05070506040308 76
    0x80c0f40c1800302c10703c821032203140c4030800c01002036000701005800c0103521250f000310001c28941940d03144181d8545c2080c0d4812141003200311581500100781552054034555180307541c60356079034203840241c012006401000e00016071180540d42505580c102c0015403130f00ca080d03207242c2d240702045241c1c5646916802840c0c3e201c490f560503018100700030726005040182450110608246032100b140e1003410001c440b03c1800b641449601620060000c054017000004001c220150000010904141c040e044c0310703440360340c900c0728821408a09e00300900100001445106200b000398007818412000401c603003074003408102c0814044410a10750b00d000240c0394140002888144030592002e40c80640502091001950000407510000707404081c169842d1105130059004d40020b102c0c41900340710300c4210402d0856028600704140c0e01030402d5841460b1580011000ea0700c00204454100d20208010042c0308a008000c0159648616205051030000c3c7c0c2d84600b03203a42900c06400041203070701 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 224709037 1250 224707787 224707801
    0x90a05040b0612030d020d0209100804061d0307030c02120a030e040b04020c0a1e0210031a09010b0f090324010e010e1306090c05030d0906030f0605311103 68
    0x41c1140d0406030448203a500c20310301e905001d54038461071105840c00368012420408011180c0c060f140889030040a00e0092594950000c004800449090320000d0809004a501c02c451410141c10082190051840e00b22107842c10740b03d00e59010b030220f8110034800354005a101092003047e48441c46030f0764414850b03000c02d08000c1960304200b07485204920404c0510034049000410704845640712014000b146008030003102100b07024a001b9400135866144c456050303500d64440208681070400e1260741c1035008040c0601c44009004e031400d455020054190b11880700310107000218002411501c01802e0720407455810304901c3d007101006807000300140580a48407103a030f4090460507484803034230300d4061800d556001517014042c1c142555240c88506020411f080b00d8050708028045510354003004c132000300001707514271540c40041d103860040e60010417103000700421514014080c111403802007080d030001340c404d00d102801641680c6045020402c190103a0450300c2c0d03518031342c0e94603842d20034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 224710287 1250 224709037 224709053
    0x9090106050306032b120c08011206140a050a0f09030207090e0c0310020a020d0c020a031203090212030315010804171312030206070306120c0e0a0209040905070305070b0304080a14040302090a0504 86
    0x36450b0846c5070030941c2c1284035907400785071507044a2903c4d9000c0c01507006070a10400600071001b142c4880c281d410200a400700f11500300c6805840380c2d007810095070105030441c1044505c0250700400580142d0030410245946800280400c0c0f0307400c055030200d204490010340742100c038040d03180406401294082100341c041c00072036070544440c00d214241208503030000e814507545010050201c0040181240c07601d201e540943c12041c0d010345916040442e04100640e03070f800440d03d6540d000c004140c821071951140c0507031802140c0c081031485032401e25030702c3e008082d000320825450140840d180003810765200c003a400100d5000e40c004c0d000b541803901c0018107646a0f03800c81c1001070f0450040d0310000b60f4640700b2401f110014100c10006844020146010f48500e214055002c0d08200084d014800f01058079800c40748104e0403160507580e2030a80003004c0c00126005048035005100c0c1e1062030b8010003481d210a645511403520b0641c407a03001900d01d03c1e060720310324881c0c2c2d910410001000052 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 224711537 1250 224710287 224710307
    0x70e010503210a0c06020f07060f0506010509030a0204180206030109020a0201110a0c030806062101051212030109090312051905060618010c020f060a0215070509090106050306032b 79
    0x81c80094000b0803592600044610841a2200802250b40c000c142806951b9060328420118110380c150368030720b1801c0400c05081220200c02e419403800000c12055809001224006c50001d0054140d802e0305400304001001c005150508000d00c85200d4001170307460000950203401a41001030f21640c00c440b0007401c59514075105501e858040000b282030740d40040001000d5903151030094a03558681d00441c00d14007034201c071000d60b2aa03840710000c0200c3c400354064140d41f02503825450624410800d182d862120720104020340e1700c100014080002c0541080b144207010303041400c040d12000c03954034100c1e0421252144022210f12031640c40078014020281c0001d4200c070400e08103041c62011083c034144c0404d101e418880ca108104003152200301300c860509000910190300d4541c074041c080e407a945002104481d841c813910004200340e00030f2090b41c100c040098a00d04503607080100c20b840c0b503440a01401d50501c1521040071100c0c072b074421810f1480030b45100d0300c40d0b002003090025081d1816 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 224712787 1250 224711537 224711563
    0x720100606050a0207291b010203160e0a05010e0613032108060d0b180a0501090f0210030905030313030c0204240905160f140304060501170303040c140a08070e010503 73
    0x440c109190003c1c1d0003213100400584c0a030019603982074180c00303007070f5400480d100342c1f00b03035002204011041c014025640720710419503e505508040c00020410600d82500849012032100020721002c0d080c541c0143c40007030200702d551144c03984c60307850700a101c10b210000640c46004030408a25141d86c410141a0807803c244c40800076542c155550349000b80c002802401100070001c1220221002000341240882c0c1010080041070440d09028079104a681c1040e070048481c00c0744291100d1091050b0300c4442c0c0c010021b1400e41e00d423011210035001407428258200700c00c509180c00541d54610411900c901d001d00c0128043c841804031040c400d00960003100031514000801a0005078101c03884020b003218a404405140350003001e5030500b0107103070884c12004002c400c00080007411b90026041e61801c0c42000300c40c02e110307910165244412100144804100c8004000380d00406004034441070004001e000116110381301d583c90400c0940c403018600da24400104407608040c402c01442c41c030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 224714037 1250 224712787 224712809
    0x20d020315041b110114160905013002040b12060a090b0117040c0b030103050c01080c0403051f060801090303091509032a150b100203030720100606050a0207 69
    0x34944883c00c002407001001c1090001070f42180403540029440405040222819051203007011242c060612140c00c0c401e801240c806100841e941d801800901180b0031368600805580000001c0c4004000d1048102c0b007c1c582c091101245180c2403202800b103211802c403440a640c6040c008002d002c8900342e00806586142c03403004c08069030301003034501c0d0403030300d0021a403602e46031803411203022000c943c8540485c55001c0008801c1000104100520030303c240da404505444643e02c05030303544035512000309907074000b00110b80e4a6034840c0c2004480e044064000540c1503035000885d003510741c0024206c1c00665515400010040d2480051202d4031031483c0800400071a0765025150581d05464255040c018410b841c80034085d080340690304170b60020142102c601c1900000f00508809000f4520920060703420807200d51001060300d01c01c0b01a903880541d0200f900c00703001c10301c0c242c3ca04c840200d40100d6001c0c9900d0201c5018003001020300d070380c81c9035544000400081c1060f20a400c00030b5001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 224715287 1250 224714037 224714051
    0x3150a140a12080c0111071202060c0403060b010207080102160302120918041103100e0f010510060302090f040212010617010303050f03090a060504050d020d02070506070321020d02031504 82
    0x18803403101c10307002d5440c410300882280b4218104881d0601400f5848040f039800d041034001c2ca0610140588000c9110303070b034035403080001c020080e41caa800c101c2d0071120040080c40100b0118081d5005440c0520041c01518003054803115401c3c00d90380503034014514910900f00201c10164100505040740d003001c401c0c5c50a0684404c0020303080307a01c5481400c01940c060000c10103206424000e440440717070040858502003565000903020b003007030010b903108038005c1c40f0020401070b030103010750f85c80707044a440348080403414040c003900203400545400740c001a03a0011001c064407244000c09000640b15260501507241600040802d00008580c80b040102d0780010400290000f00342c0f210580d400d46100e40301da6440c01c1a51501e6103c42000c2d040c1c40c100780500052180105280c48150342581c01e40e41c030030714000ca0503640d554091050320341082041240c000427038482d82c03504d0700c845880d0100c400c01d02050410042a40c224060065001c1d9002040c0105200d41900d510140b02058038144012 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 224716537 1250 224715287 224715289
    0x3090c0b0c160b04050108040309170a0c09050601080f1f0f0e010f0e04060f1e0f0b0111070510020102040e1609141309110d0f06150803030408070501020f03150a14 72
    0x1340154401c9605002c00d800201c1c04150240025101900d030780396501d02c603403100310b407460741d900c0820400307440200013101c0101d01601d485c01170324811941170715001200c0d04d5280004c20f00c0740b001000c81ea1500100300c113183d84120140c40b401c004020906415994030f040c074510420400c1306901000002e4004281045111002c4101c01d80c4217400c0040007500b00071000300040580401c03901c8106a03518070b481d01c1880100c1b075001c00403411100500300b2600070410300541c1e01c0400d01920441700e1f4002d0100300300074075105600140c1c03c03070799200150030503a480c81d03058010541a2580f2200000007004076017040e03031008a07040203041c140042c15110003203402180e01d900041d0442450b01d074450302c0306014002c42a140780440003004d000220441c0190400c601c4820b840782d4100c460504020002e0100c400260307090741520004c40240d45140c80310754542e5a65882604111840c0d50248180c07208282840080c0d8403988502c0300c03075444803110004000c007240c0150810a20916100d80c1c10143e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 224717787 1250 224716537 224716559
    0x7200d060b040b060c060403080615072612040323090607030c120909050606040b0a0f09050a032102060702030412020307151106090a0807080a03090c0b0c16 69
    0x18560300400e001648081c864003090242031a0f00d5215004000052040007510300010100c0c032850007a511001036440d884204038190910126404d007070101804560302181401801509080000c2118561180034140300e4440e17030000400030085000c039030208024035400c00030001d009070030000e800004101ca0f1907100c61070301541d07140070b0281d1408210b080c20103020b0005401010b403c000300034001803081c0c3c40180076500501613015480c1c00c16011450504050040e5016070707019810984c104002d022007150307040c0d07841241e80104040380000080341e0701c031995440e01960181c00f510281803040082c15001449280482003154040340410103110303030100644040e00c03400c00310724480e42450b00000340303800442d40151221400141c0c000c0305440c0c10441202080e402c0380107543d02c550383c00715225111640204040c12a003030400034500010040d00007000340480e01d0800180c9180c0c035480721000c90880303412078420701100143c1d100040394100308044408070002d41102d400c4d1f06005004031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 224719037 1250 224717787 224717809
    0xa0207090b010912050a0b0907080705040905030d05040c0e011d09030a09030201050903030c060c1e031506070204020c0a05010b030601150c0605041e2d0b0609040804080a05030720 79
    0x3800203502d0680000b00071092000506c01c0d608201003201e42e04000500586450032445020014800c070000021030381854069019000e4005000c1d42c100461a10075102401e00180111030020301c6400200750b03104010f0105010b80241642c03c07481c1e61200350040040c850103051054113a0051040c5142c241c0c3c0040c00d5002d0320340c280381150702c41d030180000c00d1550040345130401e0903003e4101085048905c03c2c0c0900103084900c40364008400c01c01090581c1e510059035401400070288031b11450508005006100c10340c4050001417800d651808068104580e81000f25443d9448074000042e038501044642c0c05040b40040c3c07003e1400310f581c006801c59a020400414498a900c0000c0900c0151b4614401008020030702494101c0321b403800441c040d4052414400200d2908a0010043c0d004201c40c11410b44c400c40400d0b040d2108402c0002d00c103001002112011000c200108458600344610381c81d144c81a80210346446962070610602140300c10000c0304d104070208402165a9400c000b8070b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224720287 1250 224719037 224719049
    0x30c03140606090f040e01022d031012170f18040501181d06011e0801020307080a020c100c051206030c09070f02070509040f0b371404080a0207090b0109 67
    0x134003000d105400304002d0720814900e00c40c65440442d0100c203065007014000300c0c0d84412407402c40c2550206402c5070240c082541c9519040b4480c0e003090018074041e01344c10000340d000d0090b074036040b0302c04030b0221b6880d0b0001800300f03005507010555441c030100c0f1011070216000c0484080c0700030b6042031070081d07503545080030820003591191040d00c002c0741d005013100c9010128405544903580c68501c2c8614441910702c040e030b0b130601600000564144180701b03882c0a10310603914080d440e120f055500010303400460005001b4013591514002031002c40c0300d40c8283e0340c0c864484640720880740f14900b0728001e0080c40c2034081e40100d010304a080d0f03205012903522602c41e04001d031400b00b40000492415450303030071864004040c1018842440354008001100500c244a602d2a983e5982c0f410304000990b00d0a000039203414503040c150a550354144060000001a00018802d90600514400f490251001e40e00c118000591a29496050207500e01030100e03d60700380300d00003801e03000a1954003548154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224721537 1250 224720287 224720299
    0x120e01060b1e07060504081b01050f012705010602010e010f02090d03032c06160f0c02040c14070807050c090408040b0a090312030c0f1106040b0a1803030c0314060609 73
    0x490042c000068818258121804100610301071030540d095030b101a0030b00c9500b2100c2e24551040c0e400502a15204015110407042180d19008480010484034080031410001140070341c102083c0d9441958000c00c03066002150442d00c200c81c16003101c5c42030480407800c80c010403210700103880748070413a51065410b160014185920a4807403000c2e03c80143e0745d03134070300c030102c03003c042c101c5d0000600724000c0320b40c0580c0c00b407070301c002c1181941e910850010320000b1500da9240382001d0303c1c1550144201006a040808941141408049095010300001c89101134049400e07000c0c400100480705000700190381c405400e0500d03440d115079034002c0f485100003140000404902d003c0c072400e03c80e0000c40c0d0010340007030720b03c003000b034090040c00422420b040061a0041081c0341140305884030701e080396040707000c0c1403561075985456520220051821642c03d8644958140012072164003540860096030005441c2c3c110301001029616441c1411003401d90660622020ba41c4100840d00861011299 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224722787 1250 224721537 224721577
    0x50a08240c09030a050c01090506090d0b09160e01030b0108010c08240a060314060f012c03150a11031603020a0309080f090f0312030402150910120e01060b 68
    0x5140c2442c880c40760b4090b014007886140f00200000000c840142d110241c0703c9208a94640d024081540600e01c07100313901010a44800e40031413401c2e00000c0c0c02c4010ba8081c2c40c00c1c0d10031108501c039003401540c442404688203170b0041050255400c422400351010f10000d200b00c030b00d00c00340244041006480e064424104c00f1240c2030328200d0849070744640b90050302014001d541e8200244c002c2c074070360b18071507184c0c0d04c540005101f601d090050f03204000c00507103421401d486840c1d06ea80c1c400b0f03040c40552030203181d00600040c29981c07c20941d190000480c086c41c40d1890613201607410b680c400201d150400b5014410b110310750421941d503104650042c640140c03210820102200541562403015103040000241200b040300018001e011214054034240342c13400e03c0c3c8042c10f989103607540c030b1007030800400d00101e40145010103060407403282842420f42402c1303150001407070b00b4504000c0704001c148250705030040c4ca0310501819000303000e0741c8020450f0724907220240200d4468441b4241e00c1003501c0038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224724037 1250 224722787 224722801
    0x2071e0501200a060f1d070501021b15040b03061e18090c1e010e030a08070807150e01020304031e120f020417031e0c07120f08030f01050a0824 63
    0x81c00410707075081107050040b8420205141c000742a000d05801c40c520150411b100010703170000d62407040b10303c10307801000d16100f0030102d00e00c04c01c51440800d0780450300c944050a0200b481d8094030103401d40302007183c0e49e402c1c820100044c001803007040c07002044145040d241340d9602c400341c40c40c840396000d01d1002c0d15a64150710302e040a82c0710140a601030b00c407903008650102d101a0081d2180e80c2a2101d40406a0500826036101110000104102001c021240000b000b5a000e4046144100c460042403581200590300340d0b681c1c0c0f100070816a5010003003000340b59100706070310070350100c90320b40e0345100400103802054134004001803552203880305040c0320750079482d81c101c0e0010180600100b00705a134102c102030b10707640206c03440700044d0006500055034500010451300307035a11a40c0103003141880d100040132a243c0b11501510480d034501420350200301400b000714481d01c60b0003040c0d281507041ca82000030a65540d00022502d0340300242ca152002d180d280900a044504038801e40b5580c2c1d10380c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224725287 1250 224724037 224724043
    0xc03030b030a0c050405010b1606230420060705031602031603080424271208070203150903120603070504110d05060d0c090b010c06050702071e050120 66
    0x948854040c8502c080941c184200040e44006888044800703001c6a66103407403100300c41c001d2070b01e10103510441c45841000100690300000b000e0200407144480e410130100c000d80a500b00300c50540e541645005d441c260144c8004e482102640e003100c0ca1410044941c440c82da480c014421b0003111554003240304015540e00b000380605c100d10241541a5030750300d9103000b507000d030000e100d10300503514001c900d81e0303900b6540e8040134196092680e442c9040b001e103084e8802d0b8602d11079244c0c130761500582c81c003096452001d982c1101c0c03076000c2c5406540d1a0070701d00c1403514000c94014140e1004408806100100e0000300c01c4960140a0a08501850310b50600107814841e50754402a402031900c910119030101441c054003440c507000340204901c0c0e9441061120124561400030000f00e2100410300062006502c4006412350615014200502d03039034a1a041750000c0c0c40c04d602590110310100003101c0d41c0b0a040c0003120301c000b030500003d843c0c4000600100d400050801c60984010369141d007441c070030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224726537 1250 224725287 224725301
    0x3120f09010624020c041107030c0614010303030209030610051c080c0609010506010f020a02010f050c0102130e010906051c02010c080c0610030c151d010507060e01020a0e0904030c030c0303 83
    0xe40c1c01507400b48641d85154100c0f1020100f07030005401080110320061810307100300c1c0440c495a01c0c0551a020390369508582c00c07000114220744841e520003030207260f96440c01425000e03500c40d40b80180d4600350341741050300c2c2050042c642b5000700620384051065444030041880c0c06402121071126500c450706c0c103c442d5000d852440c00c8184100000c000038000c0540002c0d000702020388441811741c1b4089003c0780c60361218039020340402c500b88085c8040074440c1d8020411001010001400c5c8040081118285a00c076405240c0c0114044014000a042c0d889280014102103075503106040035151003c2c400048420080c1c18010713140241414060264115810345940707006555030b03072a00d00c000322440c140c0b902041c0c1c1d07a42d0b5010000709000000c480241e0641c0e05d980c0740c180c440070410b6092540d00c0c10011516042040034007022000909500800d8040d040ca4400580c4484024400819129040e45004d00c41c840312018080483e40065440d041e190709132a05d5010b140700b5084c1600036000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224727787 1250 224726537 224726549
    0x20f0303070503280504080607081b030a05040302070807051c030e120723030606091506070311011116030804081201030807060f0b1e0a0305120a02070803120f090106 73
    0xc1c20340000713000602400742d04640c041d41c40015008008215640d008900900030240d210f030740030a4682d4029006554000106400721201180e0080c61050070342080c3c440a1040c0e44030341c144000c040d0180034640243c240700c0c1c001c04100d0b113008002a5034086c12002102c01030120450032051501c500d404d1582100050580c04800e90000110f6603075800901c101074110039500d000c40e40061115003240e00c1c07070b840100106a0b6460b61820041190b40140a1401e0515903c58002058179039601030000d15000c3d880d403000640c04040302e14296110300040c0c1511400401030350406e4040b0254407000d03c0d82601d8080d1080c0d80d40e00d86101d00b41304105a00fa12080940000020804200f00519045114a00900600d4600302e07600040d038401c410300961080c098034600c00c0c0c3c6030351458100c1e18000001c20f0040c5071692500c6590410102035843c00503101c000958694164040000340010701c49640154541103407000b10050104004d8200d00403040800c02040d50300758250011805009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224729037 1250 224727787 224727793
    0x3050d15170c03010c050d0c0c02031212060303040803120c07050109060f0b01080903030c090d15050f010b21070c0b0106020345010224061305060a03020f03030705 72
    0x5268078409184011a54800d03029100d81c0640c2603a030305043c010240c0c0c2c005141c40752810320083c09841409030a15002c10307410030903c0c03203c5902595041014036540c20301650400e81c2d0354500b58401c3c5518200810050195008000030003141500108071640c410020002d064070703449210b8442075910900c24040d2180d07003000d0b02002401b01c3c03a271106074004040c5070104862a034080055850031130488184c1c20580092002400340200c07038005280303000d802402c0012107139107650b648440541e010764603c403984d52a02003006074000c145045016055869406040401d0021807443c1d94865000950440b130540300410900750040e05107080c001d5000a01ca00c0d0381da11910000d40d00d400600d090788034501032222041104c0743d9a6000d20049690b250900c113055030f022008907840708900e018a04500c6609050000a944e00060000000b40403000020904103141003299031000c602500f5030480c034000511401c2d542d6039448404130303613056505e206000b0200700043e0541c044d185002d0b0542c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224730287 1250 224729037 224729039
    0xf06010b040f080d0c030f0e040213050109080316020427060f05060415030609080702060a0e040b09090a0b07090b040905160507030203041802040b0c06040204050601021903050d15 79
    0x10032000340c415a25040380c403880b034941d030305000382d070f0340442c2055000851100301d002404288148840c40040b486410000544031941d40414200e03449244111402c20b5a100c0030b10140da03212403420024940e400c01035041201c44240c0c5840c6003200da200a12480d51025040c542200309010064a0342810070b0000103003c060910030301400c00104c1c00c6020382d1500c40014114905442000703039080240c00d040500c6410f6680d080010040f040702a0390310401404030b6001607071900001d000100c050307900e000040b8480c80600c000d48a216062920580c00b103001c1041e03203000003030443d1120390007294550941e224030742c09075400d040580100000220004010411030540e80000d8061803000c00b44803400d113010441181d143c0100c55004005030002c2000f00582521a40120340700c40c6003003001840c03d07583d00c1d4103100c95840300e000c2c01180d070042c408000a62a0602c2150b502800a001a11001c0280802180c001044400c010b050000c003140d1100190b5a942c00f421044e645001f03115801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224731537 1250 224730287 224730299
    0xc0304150203041b0519091e0908191b02010c060b0619090b03040305040509070e0a091e110f0d0b0d080705060106023d090605010f0807030b06040b030f0601 69
    0x10100840c4130000b0b8004140c0d00040c14240746100120745541d80d000d1200391030820032170f500588141d4940d0014100300c20116814202e00d84550448207209020899882c61281040e6001240f10403000d4180a4900700c081d00a00151305110b6802d0380c2403810b192803500e50b20340704005000c0d607a58283c1004011465000340001144c1448060301700c0d4868100155907020030004521044800a000034020300003004181001c4501c5a0004400e081ca0700e4050326403400300d01240381a51004c00216181c10780706042c0b80c40f20300e00103601c45007000280100c0403140d407200201d01c1445000ea0544030000745130301f00030344240d10406801d81300504d1007600a00c40e051403e415040418107481c140980741c000541203000250840c0058444a44048803090b00f26000c1c81d420344504110450103c84a4008411740c402e118001d505407040030300107481d50400383c24084071740c050f03000101346900499003030000c0750310034040961010045078041140d0301900003103420f11a0f40881c2d40d0b103a1040c0400400c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224732787 1250 224731537 224731553
    0x60f030603190b0a14060a050f0303120c040f141f12020d06050411030403140319140a15060801030813050604030510051312110319030605030c0102060705030c030415020304 76
    0x5041413400c00d1015a03000845010999400e440440c0d1100f100c5404105508021002510500004041e070b410048441d91010881e80300301e4070b0408446000605024811800d1180d0000d0540e00c1c060584030700201d00402d45600d0b00400204078103000a9215210500c240007280c01e200076002e05544481c034880c075030400740402d4029180300304e04000701c201c81804a0415039115607059a6248a102609401d0003501e9201074920030100743d2051044507440b18a00034802030f84440d0312400050b00d40340700c20100701d84401100300c00300e2400701c404021080d84070500d80e040d203070042010359880310b2180128800a02d141d02c00743d00104081000014400b021a840d07440f110202824880342c2c0e0303a80001414404000c03002014010112031902801c3e114071568090385d02c2c9071003100d02c0d01d038a010440c05c0c1c0c0dc020b1078083c1d002944404003480a0b0030b00b4405070320010380a00041480d41041c00000c0c005000007030545101303071404000242885041465007c41e101d420390b00319940e0402d0305080e05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224734037 1250 224732787 224732791
    0x30b18030f070c090c080415020705120c0f0d03111206030304030b070807090f0302060304030807231c11071b030b0a0902040b0d02010e1c02100903030807020705060f030603190b 78
    0x2480c1e14204200f0b03a0f82d800b0313a80d0a40719940c002550b48c403003810814800000d420800701503c09108581400f500300b10b00b6002020010010001440402c50402680349003000444c0d210341014140081500101010000e48003030800381080d4404645e2110007080c50741c02190f001604030540c0c0c500340320509401081d2140680000d0f030361402c000343c84400020301460148002508680c00300700103400b00e8402c44442d030704055a8500107100003507440401e400701d07030b10103c008098400003071400c406840c084811005226000c1e010300c85e4544540c034004550040c1e08010b88014205c043c01c0b0000c0500d5001803010707643c080075000c624242060101d000b00440704040380994076241c0380b484240780c140d070b0809040368142c0d5442410300310b0300c0c05d1128040c0640c141c2612000460211401603035410444003144a080d0b83c1d8200080c59400c00800c0e8070001780180d0b0954000c51010300c0303140c03108821100c61011070201d05a43c1c1c0c9402d000310f8034204a403008105600f03001d407d50000c006065140764 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224735287 1250 224734037 224734049
    0x1b03100c031407032009060903010e06190b0306070c020d0b0a1b05090a170a060f090b01211b170c031c050418020c0d0905090c04030b18030f070c 64
    0xc060707500c5003815021154105e06407011502d003c0065101d014441008141020001e040e103401c100101700840c1c296206045001883e0300310340b04105072171465403141f201c0c6c01009407061010449950119445050151682c41086480c14200c0d0564546509440071551b21165442003464005007080060030f003225440309541300d19072154103c134400c42c19500001002409141914039020845010003a03600070358099004082d840c1001c01c0c10b911880c5101010040049651105850712041009050b0001442d101034103076011450364180c0e0503080701c180e00c00105a005015400d41c10001181648a045842d9001402c4102084007140d201c0b00f4032000d8086498142040141504465410001d500001c42c02c1c0800c0010380340144c8040c1c5010307000c2000503c0c2461800aa80c1010790100c903450108445c01020029820708040499100c440e2082c070508240c10341d076526035800400b504411100b10515001008030034140100d8021104003d041552007a00345130041d54143c00e0301c204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224736537 1250 224735287 224735321
    0x20c0303101a03091902010201110c03120f1b0a05132d0501050702130e0321011d04020405060a150908060604050402030d2601120506181b03100c03 65
    0x282e007010100302500c0c0500941000b906140082091002c11561140d60a904540d201d042d901c40c0c0c440200300070900d002e101d8000e19529009912000b80691002e441161070445180400183c1204080381d1040841d55401c2a50380300c681400456480c041c144046d01c900c00f0b9a2000202d06060b403e410a002c101c0c0e550160002c001091300003401181ca114160110307008020f0710006203000b4081c210039911030100022110f01c3c1e07000c220300d503801c0705a40480d50b034610141414135510561702c0d00d0051009002125410343c00c140740c86411080603000034000d039242c0021030099500d2090101c05442c400152480100b1401e400501c0c0d84484e126040036801420045181070070315001d050711564001e4014150400342e80000c41d028042c484a01e00c840c001000c3c6241d0850010103018001c10100356a10749446450a0031400e0920103807002c0944030001440c00070707a100116008202c01807503080d040c4184a101c0220742028942d00c0000d06240c906100e00306010b81651044100750300507030350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224737787 1250 224736537 224736569
    0x130509090109051c1211030403120c050d0b030a02100302182704210207050901060305130204020c0a080c07030302010e0303010f030611040503370b0402060706020c030310 75
    0x210300d00300c48034400064a070340c00000d02e0100c1c207407100f10b0380c1800343c2c440d10f010610000c21850280c00c80345040384100c50700c507000080c00145a03100b503003000040c40540d01082010b40c401c1e005002885000801c00388182c44013052049903909220f1080500c1e0090800b680304591284010000c0d03100e0054107150704440095220142000d6880700307500160b408001085013000144201003d034010001c4840c5183d500003c0e16021040c0501c114444194000388940c0d82880100302d05c29605800c01d4041618100c208011002e0001202203c2d60301683c0060b501e947c0d0841c62420403803507907000f43c001400011174044007100011084203c0f8002d500801c5107407090760b0010303201e22080c0301300840400c1d41c84003400815525840341c4440b070b50b80d01c10145816601e0001c45d0810381007606440c0d0100d220b0b1107102e400d900c1d05403a44850300c900d0201d484603100554644000d0000a440640a05004240d100030000a50b0440b224841c641045036224a480340343e80320543c07118007503200c40950001d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224739037 1250 224737787 224737801
    0x709060b04050306060f12071203091a03180f070b070501060f0510080a1b2d020d11010605040501030f1101020a0c050405070c1502130f0b09010804080f130509 70
    0x3510700703952006000d00013585030308040012040e0812a02684a51a0701091a9200c020440d01d0b000303003405030701110540118100509070203081e40c400e006500c0d42007141107605507034034200c0381e00900300070841880700c5400b62690320301821143c0420305489582c0b0042241881c24000e003003002e00c00e074001d00c5441d03220f00c99150118060b06c51950022440c107407031583e041c041c0b10100d9000d501c11400107001b860403601c4a5040e01003040c3c0d040441c0e1000a0b0144406e8001c61200d01440c6400d4201540061080000d580300c8900030b81d601040389405203201c3c5000203420010003090010b0060000e03503164100b411201240030403c588440c0d841ca10641c89500110344460900c0d000400c180d0300f07900d40020b01015101c010f01440410180ca040400010003988020000000d0003c0040c0c030740170301c4114450340d0440c1e40c0140e400d01d034100c102000030220541c11031300d01e50800c2ca04441181c6851801d16600c1c050400f00300c0c82d5007000300c2c44240c05201540300108032801101c181d505505c52034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224740287 1250 224739037 224739059
    0x4241a041109060c030d1e0b04060605190306120632010e040f1a06010905090402091f03060905010b0f04151412010504050a0308090d0504060309020402040504020a02070906 76
    0x180d030521801c414840d101035843c01801801c05032150741c3c1074034904075440016504403610000c00200b80c0c0c541e8513032402c0240b010702c10710089a0040d141008041c0c1405400703886801200b028158510b0703422203010606229420640041c040f4110300080842c1510300344000d40b00b1000d480c10211408005182c1c2220141402c40c1005407054001e0026424003a110080420040003552440501c03c201c80c009009100d6260b81d24980e10151507642c14003000042015030194000341c42800980280009030b500d001c00075800000c120000441d00b10800384005403840c0542c00a4030080c034104605061041c1900300001c000380482d0418100c000300410041106d180810012400c850010140601c509000c1d45240d503407001050000e400380000755440c00c3d01c01c03c45041b08d05802002d042001c0607001171b01c0c260008201006411801c414890050480c001ca01c107180406445025141c00d549031079040380d025010140040d941e40407802c401a55075a000d11401103400d2401c0c6001450502c85 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224741537 1250 224740287 224740301
    0x9020a170f0a150b0d020a0309020d0b0406050108030a05030f06010c17030103060b060415030e031c0e06090303040f03080c07060507020114011707030807140604121e0903080304241a04 81
    0x11302c2c8850420a9840101000350050034a450905943e4811640540d41c1c0040c05c002d030030320400d540c1c2642d00d01881d1400c02d40e034042c0e01000c810384c401d00070001400e4000043da0b6024210042c001d049a4401c001203485016000000c1c09402c81640c4240010742c8400045040e01d0080e10180180c4c007c44047c17001d540f160344200104581c8130415410b8042c4250807481f41c079052001181d00b01034488461f903a540364400c0eaa240c1c820380e40c8140b40c00d110420320480b41e005c80044080c50461402da2528515484c41c00001800c00c91013070006403407018100e003036481198100b41e0800080c904004040c0c000e041403002060511105400040d04114184c40340d0411080301002d861244d2540c6d896803100e03040150b04480a0701890601c01c024a010003001d0f00c21401780ca0f03861141d52200c0d130007a21100e000400c100c28180f2020012084581001c560340899601143c2c80e5500d90340c60a1000d41906c440e51031320000705411009030703903501c0140c2105201e0b00301e0b1407400100c8075181080200b11004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224742787 1250 224741537 224741549
    0x70c0e0f0603210d060510030e0f0a0309030b07020709050a06061d01050d0b1203070f0209150f120c0a090b010f03140106110f0a06090c0801050603060109020a170f0a15 74
    0x1840080f01c1003030303440c201400440e2407503040400d2854075040052414259000c821001960381c00c1030001e80d0034104110148210f40c00c1c05800c07202070645009011a40600014000e5244e100c08640894403c00c039000080600e800d007040182020320002001c1d00440c454900010b05d04038504c880c00785d403031045000c08601615010b20f04035448044101410031051003960040c26a0f0039414030700414001494114400c1c401075051410340d02c10007140c4030700a8030b50314072054000e00100c0c40c0d03117071001d158000f8002151110040d25110b840d1300e192403c2d62080d00d42001c145e11000800d54201d070050b00e00101e00340c03201c012030702d4419400c508403070401041c03811203114032004000d075600131107119024101181c142c490fa410f03c40c4d50396203000c0d0726100407130703109545407009010301c1041d0070010702038151200244014148200040d0307407a4410300411400d15400100580400e0048902c0340742070141c80e45a540a10f03050340c02e415241011103a8500041c20028958035540c50b82003d0010350394 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224744037 1250 224742787 224742823
    0xc060c0c0b210a09020d1a070203070c05010e0f06070c0e1807171501030b06041a0d020f040b0a080c270408070804031e210e06030903070c0e0f0603 65
    0x5440c44031410030041c080d2490040984da0071150003d42c413850102c42695020b001b1080c2051081c40d04820001c034001c1070750303007150814000000065024100407048070f90900c0d0040ca240080310004640740c071380c0050964000400244a4200454002154100c0705044044aa2545c031280d2070102120f4696003488a600701004c140031411035843d0040940e2500011a071000541d4001e030100e08000ba0401d0310404080700030050036141138003034400e0503151800c5902200344644040741c81d000704001c3c000c2c881c19002d2001c0006854030b43c48104148402454590940d55480b2200d0721092000c60190044001040c104031a030100c2804580790002190700c0c100e1075613542c03a0950a80c1154200301e401c103004000000c0403c0120b0205081e80458200702040805075103003990b0060704001064410559201d48101d0b0071381c2180c1080d07000e50302a204540e43e59903111701581544145040141480480c4802044041c0100500743c419140c028444516403995401c15989001609162006007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224745287 1250 224744037 224744077
    0x3090203161d0406061a04090c050403030504062007060f080a020306030a12142a0d1b0609060204060f110102040b090f0112050403080a140c03041e0c060c0c0b 70
    0x61242c0c05002c1c2d129001d410005900741d140c11000c8850700b040c85550300030401c045803d1042c2421442a0450004142000d501c3c0c586542c2c0c000e400d5020360300c02c1381c052128004404803a5a4811078580c80c06030144150390120791562030181c0740d51440030100c000503125a0020f916a00c940c4201d030b00809000340209070030021955070340c40d240c2000015400b040710102c0d200d031061100c200034042d04501a54400c0d43c0d07040300507913122459220505800e06074040940d200c4419000f20122035141000902600d00d81424101000030b40031289005000386c0c070000b000038080c0d9001391114403956031030f500e031a0744034201e5030618243c0c001d03401100c100940401c00100d039440d00c8540d9000c0c0a1041c105200d55400d250326010840e04111800d03800700349a4004c11403080c1c400e1140310050222840f02e280c5908044c43d030b4840c940001030000f05084e15094403819035070f8980304807004061b4007511a10b41c25449500042c00782078000c00440c1d204004070f10104910b188042591062515901010382c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224746537 1250 224745287 224745329
    0xa0806180105011a030c0d050115110d201207060606020106051005030f0a0f0c02011a01020d09030f1a01170114010b070303110c0f031902012a030b0d030309020316 72
    0x140c0e03c086c2c00395810020810090711160403500130300c2d00802d219141c6115a0031622030281050600b80c3c841e040075003120420054031038000305034540c1d01c9001e0840040c1450b107080e8071842c183c17807640320302d0200d840420719200300003890b00000150f402c81c4e13000780079a0b50f03504c092191004d503140380040814030900000340390207815a04550300452603d80486d1101941c0d600c1c2003101c07424080400141d45402c40c02c0c441080e2903c0c40380902c2c00a10003000e07181150070f4014005440c03400004c0280c0c2d0a40da02d03c0500c02006404d08190300c4404800c080e55035218510a50358200c01856116542000360b01c801c241c0c540c940d5281264a8451a85e18001741c60794200c0060440c102d40d0440020280400310040c0c0342000754085200d102d4005503640e2802800100c0600c111300320b00c0003107a04001c0700c0103054800c001038906d40804c3c0c3ca514550312941031025409070810220113034202651220450031700d0b505070040c2c06594001c3c0e09580703510ba89131600a294020034068000b400c4d040203c19444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224747787 1250 224746537 224746589
    0xc120601030b06010306030609030302070209010e090d030b0d0203060f15061c0209030f061302090108010c02191a0408041e0f05101b080909010f0e0f150a080618010501 74
    0x703c450140740024040740c5a984607001c846036894181d000070f43c08124401103040c04800107024000b0000524458075044140075520044010f00c60101601e621010945840e41502c0140c001d600030182d440924100d28030b6521424100c0d910724503102e140d9982402400c200c0d04813610544826000c807984c11000c00c011001e540075101c496014852160b00b4070752004240107607070146a010703c9040313403c0c046004000d090107042e044a0007591410501051891f00082d040344400c1c4811142e81200300542415a01c140c0840d0b40017603203c590004120030856800002d10940702150002812410000030b400b00800c0341e40201c450a203a003001c107006624094405c00058602450326106090108032284c510707510740301d002c440620010440c0071079494101a100d01404100d14074400f00c5242c1044003000070000351101780b14540700c0d00841e0311034610818a814030a40034000304001139562000c80d50b00d180c00c94030009024039002020714028018010075048500340b903000303104080c001c60a410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224749037 1250 224747787 224747791
    0xe0903120a090825141b0609030a061d0307060603140303060919060f08060601090501021203060415080a050d080a09150c1710060806060715090201020c150c0c120601030b 75
    0x5506184c0c0c003c0c0ba0020300d13030a103142c00001808010b840040f000300340171100d00d41c4101d4240e00ca02001c0c01181c0007610300041c03440e1031981201c80402c0030303030841c560f51001b076142003076841c070a01000884a003403200356000102100d12030a1000745060310700341216203d000c10740c8d4460340000c030311003c01c120040700f22080d1f510106200b0005481d996030303500040c0303884680d4419007464104c00e040180c5580c2026040c0001c0c1800c0c0007038591407052040030203184c80003c0200b4400c80c1e843c00c00502c2400c001c168000500440c9049a0ba02a030318208280c1d580e14202c1c2d040c001400460010300300f606c0724003c003140f80c3c0d8803e1858229016640c05203000c0c3c40008950f00422108096400201106415407405006000b15101400d82030a030010320a0310020911802044200000000920000203200c1880340c24100040d258070701e840100e042c50000d03180da030f60150a01d03440d03801c050504001000301a480908a40c1e01e1141001801180c1d41c98400c4a840758101c2c40040001c5954100020b03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224750287 1250 224749037 224749087
    0xa0e150d0215070609020a050604080601171606032a02030d0207062403030305090102130605090406090f06082826070305070506060901141003060e0903120a0908 71
    0x94075400610510410343c3c100000a0300c54031385452441041d424114554005044243c03240303171800c1d080c4a91140e80c0d00041c400d102d0305140c0444d5003500310b002407200050741403880020358503890360307450010081c000c00741204162000603e10240e020411109250b81100b640c2c01541c01c0420403107000d8004c1d040035106503080c03900d42c000801059400c0e00f071a12204450300f43ea040321411070500034100d5100401302407160380304206044803000d035045010110b41040c40c01a070b0702c915060100f0082c11041c1d220035040782c1490812503044c0710700d4010708151507120080742d4101540500701e450440c0054000c0c110340b00c1801d0010702151540c080070715004206200d0303103d480c0460a03210807035070141500b0340004002041d03410030003805215003030b0404000c0314040800c3d418a00509680c8140035007140c81144c42040304c1c02c400d0b00940004000304450001c0c1c0780c29103805a0312584a5008009154001c4540e00000d100000f0074031038211495003041c01035090940d01d440c20010042824000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224751537 1250 224750287 224750299
    0x8011a070204020f1e070b0606070201020f011a12011e11120a0f18020310020c010e0102030a0e070b130b0f0405030f1e072411030408010b0a0e150d02 66
    0x5000075888038001000c0d0716201c00e5149070b4407004503080780002003892540380f840c403004010380d4001c81c105c6a2901d0304008103e0310307070780d456185100607403810580303599a281d0f6500380f51046071400b0a4000c06005400300b070703800b64403080900a12030308840d401601d1560300c008000e4448040c103000ea00c600305800d101c8075014134009120400c00741c1604100d8013a50017070345500c80b00604180034002e4113100c80c03203080b500c0d4400702d4a60029441c1d0802d081a1000903a01150000f10100c0035040824200480c0c0003c66403820010303001d8003e0802c0d06040c0200d8405e0040001e840004181110041d1079400600d9002c1c9040c4405407070254880031100e00d140c0801e00020030f103640c040c8030b4400c1008540c402005850740d4526194907440c00514030303c0d1a5004000c040106074951401200d0854440d80c0038444001d0789d15042d039040510304102e420360f1001080c00f007983d0704158081c101422044444030300d500c1d0ba0380700c000080031040f40d88440c8050002c942d40c54504103248085000c510003455 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224752787 1250 224751537 224751547
    0x60c120a0504030c140607031a090f070323061206130f020d0b1305070b1c021e0a02150f04020f060a120f1509020705060721061706060a0608011a 64
    0x101240065010070b0720006030040d10507c0300c251b81603c24050171014000c5024141f4120380c00080040380c00400d420489200354001030440da11a03441210302c2c00c2603540b0311b0111519040711030303c43c01d0211911401001c00d1407003c6c064020000e180762080d0707603030f10001d41c0100d22075030340304500c411541d0226000ba890310315910000b5008401144a9450b60261124140c0d25080003481e100c001e6001c0c10301c0715801c0010410305952071004400d000e1900a025a442d4030b0303508041c07000c08243c15410401440802c40280050f80400e102c0105115490b2320785c21901e80910a0171152001c3e01c0c025030140104000181c01d040c4007001d04007400990400300505d50701d5a0500040d41d002481d030b400792594510380284c1c032505500c001c501030300c0f141c10b00b141041142d59480b60b5070300010f0070442c18422011882d02000c1342005110290a240c0c1005000c1c07555035030f4104a80025240d50001030b40204800125541042e4094008845a59846512507460484454000c46000c482003d5030002041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224754037 1250 224752787 224752793
    0x51003020f0114070816020f0f06030c0c070536010f23040509010e0f280f080a050901030c1b08030705220503070501080c0f0f09030d080405060c120a0504030c 70
    0xb81403040306c5030010416245080c4100603580306c41d0318600e8401c200311040c04000da00d03030343d041d69401110070701700a07503c402d007803405403404010340d01965010903640003642c41c01d0680020088105001190a8000c40c0c22141210380c4e84024080c0019030a0000f10410031544210345d849240c80e002c01440030282016004502521f804030b50001582c0e4440310b0b510a2140f082100d42420031224014150a8034075a0054034842041e0f04002880c0c6c3c1e07003940007014403141140c400040c55000403001c2c1d071840c800760050504d800003600d0328003080c5003614020000d80180c004043e007158050210490303a0040d9913900c401d403c043e081ca8100b0000b03102c031b07000d90014682c058009211094000562038548803c0510784441504641c0c100710b40b0105021582d035401c8203803030b0090b288400d0152a8103c10f107200781c80c0d010381030840d80d05205030302c41002c907180c000003064083c0780a60140ca0b03a41d521b005403102280701d5159402c2d80d81e00b440b0009036041480364406030304a44070740341c20044180d007070f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224755287 1250 224754037 224754053
    0xc07020609100809060106031a0f060c0d0c060515100305100b0f1b010b01050a1103160614060105031608060604050405040804150c020607020402030414070803040801051003020f011407 81
    0x2c04214003082284040c0710982400700846801060380b45401e0002c40341a01e005000348011020050280e06082c0d1074419076914541031300d2882540b842110b030150b16003400107003240b203e8075007540c550340742a0104100c0740680c00507000845010b13220340500084e90070100e0040800528002c0c6401c420f50b000710b00a44c1c0b000c014185203850003201500c0d0103440c2d101650054408a01c2c025980c076200707864200740d0b040401c0e11004e844e1350810710203481802d1001400d40c440c01080b15a490006070800c42041010391003d1304088265040104603035540380103480c1d91000756800000340b2100c82803100128440d98580b9400640030b4002d03820b10360340742e0100301908c03c1a01c0072100d007040440c00b8003010540c070703648032502d028618002d1146031483d00401c4461240482c06130140c0d800000140900c243c01005030b01044802080721109a60b801c0d100303480344c205011f00a219400c0002050101401c1c07921841560b80040504130103036001c1c401902c44ea004004030f03034141c1e5400d00032500400d0740c0d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224756537 1250 224755287 224755309
    0x2f07030c08030903070905010e0402240d0c0f09030b1302030a05061e07080103020627030d0509030c0409110d29070f03140718030204110403020a050901030305030c07020609 76
    0x40710003181c66500d10380c1014100021074000104441c90040100310b00550622416046501960003540304c446180031090301d0407410201070424034000030602400764090340280c41c202050fa9400308102c184001c1222040c41c45c2c032028012240d104003203801801e42041542090344020200c2e00450740d00c1c0e41311030a06004440002610092110030054890b003501002d038400e1403480c01800740d60460740041d00317501a45480c520a2007885105540340000d06050102c918001801c0311103045014400400642c4060304090080c00352240001c4035041a0140088a580c424920350409501c641402403511000d0400c0c4c8104201907914050b004c200c03002c0030540c0d440c07140d1095151401d1400a0301c0d441405025104152510341c0c41d0320240e2501c0a01500f1036402d140036400707100f001d10401e090305602c1c1c03c0690700915108030300700503030300703890082088900c02e03103038003144669030410800320300d109101c0940810410000503806428000050940354070040256042c1644d00340419807105203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224757787 1250 224756537 224756549
    0x12010b09040c090c2307061e09030210060308070204180807060603060b1002150606040f0b180402070804031e0b04050f0606120d0809100524012f07030c 67
    0x28407030052007200164040c603021004c060500440b1205181d201c00d0050350003941080c0080c03c0030540c00204000c50300a1610030108104d060355a4000e0400d400040c00b0b11407045016200345052011490218000d1070102c90300b00c9641c1d0b0500449809103c043c00c1001030314051580000980030010703420740c000c2d000b028090000003c80e2800c52620030110340c040000c8501c9000d460b00c92180180e0f001921403802c80c09544001c0e07980d115040400c010340640d800c030103e000d009020102d80c0c1c100040140810040407889600d03201d8010701407004a02c10305001030103110041006001080d1982c10000e400042d00400001100464644d00a0a4400d8030122200d070880c0b122000308040402001d034100008032040300c1c24400340111555a4101c0402d00e03002d00c0030080004021900070f10014021031850740c410b101924204841d2212654454036511700b081029222480551140050039443c510505c1004180c405500d0402801748602c001d070f84c400c0c459040b001c4001800b840341c610080c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224759037 1250 224757787 224757803
    0x1140d150b040f0b070f0204090c08120a03110c07151b080a030524040b0102030d050a0b1005040602060a09020418060b040f020f03040f02030a0f0809090f060a0512010b0904 76
    0x1043c41660781083c1d04590002281d402e05012140114400b1281599255030450b00000c018609180228019000b075100240c14015101d0081220381140001c04440340c0c2691b0030000c15121018112042c01405445d58a0754080030040c0240207040002020b01c1446040a5410860300100c030352003601c0201d0115200940420b42111558050040c01d82000c601c841444001e2200d108a0404048080c80144a00d0b02c441c24050185d00034070840b18808105a400d0209281070003420001e0107040e048280101c5084d000e4440c618852019030f4182c0351254007034941521490499009440c101005a0380595280c00c9c80301100e801c03a02100113a81300c5c0750301082e00c100d52801c22007114103664005004900400c40ca001d94080d4000f1254050f5000c240804001c0f050300100e440c081907130740024035002e01c0c81d09180c02d1084200240402140455035201c040d62014940b040c9002c00359403154000c07801c08028807803858603410f103841c0d00000100010303a091003800040e002070000e54069403020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224760287 1250 224759037 224759039
    0x3050c120c070608130f0809010306090222120f0204090c1701060510020c0d0209130b0a020d0b0a031a04021f081005040203010803030106050d0209090106021506030c01140d150b04 79
    0xc2e040302d11580d200002c48420070251120b6140c40141d1803507010300511042000800c4c02d409da001c3d602c180054074400c14115203a250402c2c3d44400d07031500021034054066110000500180e0b00400341d0850b80e4001c0c40341c05840c64030fa00b4003000d482ca80800704c9000c003050300301150303602c100d000482508038030b0400070844516110500142c4c0c0c0340d031032001045400451a0a255440380b5004040140d8180c03490074240d6500b281244201c00c9401d0028002515003040c0100744015030060840555807003400c105440180e010043e40c00a140701c000c5c4516092602d0120280084c80b60550041c0054048249400c075181c050302000f419103469004900000148014488101d00e1a070140c00700f40e03021840e550611404551743c0c00140300b800200000051080400701c1c1540591300f40306400b4041044a503150140a912a100312112054071070006001500500d00080ea800c581c41042e11804008400e21450f900240d103e040006041c1e038655480b0804d082d44084454003c00080b01c03e80e40307803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224761537 1250 224760287 224760299
    0xd02090708240d110604090c0c03020c010801140f01030e0304060c0506013809040603150b10080106030903020c09090d14190318151508010608030703050c120c07 71
    0x10303280c0346038003102251081c440b0496510f40b12030812405400c40d020003e10914040002c0d064881d07500120398050500750040650307504000012251803098003607500d035400e510011201c03039a0912580419042040d0440c207a41800b0b6200074010740b0600d004100112402c5070549182d00541c444d41c00605800c01078000d00509000d81805041951140c14030b0301d40a40044504542100d030300709203040018040da9540300c0d8181240c505120180c000d20856640781404c600700b001d0605140031484c00c0c0310303085460303240040c1101b02d03620a58071303440e80301d90806070b003240148082c04c4200c09501c0303502c1703090700d00d59510080280305d01d401c50014503c1501405000b0311280c01c05020310b03100d803000c0c8a44021050a1382d050f01c440c86042c50000b803108021241008026416180a40078640010804504508a40009144402c045140c0c034a00d40c1c0c450381d00b401c8590b10f01c01d0b10007941044c01001c00092195006244008484041751800c818000c1c0181da1a40300c0e8214514540c8621010050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224762787 1250 224761537 224761561
    0x20904050d200d180909050c010e1909150b0f04140307060c0b040c0306052e0b04090f0e03040803070b070807120903090f0f030b090c0d08090d02090708 67
    0x114408045012000c0500161540c80c21110f1504041c00040001484e1070a0320044820041102d032809004480903402e210703489403010020a0b000505841d2000800d060040d0404140070034040200c54403031810b1a00e400034145070040710050f810f0140c00040c00f1440c60702900503004002ca130701e42d49034a4040a411011508112a40203821481c02000341980180100d000c0741e401c40025102540c1c4c82c94200f07823110440c0c0000342910b2600c07007407240c404900c400300d0280958071007000c0d0702801d1151180180500900c21020116001c000031f00c209011034004c1451490290070215074030702402030700d604541154106104992010030181e0502813100c100072f410482d2030500c0301c02400d211000a081210790060040055107404021040600c500b08500007002850820700341e4236220b01250803141114402a55071404a202060782d40b0ba0229041c0b1003410018481603038441141c0d00e002840d0000700420f94400110f43d510400350303d0b4402e00034490001661610010300d403805100c15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224764037 1250 224762787 224762807
    0x170d091a130c15020a080408060907240e0402070503160c12030503070e01121a040e01020408030a0f020c03010603060b090a0e060c160f05060106120e03090607050a020904050d 77
    0x3555610801405000ca5041c04034101900c01c0083d50340c007111181203081c0d14060a9801c014030045c00010001550400440c4041c060042c000c140c0e480c4994808040e0405101181e40e0f80400303d9519242e0070716401040c4031080b07010043c002600785010343d00e8450541e00400304600c0480d919130048020810b0030803202c7c019202c509206aa262415240140076010042040040c04030408c403682403a0300584880e61203c0d04000e0a000c40c00c1854800c406441651043e140141d0500c4a1660024070600075502918040b000842c1800100141201c3c00721100840000b503014070442c0142d252030a00a602c0994000c0c80d01046060f01c0d8014881d01140040400001c0c2e45040c4100c001d44001280e000d030014111010192221030342001e050500c1c8264100400032b1608001c1c0748100174021032003038101c401d940c56103eaa84001048081928440100480540c1080001d43c2c542e1a20002502e0624050b0341224501310295010071100a030555055907290320480245500361740c0700b00004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224765287 1250 224764037 224764051
    0x1701080307030c0305070618060f0e0616180b0a0207050f030a03020a03120209031c1e080402011d10090f05041107020f01020c031b09070507080304170d091a 69
    0x35261620380c1c0c030010110700b040000203041010001d030f90303028000390380c04c00e40032340381c6698240d66107002c54034100d401801211140c443d101d0801229000e40240071503c00e228001e0f4a10003180c04401c54411255040a082e4240e2901180c08001c03e403a06080058540402c4a0b0020181d5030300309410000c614240e9248144654440d44080c000250702085e076030001c5515042803206c0c90140142c15000c3e003e010600d980510500e40030300c0940408040f2144003905d070380c075000266901e0712003100945025010040c00700d5010000300700154464288a01c7e10701620241110601d0b41c0c400140c0c803405014098400150300031f00500c00e00001d40d0b5600020706044070704000c21082c1003041900d034051108064410490601c1c040510f90003408a1140a10b00406a6090010f100340013901c44d04114207160050b014440080c8419005a00f01d8000382d1700010010b0440d42c030340ea1340d0301c0255400c030f207000000c0c44103102035405800c0c02d00600d42802e1240c200100780010003a09031504240040c403003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224766537 1250 224765287 224765293
    0x6070c120203161404090302031e041409040b150f040e0d030c030615030f0f02130311092e0e07051804090c0501050f09090c07050c0f030607030e0c10170108 69
    0x401131504c07542144001c0350703010354010401d0680d5090517801d5000f010106036a00d040150340c0158004558010802eaa0980709072a543c0e000000900000b07030000c6800600c2e11100720041813200340400081c034003030742c4014264110049080003040c01d03903a125004180c0e030741c0710411106602c2d8250103014500c92042c5030400100380b4092408c1d041480b5659400141542c075046d020030380030720350040c603044805010103540c4c81080302110380e054400e611013902d01ca1454900e400103403900500840c0180c5049074840821a10101c0c0c4000d1030185002d0b100101d00c00e4040003400c0a410101c00384a011140c03101d6480f2207041e003440040d00000d40000e80700b076160284000006038050707039410035a0000e180c150f889100f098040d0340c0c24414144c4403a8003480a104014207000407500814205118400380d400c2c2450040c14005c0140351b441d078840d49900100005510340d0321961190300c106620b0401c8541030103210b03000c100c524060b54144030002c0d030448100020300c0d60b6541045c0c01064030b0001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224767787 1250 224766537 224766539
    0xe06071e140c04051b09060d0c08010f0b1303170d0f020309070e06030604030324030c0f0603090308190b09090303070206010b042709020612090c061e030606070c12020316 75
    0x20b65032600e0f103414400420340740400e22940c1c41d10b41d0b47c16500105e01a103000c0112060400c0c0223085000248295900d20000b5500410307441d400c3d10545003d02200d9140301515401c60791442892800c105110b500d000042c0803120650b00c0600688803010f00407400103035241000d51021b41008481c0c2c10500c640d42009003444251b031030026030264016018500042c1030a80314100700c4050038011004040581404004400c0c842c0034008038048802000f584690160b0310003007030b02610003166001d408103020100061001d104606c00d13100440301c800c80011000514800180108001c2d00c40100d540d002100700544550104613160141503010110750501d440e118150407490200f008850700180c04010301ca244069540020b403010f9401072125032600f0048483c0c0e20398130f0049075062030078816107801e200242000c0040316400d200285182d121191a080904200d07400940b0341c1d604a281001443c020072429003240c806881c4c10010041d0490131801014601117081d4900e001000e43c7d6a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224769037 1250 224767787 224767801
    0xc080c06040b0904090210170a0507021c0e0d210806031c020717060a06050f0d060527060108060105040510140a0803040803040e01090207030e06071e140c0405 70
    0xc1524100c41c10880301d1981d0b000300f0404a409850135403c020341102a903104a4490713504046009600c4e841148903c0369951504a60015102c0680f40d030001350b0480c41400303041258040c8050032411543c108900c00016480203d01e05c00b91940c0243c41e801484040c03444510b501000021030b2010500d422220707818100300007500c502c180402c8440101c440c600d1404010b000f84074020040c14002e20218841d143c200d00182c0725001141e05000b01440c02201241502e0844440080d00c200504950031041c17003503a40700c0041002803d0031054010394501040f040320080260342e0480d0769440640095498034018528049043e002503100310304180070012504070310302800c02214a400454205050310201252a40c1503075000352100e4080003e0115025000000070011191803d4034502c00f40c0e85d90740346408034001d5007002000078032880760042180c9052400303020340c41d0142409502190708028011325110344c1110844016a40406181030319400703015071070000d01c00356003c3c403d91030003c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224770287 1250 224769037 224769049
    0x32f0306010305070e040c050901120317040b070c05010e0a0302030901090902040b070605040305070213020a0f0509030706030b0312041d070c020906040e03160c14010203040803160213180c080c 85
    0x80078075617000c0311400004003440140700303c4000420010f8540665941c4407450011042c80645081e40482d81d105494000303403101c0c4000921454224a00c801a5125030f40300f110703580c12404041c0c1e0a50b40314000042c0032142401086001d40c46038004560360f00110001502c42c00c419400086041d1045c8000c011003201042100c040030b0f44413100142035640c52405540074010344a003e500481c0048903460b02940c594010700110305d40c0c4c1c85d01c50007204100e0040f0f480344906150560075810004041184a006e80c1000038014401410b8038495450300744400407540241d0300c4141d0516800c07010010000320300284a03000211442c0101a4440c1a00032594080740036182c907024907036480da003215140c824020f844007012110300394808400542403401d04880d003802000340c00030f205000000c1660000040b68120b0700030301d02445c2811241e0304180d030ac016804900780d07001114103044a2609a03548104403c03014101c0b888442c40c0c0180c10030300080c02e9030303030041d0315640d0095280c007010355614 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224771537 1250 224770287 224770289
    0x9010609080a030e2b02090c18040f0b100504180209100822060902030609010c0804170706060b0d050601212a12110315100207032f030601030507 64
    0x103041030842ea584802c00700d80c01a0b03198004007845c1e00740441c3e4100d003c0e02440c145810314003c440c0168582c48a068400c41441403100b074090401c0564207076982805c082d008841490291400042ca0780805000705404040e40ba2145000039400030b028040680c0f90300011060500c0d0785003c6060100e0280443e103140d00021844d010710142c040018042108280b10300a101c1000c0e00440d8075004a150810241c4012482248607024100004482c03100503c01d403030480c029580e074203296488603210540da42c2c0d10603072001200c210400125002c04c00038000c5400130196543e2495030b44610303003106011900082c242e24104044014a0400c0440d411441103411a404000044076181e00c19000312071540c0a41c191003100560300d000038180d07088680c0c200c40a080300d2007440b4548208103041d855100c01ca40e030100e90031208070300e01840d0402030740c4600603201c64011903a85039140d840f2010140c8a2605500c001c126400c042401800c140c00c503401042e806078010000c9506541d229034a41c1a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224772787 1250 224771537 224771543
    0x402030a0e010618140c0f0703020c0603042907080a020d0b10050c10051b09031009050c030d1701050d2103020d0b091603020c0a02190509010609080a 66
    0x20020640d0010a54005009058100c000300000c80d0f45081900500300c03846500a4a1440e21900008440c58040c644e4400e0602d582007e1800c40d02080018403504083d4003a0110702c128481140140c42e403100031402030f8002e11102e20030214000703890703040c02c081c41d00140354421003605024800703402c101e80c0703034003c1103005025807070b0303503026070801e00800000c00c60681c0080090903901d90740303401c1001466415060341c292641054240035903001d4403029142c142c00c401505010b80d050b50b41240c05488142c1c0003d0607900140c80c05800442600d88081090301c3c6034005041c01680c500d01040101c450346036905140300d0b20403800501e0720303002605105182c002c0c122428018100060840d0710041c56000d88001c2c08611955170009009400030700c4043c4681d841c042e0490100d150490358240306140340450500a0029120708901a42200786d005525206003461080140e84040f080c0740801c0b411100380c80f60303c1c9081c1c1040310030354040c1e0101052000c6901e00b402030420104030601900d070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224774037 1250 224772787 224772791
    0x703020732030d05160504210f140606011b020a050d14031207030b01030b0f13020d1404060c0504030b0c0903160605130e10050906030f0a0308040b0702070f030204 72
    0xc581501403140351552036071034880d40400120600402c550354401800f80ca21419800301281c08554252068030490084809821140074140850b01e44004042541c600c1504801f81420341c5a0f02c03400300701c1100c050704125403c40c804000003943e04c00045d44010402500b207002c000d00365008140305003807a007ea18012225200c40b2814481216000e2004868001c1120341e80c8524510f800c2d80302605560b60800a4104404000d4640c030070b002d40644080028a0030030145221020028949003691281c0740617a0240304054500050380324180000e00594040c0c00b65250910700b01c2c00b00d070050361003507060003410312041c408210584819641700c141000c1c8140d486480c40d0002e071074419841c1d0310035011920030001060095001c0050010a20030040240f42142c480b0900b9118440440c3e46e40c03c1408299410032291030a07020140e08504040c098609500e56040040e081154640040d8080340440c0305010030400c1842200c2d80c00309251001d44403003400d25058005220b19480040c0c4155 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224775287 1250 224774037 224774093
    0x60301060c080c120c0304140102150a020318070801140c07050d110109080d06030302061015030b18010e100815070302030c09030d020f1b0a050d05190804090507030207 74
    0xb880404c1a0766040d0030881d0704613203a1180c006a03550303035482801003100321040c0c022072986c2c1d0350001540d000204480d03226041c07182c0c2d07079001c070358002d41004100c02507041c1e604992490040c400d0007040d024000d02e10010440fa80e00070301207444440041c06030904800104a200042400421800d100c0c80b030919141007030040c40002c4c54007501c807049010700211030004111075046c0c0c4036440041241c0c03080e020385455688840301044910310520640350100b01c422491001c0038400e81c400d03000d500b0010110200c808a048a9102252091b00003420003035942c01400880c0c0142101d4400034041c010041c4031130303011045181658040948140c0a058001c00407030001507048042e61074035680a800c4030f520035901d41e0000d50325480c1e819450b0071030054040c040c0712008008184403015501500c02d0301250310308003c1c803901840c05802600c0c070b40103445050800107001c00c0203800c9203000c1d00c521912039040000d074004035200a000d010516104008c0180095500503400c52612443c480172071b041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224776537 1250 224775287 224775307
    0xa14040b0904150e0f01050a060216031212020f0a03061a0403061808120109230411012d1803020f090612071e140a0b03151c02030c060301060c08 64
    0x10401500b10a000740207501c04c001d4211800e0490904803101100d600c40c0c555507070027043ea03d54032640c481c41e00041d035000c010700c0403424554900903004e426203080012007142403082803c0381c00031045014503c6000460040c00c5500d40250b1024105680190b407000350006921651072045120080c08203880745800411120501c8009215607041607a0507907807041000c1250008009010382400c1c54030340300c80b905e98403100c400000300c1d00b00b07564800350303060310b42da01c50b60040110840c6960410a640d00845801e40c0f481030900030461112540e08520b00509030050f00c1720440d84a200580e40e20502d080015a03103000083c803406c2d8003910f02e40005c0d02c880c0080f40c0c88184c2c4580f00c3c42c542c404c00c1c0f0001007602550701000da411180304e110641240e15031000d0051890001001988140190790500600d080c0000640d0060009110500200441d030f01058440414003008070b141100e421220065050900c4245a411801ca0355280f07558182000901446600700c009400e041c0041480194 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224777787 1250 224776537 224776571
    0xc03010b12090a080a050903010c08091207050a02060406110d02010c05120402010306090507020703020a05090702062202040903090302090a0b060d0b010504030b250e010509010f0309020909030a14040b0904 90
    0x43c1e1500643c0f03030369a541118001514903800703c1000c80c046d40c60480000700551240c84901d0080303030f192026045424940304900c004d5000700c5000e0f107190180d079000d10010383c1c0303810081000740100e8440079410b40c80b80c20800d080c007803d45180401d41e4101b504004060754440100c5038030020500080e9040d85447c0012030041c0010780000c034803180360405101c0300940006071a42107900c01c031903580c0107545032005d02c10031045c203540107400750340054003240c81c0d442c08011034180714840c640742c0c0c03201043e0794000070203403049040d0580104120210500a509000405036800070110354203201c40c5c4500f5011481c58828261001240c0d641d629100c089603101c0d20031540103540010800c1c4031810a041080944880d9022658103106c11040070401903025200c81050140d05858444c1444080e5005403581502c01019800f0983c0d0f0b14040401a80c03a5070300711b40a0900d000045464008141c4080c24054000e100511078107024001085081105022900c0f0100e060314041420703150b80c0620f6030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224779037 1250 224777787 224777803
    0x5070c020411091905060306060f0c0a08030a0e0f0c090c0d060e061906080609060f04020d05060906011803060f14070309020f0907050d0e0f010e0601030b0c03010b1209 74
    0x16006091a20b4036005000001c09450000b90480f55411908040a00551101c0b201e115540d048607041c00024030900d004ea0242410b03c146003081072800c4a40707051305041c0022914201c035450808014045200310510035200000c1c0700700d0003030101104403103002c3d607940d0680c0841d0b442070304a100081d42600142c4203803403040480700000e01502c0e880d1a030f502e415440840c3d6071401114038004845509010105080881d10b2a4840c003040391150b0b400d20242d09401031501d82c00c81034443c41c40d06203442e00c0c8002c0c058042c3c4220700040502308a410040c900601901d2281041070341e821014080744880303c0c800440c0d510100c00038180c00005600c0000d0035200e060142c0a540d03107010403424540580040c038180d40b08417008900d49022604201401c101035584c40d000030b00134041c5e50160600c5900c54684640494116101c3e03171003042c011800d4540038126051031740c00900c01042000040807070107420050011440d410340d0f041601c40030081c0200f5402011400011010428560381072003a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224780287 1250 224779037 224779039
    0x60605060301050913140d020f1c08181203040302030703090f05220b0a1706010906060c061505030d030e010513080703200604060221061c020102010f090507080706020303150405070c02 81
    0x9000d52440c803c089c0d1901c03c5240c51101c14090300d1250881e032010b00e034110b001d0705003641350307800140c0702c2140802a110502e4440c8003140300341c8a0710000c010382400a5440f4038840e500031550381c1c1140c03400401200307555001e1042c001180c4002d006603941e030500700800f55070145503901e610007444484005082e40c9201b4541040e103503500468080c4a0800a903580000141100c1c0e01d03991780c0100e0411a0514814a00000c0403000b502c000560150420512010085200405c10f034844001070b041007201100f84006c00d55031424200d10308000e0040d19800700c00c0020001e250750217921405014410040000c0400c005585c0300480d8460000c582d001c5548403100312181460546000d20095000c4c02903080340031103250070007145100c81441076100e03c5014152008185a40d000b0310210001c2a000b2410355494a0001450a000e80714808500340140e004001c0d2a140c411810f042c0f4070745401030011074204208001d06190090443c0c0e02014080c1c0d800542940c50310000c84008070f04200003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224781537 1250 224780287 224780293
    0x1e0506030601030c17100815070206130201020312070f090b0c1b1309080d1a030a02090c04082a0d03090b1b030a08040c06020705090a0b0a050a03080706060506030105091314 76
    0x1b009440e0101da442c4429111098201d40385c42c40800b0741e510719100c0444038000107920500010f403030100030030092800944103004882c04c1c02c2003003050101c0030780112905000600481188014554411480c2000300310701d600181ca440c0e011114140c50701200e040c01072a41c0d0a20300308900303944030f01a4487c0b9610b01c94808200c18101c0d0b280c205020391102d105540c2c01d505243c100743d130911008182d9070912400800524401c22aa030901030000e00042504102d03c005120001e401c0e0810701c10014044e8541c0701046000c1d00c1021100d01141d40c0850040c002e41d841d1000000080c1c0010130303e010345411401c03d81c4c4401100311246074004402914482a01010402c44030454000344198000d500c98a0182c4046840c0c4000326941c144520400d50f0003071410010913000d480a40c425100103402801d0600016143d06c0800c41c2008140d0040b0398141c1c0010f91242848564420306000e014111142803035540341100007100c0783c3c0060850420036000c00c0951042061394850200c181c4111401c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224782787 1250 224781537 224781541
    0x207051b240a09380c010c020a0b150603040f020307091103180f0c1e030604031d030102040b0d0b1311071502090307061103040b030a061e0506030601030c17 69
    0x19030800d50071000b0800c012070894440428031900340110705a00c100740901e070000b401040100000402c18004205000c01c00400842403070b40001e0054a10308039503900145102c2019180031210180d000317001c0001044041e40303d4282c0d0b42c0d144211394000d40c0040600313850f100c0034000a410b0903241d91116021920b0111071040641c44800914407c00c0740f80201012000f41c813114a884003103238500c56105800c0303403590918529000006c915070910001c03140303259180c04c20100e460003c09440c1500814564108015260080c1403250504201a4000c0d820546080005c011a000c0d504144110a86844031a4001d0719901c0d003034141842c0701d8100b0311841c5940400c0400341d0340000000d69086101e10100a00c0394040d000702c6e04141400390050081500d0500200c52040c9070350601101e900003080001040d543c0300003c4e5000300c19410000804628040d110701219000c0c0d40c511800c1080100104600d5803542c05680e03112100b82800b03e0801c0f107500c021a5075041c0600140b00c2da04640342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224784037 1250 224782787 224782849
    0xf0804081912030608031c060302152a151e0c0409150b12040f0b0a02120609070c0303021b03070c14061903091a04030e030d030207051b 60
    0x400301c0308080c0503a210303445400c9a0303402101a03408a004001c0143d0040102207403141547d941002008403c5800041c4181c99900080340c80030640c85640d0411404546030140840350944218059124031201145d001c0901e5480d44495105002103000844c00000400c428003a210001d1220b803403000c942d200340f9140d81c030f990b100d0b0000e000d464607407450036540c070741045158035891007590b828001d41400e24824891a2241c2c020040080f03c2c440c3c200201c0b5400111a202e030071740902c0f41e2141c09030300d980d5025034496009000826007071082d10452b041c8550160810380480009405142c050390b540d5045103400746e1011403c903e03214600c400580d09040c4000c480c024010759400d01c40300c8100c02142c1040003024025016048416a590900314075141d00980c825012036204259034140e4610304144049074100498054001c507030f8002500c401442c3c1440400141c4865080840c2001950f455140d078810815683d9404011041c140080c982d5560025140e40d80c40250b0401c20080396003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224785287 1250 224784037 224784073
    0x60a05071406040c15020304140301020702060406030203040b060906010e040c1107080105010810050103080a050a0e060d0c2703171e040602010c030c1704060608011104050f0d03020a0f080408 84
    0x1c0f03003602c103445100004900342042050706005141160300071400d090400a00810711040d4500c3c0661544d400c0169130010780b01c0c41c2c060700c01000140c900517107904d041d06003030105410080090307101e000391208000381680c000c5404482000150340c0000c3c1c5200582013a1740780034907840c00c00c641744100440002d42540540240f410b844443e0b09480c1042008080e0300203540c8203001c0100f00d220f00788100034404d4810320203040100b1041c503000307141c0003050700440d40c603502c100f0340000680d4564501c2a1a0b98025020203501e50140340312201c2c0c01e094081c02c40c40c095003400f004065103000007402a080c242c200541c2d00c02d031040680b48070b440103040094a4503034450320602e0050b500304000d4180e0350303003e07114050b9180d40701c3d210036001885000c00b9134040301e0b0050044840300d6492801003144c1009210700c01e5181e00d02c454665907203040c0700c200001c503000f2002c1c1c04d1240c141d002000d00080d40c040303620b102542d80041089808801841d018a20b4085c54110550b036204009181c0c00900c041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224786537 1250 224785287 224785291
    0x503010617010e0703120f12050106030902090702150c0c0c061305121603120c0f0528050d2015011809120e04020d050f06040b030714060a05071406 65
    0x600002c1040f80da03d158116151070061102614540c62000003006d42030180c440f2030200c421a1501f0104015112111800c588003030f044107000039a10f544040860505850068110b4058001003400c00100040078210304001040780c19807100c0840c0315004000100f103541d94a5030000d03c0d0341c0e1204080304082d042d40d030b01e074440c0704d10500050004680f071000128201190302d81075407058180b2421900c521030782c8105d0030b84541c20411008454000b01c0d9004000d00705841c4108050302d04000d070320300d1116000801511410f610790b1020004000134600003040d501e9844a410b1600859030032002039920072003c18000410f90203401102200b03100080482816200203100401001415065100880c1c0030564010415600e00d03d0106032030380660f0070310000800040000d071610002440c0c00056035401d0703450009401c0030380184005803415006040061100750020845c40b413801404820944070080c420340944400581070724000d06c03030780c115594581c100c60740c04010081504559a10708007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224787787 1250 224786537 224786579
    0x7121a06010f1b030c02090a090b07030b1f0c080d0906050a0b0603060409020307120302010f11070c0909020604030c03030e01021e070605030a15181107120c050705030106 75
    0x1440020398960140110000b0b101c696034600070a00c44168040440511014040e8140400e0440c0c0b0401030380d907902498803481c0c500380d021810360068640320345a05409000702c0f050505111003012039880355070070301c1c0c200e2124103550010044080350503a80d408200780007034410b440c0010040c1d80d61000e0780000100034420380d0b0410060b600d4000c0e060807111041041680b042003080810010b15092300100c0609000606840301c0f25511340034103c680300540c100b140582d4603080c04009600c046e20407489040207404015150039100c1d91807180e005070a0180d8004c25681e04d42d0700d000d544440301500d010319408403184000c0b50701c03400d01800e1040b04d610443d0041c482c4203060004134120060400480d00841c0041c4800d0741425800c3e56560001450894a641d42c2d010608540c3c0f9801c82040040075038001c1e908128035241001e10607140484184041030400b0020b100006d250b810715144801c0503854008403861040c80c110381850790950005505608200d00400c5a03407881004002c5441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224789037 1250 224787787 224787833
    0x30516060903080f1c020c010b2106040305130b04180510030803010b070602130e06100512070f170a05150414010915030b0103050a030f030b0f060c0712 67
    0xd516a000c940e540d049010050245400f403140f2002d200c1258003401c00140c007424000c44540c01c080701c507401c903001003a050701aa9160007440c6030900309202c6030901240710303246135184a146041201c0d514403001e0b0000b001c00c9030020340660b4419a12501801600f4510001aa210790b07a0681d400c0e105d140e4511050fa41c3d1610001c80d042441c0d040c990f1080700d0380403070702d00e0850303281c1803c004a54008280c00e030303a00c0d80c0130021031849400c0f5034050340140c00703161000c03c01c0781070010500511111181c1140140b100c100316403103204900d0413060342c0c00982890900b5012413241e87c200e0300c0e500c05211901803d0040414081a02556003205225020100d00c1d078240300b00075000c10013079a40003498400318101c8000180700c8540207800000c0c0ca41c0309030201f0b20030315a40c0e0350390f100004400d034000e07261a002919507608156100c0515140310200d40381c184110380e549000203007005900407440340300c1c8000040c0014030750300900801e001810741c00090007449650341010f0300c0303a5802c0b4601d101112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224790287 1250 224789037 224789039
    0x1090b010e060109050402160b01090f0506010203070804120212010c0207050f061e071a0705040305061312110f010e1006150f0815090112020103200f0d15030516 71
    0x10422400715441010140c0d81c4040e5545400f0130b10009512003141d0746050003240c440440440d000140107402040f02c0303000051074400508004088600141c0078074119081000320701c020071002001e503010b03251f40a0101e014203580d840058032462210418401c1942800781d40c80c0030f15008542581181c2e8150b441103941c2200804011031842400003080203d031030241100c000d00907030350140c62070038407075140c2900b00d402e0b19010114694045843ea800900c1c0000d080c4200710050211796041110b030b80545604010720f5889241c080d00c000c200b41c0400c100300d0800764040c481000102d241e00002802004201002c41100752640c0034080300300f140508184c0300080e0014806000c10702d0300c1c403540d58140f400140c1141100d90310740c054482c000d0700d41010342c082819650380521310b00800603a82040100115440007400750b42041000f0040e5002800040c0f130701101c140c2c01c9910402c0d54140c403030396964215044000401220030b80c41c420700c008c40c8005c400c001000075400410507555600200035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224791537 1250 224790287 224790299
    0xc032a18270609100203090a06020408030703030b0604031e17190908030f1606060e1e0a050405030406120e011a01080c041a0a0e030a0312060605160b0618040501090b01 74
    0x542c0b0700b80d400c0c000030703031282c0c0c0c4550311403502d50b024507006151003042d55524411707512000142d030030941000d442c0740c2001844e01d0800d0341602c501c40e0490410307a050303400c09245480b5a5605103000c08119031309000182c0341400c000182c009140d138140c0c4181c40340e0b00c840c441c0d19841d00c00701d048091840400c070320100c0401c0c54000082600c030603441484c0c030346140204401171207046000220049076002e40b9000081404d8200c05105440b03201e03500005504c00000c0d1081d89983c010290100044034903081c140804244c0c084111402e03121281008002e540e00e541c800c1000b45250723101000301d03500e88120345803c00c0c0c1c5094510780309102640c1302c09080c0c0320240c2003013040c45a4032914815541702e079039501c10480044007400d00000c007070030800d0041c2c80417000b00b0300304000c801d02100020098250007181e400d451060700085c0c4a03524100d803c00700e0640b492040b00035108406803600003100000740095480b060b0111001a00d074020315420f04161400502a048418007140c01085030800440c0b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224792787 1250 224791537 224791543
    0x507030c0c020603010918080307020102030a0501050d26040306020412030f0f0f121d16090915020d0204031a0601020d030527070503030a110c032a1827 67
    0x94203400421884c0b541e4603010a03a402011260035206030070751015600008511094051446070019030009692484e010401c07208640051f044203200700414407004011520225108036464400b880c03450780259144140c0c08240901d0b4401403186000090114400d41116403035500039210340c0720b2078407000a008080d00c00f0346e5004800390020300f008072000da00354418014000c070a030920768006030400d0750716925481e03501c0c2c1100741c0300c0035803005070502c0c1440034541f1440c009005404007000540c4480e60303510403400c800200e050283d90041200c86c112903155046500440c2c0c01003103408002802405000320020485405015000d0120000f000c14028040d2034030031245686034044040300c40c0b0b00f1200c82c10301c400000d0081c0c41a00b50201303041d04c00b000148040211611040c100c0d84200140c2890300b0074060720b00d4029048000c51040d00d02a1440b00b40b082075100448504600c0c41c880494031070500f0323105911114074004244503c01c50380681824038012007441140101d601c0c58102a5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224794037 1250 224792787 224792807
    0xd080c0606150d0506041401030302150105030607020c150c060f07081b071407091112010f06020a17120f090f0105010b090f0f03070602030c1015050f0d150507030c 72
    0x52420003c000d1410328054641c02654850350092000518060150320900101000d03002200542c3c016041c4040c44065070000307600500c41100103050520340844000c0d1034116080760203001d4400c039500c04206418100a0390348c605441ca003110240d203000c060061a4007030503182500400c1d1382d2404546800320080800201403194400326182010640d182d03038081d030700c803040d142050050b00740203e00882c0c140100300303000c1401400746440e030329180517900210301b0680c41000c45102d0364204003d80f90f00441c450b002103401180c02044000c51002444d0f052080240d5451400070140821480b82402e00d000c9000382c0d00300044900c0c200202c0007050880e9404c7c083c0003031400c0c003804052203610f040d48814100d13210282c070101130340c2c80303035800b007480c20f5416004080503070400704001500a104002440303c60001c0e05062181031280c201d01e0b10010401d00603203014030780c3c48801e01c00702d0b16900344c6031940329408101e0050200070b135080318004017029260000001d081c46404055180326a007449 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224795287 1250 224794037 224794069
    0xc14010b270103150b0a0602010e010b03010b150a0c06020c031c050601140d02090a0801051f030b06010c03032d0c0207031110020106120b100f0806040b10050d080c0606 74
    0x304a5908644400640c2040442e03564501390701c0b41054419629003070880c100910440e000810b14003001441a802e486e8012041c0340280e14000e1801800e80c0c400340904040c0000ba85a1556441a1134084428849080010386464000107600051a40000c02081c107800f03901d0390611054071070000078040d540151031240c0054480000120580500c0000b007403d00150803005280400d624041800d6190950000c40300b03075501c0c0c003000f001c111100b001418880e035281d0070782000c40c11a501c1c0c010100014000604010f80c1a0401d400c25000780d0001a40c2c1880ca00ba0034046003c8040404ea2900c6070504901c6060a10a0300c1000c00c0c0001028410b8a90064145201e1707a1004140702c2c11484500c0c03104219901e034440095910a2001002d80c1c950040303000203018900310721000031400039984412864018001c0401c942103002c1b401c00d41050f4841d0460300386494101c0c0102010f07101c0e41007981e10003c1183d850f01003103116802030214400c941d003038a03072940d5410100060862414121 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224796537 1250 224795287 224795359
    0x30f06040b1806310807020f090903030a020319180210052a031201060903050d09060e30100f061a0d02070b0a050603150603071202010c14010b 63
    0x40307280ca5940071380c0150b400c0141c0b48100a03d000c00d5031542c040f451800c600744c4d8440320004540341981000c403418844414240c0310200d89040082c092a641c0c1b100038140c40210364040080390002c4080543c5c094290f21450042c040100441d80c15110000080012482240030180c1c005003d400788040d0342c1c540c080103203605c04944001752800c204091000107044a030004002c2c40611100c0115824040c041656079401114150b241a03460700309200804814403422031020841c46a00c81e2b890303da0445c090315103080011189030a0540e9820317003007015071007030103003148483e814000280d20003c44080f20700500ca010181450b80c41240c0c1c55014603590100300039460204181c4600c0140452114810010718081107074454818500d02910317010421078841782401503e21b01000a0301d000402d1100f41985400c114000070b50300d68484c03003030512140e410b54016095a000b41c42105405800040d010443d10490301403d0003490318001c0203104400c00392000000c1940164030062040070a010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224797787 1250 224796537 224796541
    0x6040506090612120c0c0a090b090a0b0402090a06020d02011d030909100b21070305100e0a06080102070b0603070605070c0b09061b01200f0715020702030f06040b1806 73
    0x38020250400c103580410f030322892002d10340c0b8000100041203502c04203409055202d900408101900302c203907000f500602d0401100025958035200c0391500800d4921000070098030000c08035000c2d00403403104507030004080d0310001e05e568010801510390b9007a5402040b400310020301c0088000010040c00480b0350060110499034180004496040360180d58041d891a50301c19000e982503200a4070301401840b880810640036030070f00c00098001342c140c01c2c1845203180c004050820300c1d00703e01c1169845910200420104c0c14a584404050715400009654074810340c03d0005501c04151002806442660303400070f81944101d00343c410765648050140b25062610101c2c01160300a82d4150b50710400401181e940c65400b440d400300fa0079249000410007020b6200d070070900c15450000321400c0c5208001c030000049144085800d65a40075908001555031110504000d000d8803000035010300c103982413140492000125184100c1c80344542c161590303264804280c040c2c00c0e46c074000e04981c0c00140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224799037 1250 224797787 224797789
    0x40b063615030a0f0210030501230420040f0902040305030d020a020721060b011e03090804030b0f01170a02101b020a06090e150604181103070f08060405060906 70
    0x1410035003026240c1044503516000070002810080518401c98191031403040040440c1011022443d90005070705003081250314101c01100e058902c0030094100e118403503078000150b95140c0c0050030240044a41500123040000342940e1544903000f84030003442c1080000038005214022101641d0b4440091410038000050b208080d4001c00191411344c012031001140d1005802c00800b4180c12500d040200c00310242403280803200304d034800a0401c00310050f40c1c105d2000c500600c03c0c02c28101d14000620300e46a0414500c2401a43c0009158081c110180055070303030f000340304e01e044e60400d142c15440e05d0345041050f0390b508140c1c030009401504d00c058041d4014091102c914454402d8564081c1d00380c00c550010b061800c46801c0300010a0103c04c0601100c901d904807640c0c8980464006051461b2100010b10b041c080c038410800044001030b084100050980c11041c0d451014401480e180c1c2003030300025003c0c070008091400010b10140001d00c0c82e1400340038250090802030001c06c0d0b01d0300c0e660 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224800287 1250 224799037 224799139
    0x14030306060412050c03010207061a01090b03060111160b041502070f0506091f08070207080a0f081303151407170f0c0702090109051b030103051207110405040b06 71
    0x600706807403a0017403000f082484d071802e00080031640c3c411040014840c0124014a03040c0c4c1410b45903034104100524148a9000c240c42100d401502c00d08080b10110340d1440ca0504e084010391210410545400001a45240072000342080c1d8035140040600b91204102c00c070b95548803441454150307030710100c042209061880050160034005040d03400c52034040454907454211070300b4154000f80742c0f0710410089a5050018001403c1c8000c0235085c010040d4440240700c1c268860042c1000700009400a5034408940c400c0c0002c662000d403800c1c0c1020809807290003040c20800ca014900071800001d6900780c424140c24500f00d11480100c90191250781101020305002045811455010410400540d9801804900900480e0008038041c6400c03421451003641c0741c452081440380c14030050000030070203c1e4004802c0c04bc002c0041d195015030404400c405040307032185403c03901c4e100c18030051100b406122441000143d481640c0004079544500000d01c003900c0540c0800c690384e01d00c60810b4241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224801537 1250 224800287 224800319
    0x17060402040c0c022106220605102c0601030c021c03020f13050a05030a020d1202032b0c02240621030d0506031603020913060f0603140303060604 64
    0x91410f4005032050382c2c0415201240c240c002403c1e01e10f442c1581481140401116a1100c01d40d08140c0340c0120038018800780b139041e20b900611035504c0b140014052120300c402c1e0002050300c090002002000b01d880030b546290074081e2001072125000000f8410b501a000320208200320b0745c014461094401001c5014018203482502019001c2000d8904110120081e00704204c0c60725540ca100c52074481003106800c804c3d0b000601039001602a0310150ba9003101c0641d1450704110b0600e11441c136840101d00350700c2034919002011081c06042c0b4003072000d031440b140440b81402c81c1005a00188041665500800300160341d140940720303808070000c40154492a04008040c0c040e502e040e800186004546880107000070b2503a0002c50000c02210031402007580064041d000f610010811519001507046140006800b076000040468050f023004018084810f42040d82007040303082d00107909000e00154071080d500309140030a0b010b018030000c0102c2e0301139480100600c1c9010f20b8407804450700304030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224802787 1250 224801537 224801561
    0x90614130803040b04050307080a02010e0d03110a03050a0e09240f0a090506030d0908070b1b010606020c030f060f06040c0512040606050109091e110c070f0303091706040204 76
    0x41400050070800800140000e40b003080b810503107490604041c9072a2860b181c0c40000f040d03200810202c0941d810a0b01030700c020900380d8940300391031554182038481026003038000f0190310801e169402450b0780400600086c920f55a180c62003204000704221110f20151401c910780110102c06510800c070f01c218106040b08081c181c1460001e0b404002018421a940842003d0380c44200f081800e150a01503540c1c010018103241c1441030803d2160b603610744083c01228000600099138804140744d00c082403007c6241d00009000300c9444420094403070894041540c041d00c1a080b0500980710086031035841a10740780c04410159582c1c0c4200b0001e440341c1e040c80e00501c01f00701711306c20860340191480c07031089006400104041c0d00e0040010610a281d9101d0043d540c900081c260240740050070388000e5410418000c50b001c84035540c20000391182001e441d611340b02c0d00d200090401c46c81200c107404c603400b0380c458892040d42d40e16822880320010780410b10035000000002e0041c900380d4000c40d1a421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224804037 1250 224802787 224802817
    0x12050c28110304030b070e0307031113020405060d140c070b040f03051c020919030f032109030207140d02010807050d020409020c0105040c140307030f14012a090614 72
    0x410755035030559002c1d420a50341402c500c010071503003a0b0070000070002c1303000030350040c0320052070342d2900c1c51019482c40c80b1500c2042c25440441c076401035601034401414000b0001a40e40000c8240c083c018a1902a00841d88055800150300c1d001050299003420307802c2003908800d5035480c0e41e511200501494110b09010040c01600c00102d0f10b41d45051146400f8480169101d07081c0c0104048041c00b11401c10300f08100f00028000100884c1029070100d81c1030621010034034040000e01980c1100f1280c110364641341c2940841856030000d902c004503070510005103042c80c83c1006104040d030701d81401a010441300408503404500c280020204650350440041c02c20f07854030003a5059074000c010361182a919071060006120b101368040004004e41d034084100c4a0082c000303c2e48511700352001030207801d42008000140001c0300815036908840030020031200c030000341901580380d80381d040d680c5010a841c550100107030040e40d040b000d0300c43c244c440120712400c56006861560042c100008448 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224805287 1250 224804037 224804057
    0xf04090b16030e2a010309021002070e0a020c0c0603090c09040606080606041b0507110a0602070303090e07090302040b04090f03050423130b03070803070312050c28 72
    0xc500031a180e0203809075001c800780d002a003903001000c0e282594480000713900043c01c5442044203180d1181140f490720394405440c1100040183c0003040c20b100065000000d28591000c880d50100b124410754828035800315143c0c450724085412401050301d0b0084a0b400780428031405d10341080030350b60124500301111520814080810b00b5005c007554212095520740c0000d0008440a01105511940580d070401415100120350a14102c0c03c2c40c040e0103016001800c6030901c80d20501402a001000d0800007003150360741002551504a48402d600162412002295442903961242d005025aa540f01000342c215004c01c0300400001048036402540c1d80d0700d94002840081c1000ba0007070090f240c1c0c82c1c41710316000c40050303841500b6529900c0c5095541c00e05600323a03074801400703561120b100800a512030801020a1030543c20750084950351101241010400d4ac2c000c01414004010010900c0503490f102103042d124003420460f0081c8602610080c10180e14421090349004280c1c80e015000c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224806537 1250 224805287 224805293
    0xa0503090603190f050f0112110f01050c01060e07020f030c0d12060e07030903080a09020108040b040206130b040617061311040b04030b2409161206080a0308090105150f0409 76
    0x42d50303100c40704e121280e26041040142c0c040400c074a4010300141c120300a409087e640c51260f105144421503100c0d060101500c402640b2641c11349813940302160080141c5a150304008810482c01c450410041c07280c0801c100748064048245c0e10019001c500414030a000c0038000d9802403ca4004082c0246d07880d10001910b064085000f4040c4a40313440004525440b03040c024002c1200500042c01a41400b0940006136405100180d20541040403070038103888a200050f818810040d102086821044d400301e004140c1400410468016031100c1e03a0f030100410341d000c00c154085405a0f071001103032100000000c0030303030040c94038260750640320b034689525030165805030340003030704140c601252110420034840f8420950fa4020601116581044590400028100e1100408044410034076813603c0980501038080401a00e011000500429849040c0181d45486c1084140d00060200d80451001c030707010b1060718040d125001c44c50400084401c00c2c0b00d19861420345440d00299a101d0007004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224807787 1250 224806537 224806541
    0x4053d020c0a0608070f050405030703060216020405160801090c08010b03040f120315080f1905070504050f04021f14071707030801031b050f0f010c0b040b180a050309060319 76
    0x1500144d25000f800b810a0b41c0f00906241c055007582e01400002c000501107654001204130031680d104601513581c40048195803a051141240290010f0414052040100315501c091120003c2541d0341280d0740c0e640c401035816100316a4a81000c40c1c1c0381c0005002403010f5100451340140101070428400392035036138080c003d600b4042d00900103541e90036440d283d0850803036410014216000103040c4421104507950b2158000410600c11802080d850000c10400740003100040034000c10400040c505401020036118040b06c04921400325000744543e880000c079020320a151517030303441403080c10190130205c400c0c0c0d0000d4420340e0544440c014070b0300260b84110041403410b10983c0c0b2012a545107280600342005112400044011180f80500590300c0f101001e000345030741155000d05a501031001641c0320010114040c104a9401040000307102d40088140e000310050004520302c524006412600c0303e8280d800100203400402000c12207280900c040d641103000041d100c507103000d1030307204101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224809037 1250 224807787 224807789
    0x1050408091512100f060309201207080703150207050604020f04060308030a0e010c0503011406090a0302030105041b0906060c0b0901110a02071a03071704150207030504053d020c0a 79
    0x203000208000501090070404696801881e187c10240302c2c148160f80d03050203180403040d041d01c3d0b00e04004c2110045988805007821303503031b0a140a890f4601d445030343d0b0a0700d0b94940d0105840c0d210300998070f9002c040c80c51084644581d04540078011903100d6508000c04141480c1000c0d41c4244c84100100205840030015801080050360001d00c4c100e070902841d003581d00c03015080081c4002400100f000c0d001341c04050b90819001c0ba8061b03036800d540300000d00503840c15000603405600e440100402c005040030361b0005000300100387d4003965903420344101541c005000e500300094951910000040002000311f8101d410b010001c2032440c091400d400c0c90381c22404000c0016800041c04110440c2004c0c242c44282e854034041a00e0347c81e011a01401c006441080306454070028400941404540c10351200e03e64040c0310b0030b40d682c0320740e410000c00c0b40e0854000d0300d116102c16008205210074132000054030780002410010184440702c12203580b03c0303052a4100c290300521040d80d09940d60506030138 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224810287 1250 224809037 224809051
    0x121a0c0c0d0810050a0b031b0409060602010f0510120201111e160b0a050913060807090213080c180406060b03070305010810050c0d09060212090705030f01050408091512 74
    0x940c00e1810f10740084920356241c4c00280075020f641d900f80500c4402008903603001e40d0544002c80740341e0704180709882c00e11803580a0f68405140c200045109941900f05001040c0d0648040c0055180d01584410343c050741c0c450b402c502d45640200400550040420b0450458020181c4a05804020049444482c656811042500b1540344880201c910b00308002c00b4106040f0320a041020000018020f403103989804da10502c85507481d00070721411500444040c04114040d901416503d00d2050082e40140c28240141c1d21441d4001c6004a0009407218060314014221145001025140244200041c00541e845521403a010412540c82e80065014034444e990003c1c80b9071401c410a801d10500f591120f000905200030f100540b82d1260603910101d1340c0500000300c0480e10318001c0c00a00c0745010720402d4003020010485162804a03203081100c805070243d03280000c2c2a10301600321081200d004111140900000655003860800c01ea074500502d0a00d0740740081505c4060403c5004841c60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224811537 1250 224810287 224810297
    0x1050f010302011d0a0303080603030c0708071d100504020c031902060f090c0a03150e2d030403150207031106040f021c0803011e0f140109121a0c0c0d 66
    0x10400c42d60701040c1c416041130911807a40c500190000000e802c0c0015120140030414841c0201e0283d40e4140126020100441e0840c1c5140f5030f1071003d66103822041c800c26601410300e803444c2554208450302d883c4200d928401e01d1503000c1c103140c100710094000750581c180a100500100c440010106c8021044402e03a8005240500e03100c01206c010303800082003603181c2d800000114103c0d45a0703075540400d9030f5001001051084211030a10020540c25403210f40f94414030f950300c07000c851203141c001d0b082d9184210000341846035a501c0c030794a2103548402081070038134100d031415846065028111862192034005410344811403028a0302e90150340941d244c092050500085252107500c080c8031800034200480b0440040d20b910029000512070100c4100c8210540b60500340c1c8809164080d00075145001080ea40701c0c1c0703001c08c039071200301d140c2804100107007004110380700001c00b0104142d6000c1c5000d56162440ca405154000c0d02500d082d0303084d1024400c41201100500034080300c20310590320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224812787 1250 224811537 224811539
    0x1060804060f060e0a0504062d0c08010608040f0501020405100503190608030715110705060901050a09020a050d0203163503190c05031216020f061302060c01050f01 72
    0x14402c40d4400c0b02c428004070701c2c01d0300030072210200042403a401803071034400254942c0d03103003841000341890140c14959001d40040741103015030b0754614100785a030368131010403001012070000e46038684280641d6001c2203042c000200050180b590b2046041c4c8503c0016003802e5586001c10748851151000c0b1001c82c00210400892606101205034641c60607481801030350700c1c010003030383c9901c030b03110740500080300840401d40e0350b0515811a0403070b1103550410700d51350032841c180240c0380c1d034050b0f494084039401c1c00041058048503024410314076400900d104c14041c82c240410500302c0c5e810104a0b098040c1080044540d1080c2e2038010040001d524001c054a06d03120142041c2d0140c0017181683d482d8000440364124400001d94003004014106000035411a90040d200c025088000030418400021501c107216007030701d0664029280b02c0300d0046203160303510069842d905421524083c0364803407030004008012440e04070040c603001070005031402089041c0c031307420350380d04443d407810350000c0c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224814037 1250 224812787 224812793
    0xe04240903030c0906050a27030f0b0703060807230a060905040b0d0f0b060d06020a050405040501080a02280504020c2d06010e06060906070f0507060903230102040e01060804 76
    0xc041036400036260030000d040c14901701a16500421011404210601031745240c2000101c00d0b403622018452184168a9624a01106c5410750210215011400b40001c0f4001c0c034040d00406041c0c0c3c5814024011241c20030340400c000f043d5844813200c802c04444e43c0710403280c036040d111401400040d5140c0b0080307400e0400740000d6400041c005802401c007a007240c80802c21142d02001040d80c00002844d0310785030480000c0344c5070440c0c3d0000d0005440014070328100c941180042046810580d02485282e903120a0ba5496040aa0019400c600d42d00e4031079070455038100c1d100c503070f190a51095182c00354481000c1030490300600210f0000b9405a034071852041d60402d800c02250070b0400c6100d080102c11410f0369101d000610604090b086c040380424101da40340c2055a81c4031501030030543d03d5003108d00705203d00200304801613429010f1008042260381c850340c0c4c00d00541e84c000060450034503825010300c00c085181203810703d0300d543c00d00c030200f0100c401c101c2180c000c0005030f0319803c2c0360620341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224815287 1250 224814037 224814041
    0x20105010b0906190207080d0302040f150203090409061e050a1b020d0302030402040b04020c0c0f0f06090f0d020a031a07030c0801051012060f080f0105040c0e0424090303 75
    0x30308015071805052280080c5030342d40c4800c54207800d80c0c2c401c06002441032018240d25011081c1c100c003540e4002d04200c0b4036410792650180007211101c04c09000495990303081c04980c56108649800141c0040003410b1440c2000c0e004026a1031088a0001795034000035850003a029800341052400b9072100d0074042e03110014040c070510120b50580002070300901d100d02a55590f040c0070700c2e4040c9a0044000b070103541d0790340d001da41c8034100944199505d141c18081075880705081101d0f20701c034403580308042c522820708000218203c4006400c02d031400c0040c1c002c00802406002c403240c1e01062000503540140c848a003800002e52040180034180d5400c212400031400005002c1c4042601c7d00c00340d840e129601c00c1020f81100c4040c1e8005007407444404044440d4400d1840c0b940c10581491000540342410314500c00171030760300c1e0707058907a62f000b031216413400d070b07542603c010b0140754014606002c8035841d0455544c002e482055a1480100150040030024180328900003140f50b44440300400d06400d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224816537 1250 224815287 224815289
    0x81308030c030c01150501020c090c0405032e050c030a0e0703020d0f300e0d0c08070f0614030a050c190f0e0117070e030a050109060c09051f050a0c0f05060702010501 73
    0x180174800341428040000d43c0e802c00c0b82c1e0f003e4880c003141008600014200403c48014044c084d09a514144180d5548011458403002020300901c10042c41c464010080c4600d9000e22180460b17145103032690140f0307001500442e200ca101d1130098610000050f581c412915111a10a403032850b801100b80c14807000403104048059120240f000182c1125225141046e46c40109400d080780201d50315404a460b0a1072000001e0507802200380201c2c10b15400035400c0700300c070924420005041d40300d0788100c40e024002c10000f60840f00500210b40d4400d50754000d103910a032510701d11400d2104088000640305100c603c500003246030084000c4040340e2240360031742448804c0c241005010b04c50418100030340c05c0101031004000c040d40f0818800d07a024802510b246401070001d1100d40c942d402c0c0200142128030012003c1500c040c0009110306007030450302c0a0071244000d0b03c09111003035009940503407001d800e82040000200d0f01800089103400022760503800344000303049500d030402e00a402c441301 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224817787 1250 224816537 224816561
    0x6060e06030d08040b270f160f14190b030402131802150f12010f091512080909070203090918120918012301080402060304081308030c030c01 62
    0x324484001a840e082185180c0151744007171000c403a9511070030200d1224000b00c10440700794440e18088101310100180110480340044190303114058440b0400040c46424412203c400b00e0025041100c06013a80780130315001e0029090200e000700c00301c402d200711011034102c603e220402105100660900c050440d91002900c0c80030000718443c81e4040b4101311070904002e224011800015440049017000d9400200c40804229219002c1c2482e11031014024041d110074195040d40008000025018499044641700480c2103c5810312464203a042c840d81003d5440320f1003080004202d40300c00b11410300c20314450b07001e16142d403103a804020352a0700250034030851711014203440465010118580d01d07002509801581c1d940c00d944045442c60501018224200d90500000203001c40c2d85030300c50340c19881c158003080f1041040c3d0011340e074502c1c0130b6030040c1d0001828400070307002030b1088006002d04880000d84002d0981d42d6100c03549540d0049100719446d4002007000088140240580100081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224819037 1250 224817787 224817793
    0x1020310030f032106030b09150705180a09050105040b15090d11040903020f0706020a031e020c040501030c06090503060610031e060b0405010f110c042706060e0603 72
    0x82036180c904004403103001c0600040504490002090701500c0100681d0a0b001080100c00000d80c05078001480c0c107220542d00302d5958400280221408101c0750600f250100001100352500e40341128540c114203041030503008103001052072035072110318600c02401c0b5071070081030070f60401e0244026100701100300ca00a002e040355000303e58802400317075074207100265401c3c41a0300c610304004048420b80e00c0c80c0c42e04103161400210905070b011803071101c0c0d42c2540c42255289551004105d0345c0d180c0392100130b400100303c0c58412110245814442d0341640f85881240c0113886000d000904550b4280d200b1200720880181c00c0101c07940060707081c0d006140c00c4001e0300c881e29141d00401d00122030392502d5420150388288080b8490540e0742043c0f03406050035001c0140d6610346240c8441075016000352070129109e1003ca000c4548210307040030401811601408408402d44140b01c0684810502d00099540f015440400340c0c0e091050b1401e00d901480307011074054a0200807400c041006070106000390 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 224820143 1106 224819037 224819041
    0xe030a1e0c020d14010b0d05030405010c08070b16020c03071d13080f180904120f09080d031a060301030b1819060905010f061203202d010203 62
    0x132140f00020403a07011520200140c0802d46040200503500400050005500c14005400994031460380fa500307141265503030f50f0303090804031080e0415121201e805609290b040241415400c0c068001e44500360800c108503900709007503501940d601a0100c0807505041d02e0f00300101c001a00000782644030603103803610441e01c0c0c0c440002e25016110180c0030040c54501558401d01542d80301e6000010354401e824192156013841c00c2c2c01c0c0c140542c0c0c442c0040c5000092290490035015941d0008402040d075585500c072824004200c2d02850040c030042c0000350710140095004030030301452107107a003c0d04007240d14228044108580f4111003095a0b410090203410030307100c0511a000034085a18100c810741d007200d44503c01e00d07410702e01601441d004640501c014900b0510104d00a1060200c0b8044017807030110809040c1200c41d01d041099400d60242d800d040503400e0348071b00203600d18 = true := by decide +kernel

theorem cover : BRFrame.Cov 224640287 224820143 := by
  have h0 := BRFrame.cov_init 224640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 224640287 ≤ n) (h2 : n < 224820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
