-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:11:26.898383+00:00
-- url     : https://prove2.me/submissions/5cc3df34-a07f-426e-b756-fec771292ec3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 774640287 ≤ n < 774820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 774641537 1250 774640287 774640289
    0x507050721120c090311012c061201030515010e0f062101090303020408061f0b0a050405040c02100c1e052203080315010c0c1202041407030c09330513 66
    0x507070313602c0444600f5403c0508610b000b92000301c0c1006500e04000180800d60700d014001e4900d0340c41034050180c3c212000848500a20014a480c610300c07000010800100240c2081182114011198180c0c0e071a2604900103108940d0380c10507441110005890745030000f103501340c011a00450752090081c003908542101c92940c4102c02080e4005000e0000480c01c1000e03584c450801c4c00030aa000d500c07244a1a90b618481c42024103114001c035451802d5400340042d90064400a0401c005221000800039a207620605460300c11602e8a440c61929503c189140040f1086d9200a200001c1d001842260300343d00090f0002020005032030303007a507807203480400c0c0700056000c0d020143d22424640c420701c030342000f44402207050000c01d40c0780800140c1d24004410448600407505a0840e05034008a000303482170306010b2a441ca003d100304600150944e101c00100903031a52000d0769076440300541e035068088842203405180354011000041000301070500741202c1e807807420314103242c0450303d204220011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 774642787 1250 774641537 774641561
    0xf02070306180219060516060f090f12020c01050a050a091701050910020405030a031d0d06020406020d0c0203030304020f0a0305060106350a180203030c0d0201050705072112 76
    0x4428010540c513103485030400c001c080300d2007024220314010016000744100e40100e2142d000100c410b40a000c8154001208002040024404881c05250880506078151002c481d42c18544140862403440010742e0040000d042e122039160090181c0c090300ca42c0c122032201810056519000b090607144145840c0b403003030440c0004a0b0382c0c10b10803c3c0900b0185111041d8540da481400100701d1564006071200c8402e0f01800e080b008084104255034031003520200d903e0f001031182030020b003080b640d940100120b90850b0b007656080c04651100701d90102200c0d01c0a90706920074000f0030054a02540e83c0c0d22580001443e0402e2542e8030754401d17003010f00c00d0380510003240000000d076688201581d08800404880140b10a5042003641f840b410900081c2c03d015840703680b0000c40e074016913440e40c2c0b051450b030010200c036140c0004003419070380e03040707020030050055007030030040348515003c0e0741980c46c032503801102e101601003400680310650792007010b0902040030205c80344c000d0360054810041c5d2542 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 774644037 1250 774642787 774642821
    0x303020d09080c0109051903050702091905070c030f0201060315050c07050a03021b010903050d030c021e0327030d0e010c02180403020715051e0d0c02030310080307120f02070306 78
    0x340901b411400d08411300150300c0540341d0300140d8030000c1d6021003220320541d0304480340e000c01c0c0c40341d010740c82100d03c0c0292015040351800f414404002d805c85c44200c510341c86650ba1188541412104a00ba252240b000401c00e401603081c046440d580750308029403020002996905000c0c082e02c440b442e01c03d1203042500541c100125030700200c80c0180305c20f00489420b0030072070701103461036643c2a82c5819080c002800c0540e911050072800744240100483c450a40084101f201041500c6540b0b036400303841d41e40c004070160002130300101c0c0617603813494920310300402421009960340070540300d622002c028170341000810181440141d50742c15802a8000c2080c914424a10b02458040e02c0c04085800506040501c0d850000c142640103049603a034017102203043c2c1c0252442c071900200d41c000c1201580040b07003458250042650b001010390b2040842c0b020b902980c40c1c2da44511601c0e48500f000c0644415600c1d820b803810a80036500400c5c05245c41d00c1206c5090b82e40740c54920499800c0076202419407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 774645287 1250 774644037 774644051
    0x6081905033001050303030c09190807061d100e06030429012606130314030c09011803020609010e0d050d03021e250201020709050109360303020d09080c01 68
    0x11034a030b500e40134081c00e800071071071410503904500c0680541c0c3e148074422039641c885e4980300140c40c081c583c0100002e0302240d02158940070701500c400320140c000c28204420140f440610f20302600c240344481d0013074407508158600079007404416440184281c5094502145031211065090413001d2780070002c03440000700b5410149410510301c80342d8810070030000100518000540c01088240d00940c5100e1010300700d42d041c0ca02590449031601d801540c07004048100503440343c40c08000c00c100103090f82d410807800c1078100c8210740a078040c08003035003260060019600950080c850140304860080c1908072064441c0c2c0c48a00c5d10b403060071001c000075004602c002040201d502c540909015030720b2458100002c400d00c03078a000031a8000580c540c150000c107801903900034049400a41903d00041c0640d40e100e50100c00074204d01210391141742c501ea0402c10455662400a64a031640c407042003440c807820391000c601a400012410000c250341d0300c140000a00080020b010088110b00040703542 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 774646537 1250 774645287 774645367
    0x3041704090c1e080a0203220c0311060a05190e04090f0b1e04260a080702060c070809090405030d020703170105090f010b160605280608190503 63
    0xa41e0300311040b14460000c0000460f4564001029560020030f05900603100e0365000f2482e070440e110035001400009600980400f801002428001982c1c0124031a101c016400c0040c02860b120340c50346000069070034483c9004140843c4900103002020346026042e10010100140440340d056408076102e2120a031003504000241c0409070307100c40141d15550900d1070300d01415201d04001040205126181c603055200f50620404200100c83c034080c40179241c244000c4040c1180c4c00646802e0054880c400c00900458046c50413101034a62040700c850905c228941404181e44010300f08680d28002404010701c0c00c107480c07001d0300c542c90080c5d51380f0344003040d0b0325600c0c4d18124041c0c111500409003081000a00701405138600e0440c2d2201a48c1d80d9500b070420844c141c951000c1200400c00ca00b8201802200340c1229480001d54424221900c0c690360072041c0d03081103401d00c0c41024910b4010040441c481d0b00081a10751003240520152883c00311040c40d0309541c00c80e0712484540c0d54205000c401c9103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 774647787 1250 774646537 774646547
    0x403030b010207080309040e07030b04080a081308071421120604060501020d18030f060506030c090421020a0c170f060c040b16020901080d030b09010b030c03041704090c 74
    0x100c00400c0c00602490303030404d40103548a10444013080e01417038645036609642e10082107a100256004205012103042510b44060b80303600c24909800014042008602c0c05410004041e1000341d014a1b110b04e0300042c0e44e40c049a00304011040d011600a0320340c044c06000415100680040d04a00625511000b09290604060707010b01554000c0b89890717010301007030b44c000450711241d002d1428104954990300b040c070041090140c200818290083c1040020014180c1240b03009139021015126100440014880382c0181101c000e8146100c59090b18140c2d0707900d140c52a41091644103499900d0a51380300e5080d50f00144d40301c482211440101c2010804040c0003a1655030382e441c015041c1c1d81040807800d02c40b8052402201024080007900d031000c41c05403c8024512640030f40011301d80c0d030399888400d032107598000d01c5d10040303820420102c416260580300181a1082000c0f450b00b07544412400325213a81000b44201c42008880f402ea9100c00608c40240008207480280880d20401452700248 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 774649037 1250 774647787 774647801
    0xa2f0d110f0307081b0c01050106090b190807050f120106140403030e010f0504180f050603070f091802030f060403180b03040609052a03060603030a1706030c100305040303 75
    0x100da44414000300c4028007100742100d400180c00e250034607564503075022080305404c010814082900001413504501481900058103c8a5545403600000d81d66043c85900b803058044072400c540700805440d400d2406444010782040d07413803828500308500120030348100e07403240c00b40c05694078003a00100841d603401070704040544146590305041914541d009844c5140c030403126414869281032146181c1d200d4004c1d240201030501512942c0001c00d50007000900750343c89822119802e0800141c1e26080c0019500200c4042c5081140b21504e0b01490500600b540c143c0112019940300e102c10140c1d41c100117108040000c1d80142000c1d080c14a406081009031040400c10b00b20300003810007000d82410245c0380e005c0d80002000c41d1340c031240d18000f401e0039044030708105901c2d45c103204a1103046130110044000c0304150100c407911303280d003420150b0360700070141c00b8000a128403001c21003007000c1c07042090f001000a01114015410403001401c5500b40b640d90600080c2e4071010041895890b0007401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 774650287 1250 774649037 774649061
    0x180f050c01020d02062202180910020c0d12020c0706050c060f04030e060309160b040f1706130825030305060103060b0a140405040912080109050f0a2f0d 67
    0x50f211140c6002946440f0010402611110126200340302d5130251407194450703e60041584c50920f0b00424100641002031720b20740d81c14800e210307080000061034801c03200c1044851006207400001400121590300054907240307402c58090241c15410b0f04200508008cc00058072100d84402040318824508900200340d800441100743c03d000200c0c0c1c02c44003968944030195100743d0b4958401891a14101944850b05203550400c10001001c403222401740040c6c0d0354a56149901503a06d00e0000030301d451032290805503070412008121001c684c80b50301000c140c400e010040c240048a03452602d0481813154a02600204003420020154076100b6030783d00003800d0800b00080b50401e21208600d0203800c1e40d04051119103a00040400c440d50103031001880c0080041c010b00c0e00e103207007a00f031800e5044020f00c04a03520400118103103132a401070302c0c032800c5640501c4000d07aa131080300d02c0140503003070303645034110303000f040c80c4082000085d41803240c5807420690f0325500c0304502e9135030045500c0c0300210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 774651537 1250 774650287 774650293
    0x111303030302040e071b08070503070b010e01081509151f0602030703260c09040e0601030f0209012106020d060803030403031e06030b0606030603070b0a0206090118020102030703080a180f050c0102 86
    0x403a49940c400c8008506d640140596031075070454540145940f1581101501e500ca00400000f1000c642d84400340c140c1d800803043d10411600e02c040360303580e014292003408075604080c401d540030311081c5200a1340300020001c900c500c040804011070071010a0b4103c4401a080094078038141600300e02121010101303182003a2a035400404d11562070f24018000202c03001e4001010b03009540c8581228000003000c1d825101d807540e40e0305d81964521402e903000c85c09500c00354000120035801200001c1c1aa0800d4045800000c145e5210002075020085e0118155962000451042c504101540c4114440e031000a20105206000c3d0360f802c5429600301e01c101e0806c1003d10004241e40501608083c0c20b807291a12a100d42c00017908204a61700302205205000c2400c0010355030005009015228641c000c0114002d503004da401441d00407103019000d68020480000041d11401c0c41c1c41c0d100b8410900080c81c50100c900210804413602801c0c0d4002200d288030506001050041d401c1100d400d00003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 774652787 1250 774651537 774651557
    0x309040c090e06310e0d09050a060e0102031306030509070e070507030509040b0d120905030606010917070503010c0203040602071508190e010f141315111303030302040e07 75
    0x902070036002000d40c1e009080f000d441d145881030100b042000e02003810440b001d03040104c2c42150041410a00c03ca90720711819004188003070041c0040c500782c88024000c030403141d0811001341c41e230800005549046102c00c00002c0040e00303003210218050513065a001c19142449110340303180a0071a00180c41100014083c802c0c01d0b600041261641030b0300d0306005480e103801400080040c140c0508190300214810040410800c902c0310700082028592900c13040d01e0b27140d43c02d2507030750f440469a60780440e58400007480b600a030407511414041807101186e140ca03231508080b07070030b484200021501603840440c0600100750140a44c5000c9c10b6010020010074038080c0f4000c000000c0545042110039000d010301030034482982104075180b9490000303100b8203401a6421000704402440d8030760180c8a800801c0943c80c1d01b01891071142d40002000b03004010b24400b90700142081002c0d12980c0a041203403400d625001c0300c03044003d500130b40300107031585c0c5003211241c09484000c0641081100d0000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 774654037 1250 774652787 774652799
    0xc0612091e0607110703060c0c150902010c060b0d0203010911010207090203090c04020c15100e06061905160209010801091704060c030e01360518150d0b07020309040c09 74
    0x1404583c006024601200d0560036515000c0c180300303964001800301410301088810340c2e90400e02c0ba50049116002c8200040700a80d01001129a80c0c0c0c0003c2c0024000c150300004a8126003100c1e0504200602c0b07203100245950003c1d08491078800304882500f0b2904074040b8668060040d2401000c41c15425440c61400b01600d5481d69100c09925110b187d01182d030922030f01081000301c900f84191b496031307036090a000c00003617030300120340c4034142d11103604100043d1070781080c200390f074482c0e81d00340524404103041d61000d56250f001684c2ca4405d00c42c500380040056a01c0e009a0380c002c050003c000503190609080c841111a4041c030302410107401008108243d991101e400310046805203000e10070002c184004958080c0c0c0140315031203031070002031455241881c40303501040205800c2210f005195507001400541150511150200702591001824540744090f40941c1d00340003c0102128012543c0c448400c2070082e03480c03200580c00410781c1200d40c20035101e41160341e0124100100f042c0d140031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 774655287 1250 774654037 774654043
    0x130614040603031e0203040b0d020d0f020705030a0e03031611040f0e071a0d020703020c0306090c15160807031d01020610091a030124090506210c0612091e 68
    0x3e1002c0d050121000c040b119134074400d005403800f6040e10108142d076141c440c03444c800a50001140002c08030315000340000240624400c803580240c2c410301a40c100071042e802910000d0b24407135440c0d01400b0400c0f281903451040081410000c1c03041c0c68000203100c032401407100710b85001c10062091440d12902c0c0403001000110358084030000e090f1010348003200c0784039115500987c0e8040164074008076107002010340204200500070000d81c00c81d905565040491561502040380f0140c000d80c04001ea8051070304074400074411008040304a96203070040ba65170043c140d01880042c0c000031000c0700405566100c100000000800904c02000340e400c1075180c000c1e041c0c10501c00c0361180d03691400501c0d076a120300c0e400040030010040c002c100007040c0c1c00d80c190b006c00d00c0500c1130036500c07017120010480d44803d1080b140a40701c05081c4014416140e182911544814140c9004621413448813444942c1c881e8010a8001c0550030010081e0800120700b51501e05140e480c0c10726990700c8104280c07442800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 774656537 1250 774655287 774655307
    0x1e021606052d090a050d080f37090804060302070b0106050a02060c0711101206061809050403050d020711211c1b0605160504120803041113061404060303 67
    0x4200004815265402290304e40b80b110640100540201084d5500c0c5a170040c0050307110740204070101c2c0b01940c1c2c10400b1828200100d40c2e448101450b01d126820240200181c0d02c1c010300118000509088242c4400d500c0e074000d80c0c010b0700003d07000100401005100e03070382280100520300b4200e0400e00300d07a030017a41b03c40d4001c06d02d42c25400d0205000c0148028882e0111403120080d1a8030041988030600410302c0491500c03003240036003480e900241c1c1c1031191501c100d118070a02c0e170f10b03281076003403d0900028141c040c4c4281c0c100082441840c0c0d000f44180300a2034400c0c0b05201e45a05640c4d0701040c80721840c40c0c0341d041d14481c03c031309203402c0c0c03150300200c0d441a000390310f01140b400038604100c081d1400c4800d401700b483c0c00090a0060b404201596010601850414054640e5611107000c01c80e203912550051400c06a01c41c60010006058500903603041445100c658440305901800f180400c0728002c1000c0107991034141c100000c0340001e1a941905009603010f1280d18116203000c1c00c0780c400e07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 774657787 1250 774656537 774656611
    0x30c0c0a0308041404020426010524190503060a0903020606010804080304060903110a030309021804020604060f0306090216061d0a0b0a02090a0815070503191e02160605 74
    0x84c4100c8440355071554101c90107404100d041056142c05410b5507030b240101207c115085628000120307820814440d0551001036491012030a1650100d0a2000c100d01e601c0444900c410000300100b615501072010703912610b102d010000b400c0109042c000d181c41c501a100d02c0c18040024188804900d07032800b101d50103904041d020400080901d4100c13a9050300e6011828640184d6880c01c04041d0301d45c02c0985414000c54203440041e42c0a45186607001c2c0545000354003030b00800c030800086000d03461075402e80c0704506000500b65504c040003416a0301600c2d4000c0740d5000e100804081204501c00c00304805071440b06000c1c0540344045a42c0d40c1c0103400b070080c143c03200d00301c002001c4058640407142010b00103000301c482c0c0d03a9550032055403540c4840701159920000350004071030511610580c0d11035041c41003d02c4c1c0c00050f10388000010300c1c001da0f00171400b400f0388003d03000124035030000308030b010002842c40890003440d00f0603034111140070301030200160120902e502c0b4031401c803214541d0264 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 774659037 1250 774657787 774657809
    0xb0708160c1416092a08090115030c15020d02030a05090f120a0308180a031d151b0c0f210a03080708130c031b090509030c0c0a030804 59
    0x56040c026020009449102d80b9881090520390410400160441c22204020018086100412079000081081c125040103140002541c2c0c0307a128441c0d02d409407c01683c00000880c1d40840168001141854100340c841c641c000d07204100d4244003e966a20301081d901c01342c0545002240003d44030302c01e101400c000c0100108d89403400348e031b640e405190285001000440f4820002c6001500c41d4910350040c0d01044c583c000050351005940f821600c4216031002602d52100c0030b94040d03900000003160440071040604035181140c8400d41400d2016411003180b03611226101c540e0418102e281c00007200d00e0300b2240b018042500c800110000041040360301c10960a94105480c0f000c0d1030281480050b403040c5144030042c1500103500500400c41940e8520a6a4684410384801c0c80110002400e0780d1080400b0404900d04840541010211414085000c0d640306202400c0c1e0b07005075015601c0341c04c0040d07a4003104208100340d034004641941c174060542e02d107455150042c0118030035005525 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 774660287 1250 774659037 774659057
    0x80a1101030c050c0f0f0c15030406050a0608011a0306060d0f0b06061608071a010506070611130905060a050102011517030d1a12190303020d0605040c020303040b070816 74
    0x16000314181c1c0c8404558070304942c0000c04c0b90442e1951030468540c465000c7c06100d1908056041c0b0302030402a80f118504020b1031f5480d04d5884000400b0020800e0507041c0c0d440c607010a4068083c0143d031403e0030750540028150014038105414100d0180030240700b03458410060b40007131118019264201d822001a8880350b54040100303002e40300d0303920341b148011440301820040000c080003600105010b100000c0158814581503194484c080c095240d009600303000d00000169a50820309000c08940d4142d42000707058150301c1e80c001940c0d000405a80c0d1203000700545401c0107001080140340910092001d503c600103400e50400d43d50141d00c0b1022071241d15459101810021180c0003400352404020710110103030700e862044440c0908030f21440564100d8180390700f00080c945100303004141e4002140001c0d80d0254000d501101383c07403800c03540702d080008e02030382d961003011541d9060f44c000c0c540e240f6017440d082e4000c050007041e64091121890910254041900b07017202440d0860408200302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 774661537 1250 774660287 774660311
    0x43c0213230f03150618071112210709091d060c36061216180506090d080406030516030e060c07030320130807050906040203180708060f01080a110103 66
    0x58031031504801d0005003100901c696240d0240790660701d03100000527a040181c120201d100144180b00c64904145c05000c80200c100440040c803540207400340c00e22600c5c0b42ea0310f000c2c1d102034802003110001d000b6044c1e1811239074107d045c44080d50003840d00c0106490f01c44185403034182c00e06c003100c98803514800556100ca01d2143e00000d00e801c00c0b8002c18291703c45065a0b18800790348400c0350204500020711106040650088112a03481c4400d5407502d480c00c2c1c2090103200e00c507080a68601c1d4041905251103010a412030700400281c2104c2d07401040601d440300008061101407281d260400d031412088460460001c00d060390802e01445450342d03a0402814201c019202e15003802d176180d81a05410182d42d0f0b601002802d83d8800d4a098107103c954890005440340101d200c1d8a070071141c0341000904503d0554010b540c400c0a04d13400b01581c0c1c03940303803106141080c40c0d0000209a4008010700152100c9000c203d8010941a0001d0034058000c0c0c2d103140d04502c0d100707800e0b414103071100002024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 774662787 1250 774661537 774661549
    0xc090b01052106120303060a031202120403050106030b0f04080d0504060b1e1207140603040201020f0f010b01170103050c0f0619020705043c0213230f031506 69
    0x40340c240300d0400d40b10a1801012400040e0180c511901c42da004403001c103400440402074a1086400414144140b80b850b103d403075002900ba4025411070041c00401020030000901410146008070700000340701e8114541400c400d100036000b40e403400d60740d070704000000d820750048501800d90b0102c080b0b41ea03101c2d03203040c0c005480c03041c18550744801d00040746800c7d6204c0c907c4a4038440c8084410903121181d62034955202c40c031038040d40880300900c2e1000500c0e402d01100454000388184102d50a1007410602c1900f03111014428031410b94442485407110760344802c0b0040100300701c0d00d038003282d5450340e5105030703031905082c030b8180c058150404030410550300c180655000d200394a20701e07041100400c1c1c000303494030264013507284610302d00000c0d12544036045844503400000c100c8203490908407040141203100b410720801d001142c0820141d8001300c40100620024284001c080d080382e01b1042d5901d40340f00d410081940a00d0080c0080301040c0d900050000a00070038101c000781c030340c4511000c101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 774664037 1250 774662787 774662797
    0x310020c0c130f050703020c2a0405090303070801060201020a05070201081e2d010509010315022206122c01111908010909050a1502090301110408011103040c090b0105 73
    0x42d2042c000140049110502d80200700700c00007280c410401a902c0810582c124091180030210b241c0c4500241a1524503980c039246103c03541000c0d0000c10303008000020300340d440440c6d1181d49604048280482c840d08a4950307405000d0340c2c0000d50901c19201c40080a6004000029040200b1280420b00d03c001516440d0112400710030081d80900c2d0103084884001d9880201e42568401e50000704805808080d0040c103942c4010010034540c1d103980c84200c1000c1d50341036000b840540c208283c001d040f05402c1048a40303000301040700c1c03490349480c20140207020003070301207030000f4101001c03100c40c8048000b00508200b11040900508240f00080e14010485841c6a8103409000035030803c5020310307458403141c54412070791b40a03120382e21804400103480249100500310380c0008031004c00603518040c40d5200d040130300702c010304000b44000081d0a4504401d0503120500c0000750a000000c03007800394451002402030800d19505080d52003214800c100e21070100060303500d0007072100320ba1060b01291 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 774665287 1250 774664037 774664039
    0x630020f07171c0e07061116060207140103021306050d0f0f02040f0f0807050904062c06070f0813020a030f03031a0103060303082406070327050310020c0c 68
    0x481d40b0301c18a400c0b00b19805822003004000020031881403408440c0145001d038649100a8900e5902d480019550000400d09145581c05898443da4548402d0f0000d200201144d500506155107003ca148280c2d50382c00c02e500e810940104485001c0c550b440100104858440c034101c4e03650f44a0f10f00a2009200d0000c4030703046182062141c0d2104800c82c2c0281058031068807a0850b101e55902d003034108020248146220342d0407100d020802d40c07620b540002d6000b4002d04011960000038000c4100010000310f5817410703000034112980d410300040028070f0340f007031031418004d500f20107010707001d04800b070001c001030703078854981450400b15100d03419103c00541d03009014090b1003030903290240c040c1c40702280b41e4a60400085840080b507209021348402c407501629045090346803120b4040c1c2455a89400884007804101c2035070041e220031000780f01440c041c0d5100000614140c44d10503d0300414030444024410070603051003142d6022842441d8411580030050351504404080b03401d01006c0c4101c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 774666537 1250 774665287 774665303
    0x90301060617090c0319080405090a09120f0c0803181906150e0a020333010e03010e061303111b030c010201140105060c0106030b0408040630020f07 65
    0xe02a401074502c030305014251081000c40d5941c0a0b59940e58a50700341c8081e03060b4000051041c003d0309050f01045940d00404003c0e140c2500d51012905500c01075811400311a135507000c4000380b08020380e4544801a840c90002d116100d58039008029840e03c0b44080d020401c00804522482158a0440b01008400c426103d5000da20091000703440c20010056481c07038100078111540e0944149040d003a01d510f00c40e001e5190b190380100c100250401480c20702c1d04113103c00c140205c1d40c10a64108210103044101c0d9a1a00100340014205001081c90034000c0e0705225410800510220741180d108091000e8440038951604046074144c0035880300703418078000c001c1640c407a0b0721201031146050005070700301c81002d50410012400c8500c0c10340300e805034582050051200d45040c1d002051105640b200203c0c02070f8585e10307200f040c0c003400c0d6022248044002000c10805400045040325002030100e44190380495a110080300f80b450300607040140c0d070020f80d41808190440580e00265044001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 774667787 1250 774666537 774666539
    0xa1d010e0d0f050408191a01080c1503010308030c0a02100e030d1a0d110103090206030a050105210307030e1804060e100c051b2b0e040b0d031409030106 67
    0x8180c6612481c282000012048212151001d0103002210200c80785180184103800002004000580c15540201c0e0154001ca4001215184110900c1c1c040c2c00d0860140c01a00b18040c10404840c00c0c03100c0f60400401c0c00d20040001c0b6180c0010760342c2c0042072a0a15503034010480e400ca003041c000080d40415280f81c000311041200c0004003a1040008a0400304200091100b44903c0340e0700080015521140c1d4140c14070004400c021071002206041c1004201d20f441d6500103540ca4004a03004042c8030340d1080100010b1030855103500c481c941d140b00c01e1002d103503090314840d201d21440d00050b040c440c3c00c3c0284120741e00c9035894030a414207910071185040c14a0301d01071014200c0f000c1c03d041a440340c0240c01c001000b80344101183c2c0700d01502c0d10342c03411414100d001c90228001014501d64001d41911452482c014040b80042c400011507510340d030b905004c0d01500780300d04175074078500a07490510400342c56120b00881801030f54042c1400143c010b140000034403e4494106d03a203030075509040c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 774669037 1250 774667787 774667811
    0x30a090c0f0e0601030b041803200d08060a120203070e1b04030510051602030d050a0e010e1c03090b130f150207050717060118091b1503050f0a1d01 65
    0x60380c003805099905209601d41b04080000703a955688607071b00801c8942800c4030002c0d008038924402c1c58260308550b855a400c0003540360130f00210702c1d0140003240800b8100110383c581000314001038612548942081c2c889a004a035039060180245035081c0e06a0021880c80b20581ca406403030081401d690a603a55100c1c82c24135246c030b002c9070720403800328105000f14034000e00c60200c110b414011741c0d0066080640582e90000034020142c44440c582d81e5030a401c80c3d910a0a0243c0c0a82031400f10062580018045061040c80b00c020b1807a410180b501050030300141d443d0940b160000414508880b5440c01400c4c5016803800700c100c0100099900c0042c9041c041c103d401900426004030140c901d0300380d076802580d043c200700000c03200e0706400060047c0031031132294445260400000c1c0c0f000407007603d5035807030103000900d0545500020706c07070400c204041000d40942d0356006c060343c078050000d8240700303203020200100501112a030a44850501c10310380c7d04c00405041d59408240240315007c8125 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 774670287 1250 774669037 774669059
    0xc120703020114011206141504090f050a0c1d010501020c01051c090309051e0d0b07021f02030f090a0f02040c050904060f170303190b0604050409060501050316030503030a090c0f 78
    0x1c1740c11a006810711800c1c20b40c4c40060b0041611a40c10355001d0104103040c40304001c0141000f8104075030121109000c84003080007002540003c611895241500605160605104002c00081d81055000040060042c1e990105071007075a10800c0c2421902e07171142d01d007030503c26208031268002c0d0528024410b014950f00401c1101228016142d40074032402c00400e280b0540c44801d48a0f0b00f260210700548006814500710b03a03030160b01481071f610395040c0b0a00740100e03000798105903840250003100303100741c1c0580428280e405c00c01d000010311006940da55040071b110100003020344510f41c1c030310740d090b00c103801102141e00000b002401007200a031285002d0b4a946140c0c05000c0d0f1207030300003142280078200002100e002d002c143c1580e029010b0070350b0406010b044030700c5540d50000da040c840003c0540721341c01003400c0795204007808107103903040005062070b008040304892160050032400700085680441265000394040002103035406040c2442440780100741d11514108403000000103802c2515 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 774671537 1250 774670287 774670319
    0x3100b03090c1306030507120c05090c1801030501120312060b0d060f090501060903140307120c1205040b040e0c09030f150703020711040f0e0715140c12070302011401 73
    0x483e03c80c070403240c00f044001c0441e043c5000090096203c00740500041c90807028030030324203108403000e6002d151a5004100b40314000d0b035003100c0080700800c0d10761048081203850401d074030082c602040b0350344c901803440210a640d15000f405200d2040c1c40284501d6007900403c01500807420196130b64456201030800030140c1d44170f00ca201501d07148010411400074010b00d41210043d07a2202e641d20700799161109a02c156800380c5032140b004000c003d0008110b0a00f502c3d803a045038030340c2d1100c07086a040010f200703e010346200341001010441480002e0310744040e00c050b21507142e88040665101c2062081500c02c059034140d0500c00e03201700b00c00022000540705038180b06044080c0305c50301d550009405a019905000381044028403c1800c58103003540f10066540000c5c00c0824a0070503603c00c14100281d5400460650280d9420b028890f500007410039012401c00d2a928035115101030841c3c0c4800f854002084002c01c005641800c0c1807007500b20f0f58501101c0309030303007046507580c070303c842600401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 774672787 1250 774671537 774671539
    0x70b0718050901180f02131a070b0c03090607111b0301201b070501120b0102030909040605010f1703030112021201110a1e0c0210121b0809030a09050603100b03090c 72
    0x2400203541e10445c1d94000e495503421403c610f035804030b04202000c00410000110020822814081003012410900790782c0c0c01001c90f030030300360f641e41000c0d28124207102004002e0020b03c12000c404032602040000c0c400040a20b140d142480da11000000038090444518044100d003449500d8106100c100d01c002c1182d0790030b468440c0380042d065400c0c151158810720500340414410300b94104c10901c1364112108003901481501c0ca000c20110024001140503a01514000c0d031300c00050000d040c40d130980302c014214001daa141208ac000d4040d035940c2c40140105c000016030b01c0c64031780464491074903061310405140300074002004181c407c2030964000a0303120000440325000c0030050004040b040c1018031103940d070545a1521a000e102c0c1d0072407000501c50070400350112400500026110300c0d1020088940740038141d22003400f000748443c034003805012141c0c104200101c02c40340c01c842c60404071001510b480f5265130300c0381060f96081456034012000041c00004201e01400b02107041a68480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 774674037 1250 774672787 774672791
    0x120f06010e0702071505040e1008010e150a18291302010f0f1809051509010f1401050f070303050717011a07050f010c0c060b06070b071805090118 64
    0xaa54000340440720029120480941c20440c001c1c86402c54800440c1d40f040e0480c2403051400d983c07517240712003207541210184039250002009204800c0300380141c409550585000381fa9841c55101e01c2110740c0c1018104130741080e5514031501d05911100c1c20241916004080d4400314050010036104070740146201002d400001d100181380d0703082c080050b100054040e9504d00054000d9070050700d404013003200107030034070801210b440c0042c0c0142d00240041d0001c0500030907a82054011010820204050184660011001405844148250724044035050070000010000c50001a64184039040410f009140006080b00a058043c5c000d9400b824155076201000b0f44001044030002c0c03800e014070303440c103529211000500d1040c4401b038030703105003d20250368904074620022400c469000da00e40c1c004c146481d203d1300500289100d010300154050300c3c450310b0b140f01d560300d00729140c50041028050002e0840056002d03041c9480c51030141201905c40c46155860340c0c11003400601d0581e00406040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 774675287 1250 774674037 774674039
    0xc2d161506180b150a0518030601060e0d030903020d08035103010203010e011a090603060d080c0d02060a151d04020303070b0c070606140306060103051302120f0601 72
    0x40c03a540305450485440519464103041c044000c20080d081c2c00c4251640b000b160f440c4030300d036101090010000401103880751030b45e03101010b0307444001c4030461107468881c0d00481d00402286400c03540b000847c103c202c0d11711030b00c05018a001c2c0c481d07a0780303508041d412899800c008410400380c00000c5000d148a080190103003010851a40c0401c01ca442d40c03000c01041641c001400c6120b40301182c00c0c04c840d0180c2680d0300703809600c04030b030890b0030980c05184450700900040000c0040c0981c840310120480841c07502e4940d1000120f102440058070305409031404100134424802c0c0700c4266000c06c203540f03003619540b850410001f9610031007a640c65030b6041c80c08a601c2451910202c040d4100c4480f4010002d14540c0e084242d006c510005005a0301800108502000207000b0841588520300e44600162200243c1c2400400c80d40d031500908813584400c40008000c0d60002081c681c0244240ba0103e195510548108001040700d00000c2d04042d6030f8009030111940400c4521034034800f14115185a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 774676537 1250 774675287 774675323
    0x150609280f06181e0c090e130b0601140703141902060411190512011407020d122c010b0303040e01090f05070c150b09090303070f080c2d16 61
    0x131000a0312603d45500b0740c82c00381d414040c4a400a8040d940903044c0b244206950f260088004082101d01401c1e540c0078884050401c0341c0c20700c4080d0004021700c1d061803032207481c0d5104442840741100190034003000c407000308544903030354003118040a005d030040844c00c442e003000607507a90000e80301119548540410f11030b10b81411620500c032060a44500f4414910b4034080c012217281c00203521505541b5520a6407181e00040001c2d402010300da4000c08100400c41c00041c18140076080010f10f02d424000284d01c98462080c00008400c80d41e524900c3c1101039140c11801400e80203c25500b500000c180000c11a4000c039409040f159801400d018084040c034068044a0045403d40301007400c02c402ca030701241f000c900f48408008840700000320004a0710026504030011202041a45c0c000410084800e42c89500341500c40c2650403c0d01203824441a030303c0c540c0c000c40c89046c0e202d0141d0a4020060202003244010a81070b0444859550340e401c00c44140301c0702070304015030307865003c40700189203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 774677787 1250 774676537 774676541
    0x70f0206090705091504020c071701020a0c110315070f2307030f053f01050109050f0a090e0d091202180a0209120c0102150609280f0618 60
    0xc2122000c02a2080c5410f110400c201c80c20301a0078a11809400605807286481d41c0c4000c0c2041d45800b002020170619004c601d00c0202c1c51505803a00c40d07401072002402458208040201e40f5a0041d00ca030701c5a503807000403e00d40000080141028030204d801e002e9010303007081680340179004654030412107162250500c851440b4203c0d0034800c410f000c1050b103010921520a038201040e10b850704901d89510811100060f21001035003a86116a01a400032103510031036200210366083d0141e10025071401001030001071261003404c0c0900d40c601c02c1e0510b144e666601803030260124181c10008002c40c1d00c80d00360303140d11641c10100450050600858101f0151071314480e0562700070605015182c0c070720400018a0350240c26660340303030380a01940c002691500741202103800200018408202e07484002450031000a801030000800b001c14407066443d030403881580525110098004110105c44104004095070b042401c0e192800030000404006604480219085c801e0301109a00c0c50b1800501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 774679037 1250 774677787 774677791
    0x512070f020f07030c140a0b0d05060a141f030b060313020f03060c041806030204140f0105181803070b042609012f0d030608060a05010b1c060b0c06070f0206 69
    0x40d40e105070410001c42d0f006c1400551903403030103021040e0340b5507540c06540b103039001103222001451b01c075402c00c074090a00c1b541980003001c810551001d011510720109032442246003503540108901007490365050b01035048800003400103060340303a483c541250b804110b0039040004a110348080c00c1e5604441c5070010385a4040c00282e1084c610345803a080c40c034030f0f80c0041071701d981c00e0a40e259907000001d030b500c3c0d20903c020b6030140c2118441c646082e0a1100c00503105030001c0b48100741c0360341e403010448920204154803d0440300601034a0b280b90540614500440384001d01d40003241e0108810840072000c8404810f0898690101140e00d092030030f0124011741900a00191203141c5009000c00c80b50310012000b007110610352a889440c4804d1303414040d216645201090722588c0c1001440c01c100f03c896488500c3c54020412941801c0d5542906d1140e860a911500706000b00300740640c52540c00b0741c004003070300241680d45003100e901d400d03210702007211b56501003030f1320102c10b254050000c43c0042c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 774680287 1250 774679037 774679043
    0x30f0f0c0d09030e100e030715090504150f03080a021005010608060d1b230d03020a140f0303010e0610020f030f07060b0424120305030402060a0512070f020f0703 71
    0x5050044160100000384000c030400e404104945000550710f03207409070102c01d6856030350340b06e4514521400c1894684185684000e5403041c1000109210701e03884100c840036110308a40215070310328800e40d4034240204640084030004001c800000c100007441c0014484512150203440d21108811141c5045039024441c00b40402c1c0d101c0005945803a10083c0c41c085184212145029a42c1c000215451040d0b941c0001008501d0004102020300098040e403045400c11203034510309506541e070094440b9070314003006024089450312040d07070810034801c41e040c00a01104036500c030341e507070010400840401d03901c080c0540d6015a13121700051020a40381014803c08000314a0700158444081d4564440b4905407882a500da1113102c0586d518040c0341c0d4a2503034003c805906680c0b03100002a00d02d00340d403113426042010b20074440007075006000d4907030107601220041d0b16580d8440042d50345110b081d014012022084042007c5241c00c02e8100031000c0482d400c8898052004840d540c0e0340031540006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 774681537 1250 774680287 774680311
    0x301030c061103070b1f121a180f030405010806060c061b0405190503010501062c0d0807060f060605070201170601090b0d020c0d09150e0420030f0f 65
    0x900c0440c0c0034003646007406510708101d81c600b002d1611841c94040c02510840c0710018030028101203451440115006012003201a100e80c11f0309a40b2a0000c04801c1d51040c05800c68200003245081e060708812242c808a5080c0c071b9441c020031340c03516204e502c03d0103014049103208010403814200035095a581e201104000e00854a4944540210342c19580e000199a00c00700408102e644030003401c41308018550079419401402d1004160079a030341600a00c04104203620120f404400950701f94a4203d161038480e4004c40c00c980c041100d0100220015085440c00a0060200465a480f820b02020314210420807141c66400071a103d11811030080d0000d46860003038900c5100b03003e4195006a4141085240700395102456919604a4481000d103158041451101060244014018440ea03454580c201340c0c180715086142e80c2011500100b0801081c0890700d003034990398410211104103521030b100300c2203110960f0301da5a00803580f01044040c1403010880c18076070011151700804c030b04622 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 774682787 1250 774681537 774681539
    0xc0e0d060b130e0715030504030903151401060507060b0f0f0f0a030203010606050d06090b0105030c1c1b120204030f02102a020f0109030221070b0409140c0301030c 72
    0x6840080c024001c1c406901c0038210720a000c10000070f02c201103801c250038000c0c050052030103602c00321014040b100e110a05050104000000b980400e103001500d502410b12000707600d034005103030018410088240c80031070130000041041a00000a040c1c141c2c8035140030f21540304900c2c14003005007918054280c001c0c142c441c000f544e80c50240e0b05038041d400040c05180034981e482c0c0000b0b0035a10503501840100e540040c2120481c841c9004d01c0000d081c08480074860b5800c508002002484000d014400444012402d01c04078092051010b189035616007045c031404c1004e8130340d061034241745040f1001048643c103510081c09018001d4a04036500000b284540e10f40580031311124400e945854020003100d543c1d040c0300c41140c04072152117820701800c40c03002e410f07013441480030184451144506002c030b90b981c1080142c0d40d0030000e881c91a66064407513102c0c100b01c401a0f01c0e01c103440e0001c18400030f001c900464840c0c03865100600700a5a10703000010f80c0c5452102100c00d1000b808050030500315080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 774684037 1250 774682787 774682793
    0x5012c1302040906020706021c06050d020906030c0d111212161a01030305071401050f0411041e1a011b0308060604171c140412110a080f010c0e0d 64
    0x102940c0c900103480882e9042c0b0f00d507540403c0364481d40003281c01d141e011a850410306054101000c0c3c0010303400040203024146000541c03065040003000b8841c6d04607100140c07690311305000c0c030490fa01c0b028110320007006031441d04400041c0c880c0b085c0c50003444190b1540750030b00000075415800b89044d400e0546000c0440d5455117112041c03140503540342005004800c1082d5010600034001c40c042d03640c0d944c80310301e03620701466400d02c840c00d1b01d0b8945e8107020510407060360509006030030a0348018541c9035103080e0000b2074080c0400040d0100c00041c0728082c5a800b290743d400c0380300504e4060400400e508101e01c0159440d505540c0ca0300001070f2485015000079003d004202d0300020000c03c02801c041e658503c0303410303200046001d0f4007035400c40d001c5e13519811034240072002480503505000c42546030165550185000350301c0b031880000c1c28403050005000e40c0000300c2c068000081d0100040589480c1d04c20740e181e0a0340d00c8001690319028440a80c1c9104074059901e070344004002110520f07032030b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 774685287 1250 774684037 774684061
    0x702010804120216080d030b060f2b02070b041109040503030406020304060f0216020907090b070609021c0b040c05030c0105030a1d0d0f02010f0203132306070305012c 73
    0xb2000541c8a485084040340e4011180303440240300503801800c542866900090940300e010401a002d45400e1080328111040301e400e841d0080074509450030445030795144004452042d9a07029070003480042c4880038090941c40e900d11031400381511444c0404010140030000f2411500030305290020f101003070005805400854105008070030100e400340082c00329100320b901c03941d0f429000d0030310243c2003811030800752456580301b038050510121a52420403142c000e88a030610040c48030f50781d5210070045542d900e1810035001c2111044100141c107610301100c83e03280c10794058803402200c20001a282c80c0000d161800000c0c103a45460841e1280000280034003800740740c21210b9618002030100d125401c01c08040204541e0b55040e0480c015001d000e0b084801c1046804101c500402c10855554505000b560341340350300400400c00304d55010f000703a02d550386030f401030043c84c05840280b040032a419000f1606840200101c5000d0070000c01445079688400c104400700b1528100000310003007406 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 774686537 1250 774685287 774685313
    0x302120f1c021612061406060405010f03020f0724020408120703200d120e0a080a18120c140a150e060c060702010e070608060603060612040b0115050702010804 70
    0xc1c0122902d080c3c42000505081100f0340064000341e140c000458140203d90240b0680782043c12078004003402c0640201d0603920a034003c45c2e0601555a50117903030740340700c0d504884500c40180382240e01c8548a280c862240c082240000d0300f41c001c12841024400c0861080728101c466800041c850044040c0ca141403e41080700c064042c40081c08244000c2e40d00b0148a450a104020142000f40007040026110f04c00b508400c10000b8500b440c00e02d900c240004445014503080300e002c50f2501245441101c10ba804000c002c0714012203140e00040759450624448200d620411085401a0315078a0360a21217150002d51076210380c10100070000404009540c42c0001301d28a0149850380118001c1030460344102d0f10a100d135400301040001444c0d0a2180030b00451502d000b80907914605003000740709441c080d000d948641000008a401d0b40e58881c05c40d0f0b030306140003100340c03441e240504086e43e10540920991304191400c0c0310182d00b00d4800c208840019034143c465505540b910f4683c00e48107082 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 774687787 1250 774686537 774686593
    0xc0a06020c013902011b03080402120102090d060902151615060504021206040c2609030d0e010b031e12070203101401032a050402130b03100302120f 65
    0x41016100f0091041040c10540011404900c40000206100040000d103080d12204480b42c869800700000a5210382481d8000e034040702e5511038019440401402840f541e1640d40e030001c0342050810401c45160404d0700030500843c1ca002c1c82c141c01040c041020b100d0030710b5404085441c0007084d030005010140402040b690b903400090542e0700c0740d01150407030744002d1801d651b04c0c602d581003101515141c041e0300c9812000c0d1a00c091801e07181c02e0140111203005c00529041380d0410005113403504104140c2d160408201814022914110b80c2c103030080010002d05402030140c000c600040c000300224001c540140c000c0280540d0310040c3d104a00380c0c000000882c1d16000314003400020b182c840c021009042604801c03034015525503e0044160303d0f0302c0702000e048200100088000300e031041c20540840f10140e0b80580d0b92807020844100040e1070b500082d890304808001c1c448106a40d11400058901c02e580d01c0d10002c240c0f8003081d50305c030f6412804482c83d0388200061420b40c0140f412040059030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 774689037 1250 774687787 774687827
    0x8010303110601152709150b071101050a1701090509011a0307090f0209090c0a0815061605031207030f061a0403030f09080327040504020f01051b100605030c0a06020c01 74
    0x1005940103160540980c1c8076a19407519080c4240c038451f01810400c0090070340450552802020340d0714203641c1c5401c64080c9043c8200445c1d009083c0e0b0182d04450003d0b0403d28500000d0b42e15140c400340203000507241280790f50300c1c1c0740000083c0180d1100c2c1c080ca0100c01401880801e25044040015040746045600d40079000d01001c010707902c850b1b440d01c2c06500c50000c42d9440701d142d103c0c020505800206440342c0640c2903018000141ca0b042c5c2101d80b0b4101d5580e44a01884d61401d020b440d522448486021007000442004000c5070b140d849030b200511140418080c06a0b18100c07540d003400c02048850440c03500b04030410000e0b002d80403940352920b6905051f1405507841502d2070550700a0160081700d4a00b0341040049540d400e00c2c0300c0d0034008101c0301000305080ca80c000c5011000c0580c9403070706002002503001040b04808603c03852240310343c4129006035160312212406850701e0300c15107000740701e80d4182d8041480c0c20300141d003c1c1d0b40b00e40c1c011700318202000011560301c2c1e44079000c988500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 774690287 1250 774689037 774689087
    0xd050117061f0b03010906080d0f0e0f04110a0e03010c0509180604090807081207080114131d010b100f021b0117010b090a0e360d0801030311060115 65
    0x884540558001d00d0006800500c2c9823505501901b40040d100580d410000c11459024586401048815400340e01b0b5514801c56046140410014121081d04810000003c203101d004640c0c020b00707550f20908194001d01682c001a00295103a010b0b4000c4542c0c4000c00040c520105100d05895541c89000200003040c807000c0c50302c0b4186580c1c4406010b8980010016041a249449511058201c00a07180807035080d850020905000c14100907418400d0304000e40c44071047e21550051203411040708404051440c509031300350f00a1030280f03401e5000d01816510703022080e004511001c2e0f072480b190040c2181c605144024a40d400441c080c0c541803120f440e000384401c603041e0982c40d01a013079080406991702141410083c0c01001648501c911501c10410840c0c1c007030130300390440114880e0494440790740490080d24900d414880e0445176091081c208200e010355032101003e8100c0e4001d8907090390700316002544640300d000034064180c1d11401da5905110040c811318980720303441d041601c503400e08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 774691537 1250 774690287 774690299
    0x1a010c022b03052119020c01060b0310030b0105030f0a0209130f030302090f151e040510022103010614090315191508150c0f0307050d050117061f 64
    0x2001d50702806400051001c0b40b481e402c151003120010b81d800c00104030060780c3c036043c00041e0000c083ea60280c42c0c1c80d50003041c2d07a00d0070402500002c01400074500c00719201d2501d03403030710140040e0501c0141c030b044141e200000358a007000301d0754050a51140020307100040054003031111102015151502640503200840b000c908003a0083c226240309640c0075a4803804402008500324071030248070301c1903a0088511025071392036800c507000d02c4880b0742201c81c02110440c0d42240c6000e142d1001d0b400c11000265035020a82c0400c80d0304408200c4018450084a445090301140c0000d01582f408282c02903044044500d450000e4441d2031801400c4034046840703058202080e10381a101010126540d4081036140b8103503000e140003a050803c203001c10140380000700c40e91041c400390300034840505080070034103030f10118040b248000941810150340382810b032002022607000c0480c3c5046d851504001040c5040c0e8403c0001264200100510403a00e9441c908500180034900d6000c4d11070084800140e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 774692787 1250 774691537 774691609
    0x9030908010207030e12150a0507030b120601210b0703091103010e010c0206010504140a05041a0c041d160315081f0e120a2714041a010c02 61
    0x40e95100e81c1c0d6080d05d50b072070f000078407031030589043c0c0c0900c40c2c3e000201c0641100c5074003014a640b10321240c5002c6070546904005a0082100d09176050304000c0d080c000300416480094428121202000b00c544100e030a00941c2e00d0100f403425005101100781c001080140348a500030840c5503010b4032544c0303100450b5a0000e8211003051795018101d075115503104a143c2d4041c41001d0060009a60500100c00c2c1500d1a5001d43d9004140010f845e42e140041400c0c0440325500030344030b2401403517402d044d0900751101c031000d03005440344152100c60585212000b5428816607070081816101e4224034141d520341c01d80c040c0280a5840c01040d4100b1400507060f1820041e00700c80e4110b88007a942c02c07001081a110948144c1c11060b4919408100038290309204041180d81c03020307503845c041b5441040c51200110b41640710307a616a4a5140c84408210503a03180100500031030112001c00107038041001c500803801030900d106010420804110300941480da13800407120440e061551480785000c1c2c02106 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 774694037 1250 774692787 774692797
    0x10181205060f0606130306230c13050d0305072004020f0d0f1401060528050d18080f0715020d050612060606040909110405040302030901021504080d090309080102 71
    0x100c0394025400d1201c0307150004036690b044102540c8440c5400084032145007480ba2500c4010b00c0c00390340e042001c90100341c1420f40030303404180381450420360428541c1055039804c04403000495801502c400204c81c54888075071403000e5450b89400d82003100a41340c0001804400b0345e001183c140524a02c4125900e0748028001094940900350719a02201c5540d400c54905480700781d0307000e20340202c3c001c90724041c2581d00d046070414035101c0d6407140c0e004c01c0c561180c518480a03412241e02889900b00b1150050f02905020f01018020003414524010399114103185020103401c034203007008042c44005241008020260281081030380000354002003100300c1c2d00000c5619165940e8106201e4245031817035801a003007901c0d20042240d81030040c0018114440c40c82140050f640d194200760801480c25440c01141000910800c69850523003400b030b441c0c0d406880294018014109640704421020340303c02e008540090b14103082c007010020f110000c154840007039041c04440b19000403c06401d000070302d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774695287 1250 774694037 774694043
    0x51b070603050a1d0c090702030f03010f0614130611030c03070609020a080313060f12090b0103020310151a040513140705031306151a0403120e101812 66
    0x50314540f41590f00100d41440c8441c54000032200c21440b6074803400902c60034210000c45240c070341516181c9090f440c61003561120001d81e0408030000a1040c01c3c1c02c4070800300e5034203460b1a0201d6a103c00442d0082c418010300e0496510100400d010302c0e4410a019441020600d0899190030f054540c13903447c1d600300b0002210143d88862500b02103051020001005000354001107081c214403200094101d0014050b10b0100105c1d175030314080c002c0c410700140d06400c8051400700a541100d041900480d5804d0005900030310610302d00040703010807841001001c0741c1911005030300398100301070704071680c440700c0040115000c24803001c112640d0381c449134003281c20414000683c041068003030040052006000105200c400c0c020040340c088144d0464000e168000741c00941ca404008241075003100541100c915005842d1200003004541c1c5c0052081c4d80c000d0f4a00c00807143d104504984480c9144061340c1c10005891204000340d008403250032900c050940c81d0100c6c00c1e201d88031003956114000c1e060b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 774696537 1250 774695287 774695291
    0x8010209040b0f1c0f0215030402030615150304050a1b030c0501080609040602090a03080406111509030415030b0312041e0311060d0b060c030a090b120106051b070603 73
    0x8006900d0039100e1010604400d42c0d8002a00c80100d0004240110b02c1d06480d0414078240713030300c0041288651000c0c125682c000c0080303d0404e8540b404036180d03042114100d00078070980010401c0c003e45000c1480c80c43c1d40040681d032206000100356011a000540100c07098411070001c58000380ca05114580100d00410f0149039881c61410846004840707984010305000711507050001503225130f01d5040c1d10a42040740503903141282408161076581e6503201030154140440d010820300d40c40f00e00e1320100c043c003100b140c01c04031500640c3c0080c0c1c4416180400d5540c402c00003044541a81c0c0e04102802c0c660b406e0020f002111803020a0900ca41d425500000480014050001121801c41c01104a8003030000704459070440d51181034030758150602600c074160206445c80030351019001410226805086280c8400039102c1c15942d0b03030071950b04900032039405640810b881c1203090a032401600c080d0341825035031746450313800d0b0350942c030850702c107901070840804068006800304611b1004040607580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 774697787 1250 774696537 774696547
    0x70b0906071b0507140d020409030f12020405101404080d0c020117060a060518151305150906070c1d09060714040302091f03060e0709020a080406051f080102 69
    0x40244905014501c880c035240305510b030180807031000101c0700f00b036444d01000b0000803551031002030700786e0b844400e009501c41c2c10039500000b0942d00010640e484c0b6644d4407224020b44071904108227a0256004150700b00041c04801102148254814444424448540c0e0715103601c680100b803c001d05a801c60001c00c00c14a0030004650f44100c19008070f4010a500240d1400c0040000300e64020a07c544010451301180308850210329035001e65441ea4005c5c4050361800c0d02003450f1025070000f2000e052509000c0344006840d0800c0d0059100607000588000d103000f452804216483e001b9000c150b4800c041c0c190041044170a0078506d0745031307010100303640403d403402d034074002e18111004002c2010030890060328080c5010920540381036171350440305400d1603581e0500f5480080c446c8d45128001108000000051002d903500c070030230f510b200d40251111740703880301074201c180d10480895a000800300c000290105480d603100c203401035103140381051800008a000e184000311600b00c80466503001070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 774699037 1250 774697787 774697801
    0xd1b0f08060a2303070b0c100c03020a0c140a0c06030b030f19020d060e030301060c030906051e09030a022116050a061d04020a050a03050a11030a09020105070b0906 72
    0x21580d10407011900c4907041c9041194102c0031011030100020700c0c4128a0340c00e10729507401d2012401410064030301d40e403241d10040126039581c5003001002906850081c0d10f4010301d03c04d008031441c2c072401d511800e5030710207290303500c2044001e01c4541c10304601500c418030340007411210101000b014a40e50100d40c0c2c03400b0008044c01c1501071807030245d00da440b400701c5076004004108103c0c1d40c6034045840b03a0b41c10441f800c3c41d4000c6e001d1b0070109841800300200101b5500d400214055055000b5a22514041d071070348420341e1141300740c010101011107000115207402d040c0350300400310280080c050703403010140341d80421981018103d951425041c81540c0ea0094001017100c2c1c41d082400e894204030091030000811200c01307043c0036910402400210880f110342040d00d034000c42c14406001195101d11494004205800c01c101030800203040c1804603020940d180140c1290071550040e0b540341d5141d503d05400203000c1d941c000ca040c41814060800415049000d0510801d24000507040c9880c0400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 774700287 1250 774699037 774699047
    0x6060b07060b04062103030209030114091204060927060303111014060d03020a0b0c070c15020c01110c0a150e010c1e11120c13090b0a020d1b0f 63
    0xc0d0034580528a0001e040201c50b101000c011910391704010091900c89080c1400c0300a4402c00c1e50383d507090360a0101c00c1c40400d5a203070080d071181140c4010340e4081101400484543c0c410380c41944000340705540284a60040c02003010a030b175010baa1049810705001c2d4074002501c1e0144e10a4021540c1d002d0030010504091211144010840208100001d03045802c94100000903100c580a040404a410101402008424822900506250958904404d0a4036142c0c41000200c0c5c6203036508000042c180c4101450300700f007040c2030b0040c00601c101807004451a24010400c0c0510388204090f800c0385445d8015074502400d41000945006004c01d1405021850817040305410080e005105001051070b4a00b00d6072501c081c2400709107031551301e08003d10050b08900c00c00d54055a2844032821030038000414500d800342c151641c5140c0d000310307180002180c0c10f40030007404c0c00c1c0340503000501c2c0c843d03107900801e160150182c002403c411a21036a045965441e480840498902103555043d0b5400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 774701537 1250 774700287 774700301
    0x90610211b06110a1e0c24030c09031e051e0c091f091104090e0d080601110d050f160b19020f0d02090d0206130f0906030308190906060b0706 62
    0x42c4000d20313100000d40d8489083c00d030b5407440103101d4175003d141242044405a0418000c1c0211165008045184142c0d0650401c103200d031000400e15150458003103501451400040380e401c000c4015060300100c902070540300f44444112140c0c041c001c2d0b2610001c80c124408040006040c00824138864080240906904054100b108903005c801094a40c240601080802d481c4012808180d4016010702c0d04903500854004500c0756041810020f1803d0000414401400065441244948950005643e4030002c4c1d1050309071a0003084500d500140104000d003c00301803a12014580ac950650040703645ca01070300121030203007000080c0000c0c5000c1c080b0001505200f00c900314900311100300c12090318441c600c840070300a6001320781c0c03082c203689203500560110b03009808956101880c0c3c0041d1141e01c510b0049801c0350600c1007001c2070607209849040162071345510741030040d448140c0112105140f42c0404041c80c1d4031100c04d000010020302a10004040da0850300e500d40800d86480410b5801c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 774702787 1250 774701537 774701567
    0xe03090a080c030307150603060c0e0f120624030604030f0906020d0c1103010f050109050601140f04050405042916050a021c03020f030f01030506090610211b06 70
    0xb00c0c00482040c0d81e808000c4a0000d03a1246d4034400074040c40c81c070000981079540c40a4040b51910208080c0c00c0c1d0440c80100290800302d5100e040c0400c464100040350000c2c940c3c904c01580404001900152001c0c004400700300c1014642e580301c240c10000a103051000c85089001a80c1072074105c68540d00b0808038405441a40050080703070000b58401004583c0464002c1c00d0507071200c0401480352820341c0000499910420240300c0c0d9a102d109440181038140c0342180003c54180c2d942c0c49140b00341e002c1e44d08240c2c80c10f8029242902d8581000050312001d44203aa0802c0512004102904810702d041c0c2015144120510380b4070b0040d8881003003900b040152403d1180c03c100c5031074250b07804900c1c0c4a454032403c14180221480034001c070024028902c1c03200d2001d800006000500401444d594100e034815811140300d036030f40311240e90b114107040d0b03658141014180f0087c0092007540300100000d04075004907c4481c140c54564010a002c21400d240c1c060359490780070701c48164440014660b0080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 774704037 1250 774702787 774702793
    0x18070e070f0c110d031e09051e060f0a021b010c030f12150e0406150503031602010c06020327010615110106170721080405010c03090503010e03090a08 66
    0x24103064050480801070745400c04001c4492901820084210740c00020180090702141515034645005024910390342d82c00355003c0c11035002102c1c0d06c1d10603a0040144c4202801c00b50034021513074a02104201328010030395012805018030403004141d10040c12054100d40d001f4a100c1c026898460301b50209600b925041122204405009c00d42220030280003071030703c0c40c06444140060f83d507140185a1001c10700d0342226001000120101a0542c0b2401140202406c01011080e1a002000c040f4140306990301600b0901c003210894000c0c65201e18094018102009030510a50302d440882c0c2c002c55a0311011180c0f80f00400002119540e00f4003d180d110008000785401c02c00740c9401c5240300700407501004100800c0408141082d001140204120003034440540d01c20300340d140d12000700d400b40b058a010800040c03804402d40660311001280c0080d50366241500780001100c0d40f0207107140030b5060221340c180001b40303910b0903c14208850700e00b2001d0343c0c460102c0810885000d230f095112407042e034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 774705287 1250 774704037 774704041
    0x303090d23190807021906020a03030608060405070b0703090e0a02190f0806040b0d06051e0c09060406031d0709023708070c201f1d04110318070e 64
    0xc01c00c603090807460303400600207a1a85002d100041e4010380e02c01b40042c012201520010720540c00041702d0320400d00c41c4c0c0f428070800d610f0302c441d15aa0f01088a016101d41c1c09038108101c0e0202020041940700d01078a800355140d40c540209049841056401c1c0c98201d41c0054a6580002c00c0194400717401100d1410b5080d52a03442002041c00704050030a40c4500e0b55801c0c20003403551204600d6003095402001403006150401003010140750007c22000d40042c80000101c244803480c08036085500010305807828203007480750440081c100b0603001c40c5054031034010505596000c01403d80148003040000d60382e40c02c3e1044141d0103460255056000400710070b034061030350324080244540180c1c02c0ca40014242c1d02d68004681090540c0030242203071400310700012f0741c044407000360611002d003a6a0861b4000108081c103030024001c1030640c0020340e10175000041111040070f8030043e440010004544000074035100082c603402a1200309041e60300c21901034256a051003444014204002d0284080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 774706537 1250 774705287 774705313
    0x270f020901080a050919050f010501050d12080703020702190618050a0909020117070e090615031504150e040204060905190c02070f080607080c04080d0c020303090d23 73
    0x1994025019545a44d120780c001001c03842c0c104900c10303070b51a8001c0d44a0042d6058281184c0f03d1b400701600c0c080c503500700000802c05042c1a0002940141c3c094440b100304903081d2402c0b190301c000540040100758080010101580e20803d10094802c41c1c0448060010328002016150180c0310b20015441490300300c00304500d9a0724160b00d07044406122010409825070b2004989004586c00e030003005160b210284412980c0c0490b6003144c0b000f0549842c0b074280c840404005024a60460b1100156010000180c1031401c1d0030048800c0c1501a02c04640207000c0e411035585480c698100c0c2d101c40e94118100401d515050107440000c15107d007081049040145c1c0420540c00c0000943c8101500c80c805000c1245c400c0044000424010340c03038105090700c1d48151034a0311021b41d01c000005d601100400e54405901040310b04844080004244441c016142038510309503101c000c0e40e060005101d01c404984400144181c50303841242400c882e940c2007880204c0010300d41d1006500c0b54403140e030b172140c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 774707787 1250 774706537 774706547
    0x506030d0c02150c030a110a0f0227070203090103050a1406100c0602040b071109390c07030c0f030b070804140a2111030a050a09270f020901 62
    0x2850030300e868660021100782c004035000e601c0724601061a81000200d0541e619408005400b501120b5602d01da40ca0207070b264625590515100c000c0c24840c5c140c110b88006281c8001c1d162140303224440754104001c40c095800c0c40c41c000440761600980c00000780700c00503681c140f184980c05038101004000105200100c01d111000007403240f4081c0c0c400e8214442d140e80244c80ea4990150b0048082d5a901c2d10b440000c175250b049150110b0301c0105d0100850b15903c0c0400140d4841c80400f440c0d9014a0304a400c1c0024484401e44032907480d03520050b040b403e04410b48014010260003030001d01c40c00c0c1c035510b000c210340c00c444e50111282200060051002400301c00c03d0641058003031070b184c4101c1c0c4a5091014800c410111441c0c05441007503100401c1088154603034220103010b440c1c108441c000c2c0c20703080c1d40d45072525000c903120b900304101038403949003d6400b42032094454606449516180c0d11121002c8104960b02503010800074401211050f5034000d90f507a6403c3c01c1700c02c1d810310600030000f0302 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 774709037 1250 774707787 774707803
    0x191e032310032a0326340c08060402031615030c1713030e0a0308040b030a1805030304050138030f07060801030b09010506100302090f060715060504050603 68
    0x40c0c1c114802c2c1c0350f040781c0f4070003031529488240101c0210b5182d8910f0300c010000c8091128028000c100303100da024000f03641050781d0070302c808070000c2400000d41a800302044034075208800466541c030000b440c08142085410805041c0d803d00030002400c050040500d4240e1050724049400c0c0c1c1c4c14014848a00c0d1008210241c3d0110305020440c00700302003040d00d0030a550060740f800310008904015100350350b0010003200034020788425900c4807400c0203001d014882800041c1c00b4100c01c000411048194070000c60344080c2e200303000681c02e20801007000e00240001d405542076440482888188079080c1b040c01c0880c28800d01c0e88224840514481d000010901400b042010f03095010b40314a40b42404140c4030a0802410b4401e0036031510005044010203000035110b5011000c0000c000408c14031601e030003408000c1420408921641c0d0480c0a0340c0460441a0001c0591540100c6034880a0251003803510503c02102d446162407a1102202c1155101a11030b50910061004e56200420502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 774710287 1250 774709037 774709043
    0x906050103110d150c05040510180801021603120b04020f0316030b09010b03060a1a04060905030102040e010e18100b04050702010c090b07050c15090123191e03231003 73
    0x410307005c06a00081c0c916004d96030105401041001301210b800c2d5000d100300c0d103c0004800c000e2074294a43c01780c50b00300e010382c2c4000003810300d5180010002c24007803058800050603003080450074502001c0414140d800c128411003102c40c1c00300900404034104c205880085081c1c2c80c0070000c1510304000aa000035042c4904190800c00201090003030302c641000c48050041062007111600e02d01e44000c10ba544588a070400107140c04001080d1440c06008940132602c0305001c0f9071481e402c114159030b031201c020700304c40b02940d40d1014200102c00705100459005011104c002507050f00350b0140820f5900041c084011641340200400a00f50441544000e5030580010561201d125140c02c518050590800c0b580c00700c4604040c0316020a10001040c00c41c5080c4d80b400c1801c0c8000e001069051003100b0781201c180414454039448039400034081400480d1840c00655010134400c99421030016840d5400002e0788811014450035020040684a14440c00d00d43c6000d1602c6103802080b40c020740802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 774711537 1250 774710287 774710291
    0x1060906052b02090705070203070f080c06070506072132071706180103080919060c0f03090306020a09050f0a0803090915030f150a09121101020d0906050103110d15 72
    0x1040c003040c859007d031001c0990290850b0380251300d03107504214101040c441c4221600c1010702017180342c1440c0342510516540940100210703128801c1c1a074448521411480041d0024202c8501e91151401045a00450461a005c6404183c8071200000c14141100010000d02209202c4581c7d4042900d042c0d809109210181a880e003c0015005c104060b080860030b6000c1e0300013000f0b10280381c4c024100c440c821030f030500e603a161120039020b0904051080c0c82c0403403041110000881c1034040040f490038800c0c074107442c50710b440c1d0391a04201d80100d9607240000700010024402800c01d281d420000c10801c0703510801c1c40e0700d000c0e14507980b4450049114041c4440c0b001049480100b4503a41907100da00800b56000c18450300901540c4038650040c10305000440320100311042814421418865002484206041103000040d00c035124a00340b900c1c110341d402c01110104031058404d820030584152070102d503552440c1000302002c581d010000d840307011200000000101c8010f0f600b14040140741d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 774712787 1250 774711537 774711541
    0x80703080406020d060303030203011e0f1a1201120203210f0903010608120c0c0916030504110901090e060609010617040c03060908040302120c0105030a0b03030c01060906052b0209 79
    0x102c00080d0044644a0708010304250340401050b415402460584000c09011341d840c4100d030011314035000d9135104810842504600500494070300917031030b03000c5130b030145406403810b0984058244051400d078026040640700c0d080c03c100714502844005c2c8100c501440b851030012136501d95402c0e5104514110222400c00981c510894400f90401790003405440251095090400c01c001815071000e2954007150041a00440d0700e0b18243c4032680c003910b100c1002d50b01c02403c070071081d8000c11003c3d00c16a03540c00394030f00400003552003000a90281196400200d900003004000c02c1c03074500c02428641c81091030100500c2038950084d4200039040140c43c0301041078480b418100e41e040034582001c0e00350b50030580b2017010311000c1030080048902c20f032202601d1203650103074503840d4426008014000b03241003003c203100c8540c0d9000000308401c0201600c3c40c2c80901b294240c01c40311203601821242e40c4440d001c100c180752502c03801100084481c2d103c2ca0040c141d0007000d0115044610081c0300d40700c8600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 774714037 1250 774712787 774712793
    0xe1e1002010906050c03271e162403020405060d0b0a08030f031005060c1b04060b0409090c330905280b0c071a0c030a0809190807030804 60
    0x220b10380c1140c00c60000c1000c0d00b06510b058810750700864240c0501300d0080080141031660354040410252a01c0103080304d04c0e20040d02c0c000c0c131245090800ba252250070304c448524900304441c2d6004000d02040c5115143d60511080051038020006000345031040c48200901d4450303400701c0c1c3c1c1c40b00d42c044000584011a500007021280140c00240e0f40344808542d42d85800700540083d4040d10f860010650403070f0b900d2040150a100c1ca1036501000d4010403610741c0000744d100300c200c0d03031b1a0b00184046200368a5201540c0d40360040c0d80b149051a464458490501031000c1d204000380c410f04075954400640070302c9008031344036031400403500070030740905091940c0e229404900142c10700400d08001c0c0c0d601c0c94848201042d030341c801620120300040001401082413003c40f8100700c040c001a085492404048180000b50340303024413a1040100682d42d01e0704c100740f005181802d13898a03545080e04000b40a0351400c0108000c1014040c901c0380d81002251411054420040e8035107070601e000d55540c0b03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 774715287 1250 774714037 774714041
    0x20907051207020304031e11010c05011e02180111030403120201020d0606030209030d091d090f01020319180215160c06020a030e150906070302030c0a0f030e1e100201 73
    0x15603400700445440c0280115140d000c4010403c80707004025420095903004c0d0084c104001c3e01d1b60003050b50b60940c00307075542c0d5400ac80012003240d000c0c0d000000d4480034829040c844101c50030a03500b01940c00124914800c101c0022030241c00000c1c0b81c4040400d0521400503624852070101500380e0720314440042e0618400d40494400e445516424044aaa1480068041d400040c00d440c4280510f11403140001e10410a6000302c8070190b1086404000c24140c1c040c110320090140e14240c0580c0d8481d8842d000240019402940d010108000c2400c110310b0710011222880445454070010300899801740c0d446032803075001105903400060343c44800b0303049031800e9101217000401c1d1082c050340009040b600892022522402a00d491030403480f403004001d141316119400c030310b0100c4240f10744902400c282d0090164988640100d034603207035003000d110f854107000b000103e03080d19507460303034104240c4c0c8203103074920790303502956480c0000800e1400d841c00b0000b0411a28007030100e81c401035290710720075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 774716537 1250 774715287 774715297
    0x8041b03020315010302030d0e0105160303020909040327030f060203070c020a1512111605030d110702010e03010207050607030c021608062a1c02040e0f0f060a05090402090705 77
    0x2400c0f200c6401445060041d9010f0901c0280c0c801d004050281146501841440500c1603050b5911403600e10381c03010262440d110aa02581055030a00101900b510f418185034003480c00382d2038582c54145283c2c0032401d080c1960030b04489a0000040820004d014401040340590b800b031000f40e12a510709804640c038001c51040658001148400002d00c0c2180c2e405004202500b07603250391040540110ba00d0940302c450b9805444030200300019803281518040811115101d5400c2e6450701d600031910308152681c06840181e002c0c400142d070000c560b00040c1111031620250300a5040400c0c64903400e0b10b85100030200f49c103040d2259035054002c0d20a2190140c1204a240c0304204d0b15164a0056510441280c46541d00300c4070606040455641d1514160b034090102d05103850710340d40c0500008201300c403080c094891a000d01020401c1c0c1440308070140b1540c1000c1550090b41f4109074030b021851000740c4003030b01901007604d042c811600c0c0c0142e1160311603010385400c0e074143c443d039504860741e02c54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 774717787 1250 774716537 774716539
    0x110607140c011d0705030c0609040c051308070905150f0409060b13090b0601050c0703060b0307051e091b04090915021605070602060f0a05070e09010f061b0308041b0302 74
    0x103003d0b41c0c14081140d040841c09024a000c1c00c543c405070b126014950f40c0e0a004140d5640306000b07205619151038142c10910000d185417070401d0a10180c0c40c00700340c0702c524540191495811040782030000011030321949134401001451280c0f02000d05022588041d00104107034045c41c0c0354081c01c07051103050b810443c0784940c040c2142c0c04941034420f92400070007412204407049210900411250740c07080d019102ca0382c1240c0c000d41240e83c51555128014030940f81d0054050181400025040d620010074142c1040200000300c060a8039808202800100405c224400182d420a0318080341e141c4041e01d0959500902c0001c00d0f811504000014050034004403c140b8000100d03000804d60701101000071905c9902200e1010345c03540700598454204803406980b9a101c6400214201e0302600050381240181c10000d410300a06400b00d620440b00741c20030079075071070100010801140e00620f04c842100198000b080c400455a80007000c0700400360010b0900f10800d007100c4082c9c00001c000c0c0b80150740c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 774719037 1250 774717787 774717791
    0x1050c01090c060e040605040c1403070318030815010c080f0a030b040e01090b0c0c1504021309030305180a0803012606040609140d080118230402040c110607140c01 72
    0x3550301e030000e00345131310003c800d0702641c20700e240010107041c07a0241c0d408030321080d201e14100600d0348041c030a140e04028016020076844613101807600308182c122601c450b001e65244203c3d4a0892419040b0491408030541040001e107108000b0640801c29100040700c003034a016a542c0c0c200c0400c40c050000368980f940e016150034520b01038490154030564201e0321500030445190303a1079803003400a000307441d00d1140700d030440030b0541400c48007840707282d52207031004041e40d0701142c0b181c070302c98100c42c031040045002c03d0303503070040c45228100741010958800c819401000005265996811640018459000d0942c0201c09940390103104000d0002203440388401c4030b69a15260801c00c0281000042c1542c11101c0c100c1410305108001c19259000b01c41911600031a910b440a604d00030141d43c0c0448030550f55074000032810701c40c0d8005060841d00074159501150400c0c4c0104421103030701d6490042401402c0040e410300c10350201d95564071011900f046400c80c1c40c007200c0041d01c2c1c410f0501c02c410b954 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774720287 1250 774719037 774719039
    0x61d0c01020706080c1c0b040b061e03040303020c1501060810120615080d1805010e10110102160f020901050d0b010e1b07050102070b01091802060708070b070807020114011401050c01090c 82
    0x6c5e4036400709020000442d0f060140349501011b00c4403c1c8500c40b00c00e00014035009400004a20300c0c402941c12038400d107801482c043c40311840e90b040420035540b170300f0b4194125004000f1640c0c080c1c0d00030b4200c6402c0c81600e00d038524207244c82e181117140d01c1005001549543c401f582040c20014110000c111020580d490b8014461b0b0083c90380002c00d5260410040101c0041400e521a0089054408003d0240c02c80e03a6008270058070582140076a460542d9000c1204054203441b44120418480c864151440049a144104042580140c0207c0d0180006954a00c0030694080007181120000341e0554856124032150894140072040c1030035240500191007420000154020b21515001e4034200030240d0701e441204c42901d82501540c40306050842c4d41e080549003903c02002094170814081d407038242159900c0050030070441d0800007051010080090b01c1d80c081c0900c0b60421060340709540c03158140130105c0383c00040d001007141041800706005d0407004003540107015864010320146549 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774721537 1250 774720287 774720337
    0x816112a0d0302070f1e0b0c070906140102060f0708041b0902040e060405090706020c060f041d07021005060102061314120307030e1212060d060207061d0c01020706080c 74
    0x10741030501c02c40018004242e00022009944040119000000420f0040403031800e2800000c2d6084591403232418000c20000003064100c0b48104401008200e4841441c6051107001a06003400140b48040781c610040801803440d6110283c16400f40e4000c25503414a940107580d0705a001d05070b080300c0e034180d1000134045800010040c0c0c05205407401c032002d02039951070043ca1502d40c8050300c14500580d00c080b4045001c1d240c994007900e09201d0a07041395042c207994441407806012a07440c07111240c0b000909204802e9418800d441d00400c4401e001d11040c1400d00000713550300d5004007003004140f810f881100400c03d00034019502041000300f05c032403e46e00405003404542c0151507500c082882e0101500e2021001316810803007100790110b613820000302c403c1c20020340b50000c0c001980407040e10707000c0d40013400f01d20140000c070340900f0000030307030b80300c0c1c07850740009016032110400b100d9001c01d4215246070b13400a0004151115880e204400e030302e442c11290000d028010040c0c41e40042c010b13800c1d6039 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774722787 1250 774721537 774721543
    0x609180604080d1107020a090b0f0a0914130804090c0c3f21150e0604110909070e010e0d05030c071505160f0f030816112a0d0302 57
    0xc003200f480081250b2061240300880f180310391440250401c2c4a440204022802d230340c4230380c14003074000d40542011076092000698880ba990001c092007075031400c00781c4501440a10340c641c8402031b0103411114005644800180340600d00ca4030f80459192565841410311488074100025842400c0384001d43c04000706408684540c001c0b04100c0600b1f02015a0104040d00307e0f1003450740940750509980c9150b510346251145c1d0f0044c0480041d12005000d50084000482c40c0c010104544000c110381041d0b010041a501d6a40c0f54995010081c410500d0940e14030388100e802460700e0034409c000ea140c040041c2c0303581fa42610043e51040c00c205440045c00303030120080c1204518041951140b5031508620000403400d1400080018001d0055a19840f415030304982101d002e88110864101a540c45010000c81808200c00162043c018041d00d180f401c008401c51503400d060a449405840200683d1402d41e603000c00c084810010f00e8418200c60f181c00c3c00324081d8041c0840700b00c3c45c960700300070356 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774724037 1250 774722787 774722797
    0x905011a0a021005090309130b0d0f020a170d120b0f1c021512160207060c0501110a030f1505031b2101090203060a0603110603040516080106092003060918060408 71
    0x8003423103910b621300c032040b40513100e900002c08005141c14049061030301c0f5001d4191000341e049030044ca15440128061411800c0326204120110080100d520080c0c002007002c1c1070740070059441c0d81800608070346a80c0f84076207200b5484003900c502d5085400d220422a40c0e038884407010390405035034507488110800300c80c000c00402c0700c03d0100c2c920135140c01d00352040c3c84000116180058000030000c0c0243c601c182404103138a070080f4004507444118600c2c1d00400c0d8451103842011941e612100881928a40030f0aa4500e03440a210125949040c2c040394640c1500360320b40141c1c00542202c1328266a65020340b503641000d4103494045c0e0300344103649078002e05106500341d220380f19060014450062034000c0d01d0030f81742d00c58542011005804c0c01c2c8a0103400c060700c105c1d624010f952040e504000864045e1005012140c008685507280021010855182441141224600c448603840c1540b01c0700451707030004415035092480b90b0f20500340c001640c1002d200812240214401d100c00e208030440544 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774725287 1250 774724037 774724039
    0x20d08190c0c03080a050c010513021305040308071110020f18090411010503070e2701060e0303031305070509010b041e081905070815100905011a0a021005090309 71
    0x100c5200e600000da4000311845001499040b84140900018003013001405502c05181002800c04104441150079070310202e81082800c0b013821051419894941040f90403450940003c1109040c552130090070203c000f0483c00a00c4071441c0070012240c420040940f4588003d64115144c0d400c4840c8144a039000c0100030090b268075160f400350920b4804400c50003140e00c820100080403130701d40155403a400050100080c040c1404955240c0c2d03d840c040081943c00007045072202c0000d00204100d10340c81070f0000d1041140900700346003151000001c80e84c010007404180402c02c5802e02d409460f02d82e05402003900081074500000b10a04141c025100380e601d4100d104140001d03008492100000e2441002c1d4664081050048049204a03900c035040e4050010394001c2c0d80ca0f50421450060f000c0200056601041c1c1040f8184800701c88c528003800841c40240101c0d407424042525a040120741c80c2e0b807003180058903014207402080b50001d02284803600744950b1826504140d00d0342c02c00300b041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774726537 1250 774725287 774725317
    0xa03090509100608070806010905040608011b180302060c07030c0609090c021605090a0e06090d080609130201051b07030809090f01030b010b0a031d0136080a020a020d08 74
    0x800c201e98825002e51041d1001560703000c40b5552160000c5601280283c001418880600f80204480d00c41d4010b041c00f91000744000325184102c90030310304022550ba6040c004000c0807610049805400e20410411a601240c031f00d904c40303249508050505030302c1c1e8001400305494880000300786e40c00c400c1d913004a514070706040040382400001a0703269002c010b8516090f583c0100140300c2e40ca85541d030a074100142e8800003840e900030224051402c1c0f01a078051110f40d02260351040845d42c000021a40204282c2d546c06043c20449940400c0c03d941440c001d060180115030b0300d00f54a0792404101400a0080480300340755542d0070070b40301c6540100c0310540110b00031400680c100300030017034550407a540482840016840c1a2064106400a0a94004240d1904101210725000c581d4142c9260451070000420b00301204812501d00001401c610303e40205001491706000712214841000d90048100c82e59909014012400d00414450096000303074002400014040035a0180c030580c0c00f00202 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774727787 1250 774726537 774726541
    0x2d0e01110105012601021c020d0b060906070803070c0b040c1802030609060105090111030d0b0f030f19060605100f09050a080a02280e04110d20060c0a03090509 70
    0x340030700782c1e2424081c04507900d4032400b40c035100103682a441044443c8980006003003100c8080c8200342010103041c42c046454002c24055400c40c406e20505007128022620f05180500340e40110300d4500400741c01400106000c00000c1e1002e0240441c4501994006444280d41c0307854642000120050f0050503d001610855820408160320880740036003002001120703144e5801004456540c4400b407100d041008490102d031814604001600b90b49407044404202c081d051400c1c0705410181450803071203a8010100c441d0f083c4008030301c0040b284010ba01c052811401402c00c100a04000d03400750f03402800240703c08442c180d0001103078858801070f80e11300d64000e0f52041041442800e90050b90341d544c10015100006162050075150301d044404030002d1817032040580c2e5001c901007940106401c051400410040101c0304c03c50303020002045031801d02e003001948544403002030b011174255201903d002d48407030329a904400e9462011115017100d00344c5019240003000f07484140706140c011006100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774729037 1250 774727787 774727817
    0x1403181b030a2303041202040c0e1507020a0f0605091f0e190801050405030a0e03010c4e0509120a050a0c15020c1605030d2d0e01 57
    0x44034149035400400400103444141c50f0030541100140c504180c400e01042d08040008082c0044d100030000c0f86d8901c190400c5030300602c002d96030740e800001c08000f01c541001c0f4099803100000c03041c5503034500300907880d103001340301054601c0015001500011140303040000c000f5031140007415500740994059001b03160b41e5601e4811b10111341c4c081c5001c5820141c2840ba01c1c04c0c080502480c1c2c40e605109081c0702c41d030f912282c5003151410b541c1a10343c0d8200043c01200d407504044030b1103400f081500204600c0c071108070018495100b400b2841040440e904120b0100e191000030381403c000819170744a0808060640c0c1e1682e0403440122401990906000503014070000c266049504040952640703441901c80b030884242d40559080802d1020700f0410340041107202c83c1081c000d1045040050341d490325403818504c2d1084011130f5500010300c480084c0306035200402d000042c40d03007070b090088201e2031744034403030800c00c0e406602c002104401d001d20656035036010b050340c01d00c40c8082c0c030707000c9003401c0c109 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774730287 1250 774729037 774729073
    0x3030919060908030f0711060610030915180302071a09010e130f0204081005061c021f120b0d11060309100f020a0f08070207060807050405031e06010504060303120203040201140318 79
    0x790002d2b407000b00c403403982100c1030081e00100b8a040c4140c800b8149030396000b0034902103070f5100200b003100542241107070007015010494800900044140510440005516480148108202581040344203040da80c815200c012240e4000c0c4503211050000d9110b4101c810000d4115209201003440b82e680c41c500a03180c10312a40e070049902400ca0583d068002044040048d514202283c01c2400302c45080da400340780300304182501c01e8507a600311480c6a03042400040d2103000780c1040c820415103941c000080d0b40d00414411501d01510a1f584030740d41d03808601d04042151086004950402c0c0100700560f040740e000700f801a01d15100d1345589440740714100e965880444003440581e2008900f07000050081c190a580129140b07000d51410b51a4000b1905003c846a049040d012411610400008007442000c0c05420141c40c10000e40785035890043c03a800f4852041000c5e07030f40c0040440d0a40e4480da50000409110b00c0b14969a03040c4030785208050240940940d209018483d0a0740200c4214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774731537 1250 774730287 774730291
    0xd27020306042603090105041a1302010c11040c1e03050c07080c19030201050403023d020c12070c0918020906010210060609031403030919060908030f071106 69
    0x1800800c19940c0355035078908202d8192070340c60202010f8048266000c09620f004600c41e010100000c1403c0c1402c0c41e04901001c8140c518801a800e2402004480038280050000b000d40900e0902124416030404200b21a444000e9503001030400c034003000700540000c01580c0e11244072240b0030703c65030440411011a1026146000c600ca402c01600d030119400b14060201c0660700000e40e10b01d50311011944054055954084015035180e000300028560144210314411403d0381c0744192030190303111401081030520a5801e0b0291044400840c031140c03507070544180010720350489c0c6c00884940700c1211160450385080f540340c4c042e2940890740602d280a03040103202d2400d45072201d80c62650800c012030000030409130440c8100d00d804074488103e40070302c50081c81580c849502c21130071820107442c8100c440c400c00d03039070b6802003090100d1140e001400020b03201c03000008046141d01450030602601c1c0b0300b800604001c03000300c24005401e022002d41800384902e61075110804280c02890745d268441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774732787 1250 774731537 774731539
    0x90307050d0309080a0b0105130b0603070c03020705030307050124030804091a130f0c0c080405090c040e0106090509091c081e130204050c040311150f0d2702 69
    0x101a0030800390920040301d1000c01d2103030500da4038258540c0c00c80c626018000000780c0d40f107180e1800401540c02d029203001e2480004010501031704865401049280c84080c101e042044041440c000605100b844001c1c09400c00030140ca5a500032814124040c02c0704c111000d000f041451201d0449102104082044035400300c1c0c11030500c1d1401186400811103590642464403c400154a1b90782e140c005402502c02c0302c1a0000c1c000d400d80900d6030442e18100601d0007804034061586020442e8130083c0c40c110303001143c903480b055070b51031050350290069a02c01d4805102020000c074000e900710303c1d050296a82030790358107080c0d42c4504c15a0b07911141000c5504c0d01540310410001180d100d08441c1e0b501001d00f010070b51501d4000c03d5003507180c0d41c08898901201800030019011440c0c0350150b01e4111280d080e446041504584411000e4458914607504c03038107503008500450840501920100300032807000e82d486404c1c030018480500024080440e410421182800300507140507800c5042c190 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774734037 1250 774732787 774732793
    0x41a0a0c080c1509100b0a120f1106071a06040b06090906150f030603010b010503190c021e01020d11070b0a050a0f051f060201020a20070e01031b1d15420903 69
    0x234a9200c94103068501401034a0740d416980340d551258441400400540b441886040c11040c43d03000c01a0305840081d1a09110368205009a166070740c441d000c0e5030808100315130000035921410006401d4000b145910041c27410f0100f046070318080c0c1040918480c00055000303000b550140c0c001107404d84001c031910071158480a0162005030701c2030b8000541030a0710f0048a095140702c98140854140070000b1090587d00081c40c0c1110418a01900300030a11003807030f49041c544e56980720602254020480348402d65940d00140c070303c00b03864000e0540703020703004010801c9080c60960720301d070841010422201e00c0126507002543c18414421500350369950703615560000c0813590240b21411310300c52608680d02c100000810b520317003150400c5000354815100954441006110800e0001c0b61764001070142030040781c0280a03c031203086895112102c0403800e0740c5900310b103000800e490038040209800081c03409610015001801c0203d1a0455402418811031a500b07403190ba140b20741e21441390960 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774735287 1250 774734037 774734069
    0x1030807030e030a051e010608010e0a12030f090807030305090a0b0115020c030d050408060705190806180405011d01150b0906040801020a0302041a0a0c080c1509100b0a 74
    0x60b10036054015007140081c25501c054213551a180d20303081d024590b50346110220702e15201418001d10462001300303c540000e102d61103c1c030028039200d440030040035000050074a0130704101d034442d07400180c0c921625001000a100e250805514036007000c64100e020a00c1d0401007011a00c0004d0418426544840303103000580c00c202c1c90003101c850182d105400d40c454003840c50000d540511248040881c1c1e44d440c5a01c461400d550103291000140560040c42001c0040010418540c40300c1c06072550582024019900d030f00001c5a006480002ca44042813800420b03c41044019000752040e80c40c0d0600010b0503180d08480107088401251111840311a444000c010011039100500302d0010020190f9013071960355a1581d01303a0740042a9840044e60000c1c041c851082410380c0800c403042c081132551700b0b0170a0500c0141c0400007085001d000d03510b01040f2442d0703105080184900f071001514003212282004030701da59842d04a071403181d5515017001600011410407042642c1103030001c18840c00341c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774736537 1250 774735287 774735293
    0x106031406220905061f1505031503100506040501091404020904050f0a141e061504060807260a030f081510050901110d050f0c01090209011805010e01030807 69
    0x180a094015080d51004200040c003450700c3c0c40381080150182d006800140740c40d19420b40c006240400f030f61450309904405102100c643d070119107050265040c1555a07841d41000040084031902c8030030b40c188140011002000c00e44d800c400d0090b00c041d103080c000ca0340c03620600c02c16591000c00050200b80280001000340c50490440d503041402842a11070800d8186002800c2a10507582034909401d041601030b0502e600b041500f02c402c025130349500300006002c02c00703515030740f002d0044a14800d01506000151340c0c3c81d40604028011310048a041960b105810154021000030351080310b096420424403094001c5400d404041d419900c101d0b464002c0001615043c00c0a0124010070030400c4c0000c109445445041d040744c8030795101c41d522100450001400c0e0204025201a144c01440e032581c00203030004140c030014107480c4c80e940c3d198180c08038264010050311070041c0d4494216000000d015420b02c1000c1e80c181418101408141c0e00e0750920b0301844400e200042c0200310400440000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774737787 1250 774736537 774736549
    0x501050609010521040b040b07080402090a09032f100c0e09040305070804060e130e0d050f0d0c0305010812040f140f0a090e0c030c0906090714031302090106031406 72
    0x401c0300030792540041d004c00c01c45100000d800454046460011500501081c440001040c55010455140060451509070301181070390102400c088201526501090105401051855030b0102e0510503075445201c0311030480784221250705540c2641c00f4508a009150300c10b4007940601c03901549480f40064001428001c2c407860042094041210a000610004480c28000c000428403135550241c1010a44204040c5d80c900c0c4010850300341c0340901380190041c0203d1a8034060b44d15003031450700c403031450072810210702c100c000742600145401002c02100b50140d002c903050f651680100c0c0c100c03c2c01050499140e10660050945214400b50300b0498900102c845100d62080a050b41031502e5a01c000b207218010355410070320405440e0845008070760800c00007070030598001c170300400ca12850280802d07818480504a42d0280d41c1480010b00b10902401e000d0810303a40407180703a9941c6c0341c035030200464410a014121721a0710908000034a10303209005152180a59056420480d10703089e04001c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774739037 1250 774737787 774737797
    0x313050d080f0f042103140328090501021b0708060106020309190e190e19060504020105040312020d030c17150103060503070906050a06030e030a030207050a02060d020a020106050405010506090105 86
    0x40207007010040403030620303406038010242d88841050801c0c0c10381c851902030000c2900040c1f080398504c00380100b2a03013014400415522580c108000c118000b080740400020b0080c800c0060406d43c000100d145902c0c4192031040e5041d14950203444100f0b032125a1207032101828414000181c1c82804000b460380381c00102002c0703081c4135801d01c0034103e40d01d10558440c1d410440b01191500103044100003807007007502601d6084203031840600703030340c134040d81c9100d14040780010003030b1145641780c00240442e4001c03004c507009160462000c0009c1c5c03681f80402903035841e8841d0700c000003a040c0120072003894003d00741205004403542a04d50550755880311040e00400900c43c0a041507120440002c00c0d03101809001e024002080c0080358090030201030241140e0190302c81000c1501d08044060001760210503912802c40b145005661400103042c030754980150038a010790700a42c0007620b14034000045d4000d040003519a0000d201103a170b118104403c0b10424480d050b0003134000c0201d910558840c06c0145 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774740287 1250 774739037 774739057
    0x51005031b04180b030c03120406030b1801230d020108040b0a110d0b032833021903090201140d02251e172a0313050d080f 54
    0x207003441d550f407014190030384103040e00108455542d40d180003070381400d01c646120400103500034418a41641c0700c990845c80341c4d115007c10107581d41118030a0342e035003903c0b540144101e000101e1055844000c807a45d507a85007100455100d03441e0742c00101c542000341c00080680d4050711030141960316a21707004908600202210251503941d01140751412001c03024100403100c000c400510701c1005018181350154400c14103140074204580800c640f0380910320300008651000b4803985c18510744450085220310748001d0f0340e045600c116580204a03070355018142d01d41c45c0105d1a102282000d0080d01241c003c10b202070300003140c1000b0740c44902e000c0300081c0100c4500c03890040ca050300554000030039015009448820001c80c05000090018504d0012448050030780d12214000030760b41d4005a0041d52207440400040c08200480781840480383c5040080241b15208110307100071244640320745c00441c04101800d005a000f103180d00304980703801301d10350307010004c149408008050024076800800500b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774741537 1250 774740287 774740341
    0x80304110607050703210c05250f120215071a0c0d06080d0315060c0201030f181505070c0317100510020105073f0609090b010801050105100503 63
    0x100d0009001300030820040d805a413850b6020000c254105106202040084080262070f0941e0800714101280d4804d4605031480522000180112261565142c80d8412226a600a680001c075105050000d81c00540b084039000c2c2c03214000081c00005014208015001c04030104e00501050481070b40307203070060329140b500303420309542d445004e0607100103800440a68101e038200c000e406e50140aa01041440d80d00d425584a0604000605164a500c8083c0c101034a8030344a5984e2180c0e64000811450800e4003035070302c2541800d00441e00700b40020f102c007846144c000022006480f9646202a0690607a20b06415021144442402c0b00700038080065921400600080703940d030300303130380401c400c41c0d41d40000c41e0515207180d020f04100c0409440c50032020b1468115844c1c52503e2804800044414a4421100c1802003111005091070342007807040510384030144050004c01c098650403510120001e1105a03229000c0c882d4854076a004c4a001ca401130012418400e4070307200355040c400030b1000b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774742787 1250 774741537 774741547
    0x40606170f0a1d0a140604121b15091205030709050d0606051f0f0e060316020f0d180504141314010920090c0f0a020a0804141c0803041106 61
    0x30000807841a1000f0b40d00c1c0d0040c01c0e010308204148040d01c0344040b0b800042c11003454152503c601c03101610320307007008004402c4840300108610300c106a041035004800c001c1804d40180100004109404041e80c000070300c2c0700310441403882030080741e00c00d8110343d0f9041c005c145003c0500401d4180e00d0303001c40d506515440d000ca002c1c0c80320f0b01444028125002e9407840d0080851014000c440c5049040040101503013800b180e540742c1c10300312074111500c03800710002d0f03984504080b03042c20410031034810b180c02081d2510522640c03159617000241003d6200c0080c180d5108c0030441150280c02c05600140e4203400083c1c0110079680b0361061a80c0503415004d075054440e58540d08580801408070303800003c014445010b020726060b5400e1400c419030301002a400c01742301558460160410903140f8080000b11003032100d10034001014250741c4580856111521201c8003061110091700082c0a04401a0100d581c03070548044003c01c2074000264920350388035510b44401d200c0740814095041401001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774744037 1250 774742787 774742811
    0x5090a0b0304030503100f05060a111c020c03070603051005010e030a05010504060203100b03151009120507081908091e0612040302070812030610090b07060209040606170f0a 76
    0x1107210b2840790b80c0706592483c0c140800041c5149039040300c5103040c00030710207005c0350325038000722400c140d8181010081112200300751307858048111340043c05103a200621007411070300042c00e0308181404400380c50b001d6840c1c150840482c0d074101c0c6c0d10b15841400f01410001c550182c05e110310516406800c0d1a81040103445e424256102510102d4500e9070010070000c1070541404c011000e014800f40f514910b081011401d0703d8a07a41e481c0c80d510458074050036103401c40c040c03100c2030001d1a8002050032089018100651a0043c61140c0c0180b07008402c800c1d44c0304c00c8020244070400c0e5000843c5810210b0b0341d410700c514404a0461604030008800c0f01c2d803c5955607001800381601018004100303498a40380081c00c101c10741d40140515800b03801c1e0707070110341290015039510401c140c440108c0582c0d0b0b03480072152141c81c3e40c4a05408000020604107100c140e80040100c410203540600c031840d550744080b24502d540107076510095080402051250b040d0707209080e00718050400128090580517 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774745287 1250 774744037 774744059
    0x105090a0314030c19060b010c021305060f030a03200d05040306090804091107050d08060a0311041b02030408060f060d0308070311041202130603120c080c15040308060a03030f05090a 80
    0x5102001c0c085170b0401d0601000980e019484044600f0701e0010071040c5964041352a0001051100301c180303444200041c4941c4580369881c6a60100070115500c0c8101030501800350049941d0008140c000e218480400c40700c0041c3d411000b030314039541c0324a090304d941c0b03403800100b240d0981201c00f2a130800c40092180e0090040c4480010b80c009410b42d42d5000c1d00e40b9901e0448035440c09414003070707910200005a5100400841200d410000078103c018115000070018012107261280081000e805550f18031b07800030140041c0c912140446240d6150b202035130300d203284201c41e45540414240304100010340300c1e048203500204d103820003290036181181e60502c031b03406c0303504010500c010210f41e1394154541181100d401440a1608101190854403000703005642791581205200001d4000000c2044100803a403407420000c00340c64480e25090f035003040c80d18043ea0260000b03036020b404928240340058510003200d40c1230320713941002c0c12101c0301540d2940104140c240d0008901c480020040c80c81c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774746537 1250 774745287 774745303
    0x2704050f0a0e010501180c02070506070b1602030304240b030a050d0e060306030a02241c0f0216030f090306051e07020a080d0510031202010c02010b0105090a0314030c 73
    0x402100e0303603249424101038045490340c01c007001c41c580c1060010043d06040c0c031032042401240030800301d8080c06102d0181e241c400b4036400b20b07400c44d00016000082c07000d1348000600481c4140303100300429107460302c2280d0b40d0005440150124071102c5c916000001000c1070350700c0140490601141210116000908014504c1c00a80329a0004002200300e10303801a0f840035140412543c1a086041800c00302c0d0341c0d00c4400320024011500e18002d98100da013403102c8111020503081c141076441315180c42110b44000d10100040340710341000ba80354900540380c02540d04910303641d6440c20000c10f0680342180c50000a00c06030b401c3c06903070380d00032000c04c1c90341c02074600c24042485d0010300300c0d0b1b840f12003181e2590002d0003c1c0442d00041450000101014101e5607a0b45c0c00c10f40c0400e13031351200c90351100c000d20390741d100511140020b00f9600001d0780640180c028408160001c0000b03400100041d00d1611865081e2540002c62402c28000903070b40e0146000701401c100101d900f00840e06174a140b074201c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774747787 1250 774746537 774746551
    0x30a03150312031b090f0e04081b0c090112150c03200c160b03150310020a0e0405010509061311121812180607020f060a120b1203270405 60
    0x104c800003c0003120410341d00608015a2802403c2d0a03d0130000c0300d56080c0e20b000c0c03801801032090100b800e100100e400d582c0002c001000c0300194910348024959a5520004504d0048804600010b100c074816400014600c0e0004c58022143c0790044407003005002c410b10101c20306541d103d5420032030f072100f00e029034000d10080040d61307252103501990781741c402c1c43c070202e44035031040000030311000c0da12030280c0790052060340700340c0440609500041d090104800e46d944016101140000a5a50140641004110a64007004281d8035101071040c50070041f02d0440e00708800968146800282c0d90002401c000c0c0101c85a083c200c42c0024036501c44001d44411003d09032113840580004001d12012511800501201e413401c1403a002103a902e111441e90f843c86a04045200d00a5444504182488841c0284455540c499854000d84001d07011000341c041a45000e50201c2a0b0420900148180c05204002c1d424807469014003402c0340000700411002c40c05000c488481521240959401500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774749037 1250 774747787 774747791
    0x1181407030c06050d140919050705060a09090c1409010c0624031406070c120210090819170109230a0b090a0219050d1d07031e0302030a0315031203 65
    0xc080e501c42400d80d14040407581c6c01130040700c140030400c10001003d007006025025140f82821203400c203a41009101c0c0d00042e081240014103210550340440c41030161401c18004000c041725021049400700e400c0c402d000d00d002020406541c2c2c543c0a0695480c03440d200f004003240b41a0f080e03000d002001c40c941220624501110310074410032031060b0390401d00070120001081649440301d0010728000031064081c094030340381c401400015109011010b103104403520b043c441100c0514001401d54070003c5102e40700c181d03c10950702c000d0f04c52803031904001100101640564280b1011000800c1c4150200d00c000e050500075420700221148050300c1608184d40008601d0001c40c28002000001010300d0f1095104201e030701ea070221181002c0c02c0b40c42d030501e0543c2e2940b4101c0040d000801c5c90740302030520052400c4d0150070b850800a040800c1d03030702c01e5000b180803041c0100314441608403110b000300942c00a114542c82a0300c6a440031203401c01c20200d4401e02a500d84130341d200300040496610000c2d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774750287 1250 774749037 774749047
    0xb180f1f0b04030f0b010501170604020702040603051605040608070b031602011d0c03072111013f020a08010902070602070204021210050a0807091e050f011701181407030c0605 77
    0x7203051707480540140130a08095400c500294100c3c0080342d8020032551007141c0c003040754025500c5580c13104000c0c591050440703c2030030580001d101440414414507105904201c40883c200c0e85c042040c0d002c4403412250710341992111800f54903c101d0803090341003159a5691240c55a6400c200010f070300c4c90b09a0041c0c10031910030030605041203141d0300308024100b0383c81e854814070b611f40369a0011868000041c40d0003003103110012140c1d00080315020040351441e1000340000f0149104094000002821003000e070413802d8403900980c010b01d01e00c00e001c40c0510b00104065090350b0003c00380903105603001407409010342d0016080360800d890010907088203d0800000d00020040c030300c0503110843d03211988070310b0401d14580d590414011050010780b10050900c04150003000e801446502420030720551401180407203c000d8244103080303105440d40b03015041d41e58180715610143c51602c07048905d69070540c40f0444040c420910518a5100301b020020214001c00c0000d0007a02071030b6140c0341e1310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774751537 1250 774750287 774750293
    0x120702040b030a05070e152205040317010b0c0c18010e0c07170c0f010905060a02131a09030d08101202060c060a05090d031506140714010b180f1f0b04030f 68
    0x800c140e42080d40100c07003000381c600c0e80720002c05280f1101c02e604913010800ea0303a00d160030ce030080500494105042048030022842c5030400c0f000e49460011a011684014008800c00c015001c00c0781040070b000e0b04190040c41085560b076a92588200c0f600d0206290000c00e6450b0003e508404240f1408178201003402200300030f050000500b41000c50000b84510a132903190252500c00151590b0803040d400601c0203411030401d01128002d180006c0426a200c0d405e0345450703a1341d448651202e10074010034800301c1159000340c601c0d40c0500d8244240c90641400c1041585c0407940c25001070340e1001050119507200c20003003080303c1c400c000310140440c043c00d2204440d13161000c00010700091508180740410080071058540044924034503215441c0d21100410850314815140040c01038041078080d9000c0c21030540003194942001e035009a4654192040d0314402c840c00d5074078100b60f0030101d010951081c0007085445006100d500003090903a5500e0150800d40e000f64401c41d010495a02d0603424 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774752787 1250 774751537 774751561
    0x50d03111203010303171608101703040501030c08131101050903030d09051c1d010c05100c120207031d041b08160503132a030609020a08120702040b030a05070e 70
    0xc0c205c001c14005219087c0012840142a01240d0315002c2106443c00500f040b405000c1c00c0004081e00701955400b220714102603a1280d206014050101303040c0340c69103170443d00c5600c60b01c5c4503003400c4009942c500c0e000c2c5daa92502166550321141000400d10115a15540a00c01411070200c00007000a20a05500d44242002c040c80010500070f030303c0c03041401003ea00f2100e001e403607071102907660b02203a0032080183d070f888880c100d003e00ba81c03260300d038241e0392003e0603480300a0480340c94030f400c0d04c04685081010305a224045c0028005415000700a0f08116400d030403407800c0c4001000401d502c100340324886078030700a40300800d00003241201480302643e01c1c420102c0c44011940b50052840c0741141d8185104410620010400700f8040c95803101d40b000c0100b80603107403c160340e88a90300d40e0f990524001178041c040d0140d1081c01c450000240000700001d05222a000a10482d81892003d07001c000050803200e04c40350b0103009044284001440038403500c00505102100a0ba56040018203065 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774754037 1250 774752787 774752807
    0xc0309120d0203070b1909120201201207120e1f0203100b070807200102010b010f12020c0a020a091e15121401050c1804090b01050d03111203010303 65
    0x3458100d5800c0c940035a5022084807459070b080b20700160310780c84001021043d51800340f404407806150400329400c00c6441e1025102c00c0d41c80340d0013801f94105540c03041c81840500300c01c940c00c822007040380d082c025015540039940581c007410052a0b500507480c4c84800c0d1050026000d503c0c2d000403520000f04c003030b0009140d5140c0300700c000c11821442c10707421840c64401c09000304e140c4020086a000100102d440c2214006a030215200010b95188042103046106441d61107001d54208400801e0b0340d4410182050300d04580d0342d603000504105000300d0002c0d071083e28484804e0190390705020140e100e01048800400c000100003403290188100c1e240c0c82d8462209800040d41411300d51810034050b510440166420607500740c1c070800c981d142051000d200c942048140d5404c01d01042101d09901001d09461807102c1050001103c07030504000803a4001c43e0f0007002c2c20352000040c011070812074480c40e802e40c13080c24031142000c6109145032405501d01241564294000014010568080b200301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774755287 1250 774754037 774754069
    0x21c1b21150e070b03240607240f14070305040b0a020309031e041a0c03030f130b041a0a062403060e01121208160e0f150d05010b07051509030f0c0309 66
    0x4200c00790000141c281c850f075030000e0480e038500b9612701d0f62072060100480041d51b1501c01044040c1645843d2000303007a038484004d00c040101c10008165502a01980c0e109035488411308825541d0302e81039100a40014002c0d12845c841030100c81e040490f000c141d80385500071061180d13241c2d0303d01601031071550946442c000309050103101c00140d42d07000000351398101504c80414003881e0b031200080e090310141100050700a40070300043c4414465111200030030040d6441141da49561400d41c2e00d015a0740078810140400d01c900b0a4294400401403012142c0c200b520f008202c199903451424001402a0044000070303441c003503400e04104584001d0170f07622074142080501858900b1b03ea150f12044900c0140c28000358804801855440c01c0c15446010801018802e10340081c0810003e103402c0500d000605074a00400031039200f0200701179410883e80b01005040703038420350419071a45d103806003401c206844240002180100706038080c120000030f50004648840944003040f0704003400d16009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774756537 1250 774755287 774755341
    0xc030409150e0411010e0612060907090f0501080402120f030c070806010b030a15050306150306150901030312060923060a0f0909021c1b21150e070b03 66
    0x30412064008042c9622541200140a003402d009005990101c40315440c1380c1d00c8140011140d520b0103a25418500440050340c60401542c2c0349001640d40040d0782c0500100504c0c4031300100000d40c41203c0f00e039802803014000c2d44d8806000382c03803546010341c0c1d400101c1480c1c03c04aa80903581c070303003004000c0c01040c07418001d04a03549400120884e901c400341000c4021a207403407405540800340c659240c0180009130440d902480d0a039100c0d0549070b0b4121402c0d01c0781c02040c0101e80955000346921202243c020111b4080380d185941c150780000c01c102e00402010340f203c3d40010404070f036125101b4500f43e24070815590071840144480c01403802405180f0405441d58140030310948145100c042d104082030019102400d0300005049810f0030031503400107035060b43c1c01c10070441d00406004044180340c0f104000540c0b218412642840c02d00301c3e0048000300d00b00c5101c040758055110801c940c40ca0000060803208041449041028a42140a0116000007417010346800c10b0b40c0007180c60140700720 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774757787 1250 774756537 774756539
    0x7030603110105031e090606040e0f06010b0a1101061404061e14010903150603110a08060f10080a03090f0906060507060b0114030a0903081602100c0509060c03040915 73
    0x64500d4014903a807602d04014000c0700288003a4044110180c41d8940c3c00020707001490008070281d07075940700315500c60081c0e0a1408060412800003040d858219000001d00b1903603003005d0409001e03030040852141003003c43c541449215200384104000b6181c505200b0441c14200741c140025100903500c20581c55112100150341e01c1881200f140c00d48800080500410b02c5c40c200403554074100341c2014140c2900e50180803820171141c2c0c0402c00300e038440c65100103108240c80c10802009140e100700012904084c000810b15040f9520b040da100c2c41410f50054400d464660035490200d640700c1c21070108800c003000b4040c00300c108502e00018000c0d03030002d0121900702440102140600c94005001580f10011003160340c0c010114017129040e005180d940343d16000ba50a8081c0070000d4040d00411481c0c8049441c01d440003080a00c4445160001d00c2c6041c1807505100081900da01070804002003444400500e41e04d50b80185113240401c801142c4a0307081c907131810100c0d005001c8440101d010044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774759037 1250 774757787 774757793
    0x2060f090a032d0305010302121c110109080f090405060a060e0108150306070c060b030a0f020d020f04020d0c09080a05070b0307032a020d0e1c05010b0301050702010506030607030603 80
    0x4101d10441e91500d0400408800100281d00365a070307155040c06208803200c2c0006003203078145d0113103040301e0007140e2990502511400b9030b0340b81c207800500d207086030b07a401841c01e0a40b0f00850036551101504000019200301640303610003207402c00300c03012100010001c0c0c08102c900d000e00840d07403c0501100d9280700507140210140c171006c250070323804c0d05004441c00010318580b5008042034901c034020342a24940d14100d10300030040030200c0d41c00c44031545058551481e0741000200b082c505540026035864500306a020000b041c44403584c201d0307100c14442d003035a601e511140040c0031040740842c80030480c0b80b100c2c9005000600c550f040b03540580c0c07084003500d000c29030000d003c500322112041010b5817074480100440c050044101d0744c0d1202c0c0010b0218138082020303c45c2c911604620381d400d0b684001800703801140d2a20310342d0007a9a100c0200d1501a10120314100070700302003172090b800011001850310100f425148100c41800140c0d6444081200c1030a040c4522036001c03402c0c0c40e04009480c15a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774760287 1250 774759037 774759043
    0x3040b090c130c0306150c03112802030a02182215090f08130e0c0c0d1202120114040b010503040f030c080702031b0a050613052e0206010602060f09 65
    0x1c0400700b005454207251002580280d00141c05000004e2000444021204018100c0b41e10301c6001c800140c400c182910b4028404181c00e01e41400728951240880318803a96580b1020b150700043e07a041c010014111300580c0d0340400001d41c103001840d5251546088400d140b40b403500c0e00d104521200340d4240c900002889024100142400383d14005001d0340c0c0c7d410151200010090700a0050400140c041d1002116800d030208580d0b20901c99009135440c03004281036405030421051441e400748007141881c5004521000b101c041d4110010300f09006c840300903a40d004284c0c442a428254000604801d0170305004451f110102030a2492840c03d05564461200c200740d0005420800d1500c280f8040010060481d0003841d002021541c807002801140881403014404c52441950113200004060504405481c60000e003415141e41a620700401d2220302c041e003140e0442014030001c510f030007900840c0c516212080030342e4000d04940d8180080640340c190068580002e1920f04010002500000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774761537 1250 774760287 774760309
    0x8190c1401120218060a050d06090e0a060e19030513060c030c0803060d020603040b090f0d0c061a030a1b050103051005010507061d0a1707050309012001060b03040b090c 74
    0x2400b0069450ba40b2161402c43c44032003100c5150310030b0000521303403005940b1002409106a000c80c0411807a65503600440c2126051507090040360040c41410f40820700c140c1c0521041c202e81c20544000c00e1210307203805100c40d082e0303400310041200031800c070003011321480c1729401424650070b01a04c00240754130040d003022140c034030007048600001b0004a40d5152042c0900280703501400f070360b03100d080c0791618501e00d04003240d000d5003a202c0c0c2100f1203498000010703403a1100340b15442d40c15001145860f00340240c10441c1049401d0005141e04c003502e501d01308420382c009805030480040e44500c00410403e280c141c0c3d484241014200828011039103401c0d00c10f00211942401c10035035074109442e001010349011081c045d6840c0301c80c52000308802000c140200442c3c4200c02400c2e000c00c0c0700c084114a030144550142243c0d0041c002c404543d4025407520203020b40d03168031400c5c01040500d17103a0030744403290440d004004004c0706020803c90180100d82c0c01c0703030014016006034800d080200b0251140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774762787 1250 774761537 774761567
    0x10b070b0f07020309211e0c09280b0d0507060810060504090509012c010c081e0603031204030e040c360b030c030402100c11130608190c1401 62
    0x403131b949440c0d24080224146c4c80b4002610a550360304000b00300c029400405400c10032810302070400b08441a160415485100300c0407100c101b040700d88240d11500740481420b505d41c100c43e07512020388000ba03075a09021000305108000800031103003040c1d8020300d0744038050075581d2410b00382001404080e42240580c1c00361013030040001400d0791214805400340c40c0502c0a111000c2c50400d12010740c030b4110001c0c1030030650000090105100d04d801c115040d4508840b403440161148481071058801001c2c00394220a0050031031782041c6e0950009900360000f030ba800c4020071440590800c060a06005440d090250350500103440c081015185050680f048199600304009001440b100007116502c40f001d85004c0f48441e8603031910810b44944e0354010745007a88075104030300c4001d040e03a1103096a0540da0b9407085124080e20180c2040c0a03100395101d02520515481e5140030036078007410000d0400784400101300410440e01c50500c0802501c00c5d8110001c80020f80c1524142030741c12151110308840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774764037 1250 774762787 774762799
    0x30f030315170106032009010302041d030c0a231e1009050a0c050901050d0f051219080f010f0e06061207020d080f06010f030903020114010b070b0f07020309 69
    0xc003040001c1040a4102010400784611011040c01c0c056021205492003052001d440101200d45c0e000207804005403258404200001031005013841d80154081142020f204030080c01c40005150a58019844000b140d6003c2001d020901083d00803d44075075507000c800c18911030410000c0f949511602e019210402c61b103d44a12518034100702c60840321550100c10480c003009450460f455441750b8209035483c240c20080030a407464225002d0341201d0005203944c0314646507650b18090f0508000c015202c9020f07990488134540d40400051004440001d440381010858050107031039460050301214119500710014813107110101001d20503035881c1a0005000d07070740e08000814a20400351507104010702082840019038000800304005481c5807100c03e803644d91400c4282c0400002c65046000070050901244020b02950100101c503009100120301d225442511180b15007083e400050703241070004200701444041e1f284650003041c0a6500440d504264400030740d40e010700f81c150fa200742 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774765287 1250 774764037 774764051
    0xc12090f1536190305060a0c080a0b0109060c0804030c03080301212019060504080607020d080f070e03010509030c010c020a170919080a03030e0a02030d1404030b090d0207050a030f0303 81
    0x450f10404000030b640c008203c454604c0c0c0120041d0142c03043c80c0c6210302250000b40407414100840c042c14030b03180010782d211405a0f1074030108540d0440650025076001c00d040001201149100c9070315809580181c2d03110f17903203502d00384000d01b140c01440c90b0320aa0040c20086140001d80721401880c802c00503a46031051b031006d420005200484540010f1000300c3e1208000443d01d4110001c2d008a0382140160f5120703a0718010240d0300d640d80500094002902d22001074140300701151030030b030441c3c4940381600d02c40340c5500201c1c5c02c4036016070f040302c1c0c640c2c00800c43d84a191030034001c0711011803031480a04800340560342c400c03620104485181d0076000d40411711180c0c40c0c031146440854101026441381c4625640d00c2c040340c580752440000c2d00020700f0441f408512281c00940ca4081035406401091000000d100440d4840d120799695580c0500410001022801040340540120580c002a104429038140068500a182d52010f030103020000810070100b45a410801c400e6070b00f5084c0481c0e10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774766537 1250 774765287 774765319
    0x6250e150912100c020d050a020709150b0a0914060c0705040c032901090b040e07080403030f0f021804050f0c160b0f040201030c050c12090f1536 64
    0x480200b0b01c1c0c000440c850392003407200000080d04159280400303902640c69014505e181101c192003a000d03c84050b911a000c1004002c2040c0d2025110b0380048041c100c009495101003000780e032040020380b00050050200b4450140301c010045280385c401c544d00e03450700c007940d10781e682c680c1c071584070307051207140c0e60124240141e000f80c102603403a841d001041e8441010f10001c504200c0320503950580010700c1502d020419155a80072501a140e80742286000e46d9528a41201c2004000b8011410140c0303071080001140401d000d42104843c5544c2e015071240c900091410003101070403030b11446141060180040011034208180e001201442485e545d100a00b04014411002540003040241e402007007000020303001c07078950b010f0343c400d030f03010720040c0c1800360b085038980564400140b4941007100000c505000c0440105065003018010b40003040050001810680e50b034003281c01c05400c0082c51060780c3d600e820b241c4034a00e00250800786111446501074001c50f1010506502418091035040f0740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774767787 1250 774766537 774766549
    0x6030f06030c0b0d0507050a0503131a09070e060a051f0e0303030a0e0606041a13090b0c0705102c0142120f03050c06250e1509 56
    0x7850b000690401a40d03615006643d0707070b03031100c005074150a2030840410304461280c011585c194149959041c110b486031040d20340c0340b81e6144002c5854641240302c4411036003801c1d44440c410000c0d88050001c951030031807002d404c41c500030079140c400d44460406200b50741c0c480c0509641d200310a00c0070207a070b0500035800e5503a2012104400d50607c4040200b01201c1c200341c211003c038402e004159000340c0c503840b040c801650002c0101a55140c54902c8240040c100500840d40b076500342103000c1104040758131500b0160710141e40d0ba0034440750001e80c00082c0807081186254407141170008101c400512060516503600c080f00c000c0d0364401d04480700c940034a09400080c80b0b4074050390010581c2c00741c0000340d80554041200d1703016840d8001b080000141c00041d14070201c501603d012110b02146035209606482694002c40901c4010700107400d01131810440390344990a0460881c0b94907034003030f88003104064910440c0041003042805400c65440e00d40c580001d0880200b5103036154103504e0300081d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774769037 1250 774767787 774767789
    0x4180b03070b0c03072a0603020c010213090c0e01021b040504020a03140c04053619050609070b04051f0207080d120515011416020a0305010203040510060f06030f06 72
    0x100c0d032034010440c800c0c3d2081c040001c1010602c10482051420420b0860405014000c0803000e00d45c268440104400390081d0010038094200c1c1c40018903208a01400e0843c1600942100740e030182c1d5040c0c001d00c103d40006141c22802000d000030020a1030340080150044c00b81c420060003070351100086011502c0b00c400300c00c0136640c0710b0303c0c141440719440c8589a84200040d88288a10f0030903011038585040d50070b0142c145042c0141e81200602000f00d020821940d000709906540720b44001e01450902d425080050507202d400900306a0419190941c03a22045401160714010708000c00c2040c2e03522034281c100d42d040a080e607100c0c10355441300181d080050303035480300c2c58901071710f400ca21042ea0f00c1a103801d0031a0760000304000130386911210103040036105503c0c9020600c0c0103100015018000084c01001c18141e407030f174031512042d602183c10818564011501e40e900407051004101041c44041e50040b40340d401088646c0c60b049171003a801c08140b152000b81641c0e08680d011941a50b04807034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774770287 1250 774769037 774769049
    0x616140313060f1b06290a09050c13030b0103030e010305011d0910020f0702150a0e010c050118030e011b020f060f0f0a051308060f0126010504080a021204180b0307 72
    0x411000c545041c01030240001d045846c00d00c1e4034000d400083c0352510f0003000c05820003d045602e041381414003410061101070001400780b00c0034000ca8034000760740c411010285200342e00d400340da07500d98580600191400030245052501300f10060007030500a51f1000000c8165201c00580c98540012490034200590000c50510703000048103c1c207400d03034030700900159100795500700804a619140281e1030180c0e4050394001034031200005103c0d03100b28400b5903268090310002400784604a1750060300301048208401164503260380000c65a0484c40402c0000460820100c5002c09070b130005840c1115001141d12441010036901d510075106802e8414040101c0a04c075600c0080c0440a80150003040e00c44111481541e004200007101140f81401401110a0810075900300741046080c507080b80c8001070304009290529207040c0c400d01406010314001d031801591092201402420509110040502e107081040208040c0040c0d0503041508280724200284d515039203000241801190360041c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774771537 1250 774770287 774770327
    0xb031302060912011b140d02031f03110a050f030d080a0605030609070509010f0608190b04021b06061206060d0507260d0e030307030e0a050616140313060f 68
    0x100c5042055018485c1c00da01440f83c0e240a240000d001c039035141d12000c000c62060002d02c4001d101d004144c014541210811070900c1c40c283c0a0100090030328001c1c0d00598841c108074010300c074681000c000c0c800c054142511014a1008040082951003014031071010410064900007402036000ea84000c02800005066417214140006082d035100b0351406580e20450f6510300028046000210700c0c0112055a10303004040d40e288440c0b0010702002d680ca103040c89895580366800d03955544010801030320b450004a002009489041d440c040005001c24000c08102c502c0002d18200041c103503500040441d031155540f13880e460140c4c2800c5065100c5d4040d8801510b052400140340001420840c40c041c0450307240000d0036104654a0194010140d00350b041045018040b0303203c2c414010240202814103902c65a03102c2c0840c91a47c05030100785060382e0300b03d44030400c00803c2c0419060f2415510015400c1c214401144008140d1a00c80c0100340010340d50303c1c0903454050440404500c6000c909 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774772787 1250 774771537 774771559
    0x324030109061b031815020f0d020309010f0614060d0213030506090607030b01080105130b0901080f120406140703031b0305011e0608190605040c051c060b0313020609 73
    0xc640d003e0001da00e50400252260000c40e06a94401d100d07501c400e01140c011030380901000d403200341c5d5025690007002d00c0c80d80c00300001480703020043e0003000d809041110060b40c07880d21508250848403400125244241014420800c1d40011404880344540c00c443e0700c0d079030301c0340840b10b400207104e000c03034031311034031030020400410311401264981c0300b86c4210f01525102d640d825002c038111410118214042040ca20041c02141020241d29208a188900004103040301200141c000c4c80264864501350f4084240d001076250f06101b01d000c2e01c14a410b04600302814a6005442e03640700921850f60900041094428035109030490040300358050350f58440348000700300c024060300c0240290350400450964403081d900c500109001100d05564131410282c03248614014642c002c801c044421980b6a140844e4540d0340b441807114440598541550b00c42c11241d8610499510b055114000e52800ca0202328a0b01403c3c1100c5c1d10065685103491013100b0b62000071054014110080c0c1c0040c81011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774774037 1250 774772787 774772793
    0xf010b0a0c052d03092b021207260d0e031005040c0e160e040b040608030c0d0f02280f1b0504060503010b0109030b0403020a02130c0e0d080324030109 66
    0x3140c00205100f0248031040d4400b14421a664420060b000c0d07080a40c0d100900036801142d0058460600c1010030a00f00d0249900042c511740364400400903a6040b006040000c80450440031f104c0d4540504004d100440c10101d0a484030001440c1320b083c000c2c4444408410341d400c0c0840f446d02c070100d000410040c2000c2c10420400d240c58040e806042c0d00d50030100c1d2035140541c1c0e00005640310781d681d48445a9180c01030002415a00301d401c0c2d08651511400303e40300304148094101c2044c0d0700003c20101a003071400400100750052400c0543d08072000134940d440381c41c49484002c441e100010100202c040c0f4108000780d650117006072108010305003000700c0000d1022810b084460458081c400d83e510303401010300725289007103c80c1c045941c250f81040010304402e80e032540280280180d8004001076004100e0303402c81e84a1814041da55208002d42c00360308881041d840e01c00c01e50341980d10a6442d40c41e03e56621001d0502c41400c10b0351011012150200c1302ca9542c13501d400703002402286502e207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774775287 1250 774774037 774774073
    0xa14150a05040501140f04061a1804050c0a0f0504090507050c0601090c05180307030f05070914060a03060209030a12091a03040b06010f0507050d08010311090f010b0a0c05 75
    0x1948403485180c09140001d002e24141c0121816074404a500000350b11414040010846c040a030366071708161600700c00a0881c1c17001c1024215600d80c1e000c0a5550031407004680c241213122000d081c400e500c0d040500001400c86c2d02605c0d20701201e824070048840000c0003c1e20343d40541e6000300d90702401c003000c10020b141e014000d045140e0b80c41c003c848060b40c94100c8042521502500440002d205002c1009110500c540c0e050650340d01905031850b80e5200e481d440410401c01606580a5011a01c01c000081a80c4516104240000340700580d5003820b000290301d05032036200142c011500407620604695090080d081102e50207254808010301c0140702400104052260303050202c1205800340c0940204c0c4100c1c0c2c480c035401540d514450b990380006440c1d0850214000003001010301c864030000310100314880c0000c140c0d484102d803961541c03602c000c8000740501c2d07043c02000c00c2410b00180880c0d0501c1e00d070643d00104035203138660703440300341c200d40b108540321014256200c4c440c1034200f0608a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774776537 1250 774775287 774775321
    0x140712110f0114060105130306050103060207050d050f0d020c3904020f04210f06050411100f081905041406070f020307060c0c0203010c210b0f090a14 66
    0x109081c1c070034050786103101a00303c4009280c042c1c0f000001000164082d0300c1034004014a42c440150380304c4d5540c43e41c40d01d008a42090b002120001e0b80011040c080c080200702d450387e0300402d0302d4168030380040c0ca09002d1041c055041701c00c43c42038004c40c0e048a9603c083c05100c0c05000010a40c15801c05108009042e1a42c00517070321888405910911007103041038000c507040d00a5820103145014034040c000700140090307404114206400d4203030900060414000b008080e4000c5802040c03608041c05d1220006140f5070004d031140100c44030100302c0640100c1019401c03020750404071590b40c1c81c011048010b1700d82180f5000058500010032040103802806403603001e508104542c0d09940f80c9000351120314444400d140540e0041c4401070020741c0350b40044122510510f000489212980d011a095130f280894002c00b19031403111459140ca00c8560884480d10304510900000201d00c020407600c80c80020302e0350003000140000ac81c404401d4101484c5c0003050350b212082803a254820041996503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774777787 1250 774776537 774776567
    0xd170d050a05060f09011203031b09050301050a05010e16210f06050612041209030c140112060b0706200a02070602070f03030e040e0c0301020a0309020109090510030201140712 77
    0x1e07000114520782851541c06141c404083c1c854021071f42803510314128088910380c01c404240e00c0d00b42c091000d0710301c0060307174642103c203480f100403e5080204050035030324010088007000d440e0000422103d40403a081940001c240495012608003040f0304985030303000344480000800e9464900110001c242e4481441e0340310a000400241d43c41d0020011a80300d1446078150000547d40030034041034017000b00142030b15040c100708280d642e5030b80c3d03184d0360710015602c2200c901c19141c80d082c91558004803650803201e11500204038090074261118034500518101400d0a640c42e0441c440040341105400902e200d00c24003503440354001d900080d80d0341c0490007400018058200c0000340e00110021681c01c1e0f0ba410348076141d80149040c00e10008101c0382035010302500c6411a0000c9546003032000300100c908a950114660000f800003400420544d07014145d514640b108010241856045e080c0650f942440c110b4580f601716228050b01d8004c4941c0606200e02c61042445c0f42c1d50003c42d00d40010346 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774779037 1250 774777787 774777791
    0x60902031e07080d0509091012060507030c03061a0702040213090b100c0309090e1606020f0f030414010e0a1701020304230705061b12030a0b03031303020d170d050a 72
    0xa11000744030340760130200030b6240204806103c80c142c1c80c6000701072650b00c609020b014043c115503408954010000d410001d0724000da41b038040c40a100e506000d000c4c944031290600740305141c50044020305584004000c080f8808010034601d08556468040f02c140410b031072003a407001c5440c5d41c50040200000500f05201d4154168942c0f0410f01a003218101c6542540740c0400003032070580c1d0341c0040c3c90b8050b90810305000749400d0b40c41480780f10860300c7c050405603004110748003203a01d41a26140400307000b9101644140401c100509988040c07903d002020701e0728801c00c2d00070002041908402d0b8001c1c222409103801c0388401c43c001540a14840c50294800d02260302e03040b66503c3e021030502c000044181c00510f82448181000f02c01400781d004000400b0460400b5602c0c01d5043c1100604c000700c1c0e101000042c000c00c141280100b0002407021006545410100700f07032441c40c503442d0320000f03000700c07481c0314000c0600520179400d21140401010f1a9900c400c800c030824003c0030120b0b02d0300c1d03002d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774780287 1250 774779037 774779039
    0x9260105011e230607030c0f0b0708010605070c090e07080a111c020d0605040503090a030501090b0702031207030b01051b0c1801080309060708090a0f0305120f0a0c060902031e07 78
    0x64901520006255000140c000c43d200c14051010a07880701e1002e80c24040c0380c542e401c1c0040c0d88101c540180c980240b04a00d014101f182000707201d00c0701070780200c04104060002e0008518a482c1001c00c542401d900080c149400c42c03502420085071394424103640c0101c1c41b151007413040801c44102184421510301481c0f80b10f00c031a205030b1030f00b00c40d03002e50412025500e950000301980d101340d40090103081200c0c02c02a4402c0040c3e04281d840c2c10841d456519401c10784200215210225004000303800030354105050660904071890000705520304054848850400d2031f401030044516091900103c49410808451002d9450602c0c1242c0341c0601c5141d88401888403440e10064140d0b0b0184000c0c42c0382082e040304000007604101c41c207603000c8004022800b1140e94407a904001484140c0304540d034189103013032040c2400d84528042d440c44004010030080c2201e00011526000a20b0514550b1150b05090510041401d41030080d0075100704503c4c080f1410160f042d2071000011001150582 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774781537 1250 774780287 774780299
    0x70e0c0a090b180906221424100509030102040b09010f1103040902070321052e051002010e1204230d1115040e04120f09260105011e 58
    0x1445446480455410302c0f040d606003520784004410340004004040344c4071101480d42050030000c081c0005100c00c1d41d1402e4071000b2040c2419583d503c81510341c0340200825000132110b0101698101c61441524031039180c5200a004409031402c0c208090021501d540e2900c413800c22130b40c42003030450b0105400b521128030440c0f00301245d12885500b83c01850609180c1203440019400c8044102c0032300903810741c2c8080c01c201058000140399600745000c2440c2c2450420010031601c0c0c500303070100400c1003913405280c3c15500444001183d80c145c03030002010700c04402c1240100720445849041e030041e940f207010300081c3d000140083d90062042c0d49503c000540d034441010039500440b581051a00c1c82e03500205000a12001a41c100940290030942c40b00d183c901450f44107810450003042000180310030300c09605400c40800000d42408801e041d01808050320000d21881000c00d101040c1a100e42c44011075181c07400d16007030100c0280003558403484111004d0302d8424074108074070410030f400114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774782787 1250 774781537 774781559
    0xa02030a111608030a09050a1505011e141f0305150307180903090e0c040f0e06091303120c0e1905091f050607060f050c2a070e0c0a09 59
    0x328244102d65030a10301c20960300c407903180d000104082c0722181c0da14408800303d1070510509260b01d00c523010382c0c00c4428901007903500b21f4806800c2041d00c6641259803c9440c000242400c00303680303040c440f442c03210001100161910912042540302c1d40c400021400750789400d07030041070143c04c20b01c000000c0c0b483c03210181507075500316215100d0a0400501c0c0d00c2c80c0c0701525031210422074003921305814015203901c0c2e0502042c009417154001c0c06030010301009101180e01c0c118001c1d004129030014541001d000069214501030841c80400784c01ca1000b0082500407044050b4206003020309201d0060201c5001d00f01e08032070f000c2c840c02a80b0741c68000141442c0748042105562000300b810765a0b840780c1c504204c42d4262030400341040f214144d00403c459580b90003400105200342004a40900201e00314419a4005803400103800402d110000c0070200030015000110115030001841d03007601c0d03070150318190341580704122041085081c800250120001480c0d48466525038695040d035030240161 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774784037 1250 774782787 774782797
    0x605010501260414060c0307020c0f0a06030513021201020904050907060f080426040314010902131802121501080f07060302031f0b0a02070905150409020a09050a02030a11 75
    0x40b181c44500e400c182c0c00001406464110340103583c81d00e01d007181c041c03402e4900071050382c0391020400003008010005504002e01b502d00e90003514044645001c281c003280c0442c1d00c44c01103800b8162074500249000c0c1100c016605613a400402c5010a02d5412281e24001d41c4544001d41c000d03410800014140d600010322134049075416501c0e8900781d409813804452144000c0c004480c1d4181c1d504910200c0c101d19418503010385501c010140c2d40305e103186001d03050008402d100c1c206690401400c0c4015039140c00ca15258401022400702d855607103e21010b000c003a204100a5201a40c0c0f6030018040000013440b0103005204031124032966214580580e486c030007403070103003250380c80f04609010b1a07109401454105025942002c02c040791103402000041c1c054008106001e00400e54155042d4100f0401004140c1d42c2c508103c182440ca03410498640e4204800c0d00a949034482c09045440ba08080b5001b880c100327608100c1da0404001c0c802c06540300782d4252081c1d5007440307180309207218044101c42e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774785287 1250 774784037 774784067
    0x1021c11010f0b040c0309120c02010c0b1e070c0317060a0b0f090114040e0114040f0c170a0b33070f050105070e1e01090b0f0301030501110715020f1c090605010501 72
    0x100008c0c00c2110803079010f0a0410308074100b02c40c1010040004020b0602c29000d25401c0b0400210302000145040743d82c01c00809090070020341c88d20b1100425001324001d0122a10100403902607038400020840c0400035034800c809030000003403441e01c4901c202e030283c0f01d055801d0b40d90207034901000510250901850152406c0036500b603004028a03600d6034404603140b0340142c400300e000c007545c2c55540c00316541d140401c00441d4541210741c40280d0280d100759808280060104281000d00001c101d0303a03185080d040c0ca030400c601e190000d141088140c114425921b6015890741c0b10700601d48541c2003101c20000f00d07159805c203000310b440c0320300071980c0d4010298041c00360700f07401071080d10711100f010a2400f001e05001c00c0140100798109400014040055a0450150780307515600c0d1207401c550300381c81c087c0301142080c801680040c100800c1a604811051400750316106218040c1d0414401e8140066450360502c5000b0780c1d00340540c204099590181d00104143d07a6204010750f000084981c000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774786537 1250 774785287 774785303
    0x204140a1d061302181008131e12021c1d060306130c020c01170114190810090501150b09061e0304050f0601060e01021c11010f0b040c0309 61
    0xd0160003141141d10350b00140041000c003496070080507080403603026120814440c0a91003800c00c0741c1c18416000014016a482c02c0c240514240e154010022800340000f0801c074040801e0100b0380301a04111450f460304283e02040c100c221b40303000b80d42e503800000300d05182c440c060180d84140e07000f081da071034a591802140f001c03d00c5210040160030350000b403480790300c0b42c080542944109000e1040c000e000340d80743c000300b2601804d1340000d00000c180d000042a09000400180038440030b440130324078840c4065400181c240110b1004030034004007500641c0c030078410750301201c42e039109582280251900480c020415001c885072111a40c2c040341c0079079648a4810088106c25081240082554081c1792403401d0080d14490010100c2e0b07441a20291029030044001440100b01402541d0050016007000ca154102010010392078008200440002c1050403440c000100d0051241d0083d000d0050b000b0400e103011010644000c040c0d03110a24003982c03424002d250013501038414001010741008003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774787787 1250 774786537 774786569
    0x11e020d030b030f010603060605010e06090307030b090f0609030a030608010b2206030503160501180f02012f0a11102102040b0c01050402100c080703080612030403060204140a 77
    0x1a405002d075845015018416030140038400d020a100741001b0390310800c40408c0e080e2520307000501314080c03000101d100d0350302000081c515640000f8654200c0e0384c401a845403d80e5000c0d40603082c10000210300da640d000c0d4000700126114080f0050101d8000c54504000e074940b9075684070300326000e004080c4d030005007801010720b01c2007100e03051030314254816030301068040d1070344d03201400c2d03802440c100700805110300c1b2a401088020b020350001c513030954500d02130030b05480e201c51802200c24078010781404080b007881d007802c42a55200303460b1400c0d0000070207014100030501581e1032058607400d407194145161042c02e00d2034005206241c01030302c0d54400100b21541d4000e150f11611130304c40606000d608210010f5420031403000340c1034807401c0c100001060b1500c0c0c01440344655911801c2d80c20481e218540708005446036040e81c10b0ac5070075140c415844e1f034985010500705020300410489910001c1000000c0002d144c0080c415290500a40821107020505114501d86203024151114142a078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774789037 1250 774787787 774787813
    0x1a0d1514010305061323030702130b060d02090f0a120302010e0c032a10022404020a0905070306050319170f0a11030403020a0311010206130c051c0b15011e02 69
    0x3c6002200e0340500c0025903100d00d114211ba5140e41c2c0c2d110001c046400105002040d0b183c916540c2c20301c103080d034030180490348a01c0300040b40c43c810001d2030b00045501044c84500c54850810940741c204001d8a1945515112072030801c0f0008c02c41d000324019801c080c91850210400b00d5009031f02c01c0054001c08a4400c1c00d03031001c0c0398900140c21200c0700031010340c1ca26101d60365503842d0704010800c1e801800580260009001800012298403541c2405880038000184c90300160001250850b100005075615824070032005454581d0090382e1501c81c044048010345c4d80804103201c103601c6191240030001046111512a0149108005414509204003c0000d0081c0c5103080d00192100c240ca00e01600e0b640000c41004440d04142c440e070b00602003203201540c0401510703411170244903504d02c641549030f4421180071040d0180138001d190845000720000d4242c1610388e03146070701c58044c0e0341034500100da280020500e10082400603600f4a81d102c40c41c190b61741c50361315607000d90380980320b107100000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774790287 1250 774789037 774789061
    0xb1c110a0807061110050c070b100b0f0703030221010f0509061f111f060608040f03050c10140709050d051504020f0409050c01120204050a091a0d151401030506 70
    0x1d0698513040c0142400b1001900240c842e0320300c00c8072110307911515110581010390031a28018044105404002014860542101c1c00e4503407003100144511b95405542c6401c80c040d019170000a144444d0021614003d5400080d41d98140c1e001d031908205100e0352841000800381080d40e080c0e8101f4a55850500c40180250400000305281d04040703030181115031a046c50400c0c030094244560380c0d05c80480c0c69420240c010000145a140341103581420b00340c541f50b4580358091001002e00000203141c5522030010301800224a03020b1a04000d4000924141c11000300c1c1140c5c250005511190049a90316050f0003c00c00e0b55001001007141f952038186640340b03290003400c1a40c0c0080380b008038510075551401a00c80c007500c0340c400742001c503414400142040c20742c0300e80807400f01e005000601083d1100b00e1800111500781c2000f02e40401550007034405041c0f506101c5403c1840c443c10101802408421000b000034800300410520b01c2010311a060380f5802c1c040180250440400314170030100a03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774791537 1250 774790287 774790307
    0xc0f0501090f08030402010818190618060e0d0c0b0f06030a061b02061b1c0f090317070513030803060f0a0602011a030d021e010b1c110a080706 63
    0x400000900900719114a10596040301d0304a5695000200300011543d10041840e04010751600054400c40080b032040c0d02d601440d02c400e000341041180800078401c40da0081100801189140c500040447c10900080c186040c01034881e80300320b1005601c01e61003260520922500310480c2e0307082e5100d40e8a040c1d20101c000c0c2415a02d0700c641c17411140800c40c3c510441d424a413418181e0740b4506d810450180c1004002000c0300550001d1003203440c0020564811501103203510000415080c1c400d031201c20042c540640210051450301c2803080c10160814a0740c107940c201e0304005600b554410300201c40601c034802e8281c130380f1b5822120030000a1406409180c002c070340204000c84005004000c5026414507500600c01030b07460300c0d01c0c0002580408014940c0354000c1d0302a21843c849514040c2d0b0350b401c4c0807643c008043c1854507240342090203601041c4507440003009102e0169003040e041406c00b12802e02598020f180002185c01803038548100b10842c0c1104010f40500343c540303001501d5245030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774792787 1250 774791537 774791543
    0x303030c0f210103140c0112021e0d050f13020303070212030d0e070918020307051504121101080a0b0d0209130c0b04150f0804081605030a0306080c100c0f 68
    0xc14040180c500c5900b0b101c0030940304000600700115850342c1807030b0b10700d000c244140000d144c100a00840150341e020800c0e500303210290b01e02683d0340c0142e0050b62039034003040030036407214500420400510300c07883e00554003038000a401035995803110a500c007400089001c00a5050b4400c024200041c2850504010902d030b59805403424801c403d0038060940d16943c0091140c2e4005850502001500c1d1003000181d00c902111583e8400b0540c7c04280d4071344c1d10340541842441a035071082d044155800846000e8643c10b580a60b0b444880c0ca4100303402d8114080f658040351450b07000541400b000d116100500030020f00c590a90280341d024802003400181407180ca03200d0500c1c0c00b801290385000c40310001c00246a44a550310300d0f14480c00203180000d14550108040d110140714415480001c4507041904081c52695411a100b580041240c078a2401007030b500011450000c0b40350903a00040451352103030141d6403001103032000c1000701290188044003180304440010b01040101e8817078051984 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774794037 1250 774792787 774792817
    0x1c020d210b040f060302011e0903300509030736060f08100b06090307090b030a20120105270a0b27070b07350918060303030c 55
    0x2110202d000e40300302044081d01c00d03032284020000c40d40c1c05406c1c1d1400000311061101003654510005104680500c4003800040c4042d51000c00710038100c80b9030a100411410070340c0901600c2e03001030401e400948450f8800c5c0184c1000050040b20b0398049041882418448510716130307015850000242400d001d824500e035599008648025202c400c80c02600140c00140130b41e00e0078805100c1910038081100c0d01644003400001ca55440010360f1400b96031200c80042210a4030a020901d40045260050f02c50070300452821003003242c0c40e045002c944026124800e02c8080300440b1800d81c1c8081d0303201c1002c644000712041e441c014414543c0d12040c541c03c00c1e646082d404d600d4404292900b03480760601d4049429401004038681e40100e50420345070300c090308440c0c0c600105c09003a8041c40788003901e0380d02e0b03081c04905180981034503044032040001007440030034902404a070380ca400c840300f458000ca1070b035900c0c00d010510404106100d0300000b4021403a503034440f1582c225681021450303554180c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774795287 1250 774794037 774794051
    0x7030306030804080f0609010207121d04050a0203060102010b01030902062b050f0105032401030f080909090106090f050411060c0a050106090f110c06060103051e01081c020d21 77
    0x1c04000041c4000d00303800f00182a0b0303145c00b42c00581402000b50080d805ca0707104020703c1000640c910040281c442d190b00f048000b034090480f02054400c4003c50095101d840d050400001070100e602071030080d0000e030b000f00312403d0040c00560880c0ca0001c4040d500c410300344020180102c5040340c010300c08204078555013842c0340302034005040c1e07442929062680079810b8014405800c08102c61290503841c52039001041c004001041e03a607a2042c0006401158580c480809000458088615540c0050035040c0c0c140783c0480e09074001c02d807901400d1610b0b030400000281c481c1e484e000f42e5009680011150000401d644200082a4401014030405014210900e0007141d002c2c411340b0014118210b0210f50b013550b40c0a00070807940c103103a45401c008010700c4203140035a0000399081e80000e003800d0008440c0c50f541001413041c580030340107684040c5c0d850000b248220000ca001503d6031a90a00b20340386030058503082e600c0340c10849910001400e90034441203031200f54500200703400b01001e0001115 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774796537 1250 774795287 774795293
    0xe0312010e0f010b1b01020d061a040303090618031406060a050d080909040302010b09091c050403030e1221120603010507080a0504061803020c150c0703020f180403090e09010605060a050703030603 86
    0x190b04828507281d188d42da120000c215510032114000c60040d0a01c8005e40350505582d4060100307141401407008105040880540c0000c4010108001c0c6030040d000c190140a44540c45960740c204480301e60080308008000540380c14415100280994020245810105140b0511100c2d103001003095007190f40742c1880c02c09076200c5000190040c500751016000c1c07902c0305040d90301005042011041080402c12080000c2984090400d240d0f080450300d001a5611540e002e13450310010214006942c111901c0c1c1184880c02c3e4402043c00542040a0140d9035640c0c004040c22a0411034001010070303c4040091107030721171548403d034814858400042d040c0381c60072884000345c004650880259016040003010b502c1c0160401032202213010043c1c0c40c0c20080300310240c54801c00d11001380901840c07513203200c955443c4001c05410044445031258103140c10b040003840c45103a44140c0046400500200c0c40716641802190241d07407002d002140381c05c41c80081101c595200034419010940e4447c404000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774797787 1250 774796537 774796541
    0xd0213050405130b0601050f0a08190606050c070b0403020906090a091502090906030d0e0112060306180210050f1b0309030f0f0f06060904021908010e0312010e0f010b1b01 75
    0x51003480400c1d01041440d207413011500c03401030000d80c14020240040422490990304888904402d8684041d864444c5000c9500506904030070b2404a400c204004c568980c1c00000f4000224080084500c041d548161501d045c5c440c600010750040e0b0403800103003250419120403a00807801180004004450380c803405030030300d04640040040c80d00002c5030340c0940307004119640c0110089004e480d0110195034080c1180308469003241c10322181c185960b10328641680101300868000e84144000f055400502c214038003881000c038801ca00500480140a02c00c10985115000180b030403440d00d088005c08040e413041602c0700342d6241c8400c018000c1c46072401e00c9002c001c40030328001070900b143c40c400daa0b4200006003401800c01e0340724000700002c1e0f64454194540164059807881141070f10313a00100a0000c01b50080141c96080c052040400c51002000f00360010b4240d0410a081c1d0f01c81c0c1d016102c3d000c040d0b07891b6a96881050042c000350f800c0c80f0041109510080401301030308070a00000d03003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774799037 1250 774797787 774797791
    0x8030702160f030317240d1e02151207080414150609010b0c03072a0e0402100908100b030c0316080606101403060a0f03060207050d0f050d0213050405 66
    0x201c1000d42c410000c150300305044114442e074008400e00705182451400e00071040b00110040c05004001c0c804100391a003a510503422034100589084050003994140b44080e41c015040340034034040400380c8040301c81d00003a0348440302c02151406054a0310031048841c8080504251203c40d541ca242c540c05840c2080301b10500100c200c2451a2483c141c0d0800034841b07070507404040d001504001060f0b99410100840710b000b50300640040130030212060b40070350303440c0d00800400110b41d9200e011030343c21001034801d4441c41c402c48006c0507005000804880004c2a84030303a0103036900c2101c04280c52602030f009103c2108019045411074480b000000e4900021060700790f820840d030240611007010700303101c0aa4094000c0d20034502c164444030700203107200c07641d6580c590001000303c0420741581d07825203003c00400c201203000010f6605c07418140003d5104040803101840b42c42c00348040c1c0c9006e180c80f10407111080e243c00b0708041c09030003100b01039070200b9008011210746c0840804c00d9622449614 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774800287 1250 774799037 774799049
    0x912050105100b04141504050a0605030414011b210513140d05070212030c0726120306011d060c34030f030309140c010912020d0803070216 61
    0x328a500305406030800025203a000080f07103e02c00c2000348228051002d074070000540c281c603514203141244000e440d80303001e103400c105d500100910300010764550000107036020f80c0c083c60f844200b000b04a21307160f00f25200b0207100304030841a4061180e030f0750300030f00c1d00e400040d0740005140b6640c442c03200760f24115a0115040d81c3d900c1c1e00240582c0030b000411021900401c40c4000a2081407041840a82280500000240704105900c0c6000031544144256804506160103c40034142c81ea8050f807001c1c0101200c02d4262414180c201302c169400007036288508801c60f070b02c41e285803074400044a0810b10b9104040044d03c1004000c2a981c82c0c5000501c0b580b5040000b0704900c0580907031380500e94580000882d04242544c2989070b10049201d01c06044960102c1a070481e4040351600b1b030081c0c81c5805024012100046c11001400300101d5443d0b80402e00342ea4000c00d16071503902041540c400d0b654065081400950f080c80003482100003180c0001e40d030f00448001a1300048013586206940d0011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774801537 1250 774800287 774800291
    0x40816120f020c03010608150403020313031104050901050709051c02181f0b03010b09150a090f0504060308161a1009060e040f02010c06060b0409060f09020c070e0709120501 76
    0x748440503030621041844803412402401444d00e4815026030307900c20070841011260b03405020800b050300800403200601c0780700d02a0780d0810358a0030054003122403449414000c6080c4000240e4098062041d2031044204e03494420005051200b4088421003130740d11201c0b04020560301d480035a650407800050703c10141066080b5251242e85480f6520354060404522070003900f040c8807105130746040d241515081091161140540400600000341d160081d8045400004050060030362101070351042d02c01d1303c1890780100f952401070104880e800e00c4046c10742d0b44144136841c214500e500408aa040c041c008015200089404524002c135090b0384610503004060020000000540560802440d1003844001e407481d1584641641030075201000703041284112480701040400c1d03010001500c00100b459803942c0d1240a4032008020500a4030700441035401c0015114031035008640403503100350007401c1b086152031440b071b01d600b4025000b0800d1084400c808294102078865600c2554052000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774802787 1250 774801537 774801557
    0xb040c1806091401080604120c0803010803090f0108061012021306020604300c0302070f0906090531080904020f180a0503120c0c0d03030b1801030b04081612 69
    0x2154003250300d0ba00c0e503c0c01030203090b401041521400b0800c942e105800806419501c000c0c044102c07065003032500002e11451010002048404002014203100070054035403030b40810b070000040d02e150500312040740d400f5030f002021980c803910031400402c410b0b00c0840e0140c1011041200c0905003615a081480180d000c8010801030064011104004203d400c102980710010561208002c01e041c1d0079080911440e560742200f00341c82080028010100d07102c0352607410b40c4500303400014041600c2a800406e04003800304000550b0b012000144590b4009413080e01c07060795034080b035200540345c400e81e8011070510000f42c00c0c0d21140024503481401380070265540d80300981480c52262001d404a0103a014044180010348001502e603e0303806204e07582035147c100300d444203490190150200307500130301c0c00142d2108058140c2c0020105075812226500e900356200345c54100071900f480068000c040650104001c00c6861000b0b28070a4802d0450a070080096211038540000c1a541c900005003000c01e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774804037 1250 774802787 774802799
    0x24110315031507021f06030f0305090102151f081b1c05070315180b06011b0206040e070f0f0f12060512061602121b03040806010603060801060914040b040c1806 70
    0x140100c1d41540d180406c6001c1c00c58035101c1101c28481c02c0181404000910b00000340c0c00ac0220140203038881d880300429240100c44840200c2c1d866282e141c094023480c201080e000e0012505402c2e041442c00000718801c011800c101480c440310000501000c0c501c0c10386404a40d0600040000d140160090361103003603440040c030100c4034010002c042400c1500e16440000c2c090b418001d800c80c001b40b80c189185004907402000015680030000c0d800140010b00284e036044c01e483e5580305001548980d1030a43c103501090318986910741c008400642d40203841302205004800c004840300c00792000081c810307180c00104c0d10120807100c142c8810b40c418010018800d14800000c08200c03610301c003402880301e90034807540f01406071181c1c01000d07410720308503019194400c00030f44008003082c00880340c681d6952000900109064054091554241030011079180c1d054040c05100718843c05100c0c2495886446021244002030300403201da00391000009001920307100c01000da444035080004d1507520b001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774805287 1250 774804037 774804073
    0x50706020c010e180406090809060d05060906030f06010b0c0c0d05030903010e010b13090203010b1807020d0c0321060305100c02250605030a020c03072411031503150702 74
    0x180a403845181c004c1e004e1002d91a008200da078120707900081c04100d035009840c0015282c007800d40304981003c40441c54501e03c0e0865009503001d03000070b45881c0030b20744602043c152181c0581c0304d402055030203c0010030103000c0342c1b00100351540c0c204c0e00791030b11300d60007500040c0514018039047da501e0380080303142c1d0b0113460207100d012140b180341c00081081600baa80446c0400e00c0b4001c00c400d985035140800d000390b407000e412200740c441c0e004000e20b00200d0603c0b9080f0203032009481030401446049c036804c240f6170240740350010445e01500c40314400c84040e540f440b40b0040d891f0b42c0c542e9135500d031803002001136410004811900c0404502007000116403100a14000031400070206000a148a01201c40d1a4569060030ba501514159079070341e842000c850080d200340c0c062100c0c144000035280d001c0c050070031344d43e0720400950300c800c8682510f4a5504000d40380c400e10600a1a001000891701d9401e10700d1071903101c204041c00303503403203094180000d070101003003290050050f0300840082e0000c00c00032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774806537 1250 774805287 774805307
    0x12051003150506010207090f0209090403171b0d0203060f0904061a060313060b0d0f3207172505090106051306140d0510060806030d14070f050706020c01 67
    0x501c030200028940a00000d640301c0d03c511030054000c2d514032104603400c40c6c54040b0744000384040c00c400da8a04040c500100080015800750445403c1c0501180d42c0154003107039140104104140d4a00b00201407146100951000e401e0a6200d1581074102905441c0c1d21962803140d0301500d000618490301c0b18004d2400c205039100076114100410800109511000010700c0a030740180700020742e03007010740c0403404410316468003410440480305040308200c460040103902e80341020900d003510302d2003003000501121460005041d5003245805100ca00c103a01d40b6100b160004070100d9003407031411481c145030b040d507588440e081816050824080f50401440490042440c1c1c5001450120504008080d00c4218041c0504021054540c1d25407400d00a064600e80012040104803a0420300c00240d540600382c801c0501044041d400109a0718011401e603020010b247ca580342c900110b0010400d8030740c0420000c0322080d4400040402242c010084100038141c107030002c128108103880003611031450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774807787 1250 774806537 774806573
    0x30b0c09040c02151f030b0c0f0403080408010f0b0105030411030c150d0b010906080406020d09080d0c02071707052106010602060114100f0e0d1b050a05151912051003 73
    0x700b0000325040c804418001421240c2107c0416650b403a03407800d4100c18403850701c0c003152100011801005000448004208031400d40c00200300d25032402408805440004201d1404600c00b400020041000e07401245480781000b41a11024164200001c00030304417454154501d04010500d040c900d0f009100e080000303c1d090030982540c0b40b900b5002841c044004100500ca1900400c11a111580a03000036030000c0c0c1c4056155261201744214000412102008000611891500203419140144204201c41c00c2c0d001920145003020140b00b120b04084008100510f174040080745140000e10040e80a42102e60141215502d0b011503400360310034010b41c030b078400c44848a81030f00b4150050f40000b2140b01e2403c2050340d000c21200000c84588182c1400b8250714560742101ca07000c05410310240030b42c1c0048410290580d15601841940380c41c0074050a41140f042103585117810f06130340841c002c0c0c41c00d40740c040a4140740c0348182060b10003d6071001c8113051400030900400c12112508514890 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774809037 1250 774807787 774807811
    0xd0218060309120c0a0c1215110405040b01140f0406021507090603090f06110415020304080c0103050624030103021c0302070b090d1e021206040c030b0c09040c0215 72
    0x5001c0ba5541e107646002c41c400c040520300040c82d0403036200c2072202e24021608007404084c4d1690340c010880108149150464480c100c810280039062901c0c458480c44a03a000c82103030070b2900740030a20001b03150940103141800180e42e000d51515013441d009003a040401221640c440d4901240641741500400424081c00300001c208140641e00c00d42c0e01b42100c2844c07a012a03849aa8241404141e01d640c41c0900864104050b140c641c0b44180c004001721842c200880000c0020341c5012078580c084c03030254801580000c950b2801039031083c1c00c080d4000c103006210b07284882000201c540f9400c034055001c000da48003c4010819480c1a00c003504030000c40f2880c00665141d5543d0003034607054a4045d2030856039010802e0f0a180d100c1c140c4495049600c80341c00e40440c101560000c0403480521401c92003000c020800b02c0e550306000c00c007180a2640003a1b0208170504590b5100c01d02c00005003031900104061204000d284d030b07140100c606600c0250041e0140580c010b0890803044001464101c8080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774810287 1250 774809037 774809041
    0x20a1403190510030f170405031c020601080f031b07050d0b06011d03030313030e1002011e06150804020d0b010e1506031302041509140a050a1505010c0201030609020d02180603 77
    0x1015681907a50b59540f01d4545000003403502d04200c0c82c0d011f1500401e03014890940c40f81003103c00d02500e8041c801480e0202c036416a030300c03180d5956544d00988000e0080c0c100b4000030500907030440480e0205095482919865900c500114050101003402956800501000c3c000700796081844400d180e902006281d400040d1b038004660b50380f1010742030f4040c850110180c03070185481003140040ca900010805c3c603580e00000b46c0207020307041c8003034211010349081c12012941c00c0107200c1d0108860701c0400100415418403426036200340e0040041ea005080c1880c0310000840380e515050183c001d800e0011410701b0100b0883c10040e4001074a0750180130304006214030016940ca403400250b60480d004200e440c16003c0c0030111003115030010207800e0070b190780000303013a81038a0241d2040000300c10030421590345003004c4059419180044030310f0301e0a806d0074491944900103010016006040104842d603440507120120781c845038192051580c041607a4040074110500c1d00e4400e0300484040d0300314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774811537 1250 774810287 774810293
    0xd18050d1e0f0927060b04140d03081f0305070902041814131407061106090109112808030912060c0a2111030f090f0d03020a140319051003 61
    0x461441c06032481500388103200c0e5400c248512400143e840c0d90090174090195542040301c0036401a018010310241109000f038090705154040c0106c01d9050b58880110b910342419078048040140a26214079605aa007c404513004010450003002e044400586d0340f0300c2d048051040505001c00f450b801c2d420554035440003504500241d40110340d600400702280c8a034540341400120542d10700394107000380003001401c241c04c400261000c00751b41c030540705603070303a40c244440c00c9510840e1b008094019000354440c0c0790030101901b0090090100107000003083c0320300325820040e00703a80000d51079480000c0e62411401c1403010002e40c408900000c0030030703041003000b00d031a6001e401207200412120542103002010400816006900d5020b801c20044001c1503410004d80c0c821903841c81c6010319407006c0f07800c4200019034058940502000341c03441e4002c54004034041c1d4403a00d843c20030401481c038980b0501c0f102400660103043c04450603030000004000340400c0e03c0d40100112008140c8003001c0003c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774812787 1250 774811537 774811547
    0x20a050a09082b051605100c170703020a120203092808030c16080c010c030b0d03020303070e0109050319021003050f0408070501020d140f100b0d18050d1e0f 69
    0x2890f241800d080d141d050300c04104644030f00640303042801e100310035074142c4180b1002080d02074154540b588240700507802c0d910255424050740c01004000c0040780009580c0e41d129034007820046415182040740e030140e02001c40203a0300140c078001074039000100c036103000342004540581d031840883c40403000400ca5484040c82400014200440c0300300001f11001035500c491481c41e01c0b50740c00000b41e501d4860036030106000f86682c03190440403d03d0f1006041680c0307040c020380000e01d9810380c011403842c0c1d15008102d4a01c803080040038103002c4e40700c102003070320303076051150742c2c0011012582a07404c0700d040c1c0104a0440084000b91051510344014890b80401d440c40d030580c05500a0701803a030701c4482d07240550081c410a600d00c2106840c4c00c1c40b06003c410f0290300907004100c0a100b41000d0740b90706192000d084103e110f6900d40325010850300c0c282480359049268180d003098031044400442d6203903182031808041e5554001207900b1540c050b43e01c0118070fa01208403c9140640c205a005140644 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774814037 1250 774812787 774812833
    0x30f0212041b242105010b03100f1203030f0b04020f070b0a0207020108070807020f011401060e0405190e010f0903180602010501050a0902030a0b030a030e01090519140a0306020a050a0908 82
    0x402074401600c500041d13140d00c203001c80c0340f41d10303c0403c4603607944d05100d03606400588800035502c201c1100003590580c44040c00081d0b40892460401c5203203540d8060340280300701500c1d07008094403600007c08030340d070b02d10103440c4102c45030136030680e600402d191030041c03110020309207070076907105204600160340e0004105522015500f4488015250110705903d071000785001d0350115800c0440031448245070400503412910780381c4a0b101411418420441941c0e422505c8c2e004414804051105000f45900205801d01c0c400c0c000041520360810700c21300741c50311050243c021406d079080426041c0c200d0110303400140550303c000c22055040000103071601040744110582160003101280c82c160305a4042610b2030340c01000c8840411391458044d1880c1c4800d000039020540200c030000d11801c00702c90500c0b0003180d81303e0f010546401c00500415000c2200403250f040900700c44048001902c42c8001d0034401d9a688805441d281011001054980d003134000d105207410046001d80d02135019003802d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774815287 1250 774814037 774814109
    0x6012a030807020f0307060b01090503150705030c090406140a0e040302150402040612050f121e070609050a0609150903050d0506041127060403050706030f0212041b 72
    0x10807540c9521a040785440c1034100080b1444c040021690b04004c61035000181400080e01d41140701c03944c981c200f5032100388449040c0340002090740004e08962291009580c840040d44d191400d1142c92808101182d1094010043c030b105e000080072014980003da0000403d0701d9030364148585400e981c000e40319001c59054048894001d00820115a5070345c2142e03000e040e0b4800c1303204010f002e03820510354503500d500145400c0c1c0034540300e400e84088000e0845060070801c880c503042444230104400c42a0b40220780070740e0307440d50b94008000000c105000411155000b0344000c1006161070404013031b00c0024192000d1002c0c80c2c03207404000603070004140c980440304160005203aa446501080242102e0040122400400101c484030401d000c03003582030990380c45808640d506411414880c2900c154000500258411a4100308061103900308403412071201c400581008003c044c017032107401c42a035086071548002e60883c1464001d594804005181c1003201c01a00c03141c038a00d0056003a03014600e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774816537 1250 774815287 774815297
    0x91005090f0405040b06090709060c0311030d150f12200f0a06020307050c0307050f06030702030d0204090c02100c0509040b03070515091207180f0f0608010506012a03 73
    0x20a991241070302405941c0c082c0050100703241901d81000214000c4900ca840340701d4841c0481c9085100d00c02c194252082c58648022040c0c07951030a582104103100c200300755100400413203078240c48a0182c2000602d0b902c2c4440c6035641480201482090b83da00054610302c824084034010540f2070b043e91060b4070b00c6040c0710f0202215030001c20301e151200b03a08030f03400c00303054440090451750000081c0b62050040003660001e4400030101a103801c0300e882021340c04040f4035000e2a045c82d00000454203d030203130042300d01c0c001c1c2c008000c0e02a0b07081a400034103083c1e601c448101000307805002e03140403001a00010084040144d034003074698020b40410318011a0b41d14900801c41c1c4082203000041c0c0350091010f42c06d5041c2b075121162980c0034800103401003406808501c241800050341405566285100012542c2040d02650007810183c0007480410780b5121078210305030a601c101c001419605001052610781440050621100d008401108000c03c00c1d0b8101c11406117524010002e07454946 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774817787 1250 774816537 774816547
    0x112020a09050d21021f06050d060c02031e04230108011415040b0417030a1b02150a030f0501050303090a12031404140108181b28080105010b091005 65
    0x4411340d0121030030351101900e0700c1a03441c0d115045d0005841c5103004640740001c8907108089030043d003550203078454103400c1a6512005d800103081500101101d500f00d104a904000e1441c00c42185080c3c944400e0b0810140018240200d4910a90600c804100007010b446070b00f0041c0c0c0001c10f1654144615501e0100014620000390348240c1500100542d90841540311034403a0092203842e071192248604042c00031546a40a07040841a280035002d140c035072400c941d600e900d035807a401c45c8464040740d1201c04001c02520401c404c801404c08030b0701070380d800508181d41c0d02c0d02908556042c1c1281b80b096106200a9500399034202c140380c181d840300308890030074061920382500e02240864840510031000704010070103603454001030407904000d82e10341c040341d118003030003020214101744000e895800031440c541c16043c01013854000102c018010200b0b624090b054020410402a42c00812810043c030170403660809009141c0034107044004c40745400001c8000403994149416003400b800000300e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774819037 1250 774817787 774817793
    0x41b0809071703040f0906081e150103291302060c030c03040612050105010504030305192c040e0c031c020f0a060e1504080d090602070f0507050112020a09050d 70
    0x10001801c031004200001000b191515072640c101d401401c09010700c2c0c0f680021600741e680601c00842d1400070151842d80c020b5081449c8412912410350498883c0e0450710b074014410104050003940290030206054084c85a29000c00d400e00359908104103148042c0030319a804000c050140550480c0c1076035a035148880e1103400d41c024103074400340a000c003080000340ca5400a01010580280700c008214a80c0c0320001034074a40114080600011002d002103403002c00490254055074080d410a000620300030804620b0380e00700c0307504280e4144440403005600d800c040c001c4400000b0448060180903c1200100780d4131440c4c0d03000c1207280b40d0924046c481880c000d010128001407903505694051086d0b00302040a4008840000400c0c803a80140825006103e02164066580030201524040021b14444003078000c0e0101510381c1c0d0360070001c0100042e0381c04000e0b08080d1281000c0c00c1401d19003c0003518940c00510198082801004003681d0103900210132016101c048a00a2403000142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 774820143 1106 774819037 774819043
    0x17030306040902011b060e010606020c13020306011e02060126332409040309030b0421020715020f03160f021806030c041b0809 56
    0x4004036015180030380000318041e0052521000498513482401900040e00c0f030200c60107a40e403003403000f0750700f420b000341c1c00201110300160941813140300110380600d40c00f502d080c401c15030000014040340e0045d80c020b2803a0a01302003000c0c0120208501950f02c150a01848180d0601581080c0da0080b988800c60310b0300c00414050644401e41468010007100004c2403100d1180078100180d600302c8a00718903a214131f0660304100b440d40407400c2c214113442040414030f030207154401c0401000c0b0f90848000c00407254040b11000403070f42c503030030250584100010f01828080d03001558030380f40e66000409400303948441c44002c4000710350b0501aa078a202c070040d45111a00305121120030440c5000444c01024022003200081b902c0a40c0000c3d4124802030f0901d201c102904240101403c0c10885103810700d03c19141007020507040f0111072907600c140d0b42c09000704400000000c600705014 = true := by decide +kernel

theorem cover : BRFrame.Cov 774640287 774820143 := by
  have h0 := BRFrame.cov_init 774640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 774640287 ≤ n) (h2 : n < 774820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
