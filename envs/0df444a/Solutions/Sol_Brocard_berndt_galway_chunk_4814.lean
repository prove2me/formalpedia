-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4814
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:49:08.221591+00:00
-- url     : https://prove2.me/submissions/5b4145f4-95c8-4951-b03c-d277eca84ff7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 865647482 ≤ n < 865827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 865648732 1250 865647482 865647493
    0x806090d05130911090d051f0b030c0909010e07031202010b060a080a050c041e051804240207021c150612022404120b1303080a0f1b0e04060503 63
    0xc0b500740c090242c41c2a948040d400080705002104001181e202e540c207441c0d440420b44082c002003080c0014010110302500f1a081c030101070b01a1200161a00303441040e40c190000c40b00d0100c282069265594041085800851203009009450b8140005608180d42902021903c07914072074090088100c000c0c010b90f0310074600170149500070700c1c0707400141002c9440c0391182c003c03030444241c1c030007a5009800100791032138040c01000c0701007004480c00c0c031a240c000d02461003680c1c11507410300c0340ca522480d044514042c07003082040d5140907020032070019031800c9909002e4080075840c1d09005401c40d0b045031090440d11075080c14520b01c441e42d40404940c40900b400820300c00b2500d4051030a1120742c1c19a940461181280c0d200d0120150403000404041c80c08580043c64511101d00b0f0403041d0f00134030b448140c50f00c0c1c003860018103844109001c0d010035242d0700810710303000ea42c0c3d01c41d88007a14200340028829130084404510222140a00d030001119220113080d14982407161000400f011001000b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 865649982 1250 865648732 865648747
    0x906010305061506090f0d08031f0806061c0c4101020c0d0804030602160312140f0c070c060504090609020c060402010507020a0b0d021e030906011404150806090d05 72
    0x103044c0c0c070842812500030038402000c0c405a4460201c0720b00e031107901c00145034980c640491130040035604108401100d118602c6c0c0021041000710351180912009000c807010f4905903003080c2c564407035003502150b00080c42600001c5030082050f101042003c4194010700b5403910301c15080c1d851510700c040145006200c01c0d00c0f01541e0b00080c0c100303c082c0007990341215604060800701c2c40e600a035030001d01002c1c00040c3c0808034111503802515442d11030f4071946083c0305240d2004040701e03155003442c03120103078000c08207140e058491452680107240100d02494003090795640b50548d015603003c60085030740841c06008014813401110003401c01030360211b041c544d40d12401e43d90748a000c1c0000c0d05120000170100c3c2035440c0c0031171718005405844040342d519201400c404000f9400840ca5110a81c0802440c20100b036502d41200d00440d01c050062070301e030b4205922203004070006100da80e0300c40e56072507022091000c2d81e0744410050031100090071580c6041c0e01c52a06000452007041d0406c0020021341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 865651232 1250 865649982 865649989
    0x20109150c030b06070f17130e06270f0a0b0402030a020a0216030c0b070c050310090618031d010e0307030506150f030a14190b040507170318040f14040201090e01060f18050909060103050615 83
    0x14cd4841c410340c1c802c1d012503d403115180300401b0b0f0318001c1f076000350001003000205100c0d5002491098000d034215901014280e420f80030714603081c0801401c1c403040c40c074200b04042d180c1020f080300f18040c07541c00c28600d6444000030b2030b1401013030142c0003850305d0310b07071880602010b031088141802150720000e0b500111940e0042085500004410401401e40181d52043e481b801d0007120000c400b5044801140e2a4148140c0d80e1004503032541801d65602148416400c01c0d0101464029010380188014540b55030f51410f109108401050188151100c05042d0b51840071031545440c000c0c203001d1a01d00300341c01e0041c00c1001c1d6811104920810114620981100004840c00300c101c1d01d01c01c400301b440e0300c0b0009000e0300e54030280001090801214068040030b5441150040d03100340c03a410b00660b5600f4145800c0e0000b4840e55000c1005682c40900d618016140c510b070380b0000840910f403032500c8000098200e02e06541d0440258050001801003050400c8550707006980c10080c0d100d11000a00007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 865652482 1250 865651232 865651309
    0xd0e152406090112020705071d2e05010e0f090a1505090603031210090603150b010e030d030c050c060411120a020901030201050a020109150c030b06070f17130e06 71
    0x80c13202d441d40011030a05001c4180180b00c050304414480384100d48a0720010002c2e604180c4104032102c0891030708a01d8804034580d0000c08550503a00700c1d424514107030054940041800342d80341c01201103c0000c1865888205c60f41c030640c0c2d81c0c0c000041d40c03450010002407402854001c180244800000d20405036400400e6541c2d000070409110b000d90340b54215030400e40800d038804090141003410200c100f0800c1e050740b031246119407404000051a12004441400d50380c02c000e5015084550001d1905101c1d800400280c0601e0400d5498207000c68142442c18a003100d023551040da0014400c201c5151403211886101d032540c0050501c0403050300010402441032000034180440000c240050900070b400800c2140d07048404844080d41c54030b800805000700d0500c3c4030004c1d2412a48021902d014400e23100c0440c3c000c0d414800c540920765030303101810302144813214032500c00d0100c41c86181003006d0290103810800e039042c2060520b0301c1030241000c42030790040080c89055880faa51654070002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 865653732 1250 865652482 865652507
    0x40f09110403060510081501140616060b03070f09060501090e100b090f0603070c0b090a08030a0b01091827031715281a0d0e1524060901 60
    0x400061315103a880c0a40c1480405a00c00b40141c0140e00700c103ca03003444c07c501d1504030303441d1912000a12104504021042c42400d02d040e07064034402c03040b0b40c00700700303581c1c4042d007080d01c0901105c980d103855070715103004c400700c507886000c040d82c640d0000e00a55074880304800c014103415400f00100d04000304403003074420b028001da0110300030114a080080d41c034000d0484030b2980191200b5620f0034082c00042000d465454250b40d04010714001c5048810001450750345c450308142c015040d80c4510390300402070800c01d4169070401c6144200450300110180d00c0c2400f090041e203001541c015842154000340220a0140c402d0601840302c0c040440c0d00480c442845a03d6441c00c00000c1d520b814100c22a0b141d0186085d40080c000800b00c072024071100c544a0340d19180e041d6580074250345011900000792814145035074440284143d81c2480078a0300a40e001e15108070a1b540c007401070203001343e020317401110020880c08048540c0c000608885a80840c4200d00303079012031030030001c45c00280c0a940d0400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 865654982 1250 865653732 865653743
    0x40f140105040e150306010608070909110c0706090801050a060b030c0d1d070806090303040f08030c1213020f01080c03180a080703051c0902010c032111040f09110403 73
    0x215115078421030460b0041c012003401030b041802e14020220f410310070b10407428042c0c82400004540d0760300560f030707062040300c081d079a480d00682400e0340703000030b800e450040000303400080c030418040c1e000910490300076101c1070395400200c40c50441840d003510300103070520b64140c0c9880403d000b81c8250408890b0302c00000304000e95030360300500713181c0020f08843e918503a00b0840c0c400c11104c50103010800104940e1540d045416a03210303200441e031248800d4a0041000c541402c101c00000c0490002c0c650101781d000d401e0b420030710601c03000000076008481c2c1c1ca090035a1088008110b1420078100c0207082c000b0700c0c0108007032504070588006840b010f49121480702c0e00d8950500c08103400c00c26090030507403100a25445510514020701140c12080361060660000140820042c8031449210403582e0142c0d519122500304e510165520280803100c10612072507014083c10711955401003403901c24010400a544620300301000f5107000c001d812091742070341050803002050642c0780581e030540b904107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 865656232 1250 865654982 865655009
    0x906070e0117090a0501060b03070e0a0b0a030b060f04120b0a050702100b0607020d12030e15010506070819170a060e010b0c01061e030606051008150102070b0708030a060803040f 78
    0x4401c3c90720700120440e00400d00d40c2040f80c0810207201d40005140203540a40364002900000130410412012034025040700d44c1c0280100031602d4829000503a4100c000f80125181a0306405481190ba00c10b8002083e00002c45030b20604004182d05025442102d07020104030500380386000135210084950035200040e1540c1f41e200c525601c00040715820740d4010a02c2c010502c10f45001810510030601000229181081941c0403603004110a030341d41e807a0501e000070b941c2c02c03c01003004d20f40003c2c0c0160b8008900740000001d20700301c1030022040c50f580c2d4640034042c042a00841c00300400c010301800c040c032f007400c9080201009004a06066440f1489140d4807110002c0076a0b0040c0696804001d00e8400341d10181203101510801c02c041e41d00850061044d07503201d0040c841521200c0b0400ca00142300f040c0080e2524103207003000d081c01c0d81c2c144152a2181e0341c0b0b6011040399007000a081d195000300005008a084441c40341c400104424409075092600e00480c2321045107140c4144a03d69016 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 865657482 1250 865656232 865656241
    0x71a1509040212121b0d0e0a060f090f0b18040b0d170d05190c030207020f010c0218090c01030509010501030314180301050408071103210f07060c080906070e0117 71
    0x28460041035820010944e91100704040e0000b0341c03843d0059003003032140144100300007100d02c95220b2640510000e8080350510345000c0085509046071500d0104104041c0e00206a41400321107a01c02881c5030712a030740c0ca520074200107402650b00c04911504c56454000c06510a849801d00417107016000801c0c8400154598003c0c0d22901c030b442c4503401c0c035030310700410406e104c1040305201c006418039050400404d1042002941284201080a0350004508a0121243d0b21520000d401c59101500e070805a107540304460411840c07d071a190382c0e5401080310701a1320350b8940701e101c0d4400c0b1110700a0102c1d5140d610064a90b00a54690324a071050002e9010b00042c0946589410310501800800141c9032078100101190413610044500d034210000340903a81c50001241070100b210400900f4000d510f41c200b4082c2a4440c11403942d98003000c0c040d0401164542c41140840c1c0e20b00d8980401034504030038120b0400b0801891741d41840201c600328440c603640000c00c5124480c03200800e0700107858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 865658732 1250 865657482 865657519
    0xa05070e032a040c111c05040e09010b092e1401050f0c15100b0a08070e0102010603200a0501051204030e1807020d0219052a06071a15090402 62
    0x86110b22a410030f04000c1c0701154a54840581d0f803030202c0304c900f81d0b004462102d02280b1700780d0b04102a00000f0b9414401400354403420800b10390019101000012030311b41c01004a043c000381103941100540c14400c1c241d088040804803005081381807840402c8190818130f4020b251010346403003034100800405c2c3c1c00c0611803c1c0703007103540c641900d204544010700202c19083c0406801c440910307600403400d03000542011040c040d50041d034020303141c00005603100502140e10b5441c0156150441d920782c0380000118100c0d001248149060040b00d142c0b18003504240b1050400c1640298100701c000c00c1503002079030040b40c0d1107405c29450701d06500080b80f00030000303c40f00040d01100b01031003840070520a035250001111040000c61350203031110030030702851215140b08540000f03820b0380c026500050021406c1c0c030030122006220314500300c0781c15450021840680142c03e04480c00c03003c0003840a032181e8400190344c0d00c209510102542400440040781c0d408038040c20080c0a4000c2298140280d80c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 865659982 1250 865658732 865658803
    0x7060201090206040e10080f07030219060c1103011e020304060b0907050409020d02071401020d0c08010f0504050a0e01020a09061106010b0d0c0207050402180a05090c030118230a05070e03 82
    0x10b40c40101e41c8000340d113085060315089c00d072000301d100d0300c90010107140110341098068100e840680741c04000c5c5807070791141c03441b81c110440c0c4964155a60190075140e03032480348041031800d4a043c1d0041c1c8074034007441c00104072241820385034803c1e030944040140306c503800000c0b1800d0b40c1c0e00e1400540c540c40c0c1e1101100c040c0c041da80c2c005200f003101c071010000101c3d056000d0414030201c45014048014a80c00070359140000b0300a104c03604607a000c0900150805800050304017415041c0024145c0b07094102500726007046121000080301080c040102a0b44205004c0d0910f1005010381095454141103201c0c80c420a0940441f01391101030f040c690720700030b000640041c00c019200399500c007500b02800719a4007a003417600b0311400154001040605001725030900caa500d00310107515603400d09405041d000d0405030300045298965842c01149000c2a0141c0c100070042190b0301c080b402d081c01b4140649d10000c0500013000310b40444c041c07240e503001aa107132600f001c9820f041051031854000c880e0b1030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 865661232 1250 865659982 865659989
    0xc0d0b1308120106050d0510061e1e090e2401030903120921031e1d0a0515150f011b0b010308090a0506031509070e1002070807060201090206040e10 65
    0xd9520b0000144940e001360041440000ca2003080040b6a92404014807452942c029407000071401064100c001c0816500c1d101004007608050701d00301000200f03141c1708080f066003a40010302c08038007001004c02250007660094074204103900813100e17024900181c95290550707281056240c0c3c401c80140f6000350441c20000607911020320071803c1601b405140c0340120000100c42c041d0072248210998424410311180c0044a214030020061304c4000b10003030000910303c941110942a221080c0c2c9034200161403c0c00d1240d000381020450303c1d52024200c0f500103082a41c00441d850000c0c81a540b01035443c49014800d09200c180040e05169241c001240c086004011a00740340012060004039006020710500031603024807829201c00a01482d030105550240d0800b860001810051801c8040340c1ea000c40c05203007030001c401c0351a002070b111500b6800701d0300241c1c20150b0180402c61040c080e003400303884180000d2000c02c180380d0108640d403145100e00690303111500c0200c2e624001803c4100000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 865662482 1250 865661232 865661257
    0x8040e090601030c14030c1e0603070e0316051c0c2c060d0312023a0522061503050313080c0118090914070609080c0d0b1308 55
    0x280381405010703541d001d0a00013a034652584c0c030340009244841c00403060100c000a0083e200140340c0d0800c0c4401c4103844a00126520410309641040d42c4803440598410314080d038401c4002186881403500704900c2959003401864010018480ca031510b0064401c2c007950500c0304105070165007406a6000203a80200c02162307011f03004007541045403003e07805188844d6071000c4d296110030003000042d130400350000707001ca880d0301c002001d90103095016094042203da03100700c41d101d0f0741d0b0781142e0b4a45100515070f9254041000c0001040040c0318642e449400183d1701e4104c180d2001e54030041901591000b40704a071140b5644d529104c640c01103a0040d80e01030700710b0791902180c103d105040052800b500955115411640110350300c0f641c04442c80c2100064841038072410440150098800c0c003034192505048000c0075181903e0800040004010607070382c041041e410540b40c0c605024044402a1207800c1011102000c1003c0080203604866854100c28210000349042c46040c055550384211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 865663732 1250 865662482 865662509
    0x81c090b07020c01030e150c0703032c0c0f090a02070309050901090617060c0a57110d0c0305060403030204090606031a0405060f221d190804 62
    0x90458000a005090ba43c098906012001110080c5981e4820100c076621404000300003042600034000018640baa01030301d400b1503070040901a14090102240c0e000d280000854203154202c0340501190707254080444950310000b510800044943d0030140c40c0003030311a800204030b02018051103c8038001c010142a45c5d0181da901c0425800520341442000d41c06000d111982d45a5400403860600c6195103242c1a0300785034900d4411240554051141100500800c158048070001040c644403c144c003142c2c00c40d00300c260f4182c440014200304c1440301310590361025103000524400100c01803820f00340c440b01510b01807402c1c00b0507114500c0e80b01810030b018240510050603450b03001402600d424900600040d90340b58002c44c00c98900103c1c0d060200d09914400c2454a0203070401a000780c8010001c100d4806600006442592081b07038100ba00300b90962020b60b12415405210401d07101c403069200e06d291400b0280d80c544040405108031158198101030400c441c0c00195005048543c0c4040e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 865664982 1250 865663732 865663741
    0xf09120307140604080d09080f0c0d020f010c140a02070e09030415090815060604051804050c06030105060d09020102190620190525081e07081c090b 65
    0x39101d60200300242ca4425854560340480309001682e81e0042e9030054055180c0a9a200d031000104903844044883e03282c204403e1040d5071030000984a8052b0090140108000e013460107480c1650003000625542d06168920044030b403c100d0301802d00ca245001d041c2e0b903079101c54080741042e5603034100444a05220003800f050540000140050302d800ba0307503035034561102c40342c00d1b2410b4505100302c00c4142d01104903030301c210105910064210101170981c505003511807000070016040b0845001010102034100818482e041008140040058400c145194103140c04184c291003503c121503c5540c441c01c0c6075086900c00c0104080088038140400c20040092a21a000c3e011002c495103900c0b1401521010042c0d00f0003c482680ca0aa040c035403840c06c415000b9900c03078001e9442030360010010103500301200b504500e1904150712500200c0e903a04c3d0480e107e00c1d05009c91908004007400c05120720400900c00004440d044640002c00f507010868064911019124510008000715003800500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 865666232 1250 865664982 865665019
    0x2115110408070b2a070b0c010e0105010b07110d05100908030406050603010b1e120708160816060c0f0203070308030a11092803080a021b040c140f09 65
    0x1442554804000d845242d55640c4000b2060300a02d00c003802c0a4040c0c4101488900e80b401c48415440720807020341e183e00d41d031000b40b0281034100c200415200c1c1d45944042d007920310b082c412103000d000c001e420b1601b0000b86865800d2420314108442e8040d000100465090000420414407030518004061142d24618a048105908243c41c12070f106810000482d19034039040c0518170300240080e0030b504040342450010303401c00d004640e189400003149460719144c401c0a10854018102c00d02c02400446c8400200300405c504551103503d503900690100042000c0c1554000116071036403a1444e2081e02c9420301e1030f803d0008000c0254180f240c228004104950a40614452a0881002c000c03008112075450414428659031030340c044400b140c031452004800102003401e06110203501001c035100e545542c1154041c07003d500240c5c0c000098901035901000b1250396042c0c06440a1080810b0b0b99000f400000040c0e500d4402c407000419a050007041c2c190030b07101015001840b044030780c090b00500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 865667482 1250 865666232 865666237
    0x12c1303030f0207020f060d0b1c0c0806040b0f07050f0715060614070b04030c050a051605040903020c04240608041103010203010806041103070306090b09070f211511 73
    0x480c0030a040c20349003000b01d080d51094802664003d402d80054000c03280c1009000c0d401050b110083e0359035814004140e03140c3c9503880d140b20040d044a50308588450415803901c2c4460761000c0c00d6035003d01d080000089480c0d110300d4101d040300d640c3c402c0302d8440c04410344083c01030803004800c1d1500492040244619241007010075000844104005510744004076510f003844c0191400c08042003110708001414042410750150291034611000000340d91642d050a020103c16181030344080051500c030b5030701c451040c1c010001124100f02040c61650043d403a900b0002069124070b40d00c038030f5566013080c8070040a000342d034190b2840300c10350f448082c0503100389029030301520703108071f11001d0203600d060510031039041e18002c10007800c45541d5079a07850b810841c5400c0d56601030248020000001c0c2c110b01400b01600d1155104c400c051134218029454010b1550207030f01011300b010410861194801c00788074507803501c10014081202d00d8200200e5403841a07241c40349152610b00004202001d5201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 865668732 1250 865667482 865667521
    0xc022e110c0405192703050d140108070b07020a0909050d0e030d0f0809101d1c0507120c0b0f0411010c1e06061a090a0b070c12050a050607120c0801080303012c 70
    0x2000710068102109d64a0b0b44240100c00090b0320045043c0f2415240d100602251440144900085034544200e41c2c143d40c0c03d62800c40e07150307211a030304108160300102100b030040f90a600500d141e0b510440010004006104a1002c1c03014002c0401c00c0b040302880403243c0c90405c86030034050f480b4240c06a098510b041d40441225004203400240a1a4200c4040c20354800350340d1003a00b82170311610780881d440072503034080f000c0c0301ca034910f003a0018080c0740d0814414440c10a0307040b520b1034581403c10100751102280fa0403c0051b101071000109420f2402e51000d107100700046810780310345030a5005004c9900200d0041c03180300c00420941c0001720085c000c0c10400d80d4602a10b951f22151000303280075880000300301c1100c1c00424081c102c24001107000f428080c0088590b000016140c0d176081510540d0342d85c001406103028141000042d0140614070f032081d00c2c0c00503d541c588120a9101e00060003000d01010703c0d41c0903100201100b0003421060940c400b000040b50524a00300341ca00080000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 865669982 1250 865668732 865668757
    0x5150603070b070b0a05060d1209090b01030b0d1101140c0105090f2103041e0f02091506120403090e070e0a14010c022e110c040519270305 61
    0xc1e008100140c0c81e209480c40c03180d011a400403180c40c1e4a81440c00340c41d00070000c6030001412011000070541c405a25400d007401034072800a81410080c8940982d00b42d0b18010f8103160800c0484002d03130303c8d48680d8000740d07504090706100540640c00100c40000303400e4401701e07040300049a01c1a01210641c41903000f01c008104507822202840712098940c00b202c40c007030049003020031303140303da90000c08000d5a105101c1c0c0d0b00394080507490000110085003c82c01034a00c0302100b40c1c640b0442c10a018540d801611442030501c111841c5000508640b00e002607900c0b00801c04c3c0d02203010140038400b080090000a002150a40b601c5000186030702140c4107041c0c4a4002904009110321035240b11450708181a59444081c5141340c00388180342e004e50005081a042440081403403200c54402c5031552040784c0d8452803900b00c0c00441070728040001c0c4071030b031250346840300b0b114100800419040350400070040101c0d1100800f0840301d280c00041100d48141c181d281042c40400d540f0000411a101781ca0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 865671232 1250 865669982 865669993
    0x191a0612011805160c170316030c2a02040e0d052214060a090819050f010209030a15090510020304031106011512060807170f01110301050f0d05150603 66
    0x4420010b8801c00d8504e0f20310202c0e004004080c8500c9051003102d902c0c020415400b104049003842034540d4011100a00c8921001e01100341a0703916020b00d0790400d00d98501141c0380159094909021304c082600340c1d4550001020000c1152501d0b041306981c1c800c550183d41c1c81d100c0c1c034440602194001c640804000c114101c04030000881098180c040e80c03528000b4150a18158084c421103600410050782441407030000015181300c1003024901e130b0486044030820916203031a000b85464251040e100d040e074010302c001000c80e140041d18081c00e0f038210316141200034010802030024600380002400600400c524155000215002140182d210790f807104540d05002100a490701401c0c0a0b0030b00c456107400640301c0092080e4008540c8620541c0d00103401951000c21500e03140456204061a9682d030f00031856100050040c070311800e078000e0080c040304180c0342c3c9460a5100c14091988200b07420340890440741c541041d0a07038507640c003030115100d030400c1c01184e29110400300c4556110348140f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 865672482 1250 865671232 865671269
    0xc050a0b0105190308090d060b0a0602010c1704120c0201052701080a020a09060e1918050c0f0a0f050d090614100503121b030301031a0708191a061201 66
    0x3c21982400b1650030058040c01d0050041c20420917a0030060142c580d030761641d0b50f0000d04e0f510224410001c013030039000051a40300140f0080c0040c810200c11942c1c400b02503040001040c403901c41500180c0051400c2944803031544016a210300039550321100030071125400c44000e0b007208103c401c00c52026201c03502c2075511105148160311a40c151000001e03e03000d400c0140307501402c04156054801002401000e8030714106801c2c0303001c1036100c21440e200040103620543c045101c1ca035000402449101d282081d00c00c0018494480d0840303c008021003040b00306031451150b4169a03403164495010300606246003000000b51200240004100806002054540d0206101e100480c6c0300038018000741020102895041d0300a2855840192a01d0f000d45425000c10f000a40c007861080e0004822004094142041d07040c00401d20070074840064244042038a802c802e0001440006c1d034040792803100030866000e00c62490703510795080900800c02c41200314011411606079103103aa0b854030005e88 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 865673732 1250 865672482 865672519
    0x2190212030f0c19030e090402150a030605090903280302132304060f0b0f120405061e0c030402040e1f060303021b0a1511100207030f08090d0f0c050a0b0105 69
    0x288100010040b03408082c6d4070b522428520700c55a40a07000400034a404184c451000b9240d80c0f140c180c3c4000259900c8040c011232401c050100e40100ca035000640c14600000040d0b01010406211901d2601607400b1050b041c0b4841c5d012604d9510b41d01c2280717958603607582288401216218040108101c2e00e00850600d810188295002ca40710002810703036241c501410181e103940701580b45521080108903400c00181010412030203180701c1d90003064207192440900138501c08403801360b09070030b001000f80300d505959207054a8000781c0455000030b0325494600325520b80160704008901d0703c00560000f548200c0b00c0d03401501224026025944c600c0c801700b00000d071104e07541a040e540b024081c0000d01080c0490400f42414080c2420100050400b042102e858240421a4120003580000782c51081550194814411101c0c0382407054213410421125903c42010701805410003c02c07002d82ca5100c3d104100d502c001d0758000c0191011282141017429504400b4040c40d4095284580c0030f492994 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 865674982 1250 865673732 865673773
    0x30b070c110607050f0106030b190e0a110d1211151b0913060b030103060b01110d270b072d030507060902090f0f070f02190212030f0c 59
    0x194002000a1038502407810011aa00458401c1d81c4610444640041001c002d00c01d541c091401a003462902349801440c285249040504903d041821301c1015400c16a0004103513003016480703080c44d05a8503070607002c41c2a504c803a00016180508440010300c240303801450003102e0550060603030b8070692024031850803005040c0c4404202c000000134000c0e103440400060312009c40014000c2100c2030b850a030031b03000d64210707801142c800c0c580000100204032040c40b40500244007070034144400c840054a158035920404001070510040b01114078032214598101014030403408128a445910382840e2016070300200700c1103600304415040900c000f483c181080c0c5501b07010110740c2580f01c449940844450304828811584540ca803115180143d60f48107002c0d224030204d03001919a860004030013081030102420f9001803101103a03141428544c0880c07500366407600c1054000d4121460b10202d0103001d0b000002c54181e020209803041005403440c000c008206144086422804050600000c8036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 865676232 1250 865674982 865675007
    0x1d0433030c03080313080d0203061f121d0a0f020306071b2a14040b0108011a1e03090303100503030f0706051305010c0c0302071a03040212010f060609030b07 69
    0x7801020400900c3c035400035039000c4042d2030604002407003a546c085480c1c003d2001804080d40101c100a001d081a426040e0303480001c50b40c03890340584980000c1d00b840074000c040000d00d134a038004506c0300b09024918880c3c40000e481100d240c1c400070f041c034441c2ca1683d01c408900c03034020800842d001c20b100c0c01d40042034078202c0f40120310400e0742d0f9440040d1039048401c0e80001031a581c0260b00590040a02000103041100341d05421111400400084903905c4100700d06214004005000c42c20b0700020703198404003e0350000d60b8031098441401610807560300c07424044040081000508500400518003503503401e0001c005c070507141c1007059200e010f14002440c1c00d400502011011a5441d08059000788807002c201ca0780c01043d485031800d640001c040f810100da8040e55400400d070381040448001c00b40100301c151480080380a440140c0300c040c1001e48914101111002c12600039030001d684402c11b0441000075980e150302c042c1031920284002c2d0764102c1c140000845d40e900130408590352 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 865677482 1250 865676232 865676243
    0x6040b12100e06100e0907050c0105070f020d0c05030c0d11060c0301181d0d0f090b09180c04180603061b0905010320030c180a03030207061d043303 65
    0x12540c914080c8014080410050b0081045a40003507417551200c0800500035901603640d00c0d903500e08800d205081d520040e0920081296080c103020b80380e0f0780400d583d07589002038036045000b0321039406c180d80b80d4000c013101c80c003c07400b071410f868085030382040440f0b48030034004040c2d5410380d40700030f401c000900003446503000000342d01e44422400115680003109010040c080d0f62440b54010f0503603450000c600b0703200400310b40000c42c0b01c864250480544001052402c10342c82c42c0c8103a16000c54000400d03100f00e502c260705010041207202100c2401e44003e41440030010865016206030348002c0c0000d88410741e0020302e45540c0504e51140703100152003500340390b19400300c4149032600442c0209090601c0715882500c1c0e00c0b403180441d559400070b50184406143c915118100e9030401001040e5081d00c041c803844203000e00b040000d8011030f41d6021181ca40c14117407404000590407403858140c8031100340e84103240660414612440044540d052040b032403203005c2c095203440000c0c0c1c03828081c7c08003510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 865678732 1250 865677482 865677509
    0x6020c0105030a1103070314060d021f02010b030a060204230108040f05010e01020c0303091c080a0203100b0f071119170f0a1a13170a020a0206040b1210 67
    0x8a540110000c503009401a88005803860320019550140c0d001a0381c00c4000039207811180b40814141207010790000b2044a040503034225550014000d400a00744103220000c6041100c848213000b98402e620040703004c0c05403002803040b80b030310070025400350180c1303a2140c40e0400584040c0071a01e014084526046c0c445801503220707a21030349102112000700300d615640f6185651326442c000c2c00600b40a4018400860300d908001d01000d0900304e03422a11900b1090301c0b0618192654059078058001402e034800580c0c90701c1d49032032f0507520030158010610203040022310b6403101661b00018101140200030368205800d25504004003014505290041d0f08040201400315410300c0c1d004400403020581100c03120b01c1741448440c00c01e0146603040c0c902c007065810f00d84040101140596108040e00300d1900407032140d90303a49400c207510325685407020a001c1411030b850340c020012150042d400420f800e0f145c983e42c60982025138402c54840640d805103101103903100580c9648082618070b502407041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 865679982 1250 865678732 865678753
    0xd230601270608011a0a120201020d0c1713031a311a0906090105131e0c0b03061903020303030a11040905041208070512010302090603030d05010905040c08070602 71
    0x10300c0341000c0c0c00603400d00390b55000005400582445090007185d4404810707102c10381c07800204003600d011540035906128840070281d0060b0383c08542b60301052064200f000c1c4420060610b002c00000d00b40e89601e103000005602c103410480807200701c08036032080580c2c429014207007168003050b0341c00747c074900090682d100c44a10260250380349441c001f5880494002a18076540300c01d03ca003000c0001500200400c3c105100c0800300a2001d03540c002c4914000707025600f860b0740046081d5514a8001d0602030706111820034002504100691490308044e804201039120207249515501c2921618410f0301468090f90181200d10001d100b01c94000340030750304554905c0190009000c0b10040c1c0c200e030010400012480700428400e8900840c040c15041a41c078004400151111001402c40c10030300005210003146102c1e6001e04505403641520700300165280c1d100400d00c4c3d4011039000c012020b00384000410742c00300a5000a103e1809412840e030705035900e0b0b0b09291102441e00500300142c01054015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 865681232 1250 865679982 865680029
    0x120507030b030607141606020a03050c0301121106210f01150804261605060c0906160201030f0207051b15041a0405090106020109140118030c0c03020d230601 69
    0x8500c0303201d41554640750501b8658560103111404c1d8049800300d83c0429513000c040d0b4144107050f408a034840d1218555418950f000421403a01341c4001e1803d8040001e131381c1c0ca904c03588180d60740110405031141149a00c1c164440c103a180403107a80c030311a04000000203003050f1140c85820541c0003612034122548541d251407440b00082d44000001484e01104015990100401041c0c8080c1500348510100d90501c1e006090040140604258440030301004541d0b9886004803141c100041d620501140d0b21480140e0203003c2041c00c8060051000c24820180302d008039810441c10658108c4c05200301010042004004014035101a40b0b90203100c11b00036186410003141800c808841924109503445001509650090300b016005035103401401041010000084100505131402807102c1800700304850021414004080c0030403443e01a45410300010080b4040650303006480545503056030308102c01d010340c414107a005060000e12800c4182c482c0852040d060364070351900c0e0400e110522804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 865682482 1250 865681232 865681247
    0xc05060c1903150e04120206010602120405010c111e031e3703030b0102061b09010e040f0606050901110a0515041b06091508010f05091008030307120507030b030607 72
    0x2c101400000307007400b24000c0c9040c004c544c480d51007106000001980108000d0904006078440000e5502c2002c000c1c200c44c1c0f8a80544003910801c2c60300385084040350404507110401d040a4a4200314405051004c02d12603000c007d03120102030b000c0390100c00c0c1481407580541d81000110f0701c160000c0003240c40c09030380d4220090110302c6402407100044984401c514907c070b0208411000300380e581c1d40c0240c00d940c051154a6100000381c06074244410100c003841c0d0704e4410001964100802e40900e41c985584513805003812151100040140c1515140068100d07400006a03c0c0419203c2e900004410400103102d5030300b990290240c1031540c1408040038407003601030022500105001c06000328201540000c0c001000e00e030343d0340c0710020303c0c101c0c980100c01c50030140c0340d01300901e12006101074403107d03a091044a00170b0340d002c0740c5541c5642c417001c0c3c031001603008881c440c0000410b100780d00780c0c403030002250000c0d00301d01001140c964030003d0f811100704403200c07905034000f0000205c000340559107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 865683732 1250 865682482 865682501
    0x160e04080306040c21050411030c0307060807050c070b030a0624050a0c051b0109351603060903030f0504050a020f0a17150c040506071506030b070c05060c1903 70
    0x20401e1403c5c030740c4072401400848421015844a54590800091040103480c1c824440c4040d0b02500c90401d640700030a44410300b030702484060000c000c002c44c240380d100341c0441e030212040e002a5246240c45900f01d01e480e52040c0c8800144604100022488a041c5041c68104c0180a1000300f01150003a4003038602d84c012210307a20a00c2141603031000421020300c0400b8441c00e40c9242017030b148c10500000351040702e04d03030001c0c80030592520401c00740300324014280c8805c0111040010440c1c620604051401010710410400340404c410300000f0805c0320380224030001d109440a011400c1901c1281003111021200038007907500040d00d460260401c42c100301c1c2e00d600043c00002046458201c0200911480c2d89218031641c002c0e00381459040900c00c005d0b400290b0b50450314681490080002c519020b07503480680481c0b0604003205040c1c9041d803002000715842800052145001c66000d0b050701c9400d0f000761914001d00d40000d910341c42c00c40c11940401044a0342d544405100c45003207005040c0c07200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 865684982 1250 865683732 865683737
    0x2060103050c0a051f090906030f02120105161d0a08031e0a080402130f050c1b0c090708181902100c020901090b130509030a120e060705180a030302160e04080306040c 73
    0x14004147d0140502401000e540500124101028039205203c0c42001b034407981103040e450041070040c0b0603140343c3c9005005000d8034100d0400c070004d60072208010a104001a07110058100005000c040030004d4109060711205000e403000c608040558142b0454a9441c002880c0c180010018a44160041c4002e0401440000e0140078820324004481d001d8031003915403000404c08001c6600300458122101d91900c0c06419071001079030115400c0c40015001c90b06000b04040098405481c070070810600744201400c551001002e9100700c0c00b2600d45060030381c01036041d28680d00e8414041c0300484411136001d0004540d503031070100242c004004020313070a980400b043d000107920780424000c1a001e8148900903507601d0304040c402400d048034100d8140801400c01c070881845840106825034031444038144155940c068292070640901004801940540c03600c0011081c958002802404030141c8014812619240c0d82a00341140040354001d00c00e40040000400302d003016004100c00d0102030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 865686232 1250 865684982 865684997
    0x307061116150b010e0a090509120a030501050a150909020f0d050108070e16300e07090c09051507020d0507030f020907050406053702060103050c0a051f 67
    0x203480d0784221403001c001d030354103004060034104190451044540404090a180e40d00007142c0001c01c0c0d0300300d041e00c1200078a036514070000300401402d124807151011002d6015a8401003564054001d02c0d007030103180e001d9060500003092007881400000d444140503140c803a1981c1c036044010010303510581c0c131100144030030300c0500b094052902a090103024840c001e071100c0c40c2040ca0b400b048010040444810f2601c02004d07110203900004c04003d1400e4241c040f001407001e103000201c1000800c0c43e440401490206401060b60011a4407415280c0e0f004043c400401080c0d41103941c403109004490b445011442142102c1400200416140313101412191f810192030f10b406080c400380b40d00a40c2c168108400c0101180f400d240d400d54843c0090520504060070603000800701d000d00c0d12441480c002041400404c4146801001d0900403041c04e52a40b048404e40025107603003080c8412102c0d48640c20701c84205140c0086400150742e0003903c180b11103045548000e0321042d10400e52818407056 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 865687482 1250 865686232 865686247
    0x403120503061f02030f18040f110307081f091a040c020c0d150606050711090717040f06020412022409091012030e030d020111091215043203070611 65
    0x460207801c12180c004405047c8444070300501094404000551040601c1e041c4900c4403031070040b041ea600a4003d141c64184c6640f007803000d03040519080005c041d955144940080d03039010b9500490202e002c08403030039103203030040c1050105445440f821100960030000e1401100e04002100780d00c114010341180f5414420320890301c0448000e81c0010300010b000181c481c0521804034000c2200c0c007400d88d06510f5624110500900d00c0740303920081703410841410003290a004032102c0c6a0f0549811080844d039655841d0000e640c040c08020040303005800b1886521440b102104124200c000010f000c42c2c50801d00c3c1003080300c20240100f90040e500e4880f4030120b29504411203141c40b00d03109407901400d0080c02800c042c54982e842000004580c18a00c40c60401e06840341a06c482c03c0060700e10441084160b580542480e0182da11840c540d60301c5000c00041c45101905030a602c904a0034200300f4640444000e8207402000000c83c001e58401c2014000080c0298020070000d030310709507454248002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 865688732 1250 865687482 865687507
    0xc06090d02190501090b04080303071115090304060905060c0607030b0a0306050c03060a08160611070506121b0705031215060705010606020105010906121202030702060c030403120503061f0203 84
    0x40c0c00c00602c44428103182c01e1005507003001604020b0042100664202840c00c0d07400381d603a1200a002c00100500c54422280040e0100409a114203203200e2034405464242700582e5a5005071068400283c0700060004403414448200c030760555018011f4140780d03842c241c05030040c28610401641010a02000001142c900c1c46158007503e4003a43e15566410315004005581e1902c1d003150036030790014810090300d422040e0f001c4081b40c0b45420446036203034103c0c2d803250400310f855103c1c0d604000700040341c200400e2203a210600c1030704881903250105184d9000b8031954050343c6c0c8000e100398000c0010504d54400e2000156000001c44d880c041038103601008940f035500305e83c90460f8640e44503d414416580c0a00605000d805030490030440c19240186404940151250291a51035007006402c3c40c980300340110f921301c0d44c0180403940d5808800c0f116558a40c03040c8030685034039110a03007100700c580c4500101c90081600800400075507800e4070039400d50b00305030142c010551008106072884c0c0340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 865689982 1250 865688732 865688749
    0x1808190c031703070201050f1e2e0f060c03020a060b041803031a1210020f220807050a0303090306020a0c0210030606170610110f0a0807031205090c06090d02 69
    0xb02c0c0540103a12801d0418001e404d50314007404100c280742070001003000a0310a050020792182d49540585030649500c4c40c3c6101c4402d00c2e103980d5035190b007191203003c6001c124640c8041112002503442c10820340d00c0100b22a00040e007000100141c0220a946011031443d800046401100500003c0d1441d40070104140a14805000b10046038454042c07522002031310040c622014000d594100324100184a117680f0b81c0d44c682c0c1c40d0480158007043d40c81150110f0b0083e10082e15402c07500d02000d240817980c5100c408403038424251240315880e000f280e1810080d414104496145e02ca148080b41550f545201279040303400c00c80104a0f10690340c4000da6510311250141104c191000150300e410a003004240d8041c078007038001306007501424000540ca803a00101004446403810208820315490104c0c1060f00a910b08422440707204000410f100701c50b00186003041c801c0e164813110014101aa0f0140c500031a85403a09030000c03400e050080c00d080c001400a240000d10003000302206a001070b8900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 865691232 1250 865689982 865690013
    0x70b070302072c0901110a1115041406071d01300f140402030c09071e1d1f03021e0d0203040302121305041a0402191808190c03 56
    0x4841070400003c0c030384079015110340c21002c160024001080d0518a42030a80b14005c084402c00090480041008405000c503000000008401c01040e04090400c011303d0214404030740da05000700e80c0400c4001e40501c00284010781c400d011011540041e0006440000511400300007640c5032140316900000c0080d00704030b50200c03d0744006010200507650608644648460404502c020803d03c0050782e0005114400c00b58100d0780007100d0f80d10b1800888659550040070b040b902403601c00c0e1180c00390445050001c0c3c107551070103821401503ca00300301840b941039800941c4540300b00c06030700005210b600141409103103110b40c0d401c3c0c00400740300410641d00030680140c5440c0d01205101c00c140d03051221314071140d10038001506003113802031400c2103005caa00c01c0b188181c1c2d8410320800070f810407416100008200030000c40d10b44a02000c0110310514030400e000000300029442d00500f094030f02c004040d40c00c9030008156006102c9070f40b11600a02040030790721801c414900100250800c00b050300b06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 865692482 1250 865691232 865691279
    0x601110102121009110909040f0507060305060f10051c1107081e0f0d0207020f040911100f050d1109041806051324110a0c020114030108070b07030207 66
    0x14500a00c640c02034034031a07040900342d14100300c1e011103030210301783c181d130703a9100b04850010003a1654a000b00080411840042041c05a41c0d000104644c050780014030800302074543c500820101410820348941c1044141c1c0400e509000d0207034402e41000d8039598020781d480340058440b83e4011504002c0e00100d408440c3c1d038600140b821445000d8400d8826940e500110a60905010ba030442c480c80c05034549040c0e40d250301080b840c00750b40d94601040e000b8813014108100c841040d040c000310341e103c040c4e1200e0041924144900b80d6511880c4550414501561418244608046020302a10790300e42c1d480c0018400780100213441d0398503c10001e414100b82200810100c0c18540b000599900402c02d03200128442d0030500855102d08a01e4000070703040030b4411116a0f0f08107038000406202446c4008031001041211581c0c0c0c201d001d10303038664000d807501c007001c00c13110380b80d00a0f5204c240a15080360300b0002040000c0c203c10b2011707010780f41c42801551102a00c030540064041d4910799000748 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 865693732 1250 865692482 865692517
    0x6060b04030302152a0405150318070e0c0d110d0903020d03500117120403060b01120519050a1a010509010315030b06030d02071d0601110102 62
    0x416804004115400b034055081400900e000402d10800c0d03083c41c0070112000308141066404617030000119406800000c010281e4036030114500881c1e600215101e501110903141840504800098000112000301e00003817440e036902d030407010f016041002c203403840307644484a007112030180c2c1029060100d1441070000701c5601906000b4500322000f81003500b07061818a10f81d080c0060001c0104080c0ea0302034584004842c0a048203034080d203003000802170000a900d580040548140c42c1c0c43c100c422065501c0401c4000300e00703041c9c681420f0f01c000600a08204010000030720150402440c0300014185001d2905011035814151038049030728410001c918880006a40c2441c801d50760002d901400400c548000e840b80040c04a9010b800d4a060081c00324503054580c0c820307082078201c82c1e80c03030800c03109480d43c0f0f140c01c0b454900180d8007140310340602e00c4d140d4401c604c001010700c211000095081c0078034900c034443c0800800b01605041c1000604d0856141c540c200b4002425030400301c0b0780701c00c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 865694982 1250 865693732 865693739
    0x21c05060906120601030803150603090a05060604231b070606230607260d0e0c091003061e05040f020f0303180906040b15030103111516060906060b04 66
    0x401c203100102030b60f00c900034001c1c0103156101d0000308581502d9204181541d20b40340c0390145607801c500044210360000c0c0000400906010100714159054030a01c11540d0b181c85850800042d2841900c0c50a10a04540c00021144038400030340b50700030380360070510b19000c1d130300002d0705e02c090380044405d480f40f5481d200308001d080005005d0000c0d080d41102d9001c09100140e000800900c144d02000d000c0280d080000780030050342c4132000000b00c4184c0c0803956034000b03038101c00000d4150200c00c84258012808402164103214003a50b10928440d100300c08000e055a803640020656820200c3c0c01d0b1441c1c60f03004200701c01c1440398600036401f030390a90041c40c0c00c6104100c920780b0780c029030b42e009405c240a5074610b10000c0000301c2c044031080700c00d03105903518040803030000c0000034551580100815042c0c061030005500940c181c034002c0441d81001e00c424814406c0703613200300791200c640040170049444030031803060010407814450a00800d82a41a4030f54a003a40c6254001844c006800a003c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 865696232 1250 865694982 865694989
    0xe01240603020412020d02150c0d18080a020607170d022a0616020a06110913060e270709020a2703030c1506080a2f1201021c0506 57
    0x900404440c0750640c40e00e030504002c041d1420303d1010080c001e10b02d89848004550b141c0402051203505a20f050340c46448100d442c41e030b51001e546848010034120300c4031188125144400b54241d031a410003c100c05c244660a000c4642d20682c03040c3c40c00566111114500700d40c11004200300c41d18041c2c0581c44c1c5000954a0352280f1000d26001c201c4080c000c62003107041404a010740c1e00100c0945840001c1c42e0742c05090303007461065840140384602d40091078a05548960181481001c01e03110310001414000d103070300480d00c16000d070034801b0b07062034000b034031582d04540d034680d124840f1100700901081c015030b000e00d4040c003500711030340403600803544114559010a201e42507100d000120790aa100c124884224200280005020840d03c40d080c8420700c588051141e00c400c0d43d0369010401d0960f80c54078140c1b9a0350144d4103c07212034010315408030300300204404809851a50750b1180300302d042002045400305400c0c1d6414061354003403100003000400c90b84ac0d150705410843d400305140c900079081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 865697482 1250 865696232 865696301
    0xb09390f091305060901180b03030f041406130902030c0d1404110406031509110d03020607080a0c020d0e041b02070f0e100614040302090408092d130e01 67
    0x102c0945803810381084044d9840d4000707541155601b051a01400071b0b9400c0c01805092021380d4070b41c2511001070004503000c00c500051044408a002d0390352801007031020070840e8070585c103500a640043c0001803200707070303819030080d600701070710f08201441c0141c40c04880040d40e1100b45400d00c014041c90030441801a020780190301390318122000c000d00f6055944101d61541e04800551055a0300c90401c020050f4010040021200052842440003620f1800179036401044a1040004400e04049409040b00e03000301c2480d140290040c00c40c4d00f5003100221442e120380300040d03034082d40360700da91207a07840030030b0203888135550a40c05004400d042580712045800d0030342c0708079440c031000c00410028400319038004059131014542074100307607424041540c02c0c2c010f0341c00c003030744c0700308190140030030001206c0042c8040302d4281e0b00003010050301c004500f400321240018260003103810b400340c182e51800908107800340c0c00758880041c001d1002584079003161603603281d80402d041c4102d043d1640b02c01e0902c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 865698732 1250 865697482 865697509
    0x60c12020601050a0303110c220f090b0402090402030a0215040905060612040308041703180c030c0108060d020103240305150403020309010509060d1b030b09390f09 72
    0xc1100b5403519000c54596100e0f88800307020403007105401c4480c81010b20207070207031000c0180384403040c020440c190070011142c048a00c1300c3e540380c180c040180684c2400f40d4840305802c003100680e250b5540d000c1c0701c040f003c002c20413681030041c0003009005942c2c1c28454184c00d00c00140c56a261810680c400e0102d6001401c0c440c800e030014400d009401c08100d401e15031240d81403621800c95100d5140c40309800700e0041522407010408410011350700d840c00e15070300c140344900045500300000741d424192212000070844d40001c00401c00a0581d04100300d28440131441032400040030b0200998030f0440f092182c052507040343c204c140810a001d8200113903003500740741503046010380c28260f50195981c86101455410310801246106a40e0380702802e4644030b4114840505c010199100d48a411000451706880800d2601038070347c900341022202c5070300c50740c10411030951202481c003901c041707051100344440012184035000c00c40c402110f800b5081c80549030f02c0c0203483e480c0e85010000f50410500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 865699982 1250 865698732 865698737
    0x71205181507080c030403080705031309052419030515060102071d04031b03020c1e09010e04080c0d080103030305160203031306150321020102280315060c12 69
    0x103034180d0004901104a0b40350310b9100031115a079103031032544241140515840a0b0001c81d004c5080c8041c004c3c08801032081c1c600011349405001e8440101c00100c2d1016074055507c460603201c8000100c1d400c42c0400d8843d000207084003203e5000d201c000c8000650354004860320340040742c2148100c608000f550390010000d002410009003804100100c003645c581c096038105a07064082020316004038101c5207001c20b02c0c881c2818540c0c950a020350390350000183c3c24000c000c00c0c4c1d4000c0e007040c030310030f460b00b070305240100003066076440c00c0200785289401400545110308108a464004101005046c00080c40354440d400650314508010701100c00040076118911205001070754410b502000310b81d030100e100d4440f00411242401c180c001080a508626009960800040300703008415143e803130b055201100010f4801c1c00090100d00f40c1c000c0c0440441600401e85a00d6a05502500c004c10400203a142c001660720346262010580101688004040780110126a05001442803c012141d5090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 865701232 1250 865699982 865699999
    0xf05031b01080a050c19020606030f070605090d0c0f0f060806040203071407031101050c1b030f121b03041101030c090f17010e010603050d08070c0b01031707120518 72
    0x40d0029164120007402e107580b1580d00c4001030b1054520701d0640d6813402e5050401001c21000c1c4130040d54a40e0103a030300038400d10035038040d2441000001552000c0e030b101640c0e1107042c14007d01c20f02c41421980c82c1308944110030f00300045054045010030f80300400c001c00d10800068508075000c2c0440d4406005076014600400810021076007186084501008840030710b59a420303981070407103040305000c002c0105035080c201800158644180589104818000c0c00c3d9507a20079000c84555900c40e2030702e002155481800861103124183e001c0e40c0d4080e140340581940e000d03201d029651039520480b0120b411400408408a071035a140c800d003090a07600e41461012141001154003c2090700d118210140442c2002a10807076020b4008000c542d030281d000348800b0b80c40e440c0480e01c403400000d1000000d00401c00081c861440346030302010a5400048542859086840d4040c000e945032804000c66203003005002c00048400b007407107911a0b216a5881d0f182d84924a203003101e1064000030318481c0090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 865702482 1250 865701232 865701283
    0x160801030f0f02060d0e0708070b12070f120c0903030e06031003060b0a050d051005160f030b04060e0f10150e060d090503041e0b0c1504110402040f0503 67
    0x100005522450b0700004440d106000e1803000402c9031142c4550084c00ca8100306080c4a50403000440300140da04503030503600442d1312184200390302e0081b0b4107a0340b600c44860021440c414080c581e11310148400d490403058a2000c800d411003500c854800100004948040410605620541c40030707000d04220343c1140383d41080709903000b2a1500380009045280e031008a89929aa2500e0140060101031302d000c07190a00d9042c51a03c2c0d10340c241d401c02d040e03030800000a01034010240d59006400711519108298590040700310300409252108540260740c0e02e80201e41e0180c5c4181c21881403400660007029441c100512068020307413580880312407240c0d441d60280381c9800c04011184180103403001394807030001d602200c01501d4150809081c5010025000c154054807242c01440f025801c0c40e814070469a540300c01000f8840c001e070204c000c0c2c00c0b503840d41d12280400452190080c0c020070078065005001000102268810360142243e064014000c20071800e042c4000c110342c020091041421008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 865703732 1250 865702482 865702493
    0x4080d0c0b0a110c161a0403120c0609080426030c0d05180405070216050a030b0c0d0b0a06030603020f03071d09010e15010302030f060c0f09040f020c010516080103 72
    0x142c120a905a101c2050000c80710b40031007542d2400003260100c60110a04010005034400b1a0007140c2103030203483d10480340c3e02400c20441d011654043c5442080148030a0220303902034800c84104c03015500c4000c06000301d03a0701c002500141c200710f416070204620843d01d0240b07040303003501c42454030380082c070842c07040600c0450622011359980c00d04071740e19181c00002c400315091985000364440c0c030b4441440b400c04c1d07001a0000384580681a4405c405031918104010a07103144402840e041e0380400103546c50107001b0140c1030358100b2442c0800c048a400340020220b40c3c064100000295691f0020415483e014690381d4000005402901c9458180546030403110901c1c0012101c0f10b2464000c00e203850400d60183c3c49102c403000c10b40764a144041c1840d106003400f071200368400d100340350703580d0b10204c804030304580200c0c1002c3c3d00526000b801030315a09160005642039602139030300e10110440030100e000038900c00c40c0110002a251400d00c0030b40044080400000c0200524400188001070313 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 865704982 1250 865703732 865703753
    0x809010608030f0c070902030a0b2d1c1a0924010302010302090102160b041401030c02060a05090c180f1006170406020d140402030706020a080414030f0a0804080d0c 72
    0x888a007903e6071903104d940303614540300c115841058014400403c0000281c0543c0c400340c00074070202d0b00300743c99024011071b0031010b41e01c1400e14101c070598050030341071901e414041c090f042c6030703150044030003003c01d0340b04c000c4110b501e40300d940542103d0740c0410040d0700040c010100c910861881c3c00000c4c4560b0681c200c3e4070203050000030305240e40050510f2241c0c0c000c2001c001d09a0700320b21020b00e2182c60341200f50340c60300182300700c0a001e00c03a400100015030103070103031500741e58250b0b00030441541c3d070554030000350002402d69401c50189803192011a00e035041c140e0000844c00001401a083c541c1402c9030140006082c0c454200c01c0d110140310a0780c2c404140c20080c0c40e0703040c1503c030580b51410158000e00c103403c03c48203c03074504580100c0703202c0b0800041d131195000300c0030341e500240e680c0720030790700c8812051b0001c154840401c800d02005030100010f80503048003030115042c084040298a107480520b860503a01e05030082002c1180120401c8000100070380b51402480081e42540e44c50f4048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 865706232 1250 865704982 865704997
    0xc070b06060d09200414150d0c1d10090605100c17030405100605040b0f040e0715051201060905011707140d0c0206010e040507031416060e01080901060803 68
    0x1820006102c82c4540c406410844181d500482d090110300728059500b04c901004000081c0101d003410042d040e040d000740981842850301c01d49854022100c94200101118182c0d4121407444c0f1b640008198881c0c0038592040e03900c0b42c006001d2a40c100480c50f0300900203242c2c0408500c2781011024401510b0305003c402d000c2040c1e040001d110520341c40c2c03061003500c1c1c002e80c14143d107402004001c14810b00244c5d000c44000030032000c02c80951104103000640d28048981b40d004105d21444030158103142e84250904030100095494503922800300b82d0380030715102400b1001036804130300510343d4482e041019004000c1d03800c01a40c0645410300103020071138071481d5190000c1e048000140c8150080d00b40001c0442c0207490a81c2d40c503040220701005001584442005100d00400811504210041b0303a000d260010005c102c014a956252848600c403600002280e0160740c007139021007034500b07103500d0282032283c03030346541c0d41201d00004141c0d5000a080820581c103014040002c810044101e03000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 865707482 1250 865706232 865706239
    0x302010905030c01090b0a17070c150e070510090302030d030e07060305060f01030b041805060901140405030f03062d041406011d010908101b0c08030121020402071a0c070b06 76
    0x881f94410425100c610b188002c1c2180c0c0c0480200301b01e141c540c0b03c1030703c11041d0f10170006130a44083c0c6118130300448583c03d000c01d8207580701c05018002c80c54540521000d03180c07d442d10000068507540840e003055400c529140c0800d848840400101c0070902a11010740341c2c9117070401851030180005a460140b03a568a414181c0c1d07881c11210640301c0e0313045103d01e003840d0500c100c0c081e0542c2c0307032103680c85008891500441d464902c040c3d201e0500668032602a980020056003002c070741c1200e008031070388041c01d0305a106400c1036101c034140c3c0080d898511010001c141d900407078032040c0280400d03500304015240100d40d8000400000d41c0c0c1007202800c001d42807204141035500c500e40140c503100f403990403140701413140540900030320314030350828100452211640b1240007601079003541e540b0b107035034802010903800f400103002d42c10656450700000801036825040410703054001c54102e030701c8071005071201c020b2003007c3c9054403440f40306103802001c03c6e4615485c02c40e6644444420308402b5180c07a11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 865708732 1250 865707482 865707487
    0xf03040807020d020306180613020a0302060309160b0703300509100905030711090112080a031104080109030e06030108070302040b1906091404060b04120f06150302010905030c01090b 80
    0x75503c2e4540b441903603d601604488803410b11184800404c130240ca074181d554856480001e2103248682d103607600640c0c0c0505640e40352420740d403c000d81c94000071701000f503a201e0f5501e08040c8440c0c14504400410364081d01c030365242560304000303150115030380b50a01d40c0c02041d10320f208540108103c91040001410001a460300e484051a0800da1880c0e048154903043c070f00c1242c00c0c00004001899038a00c54a4505002c0f1800c5c6c040c0892107409100710b00120b0000848000442d11100c02000012990300d000100b0038ac486062020075040780d0412802603550300600020141c006201305039416080b1640d40c195072405815558554060200900441d00e81d9a0540152078900c0103080010540703a08110a90b05c50030000e00100940c414100ca22100224400b0709040a00c5140140e80340050140e1130b0500302404805040f0a0b0101119070322003078245200464103d102c3c01d9101501c881c2120549842d40c0001050000c464100a1013604000901e000580c2c11800000494403002442c0f074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 865709982 1250 865708732 865708747
    0xb160b071101110a0509040f06091d0712050c0d03090308030c0d0c1d0f0d061b09150801140d05010515130b090f180703050c0108390c030d0e120f030408 67
    0x40c003815403640004082cad0305020785050486101204101c0359814801201c001c55513031000201c0802010388050300c16000000f820426050580e0f103038241a0080c00e00c034540c0e554035940d00a030740c1d100710351624ac0b444021816070b503c12907600425101a81da4a0202010504450f20701000101d031489288140c441c1985e41e030903911160451003030301340c000400700001460700068041c3d2402505070300000514918000c03580e854140c40100d10000107603124103c80c2e003080140c503202d0281502c0c1652140300742d03001600048003402004d124400d1f11710420030081e0382100b40b1048505942a909a86041c08a106cac00303529a95441a802200c0c0060030019481d8902d090405012040400c5110300a142d00402403220016001030074100c20380c0c0f502c8155a40309400c00b4001000c0f10201c00214400108516100c0e4204201000100340c00d078880c608008103181070326541c444c030314216403940c43e980428040340d810b1000302440281800468945a84802e42d1401c5100040000300180b80118010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 865711232 1250 865709982 865710011
    0x60c020a1a100e150307060930080a0e0306060d03050f0d02070f0602030906060f030a0201030c030e07030b0117240a4208070b160b071101110a050904 66
    0x25004145158016081341000b030202001003420400184c06480352010000340c2910840302c000880380302540c00046c284005810410f40e8203001c0443d10f40000003c50000410408801400408026210fa404500c3e0007014542050b200078100c612840242d131103031011981100480c0c3e20188944e05444d0340390780f807228840003070041c4400030301510480032141040003a258000c50140f902c2d84101e0340556903400030040380c001c0c1c1106554064204a07072447c0194081c0e0062038004220f41000720f00c000145070803918203103195005440340e090601c01000042011201c1909180c1402c1c040c20340349410442c510100c88600e11040c2410f0026800200d07050016404480e01da0f0300d100344410034604403c545002d482c0c0401c5020031040c0d504403110304030b040800711002114406406401c1c02868460b0111441e00b29645a841c1d0700f0420510720b00184201040b18403610f419180c1501c0d20608148407421101c02600c000d86114041040d4001c142d000400d44a6551044802240d079048184aa = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 865712482 1250 865711232 865711261
    0xc0605041a010f030c050402091f030b04180309080a020f0d031803030807020d090f090b18090a033c05070c141003090f06230c07060c020a1a 62
    0x507034001000304000441c00e081d001031201d04490144462034490f60303e443c00c0008910400012070f030f1112641750700750248a0801400075a031941c6003400a07400603c000401c096a5003008240c450076007580e000c00c01c064101c1e0782c91700500070b110300901942c2e46035070100f0059007510500b20b208218800d600800c240c072aaa1a03001d20028010410046a41e03103005025208141c80a0001d80580c500f2824107904c20707c01743c02100c0b0407112641d1040e203403840500040402d25110b5400894092001244910445415004000280c0103201e00f40c0705040003000440c244404084101d84c0c1000205401d050082140008000070b4012128a01e101c2080e101d51146080042c892401c180002074003101c1e24840440c1ca80d0152140d00041400d65002c8040b034000d00c20007000e040b00103884501198455101d009081950500040c031601070440b1a403281c40e0071107a40c0d00d07103200044d600c001c00c1103a000d1030140705154001810b10f44190365441e4022600011036242e0845250005203104c1c00c20420b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 865713732 1250 865712482 865712513
    0xd060b0301032d140d030b060a080109020d1107110301050c040e0a0b040f051f090c050301210b0109050a061203121e0903020f0601061106040602090a0515070c060306060c060504 78
    0x500511001c0d0004c01c480d280c0d402181c003100800d10b0403030f48036014188142218802001642d4015540c1c0c200784a010094002e4007034a440181e0722490a0960454100285480c40c003c10380e6420144c0000109030030f4601c0100b00511a400c2440308000085496910b5600044503c030b000c00d08004210108005010898010700c0a43c101030601060080035640707841aa5a180305811801d601d03610800c0076140400d0103500080d00c20801084451010316008884000030f1014a17400c0c030560300c070149000404c0e084081040d40c1d490a00c5188025485500010300c10362601903c80c188944001d0488100400790010b0740d502c1d107400c56000403001d9149801c001640300100410380b000e09000756200c0507412109d10354881c941c00420b065004412040b150b4607100020001640c0b20340e1154040c0d0810710420b60042640e84003c15250b903035480900035a910000500c2d1501e90300e080c08080e00842d580103400f0f00d81303410000d20202c0d070710502c010b24440d00048003041c00c0e111881e01c1038141c3c3c03d400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 865714982 1250 865713732 865713743
    0x30b010507060623030610050f1503040b010906060c11101e2c0906210d030227010503011202030a150b0315160c050f010f020d060b0301032d 62
    0x35408580d44c4115544841c500d202640b200a0388042c090070b1503138a000584440e001c0304641981003041d403401741c01500d803882c0040e110710b40703141f0160710a1402e500309850844240200e90010300ca41341d0144201d000801141c0340000004c00c46827240505c40c510b40c101c6502621030a41c481034558013444880201503a01c5025403007804502d00010110310380340c020300b1041d10800009099000c1c15403154201440d0083c41e844040d141e2404000d1070f844030621014004c0e1452440000d40501031004000d24080f0b501d0259480c02000143c1070310b0b1140710110300f9040f0031841d040c00142d92000549055450444080c42c8402d0075000092824000340402401003421a418071250b02540e08401141c4005a08652603e010001700045c8450100d0b4400c042410200c020703880b440c400d42d1031500c910300402c162030344409004081800e40301b207000146030568000071740c500c4c1030451b4030585005200f0035801e2800c6504695900c000742c02001440d8500102504003a0100c0c01072a000c5400598000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 865716232 1250 865714982 865714991
    0x60405300a031d01020d0f02091302090d210f230f040527060a06122325050c1c11031b06060f09041b050a060c0506010f03080a030b01050706 62
    0xe0f80d926000c0e501820811441a0030900d10b00c403900514020f0342c0310107900600701d100152010101c01c0c025080b40325100d40c030001014804000c030b5031100c600d819140b4044698070319180001c901404010380f078100c00301000410600d41121502c2000c000710a000d80b25070003a900e01001c210344916005a4016542c0881104000c41044c1208154035024841d03041290b0110340d0f41d08200018503006104110100e1501c08585240c80203540c0814011080340c000c090590710010305600d10703098110b40b41c190301d41800c0d03014500441c03070b08103c200015547c139005103040e42140045440b03040221440340540d00d00400c1070301940c0203a0b02e041c04821003400322900c3c1c4e40f1415040c030b80316101d02000301075805210086081402c18007800166240041c0142c201364556a49480e995074880e001040c5180702028049201c1d80c0b4441e1100040c50f240c0c2c1c50101d01100d500b481414083d06034024203c0710101c01040001625282c00d0380e840100c18140000c4500346000180c0303544c8204c8500914aa1a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 865717482 1250 865716232 865716281
    0x171b3007090b100302070f0f0c0e010e06011106060307210b0c0d0e07060c1506050a230405040c0303120b100504090c09050918070b0705060405300a03 66
    0x242e6200700003604003207944612100800d00c0c103a08034412502c02504000e40801c180707020441061041414511030100c2c50300042d914104103050740c0f02030f0001c1100244440070b0094642e400184990480d40d0600540f80701c4c01c02c0000030b507039096544038100c058000c590524041c108007805070b6800303e070400081001c81c5400e003e8000e460380400b000c0e841c00ca1828419448560001601e28240d50554540110120081d2034a440011186102c070141a0700d4001c08a41610f402c0801030003400b040392503040705507092408807841d07242c20b0f40050096103444104008030b0b1250b072106044a8060401011741c1c204002e003e4054032502c2449500044031100e00344c60142d02500800403100d52681c104201080e0768000c41e44000580310b001d5000e0711340e20101d003c0c1803c440c08081c0041d0248201d40c5c0d01965111014810b400c400c006442030380100e0b0801003402414040d1904508001071622555002640c0c400a0311316405080f03100d035007001c28000501802940103030045001079013050543d022 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 865718732 1250 865717482 865717499
    0xf0d021908101104090b130c020106051201180b191103010e01290c01090c0909050f1f0b01031d100b04020a09050f0a030804171b3007 59
    0x680d0720800a0701c0c0b2401d0b2099841c08031501c07851030000100c5907010303d8a4a4207031214080e00440710403641c442c9422441044a00320380c866085200340d0354001180c500c2c40c1204010b141521604044a83e074105046840d005500c00708030004250b20042003841501c50000411260540b00c00c0da466030307403502e8141041c500c1040080c1d0b04071041c00205a0060b030300c0b2002c5060320700d0b10100c00305080700c00709402052a440f500190041e40310078000040d11044540710302d21125200c1d841451b185540c2c0743c168050250900030702d001e411342c04000700201400740303c0490411986444524590fa82c42511900aa10a0f04224160810100c20001d00392544620544620392a004048c035640b0300b00700d4506505050003910001c4000707460b4081190301c1d15091010116910040607407044c002c0001000080c4510047c0019222030341034420f10781a042425440c10000c2170a04000307620212800d00d4641d201541600e56084015166401c1060081c0d042c0071045041c41035100c501031003001103907000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865719982 1250 865718732 865718779
    0x504051e04050102091306080a0b040813090e010605060301080601120614070f08010806072016180b010e0a0306020d110a0c0b0f0741040e1e060f0d02 66
    0x7581106e151145106068001044910302d219481080e00520b24500c046a81045025402406070440524260700389054030004150380e004005d86a64402c043c450740d5109100f0300c0080d00041e03031304500d55418280043c2d5110f805224198104070344851803400c102d660b0300300e074414500361a4205014148200064214130903000b0240015008500015803004c0008125010380216141d4030226000303403142902982e150300580344140b04800004074042251000c0754018030b045041000c04105280441c0b0a0329401501d1904010075501c01c0c0e001542d58600400407298000001684d5080c407a0f40140a4400380c03c42841c071030b02c04100780d446190402d29440b50107120700342e00f030f482d41d541c00400b4070315010580d00240080d0625981d4940107410010a81c8018481c0d151050245e90680810303426003040800020031030801300d010000e2144c1d690780c1c0e80c0c014011104c4a00072458035242c030440c1600090000344201c2c03140940d618141c450407425001e10743c01034100300848031f0b844a4000b844 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865721232 1250 865719982 865719997
    0x12010207080d020d150b03130302070807030803040215091c0230070e160f18080a150902030a15060b04080102040e060114040519090f15050604030c0504051e04050102 73
    0x1904210f203024800300000c017034200351000360040d0350454036041c07003805605a202404400398400d600300401c400300304004944c019031003a0011592407401e44113110b0781e0070f030700607010350039070800d008a001c42c0e40c1e03100244000c1c80c105049030542e0742142c00041c51201076108582001c1c04240c60102c11244d120f15803400503d00c05e411590350316079600e00445001000c5650402d4020500c3c0080482e84c880e908240a0112078907200c05502c9131100e4012544020764002c5040d41d1184824404020000324414080000740400300300c8041145c01003603c501072081c0081c07480f00444502d1405403c40c2d0312200103070499544d1551925120000b41c3e00030350003801291321850446001880561050031a82c0e030324503a101a00341031519010501c03900e0281c840b4a034203840380d880e00109070540e0512034445801188900072414070404c8480c0c840c0500c240c0c1004e801504c0810040c00401c900c1042c1000300d40b070a44000a60b03542c0c2c2220300481101002d03030400d8800c0c01d681480f041c440c054016005030f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865722482 1250 865721232 865721257
    0x70e0c121501110c01090905060303041d090601051c02041104080f0a02031203011a0904060e13170f0a080603010603050d09080606010e131a0402210115020c12010207080d02 76
    0x43c400d010812030f5a554104542400528130540a00002589400041c0c020314042c003242d00349611030080070300340c85051010414401e00d8a0400a0004040041c40d006202c25100c424550003c01e00501e03501c1107a8802a0080f511545e0010150000c10104c0c0e00410100054a4440e5004000f15403134161400047c0d1007485030469802c0d200d191f00b41224101d4001418022000e0700300c4c2484903803a0031008400da030180c1e5400c400208031204a405500ca14070b5041c1e010340032402131804070100c00c00641c038030740440b01c24080190b10388040000c452240c02c1c14100140650340c0c0b040040c2c0540703160b0b04001c00c2e0b40244445002c04582000940081d9543c92080da5060f64852004407001c8108040d0181e001c00d00341d19004620306075600100c041042c41000003401080c1c01c02080990307010000ca00358021030202c0420a610700b036014540901070044205204100c610b00003903482d55045845032052417039118041e03d41d00b0940c11202c1c06a84031129984500721020740340025040510424a07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865723732 1250 865722482 865722497
    0x141c1104080f0106050a150e031f14190e011506031d160e06030307140609010b0f0d03081e07030f05010503241b070503030a0c11070e0c121501 63
    0x654500600070303402912005001b00c11a036280821405504ca13182074000180003079604036421685051003038680c060741210445450b520315145200880e0b50580d8405441586079090044581818400060348034442c5030224410201110041c01466080d151303107401c43c1c40400c00902e00b5016000740410080b807508151619000c82e811540310306090034114000e00742c400e014407900d0760101160740c0000d40601103905040c0a80e96070700311700200c4513181d01941e00402c10440e0004090003a094040003d45011061602c0032011960346031700400020180406500020080843e03a407e81d214800e0400b9941114107044801800a040340c01661918505001c000714480c1000a03440c1d81400c04002040c80250070062030703030f11f48900540405090719491210350810040d01015102e201d010b10041c0d030743c074102060780c001160500c00701e0b403041c840420100c1000240124010080ba40300b4400861265900040310f01148104079040705540c00e500c040c48841a402114040181c0d003e888115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865724982 1250 865723732 865723753
    0x4060b0406050a080c150d0f0b04060b0a0c0803062d01030c0923013b0111060a050c0d09120e0405150d0f02032a0a0501141c110408 58
    0x1a0f01c201078021500d0550005900060505140184544004040b0308041c10040940380143c203071030080507180e0240d902e8032688546031800c0c3c4110f00c01084c3c0340345024078042125a000c0c01410f41d100010300b000344040002011501c9525840c4423480040d032603805c2060001140d2880001d50a40b00c60010303107010048818a4000d0b800b00040d240c100788800a100484071006900d4454401598108171005c031410070448411030081143c0c0a110488941c500c10015000d4860401c0305600c6e03041084400c06011003550100d42d180d007068044901042c0c80e5030701c00c5240a0f40c1b082082d91003500d45003a207540180a048405030020b04910307610a920300030b6100400042c3c40c4103a5030f62401c60000c0312104240c0c5003501040d000c1511079129030141546d2500001d08100700701d602c129040021001108031001c0c0d1705a84101588220760805400d13041500080c12600300100e100c601c02000622484248840400b06024a40d10f02003441100394030003018920750014440e2194034031401c000c88 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865726232 1250 865724982 865724989
    0x9020a05040903080103050c09060906060a0e030f03072a03030c061e0204032619200f06090d14071509080c0c0f090714070614070e1f210504060b040605 67
    0x55004ac80014400c40f0342c0c1e10b60500308041ca46c0060020024010f400703130703202403949080c4070740180b01c041d20000d191207040c81d05049000300b10a80c0c1004007144541c0ca1181c106e187d9480010540c0d4252070040c40d01e1041d8035108008040711007164000544c0c0e0410228004038540061007a240f150041301c840c500607506108049288900b105003228060120822203102142140344202152405031042e051a03028038080070b8419982c1d5055800819204410702410441c49030002031143c010003103aa03043d003001b0070000e510000001920b800040340024403900c004403001d01c46110f00c0805c02170110b45000d00302036001c0003501800380203000c02c6000c1131900822250103280054101000e598401204540403020303050440e920714414823035107010400c40c0c032030640f881c0d55560001d241c40c10000d4024091400070101d1600c1349100113655030880b05803d80000301881d85042981203e14000d680903403107030241c0c5217001c0003440d00e8204418030106170400d01c3c1800301684d00b04003464403202030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865727482 1250 865726232 865726249
    0x1050306090402041109090a0c0207081519020912010510090917031f080706121127060a030501090608121c06090c20010203130609020a05040903080103050c 69
    0x46603100381d03814000380c051300313241d007041802003180c120f014905000303000001c0210f5000c0d5582004a41e4952409460a03010070266000d825810300420a414480540c401e00b0b0780010304080100102440ea030301350038801e070181c64080070010141d01a01c800b0f944118003c1104542d050800031104200040001851190100254100c40030400082c040d0042604039440a0000040340400d240800501d2100343c5044014028507070150407541d140c51001400040c050200c00c030140e2801e10207146202d015001c490455203032440d400b4400e16200801400c52031341074171860b00300030001202d044040e3300d50f2042d07040e82c4040900b00007458a44544580d9000913151724111b4110070001d1785401d40b4650345241004c1005007006c1222902c2e80149420b6602c41751403000801d410300700d04103030700008202c1c402122014600850951521507080d00403602e8600f805040307250b4400f07600d810364980c0207510001d000e01820a000c1c2e64900d10300240515030074841550107004003100505e89180a004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865728732 1250 865727482 865727491
    0xb071706010509240705030309100b01080609040c0503010203010b1b0a240b100e1002010507080c1b010e03040501090f0303020d051c0606020f0d020106050d12051204050a02040605010503 82
    0x100c00d400d0400100902c00d41c103000711000ba190801001001c80c40442050003051700324418400786403a810000701c403516200c0203e24606400e410280c1a81c0d060b60722a40d031550100d01202d04607565101e03401d2280e562030302c1d81c00c102d82650000002003145412400180803a075085007034003900f800c0c4624550748035000b0940081c1440c0fa20065801e40052605084403140d281000000d11202614000ba8111184200c4540441c0000303201c8540c41c640742084841c03606150000f1b020a14003140011714a040003003040102e04004240c0104d885180a11004206100c400030090b44401c80340503582ca80181c4255800140c541ca804510b25035030540c0e4808880e8540c00405000005840c2500c46410041456031001d11000c5401e601d020140200401444660090540702d81005501410003403140707009005c0d6030400008000c1a01d030b802c0c05000c60758000d900e030490203c03034800c100d4441c464100540c00c510010000d0209100c00860307900b8000f8400c44007005210360703880054405000403035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865729982 1250 865728732 865728737
    0xc03090d0207050d080a020708030a08010906060518150f0414031917160f0309090e03041a07030207051f020105150607030c0c090c0c1e02150c15040b07170601 70
    0x20803000000b040c40c005050300d44042d0052310003043e10b81e60003c2c5507801c040c64040c0054000801000000d2261041001816081c90b2542c074101c03024610000c0300e4481c880190154551203078603410403a050f8103650113004001d45159543e07a407200d112085240c400003081c800d00400c405401440d4003281002629540701d904400749032076201e01018140c0081504600d00300a203207032500003900c1014600c4203248a91a0001010f00307010b12101120b19070325500d48542d00400c400d00c954448a204050700e15480c12095a07552a01d280490420382181d209a81040380d0751172243c03481c0071071814200c415401d40c0c020000c0d5a10940c04400f0b0400030303a203494010104001c0080401c0c4903810f2050400d00444001d07130420754480c01c450407140f42003c08800500781d0b841440400a1050300306000d03201c01e000c0034200c1c0001d500000d003000300100101c0c420030000560644007003000d0002c447d1011100003400038070b1505080c0740011410440303443d000240400c1d050180d070303003150300c01c10f0103040d040c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865731232 1250 865729982 865729999
    0x2030604030e01142b0c020c0609040b09070f12050708062403090f0114040c06080a112a0609030a180b07121d09040209070c0b0c03090d020705 63
    0x60314160769035900101035504122070f8100b8007440404c0301c4000d280b401c14106003000c0000a20954403504c03000c0e800c0b5604002d00b000810624607030f0000b054821080b007102c04c00d0b41d40e038080f0001001040b0310762030983c0203005007007000245a0406066840410b0588524490501280d41a8200d510807900c0001182a01000ca0090304206103510001b8088400c07150241024a4034212250002c40344840c0643c0300790718200d640f06081c0034800e03001e81180007105240c1015503e188003607202c2d00440040107800b0000410340303111f540210304203a80342c809040da1800c00001da842c6107a040d85158140c00c080e000d0201c000c000026a06108050f04801b460a00344948030444050400341c42c844e015541c2200c011134040010b00040180a11070514450846c01c101000b4200b1108200c14a51001c001d03849000e40d41c8a9601c107070f500c682c0c100e40120745580c0e1117806607a42080701d400500518055420000300d212800b0043d405802c80e04101c40103610640e40403641c0d481c00740039150300280740c2c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865732482 1250 865731232 865731241
    0x90f05090403110f01053c0601030e0703140c0f091303030c0207030614180712020d020d06020313020a0f0302010c06181401060f0603020406050a0c0816050a02030c0409020306 77
    0x90b84008007403629190075610b02210030700d44c290943e0010343e079010b2880f05081a5000042a10026140d500814183c024004901c040001a1804003c04032418180c44200020b10007005010b00d03805940d0000400e200030050070308480d42c032502c0007142805120754140c401c0d20f81c50080b6500e442000c41d50000c00c60402103590480181002d404004150f200c0c41c03501100007840c900401080101c003491094140c5080003d189005801c00103000035a00705120520190f003550001da002035405807030a0604102c28400700300344031680300010b04407501c0030092000707801c0707410f0502115500865020303a4940d00c1d040002038005003444000e003c90703900521600002da207900980303500e000850001540080c2d0380c071b6815021414082039580c5035903070302c000c0c404000c11131504400381000b89411418141000406411446400e40001c240400c82c100342040100780822500c2805494120032030703044661521941d2080800803c1344240070700c1902900c0c0f4100391150300700076a0010700818241d00c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865733732 1250 865732482 865732487
    0x6040207050318151b0607032c100e01050601020c09011211030319050c071d01030b04050c060f040906090507050915090910140910140a031e03090f05090403 69
    0x604030400e41c00c00401011402c0900008000c0e24174410307580603002d18400000740340d030705090700201108149480d080d01078200f1503c09003c00b001610214141710b00980c02d5038640e1604200d5443c00d008076003800d5a9150524064106e00c0c0125400e0b02103500d90a55482084002002401800d40340006514048049044c1949500d10f83d0800f07003e076032038510364100d100302d00e20014510001150000500064810007001b2600013001a000d811030100000c02240360b44031018030006d0014030340c64000c641071290501800d03040c0c0307100a194958800c1141c4c0c48c180e10781c02038450224420300d4100c00203030005450103050702c02c841e0342da6054a48608d20042010740818085001c0342d40b8002e000740c249540b07821903510f0003500078803880d0441e540b42c0400028090f240d0030445000d8116507042c00301c50040420802d003907038440300112060300c6a40001c51050b1515910142c2443c9a902030061100c2861f00343c070341d9076030190303a0f03402c0403903140c0c240004840c41030700c40d03507070009507001c001000b0030b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865734982 1250 865733732 865733767
    0x1202010504212d1b05120c0102090315061306050609270709090b031f0c020c0607060903110303010305120d02070803180d0311160c1205060a05060402070503 69
    0xc2d5606080010480c800c0502140d8540c00340c0e54021520002420180385400c20142d00111414820440d0302c05800c0d039804c4e446a00640503024a0385011500a85100082d016281c0a18001d022514410b050400401c904501920807901440c186110800001d0f41401108203a4401a058a21f0200400300303210010504a03400e00b40350001c0740304441c0e160319092616011f250301d43d5a001d92141052040411688400d0155100780d110603a41d500700490444603d032601801a8005110240719070160300340400380c039005900480005400c01000300325444008581d010b551904601e80c900309000750380384001c0c0005045580001c0c600103044406030010480705d55808400760801c1c089503584d40d400d030001c0d81e560b4482441c80003403010011007000800401031284c0350500441842c01c5074000a807040e51083c0e01151440ba0380c04050240c800245170003800c0e100013004404d444c41c00d0090310f8402c2500c2400d003060400c404281305152a0080d10120380d0072030b0146240841c440c1400e00001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865736232 1250 865734982 865735043
    0x6060903070e0106030b040b010507020f01034206082a0d0903120507030203100e0405150403050d0507081b0c0a020a09020705010f1802150c191202010504 68
    0x14881c0100100d03407401d903000340078001d2010703480128041031800c08210a64030826071040c10800140065005650750303944021b034040303081c28001026180524031000c207000e0074481200014007400c43d0b0428110046000780f11042802c040c2560644400048076403802c103441e48507000c00aa5800c00b081202c14805109602c41c9a20462505440050304003da891050064020803c0c07000c1c00302070041c881c0142a480005490114958648441a00000c41b0f031402407449849900000504119003005940c000b8000994141c98502c0c2a15008000da03201d0002084a1424176001c0384179036010303007021406a600000180f0034100418606402a0440e40c5070302501e104150480340541c65501c01034000d4170000c980540d07140102c0c2809400d5034075104580044a1601e6182c806010100c0748500744580d040b258800d0031110522907034614003508201035020f0042c14640503000358404140410144600310101ca810311840c03042c1d007250400c40f00071f021400c0c8400320600700e203024514038100c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865737482 1250 865736232 865736239
    0x203130e01080619230a05160f0509010306090501140a0b1e0306030c12030406031a0f040b031f140a0b01090e070c080705070e101202010f05220510050a08060609 71
    0x328224940303a0804c03942c5e0390380c009500f02c41030f09009211a42e40101940300707060281c21156003200101c000d10201c0c08094040411074086011065030b0300c00d400ca40c008184501c001e100300e58441c10384100f01c00e5841c003a07034030a60242d10001006408003051b10f161220081e603107a1060400759501c00941c2c0300078919985800b442d40c440e0b0071a641c3d401500094440c4000454803107060200203000ca5108081d650750351000380490302c1180d6101031400740301d450f0075600807480c03030480c10103e840c0084051010020000030b56440020503440e074030140550800b0340780c95005071140500d4030111510044c0050005108100521000344207020080c3c100701035140901c8807800e1074561602c544c108080485542d081840d040100b00781e4030000913002090301102820b06440d01041c0e280c8000804070013030501141040030401d490059040d500d001054070740d0349008254000000c14012031034001c0c0c1d403103643d040c01074442181c403070820b844426103140c031191160f454032010801d694000c80d1011f9030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865738732 1250 865737482 865737491
    0xc0f0409080c2808091009150e09070906050904050403110a0807060507050c0a110a0312080703060e011d0405010e0a0c03030f0c120e03011b0203130e01080619 70
    0x80c0da03500103103000e8801c44090a00703100c1c0f030a0000da4020092021034041040c801a41020841090031500800d9044658000c403540c0284180c9040c0130130b81c0484a01c40a104002c260a600304080e070b0044541111500748560320307104183c40c1c9401c9401404009a01800f00504c1c0e81882d6004680050003802d004054000040c1101d02d000680ea4044807052004500c2c2405c115090040702d40040da6824290b0500d880300400d1170340c801204001070401640d017000020540c42e1241e08501454001c001070f507a41d8184c98020b00321480c240c03201c80009107072030000144031303400110042c10383d400380390b910890404a1140500d202000350040c0c4165603584100d04c1c001c0000c02c00d040b45c051241234040600e9286083c01b800c2c403040144240148106a100f0b8400030350900910403000e40141000c0c0c010405160109006200000351070040108001c2c45c26422600000900800c20b15a207070464001d0301c900300c15184107000e224801090b0300c01d2002c00d039507510005a450804541d81030000e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865739982 1250 865738732 865738751
    0x10b16021005040e090105010e04032a03110c01030b01120b060f070606030c080d1b1e03031e2318100506090a0b011e0314150f09090c0f04 61
    0x40e145100014801c0109000140421001c03400c40e40303a030341c800c1441000f045650326207143c0c440500d5006100404002284000c42c40c0c05d506540e80410715454480d090b01c1e4100289005062040d07002c40b41c3e0302c10304c00d81c204608598407034011041061010383d6400103017440c0300b03240f070003401e90340300700aa121406220008060f0300400160a515009520100f603280c5582009484007506400c0020103410081080400e1500314040c411000d12070b0050005036101c41c03c06c2603000c03414500e101c801c507190b040c40206055041d0852403801c031032084020360319600242c80e001180c0e44605544030701202d0f150416040c007420501070750301c01a100c00250035071402030300c410b05200c1038010542d40c0c0c0b03903100b06100b410b0800701d2420f980444051801c001c0d18255900103052051120701e40c0c10b503403515921142466100780c01400d50300c0c945000404160400d448240c80403030080448900a4141040f801d41c01d2600d480e9142c0965482400b800d4007444840920010700281c0c0c9940c0e030020385424002c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865741232 1250 865739982 865739989
    0x20a05091e010f02070f140f060a0305010504180b191107080a0e1210050a1b030e0d0f0914010311030103050a02130c0e0402031f032a0e010b1602 64
    0x10300c0070440000c000303010019034600142840d0300610041013150301090080c86100701903611041510300d0051042414660a00011580090349605907003000000c42d00145890701600424142e850807075060007031000c210707484440e50040100c0909109040c0c8049a01020b040440051642c54004040b03000041905540d90342d90100c0c10894280c00c000400039101a0701115100003540b04841c890140c03240400015a00c220402c81c5a81072030b5a403020400408207030348030400200301201a418000081d40c0007a000385500744000c03145004159141006a10902c6005490a440d44552007442d08048500a143c00d43d400014149643d038a83e81941000b0400518000c5101d40700070007507403644d8070501018134644107400e038006003003942003201c05400c12100180804c06640050301d03950369186080c5110101d034003440f0000604400403007804450322902049620361060b102c02c0003440d403650128041103114810004400c9070041c0b0144c0f02c580000d01e04000a80100c000030452074000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865742482 1250 865741232 865741249
    0x503030703021c080103030e10170a150b0f041a0706060f14030c3109060b15040503120c030c0d0f170f0f040c18230613020a0509 57
    0xa03005a402110f4101000401c1000072042c89100c0c030344130b5030552555070003400041c500e01800e0b01c20a8076a9204106030310076001c0071007580d000428000c103800c00a003d04024040001d215840780c261070b6012465903001403c44025100c58a4023514203458440c8034141c51000c1d0311200c450050030803104020600a0165901030300ea20f80c03da0084034a011046464020340590320780c0a5040620b00c0405070707a0b40c0b2144c003082d85020100c00701c200340180810104081d0b01c0d040c020340310729049443e824404194031a818002013600d4014140081c1c8542c900c01d0700a51048640c5580410a40d4610211600c0078011524003401140d08050000d0503840c14041100300e20340009141004500711503a001401c0d035100c900d1b8901150709400c0070240c1091498009104c0c00c2c840c0d8022000c0350070010500309031030041c200d40441d0308404082c480868007401d00f459001c522040c80005200c0e400d00c9405035140540e2000f480e6034800341d0301e82058000b0b5000917450009005081c0003124140d1110100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865743732 1250 865742482 865742497
    0x304080f013201030303240305030a0e1210020d0b18090c040905060c0f07080310030318060507060506010e0d03020604020a0b03010602071403010920030d0318031206050303 76
    0x10440d030801d1048204040300041c0380500081d807050000300a020b0308141c0710f05482d05440c0105080c500c500040c0d0003941d0741341c03240900a219403000018010007002400300c005032640c03581500c101600402804407001c00803809540c010314a8041440804d0740140382c4200704101c0804c6000111001400003c0030400f10f16111680d1420819640c000380311200160b01c00f100c0400403548140c845c150b0f00c1100130301c80c020302c400c0086c00d80c010020000503115403075400303621699079141401180381e40c00301c20702c030450100b80f120000d0b03107104089410400a80c0c4041e515a03007403e26507118000a0080501114113011244506150f41c2e1079842800c0311650280e001004a4282481807100340e41082e0b00049a152082c0018459250301090050845000d0500721403010f03582c4c00001c0c01008406002000224200e202d5411003565803450140b510003103041d03030418020008182c0981d84202e01d034217072007001d2442120001c1d00801c0104075035400c0000010b013241e140d002103031842d8807012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865744982 1250 865743732 865743763
    0x406030c2313050603190908040807030311070602120a08060d02030706020a02150304030219291504110a11152e06090302040905030c07061809060e01050f03030408 72
    0x15002c28402c001c0c01000010101500d020b813a62030100b21000c050400c54580b18010754840c0507803c18041d26009a40140240000f59205581d0780c0c50007511000c450a003500440c001d600f400101a80046a02d244032559507035920b203030590301d040440c0d1740000181343c00d5005490700154009a00c04220050180140b50000c2c40d6406040c010452000710500307560b00b103280c007001007200103179006c103c3c1007031120706e4110601c0107045403810a6800302d80641c211020040c02c3c900f0300c034001021403c1da000c2c22039800c2d001c0400008c42d007480180c4070480f0030380b01e209408101035030710f4030300c244044500c55101d03506071040c00300b2081009500c80410344028846603002100d10002400c00b450194219038004444030880345406405030040b2284d100107031040ba6a40d02c104c060000c1802201e007002000010383d18102d84925000d4818500c101d1a1416031030220320201c5c01c00700500c0740b00245d03108203080d5000c5030b10b003004200340030050003845905030105000c0040c1000007042038040456100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865746232 1250 865744982 865744987
    0x1b010302160302210306030c060304021203070b0411030d020c06091201092a06270e041b0b040602061816030c1a0a0c1203110f0301090606020102090102030406030c23 73
    0x14044500d0b49100140d582100c1c1300070414000583d4001407100600070060b035030940c9075651030001496240d04001e02e030300b944c04005075080c00c0180c081000c510641c49100c1c0798547c41032a505050b40d4101496a100150340203568400c0b00d45401c50141800c0180100041c481250700c9100710700303541c441c0741e00315164000002404c0c000c1042c14540003846581e040310000c5c035460850014002c1d06480c0080880d00c2401c4494011710b007480803640003421921017007070b540c0d060501c0c1880400c4450032180303c8104009801048042c09030040740c04030380c020350041c0b2030740c2c807152035020100c005003d214803240700c1d4002002022054100d07483c01580195541d00f0f00c03030302d00907014032602221041b0b141a403d04200030b0300e0301500600d0414103203400c11201031081000f0f0703030207500400c1042c04d880301c1c0c040040341c5200144020002941615000d04041c0001c0366100b0301a400d178018042c5080c003582081c401800004e220740c5c08400c00343c1c214035100c0f60f401509400c0c4c908a8030500c0e04824541c100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865747482 1250 865746232 865746253
    0x309010b3a11041a0f040c0909020f09100f02330603070f0e1510080c03270a050f0a030203031b0f030a060314060c09041a06161b0303021b010302160302 67
    0x100c51103070180c100c2503409000c1460651f0004028410a00820b01c03025804500c11450001249c159032058074040d0241c0c082d0412010050300702501411294014072031a10300102e1200c0b0012266031800d041e2800310016200c00c00c0c00e240300360000340000d03014450100009107040c00c5044420040030b64505021840c2040074044c2d047d0441c2c04e555900072841d54603005510360740108456404210101016200d0f1070300030050008003d401080081c4440000390041183d0002c1003000d1403a00c44c0040300d42d41c0350940400c42d140c3d0030007200038000d0b03002440022005440e4042c000d40000c14580424500a071020618020b82c100b81d500d1503e1580c1c4400500c100100b520074502080ca555008200c1860071858148883c45201d0055000d55283d220407000e0b42591480c1c626905001001291901202101c0d04a0041c00c0007050707511501d0790303042d110502d45130343c40340d8256505a4081c00001d24580d070602003c1c3e941070020303410543c0c20012411101d41c0c0c0c0c281c0b25065486a80648a4481c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865748732 1250 865747482 865747489
    0x201020c0907030504031403191e0c09090e190605130b04050c0a090213090e011e0e060c12060118050303120103030f090f09110f0309010b3a11041a 65
    0x1100000f07c1034403080080c0006880c455900d005038003100440829040318214603182114400c3c020f17000790707500307120491501a4014400c5410b89070044020021070919407501e81d62101c00082407421413151004c1072022410701c2e0071103503000d0958001000500103a44e907882c0b052030110780a441c5a000350380100040e14040107a00000c2000d00c4041d410201688400e61002c51700e842050a6107640780c61302d441e4001d003900036610043d0150104601e504a88008a01038080050389404a01031040002d68110b1144262040c9019602c81c83c80f42d96111001510301091155a0654141d5032840014142d5020402482401c1166506900c25490740c85c010b0b101078511b50361a801d010700381d03030180814800031100c0d0045410030400401e401c11400550f441034400e444210202220000c00c00c40005c205403c01604d02e207040d200c001501c030303a4203512041410200c80b41050080c03048622004d81d8003000a04c5646401146100344202e82c0d4070004040364800090840451440c0003286071528 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865749982 1250 865748732 865748747
    0x53907180902120d1d04060518181510060804030f0c1e110909010b010c0609060209060423040b130e070b0a0c030e0604060c030807090506070c090506040b0306060d0201020c090703050403 82
    0xb00196000d001f00703401c1c0310000303c125940082550200d0410301c0003c0c070340f0841900c000382d0210301700191100351000d15048542090211082c03904440800c0c5d0000300301d842044010f1086030544c5c0c0c0c0b640454404041111403044000003034810503c0500d648404942c540d5036405a02d1050b0800c8142d514498240045882c00610ba8480c40c2d01d454542c008507600b1a02480c00e0301e5000d82c001038440060314001009010b0019015007016000c1004145420f422103680d418000c065011213094284004010940e4495920150080760000c41d1840940c11a007000c851102e41d81d054452060f01c40c180c81d801c42c1c100c004c2d01c00009240c00f0740c10040c19080100c101000c0801d84181e4a003d0800ba400350211041d20b600908118082c4002100544961b070358202804008220650714182d80c10005a00d43e1540a1205030928000204904e4a4548904a480071000d009003516584060406c5960841c80340c1c00d82c10b600400340c49884580d100c1120600c0b503191a01c0c00035490409050050189 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865751232 1250 865749982 865750037
    0x18031201030b1f051003020c011109011e2102160605060a05041b0e031c090e0c132309090601170d080610053907180902120d 55
    0x400500c40c3c00d014904940701500280d0728181c81d01880b1101e00761080f0001d104070850b241036035283c0502c41007841d030742400908151034240d03140008800d118042d40700802050312020045640c3d0300381d05110f40d90036000d0f00308000710329600505041003070b2104405050b1403801141e490b039030b4908010b0146007041c0c00c0400741106640030000b0709204100800341607212248170007406440d085598090390304100c0e0320b20003503d00052400140400300d020f8450070f001c4c0900c40782c0f580f41d000010004860282a100002c03018100301c0440381c580b01001301d80709003883d029880d000c1c4144483c0320303e454514506018035400001400300790324100801400800702502c0780708540150203920034048e48072601d80e801240482e041841e10b04a208159468820074001c034055054180c144201f40960b0b131100c0702e0322a58550700d294402444400603460320750701c2c007800011f1989400440b90002d20380d803240c0d40483c8050000076148101c00501894035422905400018400a0150102026009d82030b0080c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865752482 1250 865751232 865751251
    0x171006120c140702040905030f0703030609140708070207080d32041707090e0f070b09010f031503050f0a030f032304020d0b1515040b04050918031201030b 68
    0x4200d5032040240038841c1010100402d48000c1094025944d032036100c0301700346030b01c8012a55244e401070110305080c1c20400c0c094000c02e00e4541c0000c5c00310154002d4a04140f09102c418600d0765a03c0f50559201c00040d1a510452191010200d01c25034104807100031101107848031458002c0314540030f54001079803100480030a45039034402c001d03030203074005039000d4400700b1051000303500c24107031068544041c1c2d6000b5203026040c156400c3c180807012400c8a0302c0c2800701e0580e40180d84404840c0014412594540d0010f42102680301600d4803a074000f00440039441d88691003999681c6480e03150043c103031030303220b0243c2150100d11f0415412500200411030941001d01042c07000566400038000700381040c29501c50203d000608556403c612a20210781c48051200141813091403410021918030034a80607420800344044804560800d0740e04640c10f60f4000c0d0326180c11b040510043c02405450100000c540358120000c01c0e10510103001099082141c0310f5856165084c506070084002c1e00c110b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865753732 1250 865752482 865752491
    0x5090a0f080a030f1205010608161112180307080105010e1302180601020a021e1005122d070e010e0d030e01050f0d02131517070f17100612 61
    0x44100802d18140c541d40504000c0e20407621090f09540c031410620014101920348030010600e2500401000d01a02c8008441c01c4002c010310b000781c547c1d1001c02410322140d0300650715070140c195035100910b20200d1011076003100070f00d440e0200c0d1034000590050718141e51030b02c0c010303c511b00003142845e600401614110036062002d0300810509010348642c02d0040c258900001e8090b402040040c2d0349a6025154100c003e41e070482c101c00380e2071f10320360861080f481e00660007110341c801e909941040d01d4401010145455407080003605458858882040410802d62070482030445804203100b20102e4551031100308058000510102c091100103120f940004a4a03011039481709165a02010a0030a25540c0ca03503e0407402c04d0340a104040107134a4000540c00e18500081c8407113004a94542d40300040c61245400300b61046403d00c01c4196a00e20759100142110384910640120220642020803925001040b91480004101d640d0555072071351060401416901034059105541e01000800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865754982 1250 865753732 865753739
    0xa0c0206070c02010804032a0204151a0703020a140a110603071d0105090a141003110307030c180e0702151005010c020a0e272103070908010c05090a0f 66
    0x400b011000030001c0e04022440000808050054500700e00071038a219240d8503a030614940240e442c0740d141b1080303009038103041101c42450804001c401c1541c924500d01102104090210a0560044182a01103101c0c0b1000310b400b285507850400e801c40d8402d8068503400295091055800c401c0e9188a409040100700b041445940704121440032407440120007a036042c420012107460098121103640490210000640c00d1356610405001c48002d4800301d44600740608150304980a01c241d030741300c08400300001030205102e03601500c03190031542412107402c1c504c108640c80405258001c190101007600902030b0054040120b030070451700f03280d040106460011a80c0300080c400c0d10400703041c000c00100c1042155500303540e98001e055103452070889482d00d0f0205c000d0740c10600c0b041d285250742c48044620100380c046011300c960440315080c0d4020700d503130400d08411980001e0003a4100400d182011032210001e018400310003c1c2c60b40d07450303103a04a440c208581c0100c00d520680300800c1005080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865756232 1250 865754982 865754987
    0xb0c04140d021323010b0d0b0406120206160b0c04060206090a15090807330e0325020a0321020304050307060516050d02160602030915030a11040e0a0c020607 69
    0x1080440584580403607060313040001c9081e41034021480c00c401c0c1c0d44600021410704091000380c483c06603200c00c24808014900144000c9610701d0280090b074030203c5d0512070242c14914014001d07104a541500b045920944030214030320010f445220f80e07035a0000c2e00300569541040360399001518280944400fa1095071407174944010300080d403020b1500c0d05c2640051040c4482645d1040d50800b000124030788000d507010243c4070b0001c242c03050754020040d21070180c500c40d00c20720030b070710038013200551624a04540c207440e880401514444408081601040140c4030b0b103400e0f000840c450620f9501080c49420400c0c48035106090340001c41d40203004c10411582c00003425801c8841505045035540001241412086000c50b80908544607000500d0015607000440c0682817142c2901d40610325101d010403a100d1145c0044203501c500b10010072200300c0400d100550f00a40303050400074100c2e441c0102d43c44131780c0007640004000c0091008019451001c1e0003550f800400900c0030301402d20341114003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865757482 1250 865756232 865756249
    0x20901060e1e01031107050706081305060403080a0608030a090503060a0b03070902070807200a0b0f18010905030d03150b0903030d050c270411131a070b0c04140d02 72
    0x2c10705481031403207806010782d0296004548072100c0481c9155a080d09080c81030362a42c0300d2250000281c51100000c040047c105101c80303c1301e511001500403a211520129a0200b014041c1c04241c1d0750f40e440054510f0701080141058602d81d150345801070301c0c0404060400c00c005000b8024107003002c103454115540440d804050b580340200041c1c403003035141030444032030080600040103030245226030900980c0381d08030075150070002c48260909a84401d4140100d024a500c024403a100030b00c00c00c5e4032004402418094040c06241181080e40d6801c0041d2811201c5282c032400329541e11801080201c0418450010748a03107a0204e03d00f01c811400300381e6034403031090242c0c442561072011800f00d00000c0c045a03040849526503251502d80c80341d558600c1141c840303000d13100d00d180042000d038141d1454151100402d2500d0180019803030082c00b01c801d81c4503500f111101038410440d080000c0c0030f40840e2400303950707081c541646650902d566000001d200010b1103200e5003008420000586c0c82e2102c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865758732 1250 865757482 865757509
    0x403020706181205121b0606011d01110c100e03011803140a03020c0303010b040602010b300a060c050403050d0503090a060b0d0506070e0118030b0414070e01080a020901060e 76
    0x20010842c3e10307007001c50501c5800030001c2403842000458000f405a01c0f42d5000400d01d03804c4c203586454403186c005449900c19061040b403c2490403110700345640c06812042c0c817000d0300b20142d5500b4141c0400003184040c1440358100440e00701c0c2c1032241c40b070a00741714200e103102d0b04c0c41813001d4410307841d01d0107050f4103241c1300702032140d00c400104080d8240c481c0d01516011813540c011a0740313a5840700c140c020190031a010712070041d8600340080c0f1380340c6808551042c0c00360705581d034141c0840e201001290f0f03002c0317205003a1505e40309126000000402038440c80c5074450040e6903d07030700c481c1541f4000e070070915250400030030880b0500c24040c2d280c0000c585a441d441e40641c1c0090290820008626502c600140c058880d004100030004440d402c40602407240b038003680d858541c1c0e04140d1120001ca00300d07020140a14101c03030000360001d10403241001d10501401d04864aa81c0d4440e030b074141001c000d8104d2641a042400802d08500700711284502509035410039080c6901d52401042c3c41c280d2801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865759982 1250 865758732 865758749
    0x13181208070315180e030403080c060403080604051e0c130906051801060203040510030e03031e010504060f120f020d03050703080f01180f0209040f0243020a0e04030305040302070618 80
    0x80881c005e008040085070001c40c0d000d2006034807184c0c00444c1d9502d03010300f141d041d004140040005000e03407070a80315091040c0103038100850710083e03a18000003900c0f002080c002009404200c0106404481c00122005198102c00883e05905150034010b00340034a489204d0505804401803200300d401000307076400d954082e12440790314415004201c01600301c02403103a1450100205000f01c0c403140d8114000809a0340343c0c418541d90381c0341d00340700c1110800d2281d00030220b0842c0c0e0900c43c462814803e1100a0300504134020f820750680c0029810301c2002d102100402d0000a000e408c02d600700d000958026080e454028507503141161280340c00350018884a07080303565a82c480347e5003c00394140c49556002500400a40003241041802580401440b03064601501041030701c4082c008001c07585981000d604062407200b5202c1044a58441d510891380581940c60204104500c00701c0c0ca44110700070350f0301040c5824603080107410080c894201000700440004a0340d507081c0300c580d4480c100d0b81c2a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865761232 1250 865759982 865759991
    0x70f030e0c0a0314060601090f06050306130615110a022110020a03060801061509120c03050a1a09010b0303090111070e010909050708010b1318120807031518 69
    0x1403590078101518012000e920601c601008403d0101d2003000d14280f80c409402ca0308152074070300054032402c000388218140903990310014041148107030040c41d0001800741014036001e604c0380032030050700c0441e0009c0b40417001c2c00c0700d10322813103a00103000403400390200060300c2c13101c0864001c60121012501285041080c45010320902d81040002400b00245010304540712803022030014090700b12031051a0b519800c20502080d5420002c0020000300c506481e070a424a00e40a00c032002d40892280c1903940390a10f840002c0410414040d01505501c903580c001110820806034940c2c03108080e01d0f2050b10382c5010507249054038008115541c00c6000d00f0a01d45112450000074585545500410014104140001020809500481101c0c1d1191059455541e210300d4998200c4010062007507000355450721044144806600c00f04090001c50342801401c00e160301ca042701102c028072201c002a03550800c11118690510a07550f02021909040c00841e1600f07a050302035010b00310207802041e548 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865762482 1250 865761232 865761251
    0x303020a1107090b01020c04020316080c070602040909060608031911030c0106030b0105010f051c183507020916031b080f06060a120c09091104090b01020105070f03 72
    0x307104030151901ca4104541480d61034150840140038242031260251041a095105500d0a8000e90380325109a5980c0c940d05000c20310122303240f1401920846100104000380d40125009000070800b6110780c20020580c1019450300301d0881d05990300401890300144840500f2200700040d01c0110340341c0d85030210300382c44c1034200c00b8118400c400b0049040d619044002040040c1c0b861000c0c120f0344242c0f21200070805001d02603d041c03264145a403114092904542c4840b0b00c0e580c8040c406607824000103405203890342d9400d6412100311030540342c80140d440302c0c10380080f40c110005210484c46c002c4030700b0b2141c203070702150000102802994580041c01401503c55209901c46120b207452109550001848008046c0c228a002c0c2c501403074058200000070701908000b401c8030019196990b59062410441010100070690508400108026030000080303c007880d0007090407014000b2036155503070b4a0070a040085075600381d405819a4107007800c01002c250001004890140b0500700803030401c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865763732 1250 865762482 865762487
    0x2060d050c040801090302010e15040201170c0f030903030a1a2d0d0b15010309080d0c020f0709060603150e13060f110301050909060c0a050a050708070614010b0310030303020a 77
    0x5260043d00040d80303406203050500d40c0c15000812400c084005540040302d08102c1d12901000c225000381c0413420181149079074000d82c2c21842c0c0d110600001c034500704858804061290303030080d507024207290720100c01c0c04688200342c4148981c0e00396191036601c449a9400226081e81c0000040c1c084107410906480c00c0315000c452414101c840c010002e50000a140ca042400400b0a845101000b5032042c02d58845501900c1612000c035002004a03050000304088130014003966210307903085000d410a050b0720304000308030322405400210408182d0504101000b8102ca41d011144180480740e000c0400c1001109128150414141c8052980800c000c0c200000501500024000c0140c5030034500c602c9403d580c000b0f035040c0e03030b0120b8911490b6142d0701415562460251403460811000300103203031945025800030003480c2e00c2030600d9070401050f0745642e91f041c1c0242c1c50a9a095488105001d02000d0000103503016002c070303003461411070900703010100d605a214080103080c503900203102c001ea5030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865764982 1250 865763732 865763737
    0x706051b01060306020403031d0303040b0c012d11270612040f2f040b0d050f030304060501060c0c0519180b102a0f170306100c02060d050c 61
    0x12950001e100d016a04d1508000a40c000c0c40141d0000b80200c82001c1c461000c880fa2046e6404000c00442c2024148860155154484080c0404540da01c07407065205501e0001c01c0741880d00b81001000f02c62a0700c021101c1910024900d05045003001c0104143c80e0780c132200c0940040c0c0310041c0c11007902c084c41001c01c0345841070100c0c11802c4240c000811080120303541031800d41c00d20400fa84110700380302144244000d030fa140101041c004001a040e00c071401c10354018038007000300a01a180c0c00040fa284e080c01e1602004044184d03030070000403c03051142a0040780d00401080c035003410591030070703220341e09a8240380c0500d91058408259000a071608058804c0c040c004248924201e0f85400ba042c1e4000c14401049600541000a025090b64000c1c449141d100a20780f0303225006031005015000c003010916030494407102144450004501008407043c561868003404551ba1b09280c801c1000c048540703400da42c1007040c061900030060b15103c2c16581d02620b400c00c003240988482c09482a90b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865766232 1250 865764982 865765027
    0x309090103080c07260c010801080a0609062711120d0507150203070c050d0e010903020909010e060f1005090420030a021e01141e03090a020a03120f080702070605 71
    0x14800628504016920170701140021412030111036003a1685801921000c40074401c0e003445810034604000881c0464101140203807090b900095001401e20040e80b220041c41780601204002c084001c0400502c091400745a0701c04407200c6480351964000c00795601c844c5188c4004004c004200001000200500380041980c0488159140d14103a4030040c030002c40c030181500d1511491000f0b528060041000c014101c03410307510203640500756003d02080d801e01a00b40411503603a103002001c000d4040c030045006507d50704108403141415000600c0507001604114411100e9500b40400a00101c40344806e080101a8008002c6031400000c0c1c01c20000c070344082d400864007802295006024400018401c0c003d0321410f28044542c4941151030260513003441040c01540103228040c65510701840d802070507541141c029034401e501051615035250301c1194200234002c1145011900411a80070f0306030301e403910120300e14110070029038034482da1080c10180003001400301d00000156141d06c0a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865767482 1250 865766232 865766249
    0x7020d0f02090c0d0c080702060115091203031506031a330c01060603060311061e0f031504050f041103030c1e0607111f1b030b09090309090103080c07 66
    0x183c1c41d000001c4001c903408070840303030001c034604010441204d004000d0580218010340c0102180ea09010070940d00c0324402115030280013019a002402d103000c0c1c4480c1d40707510f200f9a40840c110f00c21842c056000d03069900510149800d000400744114090304201c01c510000704d4190401c90b040c400350140d0001385140502401c5100042d4500745801d010042000302000c5008214883d81c0780011011180c040c080101607298110f00b0b950300380780550241608071516818161b00c01a4403254003416800702c1050106110040100b0442c1c40000c0309500d400c42e0191018002c900e41ba0f544455100801040200720070b590301c00b006400c4d1000c000351042000d41d201201c05020404080102c1030926135044041445074031f0008410f14030484615002c03902a000519100031050481000040e0300300080c11155611800d191040c0b540090b00e800759003c5850010b40001c01c00d00344011007900810b04501036200308040300d581c5c0c030b50108135811a07820200c040d440d40d0307000c40701034104034299118089 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865768732 1250 865767482 865767499
    0x121305092a04080f011401120c03020904080c060a0b0102011808090d05030f07080403050f070506030106120906060605070b0609010506120402040f06062a03050d0209030114090c1302040b07020d0f02 87
    0x1000c101540176550a042080306d1600702d0f170340d0714020400400c1450f0010103010400d24100014146040140d41051089207454181fa048001d0340c0c0c9008400c0b00c0390b44100381c070303030042c120305503028818421110030840c80310304482d00d9521400030764440c40072407d004003850300f8000244807051050300c41c0358045044143d035070500b6013000202504107010685490040c0783d00c442d003404001544130100c8001800150035607207000c200b554084a4040500c081c10307150100b600020741079106580282901c0c0d04c80300c0d100c6c07101d070034014900f0000605080c01000b84130b00600c01da03a03814040d540c840700d961030710031880d5a55201080c06065288200c090b01802c0c103001041803600042d4502241e02012000c030000080a8080404a50a0764001d40030900801502c0e00c40c0c1282d400401011601500100b03009082c4224824031200031140c55a4a0700901d503c10998035002028441087c06a40e065040c5070506150349140c0c46130210081c45401d415500707a041085c02c448001609800406500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865769982 1250 865768732 865768753
    0x80709060c02190506131e15080406060308031003052e0c090b070b04050d1403150f13050a060501031e091b29070b010605031305121305092a0408 64
    0x41555907501905d0317180111a000c19a10905803c07684048940c00e03402e20041400300d8072300b0340c1c2981001e4030550761507446600202c04103048400650042d8600444807207010704e1420135900303042c81c40702a00d604994a11941d0a030b8118002811130302080140c00003a044c201c058182c0b171480341980015942c82021070250103000750600c03550310680c0280c0580f0299000010103d80c4810100e081078072100c024004243c80d8050140c2581180b803014007038158940003100021081c046001c070070804c0980b181c00308600c0508a00400d401030100303080500100e40b1503da861071300381c41c10dc03000c2009a5158902424412180d40591490040301104a5100d864901330110040481c0c3c10401c8003e080000110444180003101d8007550403070203003190b80e420480c0440b020351001d0400e0301c40c0701556401c3c3c13000c124240022004140c0c0b842b419907850b80e64a418200103686940a288180c0a1404001c031b50002c040702045405080c030f281104076a0408100604c5001b29081214a03200701003288 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865771232 1250 865769982 865770007
    0x20c06010801140106080c03010e101809061a1f05040f0b04030219150c0303020d0c0905090c0a020d0e0402070b01030510050c04050d03140424080709060c02190506 72
    0x40b10042c1d1400d040e00c0366a80c07909001e58106c0380070f840003003884c0c80c00c00041020541d800d140321b030011403102203d0029503581c103075000c000c074100030a140001d60341c281e8030b030400005121704040061120400300362802108002030701d107030700c0780c00540905941034940c1c251248110101d40c00741022490040000307445415101180d04a80030890058241415001540301071840703038070031a031000780008110140b0384021655070503144030803000d040d02404103000c40d0500c1e0241030408003003070703891a10041c9458204004141c028103c00702401003000f40c0500c0660200d0070320905551800c4c44114081d4071400314009201e14580034140c3d240460001c81000710125607088401c1d0440c10600682d1241078800309648244d01c980c2c0e42c041d031007030307100c80000b40a010f02009056035211442c2c1465070b01d944c8400c0300d013000c04410a031400f5981d010812590480c50064001940307142c152601400d01e0b002501e203000120020b031003180170341c6001080102c981c0c0440d0142401410301512281e520184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865772482 1250 865771232 865771241
    0x41a060403140105090a080427021602011202210c04320102010c0f03090c05040c0801030b0c07050a080d0e010c02010b1201050606070f02030a08160b0a0c0e01080a020c06010801 78
    0x484a80f5401c1001042012200040c0107080580103101e4520780b030710344050240444a468591502261409004040300c0742501c0a80301746e100800c0c050760b20303600d2840014490510741007200030803403041c0712400a418a20074040000c080c83c00c0b45821a4495480051032030180d82e00160052800d4040003201c40900150740504e070740c008940311000c200c000c005a0074ac41d00c40c0c1c0d10000040f021822049064803e410241c0124001c03400f03078901d00d895401040030794507035041f05000b00b0314102c010003c0040380700c0d0940e840300d003c4604034184055030f0b4499440c3c5030500c030f0280124802140902007121283c0c0840300344102e400080102c0c402e50600030703001e010304000c400d10480300c9001016007900c040c001c0342e00c9124014122440c00c1410f9688007080710001c003059801d482000d05e0500018001d400506030a140a02c400c1c195042a180440310a800181b00003025810b15078423000864022621314209042403e0441d00d80d60396003070300e000900510400020521402c03000060085041d4030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865773732 1250 865772482 865772513
    0x1d10210b0a020a0305070c02130507110a11012606040903110a060b010f090e0c220905040b06040209090f07022a0306150102030703031a0406140a05031b041a060403 72
    0x400303006940d05e01b50196201503003c0406900700c94111804001c03245240c0c030196006800781454894501c11524603842d000308110215072440d0b45140d44101c6680041e004119618910601240e410709444500c68901e40a0b1800340110b40700c003100800c060007400b55041406078942290b1800341942050806000403108181c00b04401c0542c6403511440792410405031411400912410b0f101c103100540385038400403000040d000c40b6480685e1144146072588001d000318140442c50b030929040065a644010700400e20503841040380303034078648518001c50fa00008240a2611079500d800c000e90902c0c40140c094080340c091f00c03180c900e002d99040c003a0007881d842036080715040da41d44802d0003074100c950407020740035a2051000000292103500328910401c804400d44084d04c00500129003919003c1c0c002241540d800c8545a0040c1440d40e0264002c2c5422030007031043c440c40c44848000c00704e820032828011500c0300180f020400c2004914288904003030f0440d80c0d90b6039a402c140207407604041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865774982 1250 865773732 865773737
    0x1090606060f1b1a09030301081002040f030b18010204090f050603070501090509070519030e150606091203132402071404020304060b04050901061d10210b0a020a 71
    0x200124007984590111001c4142940326182d030035040c0c03825005943d00d40301c011160140d81d8102c400313561000d00d8016000d40c00c448000c540702d50404441f03600b400031200304208124030510040050704140e0080e4002c50350444108121074407000d0b40302d007091445106001c6a0340c0006800148500d86510405080ba0f03050400c100f00c0d02e41070201900d40b50544a042c0c0000c241020510462401482003508000e460814918004503402d4403030b804900c078181c81010a581c1d80345800301b46805d000d04c40c0380c50509548040035180060000c0d406020340800c03203000e9498a141c10582d604100121020035800d0642100d40d40d80d02d05a500050a021f09180000e00c0c1030500448041d00000e052010750700503901880a055116060000a400091081e41c000383c60312000002c540346c2d407142a000d45002c90010948a04001c3e010700d0030801040c9011041d0f44040402c1100701000d44d401c0c0c01c3e20765507204800132180c90501d01000788203410000c0c00c0070a443c42404141170341503005101844164 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865776232 1250 865774982 865774991
    0xd0614010905010e030c060c030705010e0a030e0405040c150306030c151704030804171615050c120a0902150a08010f120b1801060f0303080f010f1203050c0c0909010906 74
    0x7403004466542d04c038000f00c3d4140d4041c8401c000c9918102028290481191081f00e060140302c1d2515030a648c4010b02100841d045000d5850606500014a88600000740c609000c5410309980f61114001180321310b10039008082c80402100c0d2080d0090300003103801c07048912490340c5604103440c170101d10801c0710340407030380d071203581601001d50303084c1c0034840c541507214035001e1303a1151103001e00c1480c410060f0308005010014111004607203580003100c6801b411100942d5004c0d85224403c40754060070b081c048220178081d8000c03085280d03054542c030000d41840403d40040602c0419581c0d80c0e40300324210f8188000c0f03104802c043d03200700420704071080b440c2e01d81d2030b06580319141036560001c43e20180040c1d03407076400200303a820180040085407a560000181d5959a02c444909041c00c9810490000b172005003800080b086c1030f000329001d0f00904401e2846a85481100c4440d11212807005003131203000b03d404c0ba4019428030440c0b035104d602611580e503500d01281100d00a12a03008202c0d9410b180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865777482 1250 865776232 865776239
    0xe13020d052410050319380906070509030c010c02030a1a100506030c0409090f06020a020a030e0405060307032a030c0905280f061203050304140604080409020307050d06140109 77
    0x135507620f1407000c01b10b403d61440d9140c1c4413114a80d40482e00c04d40d880c07080c00c0300f00c3c841e2000326406800d00c840c02240c0c0c0001d420440f640d142400805003941040148c1400030b0b6819136000b140c0a04410300900f411480100c4038400700c0d08060001001406510291a941002d4003801c08000d02c110344944d44c1d50b40c402c1c1c558080050a0000392112101b01d4003c1c442440703043c40036400f041c01c40b40945420480c3d4015130b92100160380c0020065401600109003006c20560072030604808001c040341c0a00251a010011030740d038800c0b80c403028061400f4100801030b10082808040780504141451030f814540300e06103152201c40038803442208074680400a83d02d0311950f0030600401c2c50340848490082c020181034406490b0000c95054216a20300c2c0000e0340c07021011403890301a00c07079283c2580342e00d8103085c1905501d0050398501c805402c21420440000d10042c100c1c0e00f0341d444080011b032240c0750302c8000c036400e000d800f00d030002e4140b0b0100040381c04200043c000101c00401d80e5010643c03502c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865778732 1250 865777482 865777489
    0x70c02131104050105070201051209070f0b0f0a140d09111513030813080109291909060b03030a030f0b030c01120f0917070c0e13020d05241005 63
    0x71004001c484400900c0140700b07643c4240020300c0e00c607005140c000d06100384210000c0da8008150744030451a4482c960402500d010300c44050006d00301c18840c02c0c01c10407011200010740c807902401504020818074040101e101c2d1000761130444400100420900d4403620f040155035042c14100342c4107045180604588018480c01c41e00b1040d03060785113480e4240b85039203000f201c1c1c1102050368a03000d907103100030484440902c90120082d0040020301c440824014803802c0341c030011040d98041481440401c07071211200004841c8001c000711000443c00028140700340103083e442e903c030341d041c0400150f4a00156140c2c010380540350703040c001040019181c00c10141d441c10242c108501092410003003410140c04c540c001030360105035801c0402e0050a5a503109001900c0281d255404100410280e00b40010f140381b020180064030480340c807a0a0288401001400c60b0300c000344100c402042e41030801600f4031031090040584940564040040410f48088200440d21a0540d00411100081614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865779982 1250 865778732 865778741
    0x11502010b04050720070b0c010515030a1e0f0b07020d090f1836110405010e040b130215070219050603181f020a02010f0e0607050a17070c0213 63
    0x550791103140448030b200301010b10050341d01d1407481790b9000310320000910700c01010040c5907580c4018000202e5103400c2e151328204819500480b4000c0d400480c030000003441c1007050b2035940c03c0104071031805c3d0b091480c1102c030702602168001e201030940b0051101c410f40014560300101640d44800e41390301c1c1c03100e0f4255920703404c034410060500ea400482d085441e50356170010115900511013207407400500c403400b4101075801c0b41001810b000c07102007a41030000305101d000010000721411f00071945032054850707951401400c0541090034000128403000709200c1284000c5d0b90283c0361101c1c0b007902040f01c090540110f24264012450a0400346030202c403041d5042c00d9a90060020382542c0f11000c44038020b5400009000503031007000340307090244aa880c43c2100c0000c0325800903a40b952901c10090030b40b50300c2c81a0324460703410710307070114038811000c107080c0d038803144500d012900d416414600f140c0200d001581102d141003a1002c1c41130140c1c0c004510292240207442c9200c03001000c0100c10200d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865781232 1250 865779982 865779991
    0x3030a05030a180213020a09030209150108010e0c03040320150907270c02210307030b0f0f060f27030106081c0c0812090607030f02120c03070512011502010b0405 71
    0x2820004c0c6400700c00d1705038003501803c0e0321032414508207501ca60100c1c846480c01c3c1c2d0046000c45003010280415a44503059502401c016508270f010742c206614401110702010b080142803080c2c24007200740150000e0300d00c501daa1401d404440f4440c0341c0320040c489201040c1d40459a07402840c001044075011503880103425501c1c00950101c1052190301c180060200b0802a021801100421301c22500c5514070122043d104010f0680e42e402c0180015007180c0c16000418000c2044405280751583e9000d00042c2000c425229241e0744c403018540d10b500b42c03194250040040601d814070b00171007000c1b10442010840240d00030000d1a45800007035507904020942804899864001480c01c588136031403945805204105c00b505240c1c072600c042c5d808610403180c2851a6000404103d2107a906006200821000010451810b00c211214072400d1200a220f240c2e4030700000046038640e442041200c488410840001d415542c45a42d144105c1010107545801582468004032881c5820311445004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865782482 1250 865781232 865781239
    0x10e0a03020a02090a09080307020c090a0b0108070f0207080712060b060343051e0a0f0819020c060702010c05040b04090b0411190216030c18090203030a05030a1802 72
    0x42c038102c1d801c0042d448401003410540d41d4a81040c8030004010f1009540501d07600d4001e030002010302c0042c0140c0c1e010083c00107603441e0401e84c40308800d03600000341c241c0155607480d00c0001042c540c47c05914208859010343c04a00c24160b00041c0100d10320f00d5181d40038881c0f002403010f144c16004110f41404180ea550b49000036246514468500c0701c080791150004e0341e800125048000504103084960550008002c5030000950300c1e01400c0b00455403c610204032549800c100a85c00b00500852904072000f09010841000c40c014403c90844c425094003100c0041d580c0c0c0c40443e011607191002503a041d000356003041919214680144140e505450684141034140380c941a4080040c00e21070341c0080c0c000755110394904100444800421507502c401500e041042008040240b41c804050000900b83c4045841440060120103080003140d42030810f0915440325401018020051100c0080d498800081c070080e810b40c021002d14841e002c68502000b80000e0030404100312a11039900952 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865783732 1250 865782482 865782493
    0x5100e03090d060b06030709240e1e031002040f080a0201170c070b01030506190203041e0804081005010e06010c050a0615050d050601080c010c120509040f1409010e0a0302 75
    0x2031500b0520440c0303031403c0c000d800100702c69109201050f495402900c00303c2c00180c0d0301409001410044070340c016080d250b00c011248040704188014995241809114883c028460301d03168656541c103d002110787c0002d0583c0c4a40905200c984c0081d846071050012010041600054505011401c003000907010707100c141e1180ac510703036101e00c40c6a004003200c81c240703024081000400c0d40885018042e5208100504050904110540b1005100c052044d1501d004104100c001000d06e24280203110b2103c11000303032a100d900d400171550155401c08045485420380e001c00498040c0c003e50b04a40c42821030030250b031511001169182e01001014103c1e034010700d14540000c10603030044114414052170311503865210700000f015540f1000081e030b602d0f4400001406121020f10040704251000d080940189515990301c412440201101109122010a420016440b01d40020746007200d109000c100490542044182011055031918140e62a00c500d009200c0301c0040c040504c550590000c00c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865784982 1250 865783732 865783747
    0x1061e060c1502031b03040312050a060302060708091c06020a08010b0c03071128210f120c08160302120c1f060305010603200910210c08070305100e03 66
    0xb000b80d44040e008000001d80300d4075114001140402450145220b40d945610b000f40c0700c5424001c2d10000f80c000a65203250403420001682c0c2c680803900c03c0c6500c00385094464000f42c001038042c119052603510031080a8024104018556000700402007954550b034080f6621055141650f00030f00708401c0e003079801040280c020940641d01001c0490000b03103400c020301c2c00342c40d00564032011019600020303030800d2018001040d540a80861400c500c0c0460b9410ba00582c4821a01401d20007003c0c20810303000101000461044030507040203500b142881c1d0340d41010100c441151000c2180c250018060928841109428035049600500d804030013000402c500180b2000340c10b580150000c5419034030702000000550a000f0440210f000f1880841400036030b9000e44c40381030803c0e03402481100c0b508100542140381041940c103031169040607155200700002850200350207400701801c0e8600782d200c0018400800140c910640344154203961428040c0382c41c0c035059410310380007013540d40c001b400f201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865786232 1250 865784982 865785023
    0x17030406050a0c02041e02040f05061e030907030c270e0304091a090906011505040f0e1806270a020f4b120a08030a0e01061e060c 57
    0x495180014000503090b50b003906d0401d030110041440c61251900440c0400c036101c490300201d4010002a40d0040c80d2080c140c2ca440c0c1c008410f08050b000c801000310118001c420100420710103154004032201d01142c58201d440d4181642c1c04040709142400d0802c102c2e03542e41401485609141038004504081c141042d400140041000d802c20000c07035440b840085540c1d040c10b40d03000d428404080d00c515410300b10401240c180780320900041c01002c1004205031200e542d50107040302d4036a140e40c0313166120b01c190b40c00c03049440440455070744a203005100807504050644501920041c400701070b60101c0c507a60541f500d00d180c00c060b602410b501c00d40741d00c81c280041c040300c07442c200c03041646101c00d811018405c00c5540c0b001080034170a081c010075145118070010303050402021a192620150b500500135621100045c000f4544000880814030f024450303041402211040380017804020b4950b03034100142c0c16020794980917074030100800140da41c010a0386401c030603007000d9050340300c0c0e0142c80003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865787482 1250 865786232 865786247
    0xb0117040605060111100b0a1a030a05100312080907120f0b0601020c0316030c240e03010b0a0602060a05010909030f0f020c040614030f0105070504051207150917030406050a 76
    0x804d0600204444014170300f407080c0103064448624a0000840c07d804806000c1d83e1b80b0346410200a500c01c03440c485010013011020ba030b0380a6101e01c00401c85580e031906552032611aa80000c4c6245c0059140720601d0750413481c92071040d000c0f1022220450f075104540c54544440340c201038265a10740659001040050546c00c1d440391040c011a184002d011010910f000d010703074041000c84005050500811001e4404040100b580396a03400d41d05901840001075001c14208074810f004009030041c0d11902c0a40045070020720040043c400950740e801c0c06921400100c900036025881c18002080a140314400c210003030350555580040000d11620503100813506004007800e505ca59944260540e0b1070b4000e007400f402000e00400741040c0000103051400b18611900343c0c550341010200045207620505680440300e04413117081c480340b52000d0b214240b039030700e030080400700d0030b41c4d490f4032010350704100c110080310000c140c4c00061501d0018110740703a0049005041c001081080b4007900c2500c030b07408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865788732 1250 865787482 865787491
    0x1b0a091814010b030108070503010c0e0123031006080a02071a0403050903010f0f0e0c01270e0708071704080a0c02120f2d06040222050709090b0117040605 68
    0x4000421031041c101d169035805090b844601603040000051203140e0003800000c0043c142a0002e00610070000b101800040d5025440303410458842c094070b40020b09550981e02651400b14a296a82800c007410446031607540110804103450b180450200100c40c421503030156004541c004c68422405000c8011000241098007040800d004c1e0130785550b4203118880c085540301000041d8142819600c100b43c911040d80d107c882d800503519421603076040072210f2601c107090300700c2688048600590031a03c401c1c68000d03c00e61302004c010003100d03940144030f6a00451003501d60280c0e1040f0140244d0382448111402407110400707000b062401405171200e4802c0e2480200f9036540b091810321290b160000120603460107912030b0907100902921446640140c4059a90711400b403032401c440960390b800b002c0d000900821500c401503a240b040c540c10104840c403992410701840c182203000500d12040350058240a91a0901d00c81c41503014050542e010001d91120404680d102c2c0c035070100030b190051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865789982 1250 865788732 865788779
    0xd0806120708010f0f0e0a0204050a090812072709050a0623010806030a02090c0c160311030706110616030609141b3c070b1b0a09 57
    0x8014040c0c03400c140704a00c05041c1e150000507159107030300000010785001c3d1344080000c51502d072078078061000c0803a03103014040d010345002c201030f120240401c1c01080c1a640c060858800841c202c0c8139080345c1c205950140c0410740d41d01507208500c0c0d003804100081d1184c20b4015810b500c0041046c0d5a103034001a60000e009a00040c48a5071200020f100908160355409072903141c414600c029030b0441641500240180c00a0035400f00382e9001c40d811202c0580490b035910030124800184034000c00c104112580c003507050345511584da260040780740001544803486401000ca000c07440901c40c11840c0000d90f018002420a07072207980f000900300110444100030107460725070108404a20303005070701500d544441000c4080c070b045108036114607040b2081c00040c0c80c0811110203188442032504000074148a00d450329902841c401440c0300551041a038480000407138010140800480b0152180100c501e444008808100581301107204542f80080820100780c010301c5420300c0c030300f44074118902d640d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865791232 1250 865789982 865789999
    0xc031608070c090f060b0f120a0605060c1b010c02010e0907020111041203020c06040b120c040e010303030209030105090c360405070614210403121104090b0d050d0806 73
    0x986540b94401c90307a401c52034591340c071604060b40e00119403152070000c00c955202da41c02c0c101b2452000101740316058900c506e0191840c0480c0440000d036102200030b0200600603503541d940010380e02c0d1074001c0300c980c803080e548c60810302c484154010604071140c0c650513504c0c0220003005a08101d00f43d4000751501c400c641d40d420014a0f0b00700c000005001030b007108140b03030b01c10851500d00240b0b03001844941c035000e03020a000c10004c0c40d5000003030307640054a903c0d000355180d030b070300000b1451802103038400100400040000428150154010640c0410544c000e004996407180e02640d501c0544595a400c4000c061666001c8400c01d400384c0c46041d0b040519259198041c1c000400d081401e4501f503030780b0340008400300907140e04541c504809040050310b442c2405641004642940e154101c0c0200c1c01c224900014109071194204030b84003022010108981aa01580c102e929001402102c4a491910541ea0414904113000c4454164400010210358600f031900300c558090103454141c000d88103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865792482 1250 865791232 865791247
    0x2090f010c1b031b0b0421241d010207121b0501050117010c0906080c160218040c0801020702090a02070c180e010510080a031d040e01150603020c031608 67
    0x40c41d588000841c0203c03107800c0010400315042003880c1d5a60b10031a0342403020001008200750b0101c0c00304002d0725211a849800c400d904082d001c9070003010301108c00304039008000c0010442540b04181c51000d440c20760f40803200c2c8206c410308078400d0440180810a00b00c105601c0c9034410341c080d0f0036410003844e841c800310034150f9556003564002e81014107001c644101d12403003030b0401d01c1f401d40d5103200c40c40d006459070320b0207401405141010341850b44001380060318540d03071180300b050320242c1580900186040102c1c0403d0716803060b0305841c1114500540e03a400100b800050096400e216002401125661580c41100e402588800c00c119804801b83e280013601907039500c40e407114010310420110710381851440341821910700801000086904410601241d140011700000b15076042c10445440460fa1402c108958040a4081d0b842070400031503641d80301040d00301b030b580c001115808904281d1030704425010f074007920343e000409038024068400403d5040f02203581c1c2900902009141001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865793732 1250 865792482 865792523
    0xa0c240c0302030a0b24030403022d0111091815121c090f0504020307020f0d051206150313080705060a020304020f0a030b070e13150509070302090f010c 67
    0xca605030240829808010803041920382e002e80c0c2c80b07452049a441000d80590f070303440c010002d4040c036410030044c0f000c400901054020071108005154020200c0c414031000b0560940d410030101c0550001d508014070b059034020000d0070740b015105c0c010585100310705070491060201300000c002c0800360300e410140709119106ca02001c0510038204000d0042c80d4100c0c8110565060b102d42a0000c0002e20402040461500b240010940304200c0d405079413600c406c4412403070501000036580960240c902d6002c0780641100c000e10714052065200000ca90b1044100000c038030143e03901c403c2d590f4040000514181032481ca21601a11408040341003540ca0340303c0781e18005088a81d40c4d0740e26400820300055107000c140b800e1014008a03024001c090866840d1441ca01000d01003409011a82c22103180c503503140f400c6900c0d00c2d03017030303010030410f44501415004950803184200d9014000f940c0204000910034000c503400280054140301490302008011140c00300c15400031380d80b807140c042c9103003031408 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865794982 1250 865793732 865793741
    0x1207052b113f0c06011d040203060f041b15121b110304080a0308060a0806090d0e0a08030d060603111809060f06160314071511070506040b09010f020a0c24 68
    0x108140004c00d074540c10118001e400220907404082458000810000103a1700090041e0380040d56520600700380d1911b00e4510b015402c01e207440c1f410182041004214907041603043d030408001a03955170349031400b0307181540072181110700c40e81402c0c001010310301c00c0e54080c191640029030043c04481c5003e40d43c5080d5410401a03150880011703001005202c25440e003004100c01401034800501841d080c0001240e43c0d4031540300000040c080503070300303090303456440f039200c3d81c02494181c0640340d41e60070b0b00c1940c0b002001030b8066a0013080c42d14001c150102c1c2c88500740c644851117404849100d8a61904010804000800041c0c1c0408401503244aa864075000740182d001c03040c05943c0101002c0c580942040100c1d0740c802c403080418810400410000c240313200e4150000725001840240e024a01411481140c8002d00306100b10014070041282c440403991140309040000c100050084607034406038481c0740c050f1400101035141d1400031540c4c01c440740b51914030524070320102405040d821010349 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865796232 1250 865794982 865794997
    0x312090a14150d02040602011b021e0f07030303020702091e0a0f060b07050a0c05040203071209060b120706080702060f0a0b01020f071509050904051207052b113f 71
    0x4e8010034104101c03502400360114604d444032a2481c001a6490020f60394010075180010f07881c59644580703182c0c10280b280c090b40d01c1c2040c0c15500659201c1c1809406584400000c0340075903d80c0300081e03804060444500020134121030119610b03190040a1805400e00c007001c006003079500c44d0006080b1000c07000a2502c140b052001d800044921b0034038520001d800c1d84424020382c0100100529668480380c26500350710120b8002402c80c540f4146a00100315184c44990861500c9940c88114500040d56608880781940e602065507104241241c60392402d84031a4455000c0300081303040c0218580165201d904184101d0320305400c003100e580e00c0c00009a000714031001c1d44049203511150f00c24124000707040169807001e21414141c9d2600c0c0e070ba08594101e59031281e40400d000013000001d0080c0c0d071100300c480400800e80003002c10343c01d1405040c0d0b10400702042007403000f407502460216048182c1e44a003100203140100c1018114460320390a4001c841c03040b05541c070040003211040240412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865797482 1250 865796232 865796257
    0x50d0822030213110d021c0f060807120506150d2f030304050d03030513200a1403060601180f150206011a1804180b060312090a1415 58
    0x9061550040c080790303a04590303c2191a030709001e40084040c0300002202e945076403103440103944540a070b981c17140000343c02c411020b0107401d080f40030802d00041d410100686410200f0b448606503207044a502d4940042c000512580040d00040d584419600c85803c1c5401c0c003501c0800712010380d0b61003148010401140c2030b5000012451241d280e6030643e08500310340820703001580f416090000054817449490310040403da241c0002550407082800c150301caa0340c1c450f803c100030b0f8100c00055030b5034040206446015100c40d800009100c4000340600e9101d10020303014142544403000112118802005850071884071034000180060018450b030300280802100c0851080189100038200681030b8000e95240c59000c2d40c150003030740c231901124a200d803150350400a694605000c1806850410000d05182100080704c10905c000b1400e0144078210031410351718062203401c5c080c00c840c05005425a0444048941407190201034270548075184c01c001c104011420060310760441030b52051000801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865798732 1250 865797482 865797547
    0x308070c080f340b041514040501021908240619020109111005030106050c01110705060a0c180311040216030f0905042a1e03230f01050d08 61
    0x22040854001c243c5201003010b022404402d00d521503007954035001d071029140c110020b41100c0041016800400c1d81c00d40c0c1c1c6170203007161901d800c01074001c2d0803414400d541702060000150755144a00603051007400d68404903014041e140070f03544442c40b101d501480d00207808001c1219580c403034440c0413026030043c3d4004036030503590b0710f0211100032444190b5401102540109a0070a03000800e4905403141d9283c131340c0d26030182d41d4180c0d02400d0140311f004507484000604005020780420610700c101006042809034102c2c02c0350480b18100e650607803505815292005100244841e48451070b0140000c0016080120f2208001000d001d01c59080f40410100185210a25009181e07903000300000c850802c102c072004000c1003d102820391404180c54038086400c00d450b07019440e82403500755020040d02000b80e400c840a8020845601c6a000890b60120101201c440c0001150300c201041d0440303170010392a180510003202d8940c4012a403c0034140b08803100400016624035a144480b0309000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865799982 1250 865798732 865798777
    0x1a04060b09190303050a0c0302070f0e0f1501050f1c0f0219030b03151905090313080a02030c040903090b030f0109050711060610110f03091207030308070c080f 70
    0xb003a060000d05035921030000c00703420400b00e80c00c48151100c1000c1c6003400340c00d200c000d00c4d0407424548903404c00c00707951290100208090b80d441060718171400c1035035101080d40e103030100c51080c00740da42003585000500420045824035611409000318007100500029888404420704080c0d80c6034480c0b025103ea40400c100500c030a104c002071460b0500d904003003014015100c007287d20b0740001c00d54a40900884000300e01c00001c500300014000c0d892240811150a0401c000345d241d601500005224520100001c201498003168403041ea0340d0040040c960500d003c01844050701018078158280840100700080702c601c400011841854446800742040d8100305181d000c50c4c501426010402841c5401c40c0c45840000842c0f680044046400c2050005c500034116000ca50b8810b0a401c80e0140350042c0e8815440040a041c44d0741c400c0761840f0144903961031150340e032091440041e00140104011621980c007400001440c18001d6400500d0300d030070402e401ca01d6038007400f4042c840000042146 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865801232 1250 865799982 865799989
    0xc04091101080705040e01050d02062203060b150d0b01020307170301080712200609041d0606061213020402090a0303120e011104031103070801050f041202070e01091a04060b09 77
    0x155800f802c242003050410341041c20540488005001e0b1038099880e610310003095588020a0313581d514100107881201d41c0b0301800180403110207100c1210102e040c1010120b040c64100e9080c0004504c8407034250034444a00e40d40d41c05403d0060003981076000411206010412401c0ca0202104003052080c0d03403549001d030b40c0d5141024980c40030f6210300d0004400400030b00b8860100c2d0030f901003000c9421b0407056103000214a4401c1112581d88103140c0424100d440403007100e04031f0003000010a03202d042e030b680402c1c002240719a15984407800b01c603000040b42d60300ca00303200714179980c005000142800303000e0010a0100e400c0e41c1040d4042803000b440f42d001c0311aa4040e03460443c509400a00c0356058076681000d0b01e000c0d600000704540307a085684502a1000c00200c001003100d00024001414610700e80018820103450070390306042001d08454103d40001401411503481309450042a0f01c0c0404003c0242840401607582450203042c41d00c10741d41354060a8050b0490203006507a4101ca0b0081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865802482 1250 865801232 865801247
    0x8060408120903031b22080f0c04050403171305010906060801150503100b0d080f04061205160c0609051b040c0c0c090b0a080627010525020c04091101 66
    0x2200c1240e401013040003843c20303140800c88803d41001580d943c031841071441011040590900e0703032a0000601c00002840345c0006503081d0f00440740e10a8a40415600084c4401d49500f241c01502040310100300f6007001141e400d002d036000901c82d039940807000c6e40e43e540c5800d49080140035510a40c82c0c17071080c04032803028481d1400007100140c5e1814283d203020042900c40300c80c0702402e03140581d1420040da06031a0105081c065581c0700e000940d4400044165807104d40241c06240002928601500c410812500c0340a00691a2550302007581c01c5d13420085400c04400d0800b03c170440e443c2c44440c80000e0041010700c00c19082040c0003250903506400740001c43c0c61900c600d1080081c120b0070500418082c45401017501e0f07910001080c07043c568808a0f03801e500030f81c06044035210788000c004003040030300e5a00b030b051131003403011a0140c5004e20b1010300780d40c810b0726a01003801ca05180c8001c074243c2356800340c10f05a85030043c0c078170801c01c040024045503000c9000b60b480c0c5032441500340103507901404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865803732 1250 865802482 865802491
    0x10809060402031e0102070c030c08070611070e042f120102040b19020c0307060302070c0f0302060910120e0c0a1508180c2e0201050106270806040812 66
    0x900d001c0c07400d600029924480320303003241c94003540000c0d810a1070400b90100c44100303070802301d041c04040d0789203400038210080380300b0b00d0128000c4020105d45d4910440b02c10303045050010040c44054100810f0b42c12945010380304036000c1c08441e20196100c141c1400c4001039503100e020340d0008002c0802400182d202001c08001369034410003050001e00000c6080d113101c040c4c2c00480303545101148100381d02c1c120890026540c548503011002510a505800404005100342c840303a00e0b082da9401c03c40203108543c0002540a0014000504581009000c488040345945000d650382e0150008080c01c40d40380081d880040c0e08003824200c59810000070800041001d02c0d0444200351640320000c0c40c00384041d0015a0800a462988207089010803044012002c01840300d003150f03400c0042d550013030008a10b8010254015142010b00c1801840742604a40b61511880b507455030b00180424202c960210090205800d1000400c5000c010000c03c4c0c1b003144203040c81035641c0340d141840183d2050081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865804982 1250 865803732 865803751
    0x4050f09060a1503060b240a030614090a09110a0b0a0813030e090a090c06111006081b0a0f0e071d0303040b0f190e040c020a1709010c050102180108 65
    0x901c041d14080f40f0100041103a801c0b40380080c2601b131740b400285900c071000c00c4800d1400341c125078201c1d18411304001420611b1080d201048825074468a4421001c14100300d598040d00290010b24211201c1e0032415103180300c0d070755445010880c0b50000317601d1074898000340b480c074030041918036045801c1406240c0218103000d4441c40c044544e94000c2c900150034602034041d031500030204200f540207030481e602690784100b00c58a100d407256402080710b00324000071045442030503098500415144548015520004050810103540c8100c400e102541a00e006400c03144100d40004d400e84a1a10403000d0034200308030b1191410070038002000040c801c00655855000082500f0460350b0000485041f12500381541d92a0700100040071614012010291080d1110490900c00240e01c4010401c0c092800c0b503007004284040c28040760740b844907410041030890b05000310000b140091000c2e2140c25014540002000084e59403036003a0b802014a040f104d6005244103112584c03c9180240c4c052480d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865806232 1250 865804982 865804991
    0x6150d0b04080901140d0504030f0f0f050f0417010f150e06040510030609050d02060a140109090203070b040f08070e0f040609020a1e150302070f110406030204050f09060a 75
    0x2034640e68210280600001e080e1200050b48001c42e9000d0f8800840000007035038015220740381d42510b0006413200300e80031000a43e032103161443c1e0303034060080c2004081c2140d80d030704610061001d0a82d600d51101030b04c454818001d00002075007100b035924407002506a100040b8691481d1420f00d800e90700c280403282062040000148112208072400d16407100080350041596220300c082001542840c1c1c1014111500303200310318050180000d0003000041165080b41e8880d9210340e00b003001c480140701e2034001071305454010030185440c2d40103690401c0c001800d0302c400e42e03560001070025a05c26400030110401ca0711080103405020700094005110180010603203103488010310308104401030005005940e20f8012134190744485a044020b01200110740c0001d8000c00c00c456064400707071154403000100c04012030726141c40f80c005d03100580d40c80f8040c075a000c0b10366512042640110104150080eaa50174008096501e0b8021036004400300320b604025070410458060030000010000c56006081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865807482 1250 865806232 865806259
    0xa0506070b2d01061e0219030c05070803041e0e040b0105010c051f2a020303041410050103030507030210050705030c070312110408150601021c020c030f0615 69
    0x11424598003056103440201c0b011444600d403000c0e520311800144030500e10800109480380c00448800040c410644650170680f00200101d9490b40012020f402c2100c001e2083c0001a010fa2500c0304158800c00c107561890340ca418045266811076403150b600310307520302004d484501c0415214400b80105640c40406450662540d81c8603810601c58681040b014520120600206210001b01c09240458561b01c0034060303044440607002e031003512140c841d4940d8000c03034101403404c0c1c0c3c500185080c0d0055419503a90b52a20034902701c4041040809000d9041520020840c6210f1940070b580b1075261607482c3c0e04c20b4103000345052011100120810b290000f0321400b1034010f01034035403020002c2ea41960354a0189006c603030540d03031510b0800070b15003044548402044c0341d00140055401c510112074074004100c0c7c10b01d00d241000e480050158000a2103031444209100384003250303444a00448944408110210b4a00520070003504c4243d0015000d100c0c45034a0380114001800302220304040e100c42 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865808732 1250 865807482 865807493
    0x30703060e18060112140a15141303052508031e060a15050c010f090b13030807030b1f1d010c031d0d0b040b0106120c0e0d111207050a050607 62
    0x103010701e5421085c1d101807042000391045210207120359440a6a01c44210340c541441013403800d14100c0c0035281010700e062070341c204545580340301e00c003496040c102444594806079541d510650b80500e460900d42c101c200039140c0c41070444482881189041e90703a2a15940130600601d102802c00d02c1c1c001c258003840703100e6842241d04026600200302c4401c1019004805407150311500302040000d50a0011300c0c0c0102c20280d2003181e035640199030040c0c4554903201d203038084500104006000c11324545c0810307034061082d07100380303851070001d0002c00e2400d0311868102c3c803052022000c000014070000000c584050300342071200000d074080c00c10500080d0946d8000d0100b01c940b4044c1c9560f040030004e2200d01c2e6441002d43c500e102c1d0003910003021400d0a00300390380044024044e0328082003480e001c1d0800e01c8901c0c45011402d01c3e46070b440c0c40e0303400c90f01000c0264201402c0010f482001469241c6030690341e038901d540840c650f48d01d005042c8186400103020032280d01d80e00040c40303140c00f4001840882e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865809982 1250 865808732 865808743
    0x1a0421080402100f0504091508010c0305090d0e150d241401050f0d0e0319020c01170709080f010b010305010b040807031707050106150e0901051f0e06030703060e18 72
    0x80103081240d1134200b0000121040d000355032140308030500b085000400420040100000d0707661900081c0a030704510501942903801c21398440b002035008003104250a1720a000c0380941c2c4030020100b0410941c0701d1080c1d00550400c580440c3d800b9680c032800c403140002004200100c0f0b01b89515840120f250010101d11040d426100506205000440e050f40a50300000c5904900301c0560030841501c03109200b80d82d07074104204804c406518050010740d03141c00000d082004441c140d4a1040200400b003024002c20310191405007800700200d004540c01d0000d002600340810640000248806080001015038006900024018004020601c0170381703804a034480989422004060b05503003000a00d050034450b1b24000b400035460020045450780e0900030203d42c0c000250788203170a2041781d10400810040c04e110745644104082c40b20018203030382150304000541e80303041c4041c112410702c0c0172411780c1c0d0044500c0c1000a54400d401e2004007800035000d904107548006004820034107852456569 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865811232 1250 865809982 865810009
    0x30807030e0c1206010806090714150d1109030d080405030708030601270e070323100b030a061a270f03100c140f030c071a0421080402 59
    0x5407100200c940801042120505010024100c1c0202910120300151284421302070140203014140200d100c0345030001c1c1e0302e01511528504420320380105010131114a810031400c200174801804400c0a20421b40704040303a010310000c006949440d048101400d0402241d8041c0901c5130407010700010420001c191038002d07501c000880c1e0b17a41c41d03d100690300100e10300d024171074080c91420021000e8141342111030480e400c1c400d5004403901c400c803041e826981305550f030150280d9a80c81515160940000c02030300f000c00c21502014203904d03408082e5290f0b008889402d84144c45250401c00f40c0078100300d2154440c0001c88081c20800e00301c40c202c11540a0300c400150542300003860310181d5445401c0321a000c0c5e002002c641c0c01c508440b4801c00507003071003184040401c01080c6800e400d05a071104540c0c0c5001c503041038516650b10001900119005544141c880c0b01780c0800ac10300c804100b20600340201d00424481801500d191038140215200441000410180a090000588a205616211 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865812482 1250 865811232 865811237
    0x62b150213242a0b13050d0305040803060409060b130b03060907061202030a06090f150b03010609170a0c03050304030b0a0b090c07020d0203010f200f0405010c0519080318010603030807 81
    0x99400e0743e05040c48101000c60050048640740003400702103d50901248100e07441030701912951024034405400302d9100300e030054100c0b08200300003003441c038280d8031031400385100d420700040000d52036021490700c4007030314424500c1540c2c554a0925a1408001039a03010495000400c2882d050100007801489941c0c1c600c80c00c250080041880903681d90400c1c0060501882c0030025481c1e511000c0740903100bc19190381000c40c02c980e010400159000403217059860a84404450764a880c8103558807031000100b4011601a514041d000075800c0100c040c002e40c0108001d5485070b0844c100843c0c4410080d1145008516100394035419031a5211050750110103c0e04031034072000a4008510440c000c00d0009505500c4d00d002c450784138a880c5e2200346034807450450000304002d0340d18000b10f00e02c101c40305910074110502c82003085620a00b0001c01e5648200c0c151490038643c0095080410300007030302140c480101100b084080301022000058000060000344801440c40c0c40c0a00140303005401c40c0c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865813732 1250 865812482 865812527
    0x705010f1a060d09060903031a0111030906130f0b040305070b0306030a060e010b12030a0e010309110d020604030507060915050a0f0818061e062b15021324 68
    0x1401445078840fa000c4d6812071814050080709180c024001d000c50000304400c2c4202d0500000b05520900500c802d9080d44001140b40800010800183c1d40041d00c0200311141c2d1a400490381c5801c660300c0720000d0034007001c4641c039141580340035810100300d41c10850f1155000c0c400c10a10f07690004500803e150890000280c9140c100c02d454050840480c425400c07201d460351080f00b11200200070981101c4540d60700758a1440c0e8401141a1960b800020f0042254100c8481c16031801221406505100400c840d20300380d17030780d80e441781031900c5d550000c0e01040401104200714243e21310048500e10091402034030300000883d028113800032010f94041084981c400040d1604441d0a80d01d41d203007608070071215145002d03d0340c2a10a800c25041c3c803011590071380400c0d09030030040041496000d041c0240f8205580e4510038203946c0410311001d8403d042c0360203c01c00322540750300c0200070311402c1d1503100481c203040220f040b0203010101041d90501d1500c44e01c401e909980280c402d14200842180000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865814982 1250 865813732 865813747
    0x60912031b09030615010201050604110f0c250321170601110a14101b0f02010b060705010905211602060c0708030d140f0c07020d14030705010f1a06 65
    0x1d0380c41c002c041001e6010b00c00d407001d12032080010803407411604000da009020a64a4005000580390034201c46440d02c0c00034403540501100a00181601c000d0f00c0c01111040e0b030020302e00289103010b01d16180ba11013041107050051154030802012400d0b040d01d26240f0000c401c1030010001c086e80c41d50703484100d9070748010800d00d07803003141c0c0311041c40c1c3c1e070504554088049081195900c2d00084042400f8483c100e00f81c20a02e40b5801442c50781d400c0c00e00070070402c45501105940c551005003d44d403c55581d4a03c0c0d103903d66507039016100303941c01400002180b550a24180c0c2c5055603e4070841e48800708040c0c00b030100c0d00201d00301c8035804144c4a50400c1c0921502c007003007a0340500c1400c807100e03004003000480c004038004007406c0703216a40c9009003c0d46840002021a12a0658110681d0300c80d02c03001954484082005046280c0701404119a44006880d1a030030007150207a02e42058100050140c10311130309020300c034640c0c609220100030381c00c58015060045c050015119000c1d070790124004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865816232 1250 865814982 865815031
    0x10030b06040507170c0a030608010b0604060f020a1e0b07021617030f071a0a0902030a2a0b0406030b0303030114151306020606011b0b0a15050607060c0206091203 71
    0x4c20224200709403d49282000140003015410032060340001a251141c0000e110f1070500074203107000760103040705140506054086401d160803505030003c0d8420710f181440050b4460b26510783d0020b0941d10380070303010f60074545070003001b00190001d4210b60100c0300840c0a001611081801c03252001740004100300d04000c00c038214000c5220584c004140410004c040c420030000523100f13406020504900c81d82c600314260112141700c0e0001c1d425030301500365440020b600310001c405242c00103c0503c50001b1041d0f440d000312441d50840c000701710300890204100c076014050030315240000c0300610f013550305001e0312007248807038401120701c2500a5049124050300c104101c03021020801c2c80800540c0d100c070070281da82c40d42582d0050002c0c40c200b00148030603034200c0c05402030341d038400c143c60103944500c400400036112040715608091442580014507035202401000744030f00c2444041010300e2060406414401d004054038070342d0300b01c480703481040d0501c0b00480341e106d45842004a803241c842d081c00b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865817482 1250 865816232 865816247
    0x3100b031b0304080304020a062c04020d020d0e0c0109051323180705090c16030216031a010503031903090309090c020610080d05161502071a10030b06040507 69
    0x740c4608503000810300060000800040d80f081f4001e907030701001e0070348d40c04084440d100c1c003043d600d10140d50101c00c5d282c4108080a0082201802000941454009840c3c1802c90b400b03d21040c501e26603030007544920741c7c0c00344050f2000d15804d08044030181e05d46070200c0c0924811280c2d00b11420b945002a0f9002090003403a40d10f00320b000c2c1d48a225604e0b1980c81844111502074200480d849400c00005e000c0c58080c2826100382c03050440f403418400585030102400d950400b08034207500070404140000004940c0d40c40084d030140250380e40f0190303c0080707001c4125040e009a030080d001005050340455200080e48000382952500060540035420122000021504921643d50510a08d201c4242d400102e03240961000c1c2c03540801306540b0035070503564454840c400b02c003080d800c0c404110b1201e802030f000640705004004c8810011140901c44080b03030311941c800c884030540d18012412440c081d5403041e500c5400c440c500c0e2611401d548550040c0c020090180384140d454900140a0502c9001d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865818732 1250 865817482 865817521
    0x90501061202030a021b030a0e061602190302030105090721080717090405040b0106180509190f0f06230102030301030f0204180506060415050604062010020d1103100b03 74
    0x41228806c0001070256441341d104030f01d000001405092085070a00d024070442c0d5111000401800750f2401039420b00c0000c079001480740d00c252141c03040c00000341e00d003070013900d10400018000d801e10b5400c29000903d40440403c9501d46100c82d000c501002842030411140c0c0c02d50444150120006c401c0e01912a07485030750a02900a030408081c0002c001c00080300c181030300d5513919010380318080b0070f10010400702c0b9407160706da1101000c004140d203404c0703a0210141e40c00040d44082810742c02e140c0e4910946020600d540d9000e99181810060700700c134901c030380706112480a00442001e0b60303500003d640b800103010152006171680408000c55845900100114032941d6200c0c564662a0900036203c0c0c8080f140b00b0300440c2400a10440300c4007942c86c1c101600c2c0001d00321401d09081500407500c824801c0381c9a03101001d0140441a800d00030400d604210ba4006005650703940300325151001d42c0c0204104200301b01041c010300000000e0002c00300d0603603443c0c080058880e92482c560714200c05000340e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865819982 1250 865818732 865818757
    0x11030405100315080a03081605090a0905090109020904050d110303070504061b1209241706030f0a2603010b090d0c21140708060408090d0c0e10090501061202030a02 72
    0x17020780401d81c102c414a8819080d8803406182601c001c082617886200d82c110080c0c0c428a10f410030f01020416500084c0c00003400c400001d00180e00703901145543d08144e03000d807881c3e8007510812480070742c4912020104441e28001c1c1d411400d000300c0290503802540115000d00c000307205d002482c0c5006c0900c04284540107104074440d04032000000c2c000f072002d030180740c2c0c452056690046040859a6802c411251280d03038000b000c02e05986101d07507030761016003d80d40c9070040f5000700010302403c0090301140750054036904903600d10000c00010000f081740d00170101e080c0510041144801803070544503406d2069030750300f1822503a440c003c0c91018444c2c0040302c2c0384041c49010301c1c034101c0131014105031500c11300007048030f101003030401c6a460b072092007070b0382e119803126000400042251020b480c591030040c200c4003d400f0319964906801035682c204c6412000500200400c0c081e184600800074150384204000745d50601d07034010302c240c4580304942241c2e0b80000104a4145081d41150010803100c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 865821232 1250 865819982 865819993
    0x2030d0c0e0604030602091201180f020f060a081504060f360209040e072105010e0d050c0d030507050901050a09050307081f0b0d02041a19061103040510031508 70
    0x5c2c40d001000b904031500c03ca02551114840d5409524144940079140c1d4001d080030078103164070b590b0344005032178000d4200d80203030740c8007000342c01911800082c1000c205540c44000403454003500910b000c0c3c00e038103030750340c80f560406504001c0300300c230003600d241039456910071011540b0f9607000024200040701c0b03905052001014a241c2c1606013980541500481103c00340142b012000c0c80a036030300070074040c50084201d0040d52100b0304003540c9500b80343c28440d0b00003240c4116140300c0b05040c000d0460302d020105030001460307008200140540032000d2140d0408000c20700303008000800c40c0c0142420b15061084c00184c03020307014000c0044100409005044507810782c2c9601002d03464812195621200c1102e2147d442c1e0701e8001400b5202d01c845c0d014111400c813441031307000c000242c0b4900400150508580c040142d06846a0303900064210300003601080c1c0900c6c0c000300410140f1144850001d91308280400d100f5030390768046c00b100b9440740346008130318030081181c08113200b1501e5100c041c082c07145 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 865822482 1250 865821232 865821239
    0x110d030e1501031205090307030f03030b01120510140105120405070326071104020d02131a0c0307141903082a07060e01060902040b1c0c02030d0c0e0604 67
    0x19000001602040001d460301c0000381c1da01d42803989028040201a80c589000100d000c034810005084080401011910025a261503005000384000c1d401d42c002915014004502e58200c80030240317805030118204001e10f490105880a80c80500424070554142c196080a60307104000b500c2014400d040e11901a0519103041039860b03240d0b100484142a10188180840d03aa0032440d07103450910f0401c940c5410240e5540e2011291486100c5900a0342400254140100c03807015000f80c810401d1682499030912544a20070078003034850b8401440704105161594030040f0580d2007465010010428504e4031050090a203181c0c2c21410310041c140792894018181d000ca8084d029607850340e0422019015003007152034955043c120890003410400c1010001002da40c0324840595104000007140c03034489000cfc03003d0740c0c40740d80b1a10001c4c60210f815182d00d52003c05400d2a0b890b4004204031140d142c1c0340107526400ba8a11400b60103075544d0210510b54083c003c1114106c0e0b00400c4e441d030b540e44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 865823732 1250 865822482 865822487
    0xa050a0807031202030a081503070b030a0b030c030303101a0c0d0c110102060c040e041a1e01050d020901030b040305071a071b021f030b04090303020a022b050901110d 73
    0x610300c03054500b0114401c00101c3c0318000302c11500c01d038115a58000300c80da220000f01e2400d1102c85101609440b8046001840200030000b840c019594124040341043c100b100701494036000410b01c0c1d1003a0001c00c180000f541c0d0180d440c504440781d00d0559120a50444c0142030325028945447d80f03540a0511001d441c9503201020050b0180701e0f4143c924070604003401240d5038141280c4620900d00e01b00070074040306221556040e8018031032002d980300000f102d049c004081c1d03802d0b00c01400000c904809590701051040c1d841e4003400091340d800b50880301e1a00000c6d00080188406040c2c40c40c46408601454800c40485080d9600120484c449000c0702e120400c00c0901141c4010000d485a004606680d4040d803041085c40c2d0028010200e50080540034164842c0002c4c050b414186d8a00151300c0a0700c0b43d016841c407403400303030700c0058440d4862203019042401079085050700c407107440b0b07941c5190003031414448800034240c41c00e00c0d151801000107a40c202e09080c120605c82c494104008082603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 865824982 1250 865823732 865823743
    0x3120c07020a21060207020f0d2303030c040314070e1317090d060b0f03060903030907080706050a03020a0905040213030611120a050c07172701050306010e0a050a08 72
    0xc0c4260352005125545115081c0703070f0f02d101c207000f0b050020045000c001081d0a074010303003c3c090004186012014520000851a0310b0041044400b9070f850030701003000c051500620000c000d1080e01a500c1d51404202d9040d8500c203500008042803010018004075400c10804403000c1c2c0110400c1d0b081074102014454035004004204403071010240403903803010390046094818580001c4d0546640d64410780c1e4210140003502e000c150004202c5a0703502e01a50b04200580c0151401d101466503420180315240c1080c0031070b0008000c50303200140400103158003c0448805003010f150050f01c1303000f00c40086424110950006038410b0010900c40e40071040118000704503803141d00104035040101c18090f60074004c0c00c2109404003d0140017448100c0315070455075200c40c403000d10f9442c02410b0b5030781d0319800c0120108003e0f4440c001c20720004000480400704944490140503242e03440001d00024943d00c40140308a0411240380c90540c000c0d100d8a00c50381c0904402010310300384680310b20681e50b070345 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 865826232 1250 865824982 865824997
    0x21509010e0328090806040201030b0f04021209010e07030804151b03110d03110711030f0609060106081f0b0c0109080a020a060b1806060c0313032001032c03120c 71
    0x41c104080d540d03c64000d0442d5400c9600440161107141e94540054000700f1461444d9500000b10608480d05039841e48001c1070000c6504844100c02e0030f209003400e00b101c0c03409915913000e60284805002260a03175060f2011940c8102c0b1002c05114007003012100b2024404138a0a604030340440c0c40100350b0071001c2e1449000a03002200c0c01d5800809044042e2044d0203070f0082414010440c03c804141c0070350350f4101003c000340440d80910381c081445450b000c011950210075400020052080660010649800910450804901c40100e400080c85a401c601c5940380e44040000ca100e034000003034101e07c22198110b16140d40311400e84801075280d4403085805c85070385241800c0e0300310a14110a11072402e04501e1002c65860b0f07900f20a0240f2a40804509041848144a405807011400c0d0210001d1403149a010302002401c6c2008480543c0083c0c1c4036050605010503441d0350740646000c2d80505007606c2c114000b02c080300106d5411403042c1501100398415040030050291b10203002031411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 865827338 1106 865826232 865826287
    0xb040207020a1d180d0305090c2d03070f140118081b01021504030e010c020a0306050106022503020603060418060605130b01021509010e03 61
    0xc030205a880460111100420000c4103048040f5607500110182d011821460500c81196128041034403883e007056a80c000140032608100090482c11070046c1038455400d0744032000c049200100010207035040c00d507200c0b403420350900044103011134007081c2d044c1d01c0060400740000c14440c01c00446904000be50600242420445036240e401000c02c240101885401c1151038070705084015001ca040d5000301c28410014503c1303003a01d82e0b02551501c1c0841341c03400d40500580780f841d482c00c0c000c1e401059185010040100340ea00081c1600c1c0940c00700c4031140c0352109080c1c02241c26189004041101755820401424040c0141d81c00100051010607909030710b0854410200784a4400d8403159110801080242011210f50040f14104c0700d0a001080308040080e55892820241400041c0131000103250070320290b100d11040e68201e81540eaa840341d07000480c51000900c10668007 = true := by decide +kernel

theorem cover : BRFrame.Cov 865647482 865827338 := by
  have h0 := BRFrame.cov_init 865647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 865647482 ≤ n) (h2 : n < 865827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
