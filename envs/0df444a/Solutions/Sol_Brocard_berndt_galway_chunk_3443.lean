-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:45.537256+00:00
-- url     : https://prove2.me/submissions/28c5156a-7545-48ee-b521-8c7c5f7054d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619064748 ≤ n < 619244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619065998 1250 619064748 619064773
    0x40206090a06030605030f0a0c0504110d020301030309091a0d20180f100e0c07080c19110a0819030e060a03020712080c1e09040614040507030c0c060b03 67
    0x5840074058201c03a00c010072060704140c241031500c41c4005903400b15074880702003200800d0017407003c0410344500707a07030100d40210140007141c06449110b2404420b036200000010506a110458600b501c0d0707204024045d1013800034806a50034000074042e5802000f48040600054a12600c10070810041203001c00480c0c2c41c4001803041c40c100c085940d0100e24280c204010710501800055011120070044140c1908202d0114000740005000300b0361003000284040c14441c1c01c40503580700c400f0050465074036282440000c1405000d88000700c491850043d007104503807030540410410381c0c0d5960010036101242404244101d0b10130a02071b030034482010401e00c060344502c0c0081403401e40360b8601503035984880c501031801200d07115a600030085020144185d0700300b1b04040b52a031004c0d029809010011200c1049501c0c400c4000c80c50b0310500d481800108510500114200800c1c12102041f213580c0b0b00344181c0546016003c0100060b24041186000480591201c1009030002e01119090803150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619067248 1250 619065998 619066009
    0x60501022103070e130c0c06240b2113121103120c0705030c0f0d0207030b0c031005060c07140a0302060f0a090806040305034f150504030f050f04050904020609 70
    0xc004030700103071404102ca000d01c881c9004030424000e1480101d141c9d00d581c0000e984681c00c0e40d005850801c80c00080910b4010401e4141d6510101541804141410265400d84004070140c004480c078032001400300070301d240541011036184140002451505040b61003006a192001b401e40d132240d5401e016220114108101601010240c04001e00c10794044404181c40c0840e444283d401f154440316007400001c24031001c4507004036203101c0164480d280d42109a8105800341c0115400c641701140141c080d290016000044a0b182d08076440c2c586035100c24018640c3d0603000c00303904400204400180c900c1c040c1c00502d041c05031803034020304082e11501d106082501c25901a0000350010051051039201402801d9900c146250469044040e1100c908a0000308031858401210244e00c0301c1a0900081c035103854080e805071140000002c0f40d0a01c000070a010b4400703800040030200b01c941811b008504460304240001042403c203440d0504008809030020402c90b08405d00340400241c07512030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619068498 1250 619067248 619067261
    0xc0102030c0a0936020910020717011109010f17041104060509040f06051b22080f073c060228021e030a06060501022103070e13 56
    0x20310007181d940e628200d0000e0803112580c01002d00d4041030860516000000c0c00c520100080441c1d0074150902510f4280009024102d400c50704070696004e00e10116034007003080425248140c00654800c20510210f608840b00d654814001c01c8007000603400b01c5d8000c1042a82c41065840e000060303484a981403d030301e07102660f041f17032a9408000940b9072403409001e402c000e4241620403001501d1709860b4039543c000c03480c4020300070b6030b078942c04150100991419003000380c90300500550f54800c40040c0050321402c2c580e822840d002100404280c0b001b01151800045013008000c2140c242814895103c0003c2400003101000c18002d114010341820003041c0001c907030785002c001d9124a4440040d041030314200d81c8005040e841c1c14440c0d80c2900200d00c640744c460701900c07824410b00c00388268103845942108490342c544529a000c07000c1101e141c001d0810b80d0000e07826155810182c201503248004960849a8050001d000180e402440368001903000c4000400045200d0313a0a550032048440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619069748 1250 619068498 619068511
    0x60a0225052103190216020d0c080706020a0c06080405060106030c05043303050105150c01061d1501180b181003060e010b190f02010e150402191401050a050c010203 72
    0x4003c0300f08600f034a00c40400c885400101c1c0f606500d0005c01c50741c211140260048028030908401c90714205014651800802402c00a4122828191515000780d900c602518040782c1d001840c15002c00c00078410060b841c029a484002400c4507401c000b401e5000e000d44036120b8040000600c00055440c40b05200d070000780d11f4408104411404030b000b103894000e450f034600403d060074440100b1403926903080410002414000c125200c00450328254090102640302d011058980e01c3d0121000c002a40024001c101703105508406800000044d5814501d1251207403403d00b80d19420000c80710090001c2014038095050081c0d5484108001903842021441020010f559601c0c1480b21404100311207000d031510403138060a04501a005000740010b452450080145019200d0010390003500108411004030003a0354009049500c0310101b950304940584c070590b01c00d000e911081d0420000d050544211101c0d8142c00c00c80c101c01076403190b111071611010003504101a0031300d420284080d5001d0034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619070998 1250 619069748 619069813
    0xc1401020d060e01080f0f07141c03090518040b0a0207110a0801061e150e030a060501090b0a060f1d0d050708030408061e04030c0611030403020d02060a022505 70
    0x14144240b551030020080303d0480990b1260a87c0780d842c20000a884040740c40d248281011291900003088411000d0140c0c0740089241040600406800000c05030035254166698040441d021501c22551750041c0c90141901101c600401c01e00051500107010850050a010782c2036540c50f00855298000c0354480d21070b40e503480109000441b0066401300010000456809142d41060181512003030503010300720034443d104480c1c4101e500c0c10301440c0200750b0000001c00c440c0d81d540c40307140c0107030800e046014460900414081038840c0200d2803c52250713000c0ea21250900c0000ca45042607103101d0744803c0c0c0c004200d0b07036950001a81003000e02c001d064040042d5854a24000501e49040750151110b40941e81c208015190510b0420000d544280c0525180310b4141c52420007030000d04043c00344004984c4000108800e03d500010103603007445e115400c44030300d0f036108112041203004110b035000c1c60032101c1ca8461504200746140c082c05074001c0302502d402c0420b000c02d00c1d510514000450003030a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619072248 1250 619070998 619071001
    0x6061d0402040608160513110a0201020702090f07050d0c03021603110606030a02060f030a0612030503060f0a080c01080606160308090607021f02070302100507030b0a080309010c1401020d060e 84
    0x141040d00400f001050340d4002420005600600c0d1642400c2c1070280e01c0c0140c841c4050701f403402c0d5450300054090400703940000c0e81c2c0c508403a4004c1c082d5104007016401340701c540c404180300101d0107514078800c444d50717030300c190130b081c000b002c508050644040500100758081c0000203151400543c810a25403180d00c804a10508051209052a200411306031007078200011460140e1a403100301e820451140041da503503a40c0d0800b010004007516002194800c58400a1004150300880154080d800840c1c40d90003d0420004101c074180e514002c40039590410a500c030b06550040105e40e07000400142103604024820351000d401c1c426444090b0002400f000c10300034141400d01c100c5800072604c1c4003800a0380080c107000c0c025120310782c1090720306a0740090348009043c070910034a5000b407000c88040c04182407107000140500310003020144a942c0301c00000443d800000112600c510301070f110207006454a444401d8507001e2010140d1065400b001f4031150408240f0484010340004050a2802d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619073498 1250 619072248 619072253
    0x5130f060803360609010807141b01050603011a060d09060e06190c200a0b0702101a030a170f03040c17030304020a03140708070b03040303230f0406061d04 68
    0x8200483d5107001508404640c0012900c070350302165071030442030814110300d8030f92503000c59104ca00f40c12204190080440d0071030b20141403007075a0340c107564058000e00164686204060890b10700c06c1103034030111104680f00c803075414000701610030401080d20019180001c1d890b402d01340d03030110081c40a40e030094000c01070390401185107154150400c0e10304000f955000f0f5005400b154030907880c00c200c0c820401141c0c020031001c10071a050194042c42e89070450500f036038042d55071004c5e04204002e190800314280003200844142c403c40100c024000d141d080501d03180c07510404c160264285120004004407440c5209120086004a114407444600a45010803400880d100d80c031125183d170300f007041800090380c0c45070009010f898000d1390321900f005c04013403032030310302025584445054091110000742180d40c0d01c010b1803080d8041d840502c528000345454498150710b4a032100002180d190205010140c19a8040c0d44030b0b1280200058494803100360841101c0d00c050503200100c0b50400700000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619074748 1250 619073498 619073557
    0xc06090d0801081f0902060d1a10050c03040905070507021002150c1c1a180415020f120604020f07050102090120031206031c09030606060905130f060803 67
    0x140300d6180070b059803144d0b807031507401030101440d8400ca007503858581a209564400049803000300c41c0e401c0400680d1042940c54540c048c403c00d44512411001608500c86c0d40602c04490094100304055450030303080c019884014035020740780b80304000c02801444010785600c40e0038031052031550020802e80484001c1d031845c615004103558001e40051080501c03042500101d00300c941c0d1501408030f4082c86c40c181400403101000841d903802039038810705406804805008034002c07801488a540a10300f0080e541090b0f114407404008001030400401440d00100c4180a400200007480945440340903910142c0c60341148038150391a950010360090250b820a0390325104c80355125007908bc010156007903075224054080314010390148040064516a0180034640e004050146501d007002009840148024124002254514a00400407680d140100e00b000126440100000b00e80ca8090130700101928580070364810082c3c4900011401ca0410310103010144450411000d130560005070189 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619075998 1250 619074748 619074751
    0x30e15090a1e0f02010f022b02100b030303040209180102070804050102060601020f1b1906080108100b090103030509131e0b0609030a2a0902090a0806070c1203020c06090d08 76
    0x4000d00c0030701c5160b40c000f03505646011042d41d0242001c024000040001383c0c1400f02c84400c1c071810700718a46480800c12140c80c0e500f205000d60b80c2c2140c0c03d0042c1440ca4a04a8103402d070415810341c000d00c00103005284c00581c4c1d9500203000210800054440d50049007aa00060750444100a002c6028490755a0400a440c0e00000074401000c0000c40c0e1441c003600d5213400010760300c2001c44201c54509648030400342207082203103d508000e8182e9980f0000303107548000c0c018407219020b46ea24100b42000c0c40e0180341d8a0b5034004202c43c86a910b140d9080d54264412410160065200700c5408541d0100e4401ca01c64400d0310442c100201254030b000300308aa04583c2400d1189105002c0040161400a041c41d02d0f582c0c0405440c8508001c800105040000640c048007110304800f404a1126416000760000400070380c4c1600c1c00d143c40c1d070807581d141c0c2c1c0c084461100103a40040d2240c04203c3c9001d4940c85008507040043c03500504e4070f80c003410b00100300e40c602030a5200e1102c2e42c0109a211911a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619077248 1250 619075998 619076033
    0x204050708040b04030e0d02061b370201120e060411060403052107050304180b09010b0901030507030f1121060105030406020a090b071b050103020307020d030e15090a 73
    0x20610b003d07540c64080d000f018101804000240355404241e4803681458108160024001521a03d003800b000403692080408020140106069451810002510703859251007080b405104030780c0e60000c803103031410076010a034104502403070004207082c114405c81c566410600c01802c0140341c10b0802e4036400103821860340c01030303a080004101207000031070312840712510350079501500300340350491000c01e000b4200060007500002400050f010640c80540651045c00030301488280129410801b2012003403045010b00790017040301909540c4a92b1200764000094100003513031304000500b0004030745a440c007080207088006083c0e482c0407114030030040086604071646803946410000200f5600000d40000d01d2560007107100c4540300e0003000400081c00ea10003020362a0b009134240750404144c500001030a8030402800031030294802d008a0703203d8581c0750001d180381c44803030800314000c2c440b100c4a80340c0c40c0200810000500d01c5d80c45007601030506207006201d40c0e00c0740c0c2010b000301101d600d0301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619078498 1250 619077248 619077257
    0x305040c121214090a0909050a0c080d02060a060510030507110714011b170c0304181a19051509061206010f0f120203091c1d031609110408060f0402040507 68
    0x4426103617101c0c40301400f940c0440f10040749906091420341c0c58a07401901c02080c6e15052440800d01220005400c07810080c00d40c225609a25488014412180a8000c164010034541d040b0010140250485c942201d21841e064203603400200c03519003424055000b0000005030683c144180b580e10441a00700d81003201150011800309030740f110840440b5030030b1140c02010101d8568100f10061095400900003607280341a0206d030140c10314001c0604108181c19400080403113440d5042c0039001850304e00009181050031800c280401c515140c540009940303101c2c0410641e40c04c0e8507000082c007144415030030030384070782d0916100250a1034009490740080124040a603591941c0c4044106400c20000e540103a4944401c030b0840d0030007030031003210900d000640c4070f54142d8031303400011465007441c1c2c003a4403900346403010b04040c2c5070051106004010b0402940a0004140507809a13048030412407007145030990314240c803810504202d0380203001007a0807042009604090081d143c2c003c1d541d252 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619079748 1250 619078498 619078507
    0x1113061809020102030d2a020d02150603120d140603150103121106090a03030e15010311040204050a030609020f010c150c14130f0b070c060305040c121214 68
    0x320400303500d8001064200c0d5241d82260301964024001c40d001c45140050a203c80080402d04003c04108031741d9402002c2c002440c2d607400980701048042d5002482d41c0908151100400321440c1e1010180c506940340c06826001e49030400101c004100d50f1110003004128a05008a001c4195030014840780c02504283d0802c80d6007008528024196039011914040c020184042281c1d5500580300c10546445001c06004444c1400100540c0c658402d603010300000021030041034403022444040542800a20300500010f09032b21150140c14001400040c04e207581c0d000000d44502161b0700c243c0d54150349040003015400c0281c2d0484c05030400b828003003401d900720781e1081200c0c00c440300c0b40801c0075580c1c1032052500303215160514040c0044160aa202d008a1104440d4994580308551600da4110700000746011447c0a9401250b08a0070f154161450f11405401030b140091081b110562100400700301084400d04411030280203003500203800b06810302c082c107015000754820030782c0c0d00b0031b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619080998 1250 619079748 619079759
    0x2010501171c0f03020d0501080c0f01030b030a020f060705011e0e060103032c0a06020d03050f0402010c20030706030204050414010b0d090303060e04050d17060603070f050c0a111306 80
    0xc0b904103030041607140c00207884071100380841c024000c0c407400b500414149000080e0042c2c00082030581c2d090121810b41da000c4078100190304840d002080c00e50590030030014000945001c0c0c11180316600090a00b03881c101302a0b0707445003103c00407240c1c03000481010b201d482541c40300b03100f521030303c1d16003c00a241a50442c3c5002d00100a004046124201029402d01403020300d940040410600905103a08407625404080d488502d0840c0d180002490013000071504a06c14014500590f010b071180d4040c0c01541d1a00342d0441c00480e00f007440b1840004200d0b8664400708240d500030b250031380d00140c446050404210a0f5a00500349c0c0c1400080140140300c404288402c40e40c0815001000041000780c600c0d041d400760038240c1c004850018400c04120910034007282e05106428540c3d02c2d2031000b801d0442c0185409020b0310b029402074014400540c003140140303403261744032815040c81e40c01d00c0184815079292002c00c9204071021000c4d00c0c412202e5003000100184580380d20601031110354100f4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619082248 1250 619080998 619081033
    0x1005010b1902100510060e090417030414060108030901090e071d12031c0c080c0703031d100903020c030a050c0609040b060f0306100e06030f09120403030201050117 72
    0x11081006511070080c02510158003c1166600c3c3c00e400c0380081c0200e241000504401c02c100b0311070300000c686250055400ca1034940100d5100740d6003e19802d40000500f400110380e500010012100c2d01090802c1080708001008030f28020012400155a200d0408000510254150f84a4001854201c0c1400045904200364001f0362501c065018010307014007001400c428100b0320244964000020410045420201700549080440710300348041001860104d6191900311240018860103100c0280005d109420005c400e0035200310110310350080514003810491144030045241e50340f0f600c09803c1640601242079502c40c200d002c0d040040d03403512910f84800071800c80903c500d00c000348a10183c0d5540d44841c42c256000b401144d21900e009980c02c00700e034002d403003151241a00d6070740c041480d48100261040050301904031750954903252601c40c1400c802a180c03000d1401016103030211860382402401c0210300a90000c1800d5140c0480c0324828802d21306d170034603035400c0b68090040c01d030394a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619083498 1250 619082248 619082257
    0x23180d0b092b0c050120130e0c0a140706050a02070302010e0601150c06021603051c021303080a20031e03060306180703020a03110301050a140c0711040c111005010b 72
    0x22810f1101c010701103490524010321204e1000550b07040092224202e072190903001e40000c0c1d0008018070149a01d852800100c10f01c1202c6c50000e0181c104003c0740c243d80315004032154680c4080787e250509200c1d94030f26042e150308440345c00d11a40e01080715802c1c035509014480030b00d0510406000136504115142d075071134501919060500003006850420014640d04441d0766140c8400c0e10009c218a502d40203140ea07014005040b480d4448481c00301d0b0303101140c030032541404c14040b242c0c1e00c080d1030359030340d03002540080742d042081c807908540300c6003004a00f800f1181c4014800c0003969a8507070a00c80e40340040388248412842d040d082c0100100e03903e0010703009030448541c40142242085401d200303031403e95036400094128825400010400140040308290201c00320000d01c843d60321328a405084038480845001540314440c0451507a107608001411042c0c09440c2004040a646010800750b0708400b581000241000d818003031250350500c00c107000b84d440c18406003d6540740c68610800b9004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619084748 1250 619083498 619083583
    0xf06041505060a0912030c0210080f0a0902030a05060a061505030f15120a080a0f08070e0f030106031703040204060e1e1e0f0105040c23180d0b09 64
    0x40012442c29143c0135034a024020041c40040030b40c000040d107402000c082c20200c0803400341c0c241c844120803403401020120700c40c00e018902c6661a40d100500b0344003409500c80c090b41c05008101420b000314000303000403803203804425004580c052800ba5a0403240301101c9052080000a1040c03100c8000303a000341540040741206e01d110000c90b07410000c0c080c10341c12058840c80341304034401f150410010401800490810362286140286015030a840d000303001c864190001d620b0748207040d02c528120b04131424a550103000061200e44903615a01c4e08404c20750807481c0781070044100811403400b0302415016240c40c00c1c002d510380c28694200320074410024000140030354a000040e102e100703c80d003041108125036003122090704002d001d10f102c942c420702a441c0540e05100b91032200a011f4041e0392171109005098036180072510015980030b81011200402456207600d8009480d941c080310202003d024074401b0843e07040c0300c0c1c04581782c444030441c2908641c81c0f036090202100000e0300789501054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619085998 1250 619084748 619084759
    0x90303030f1005030307151b05090409140304090b040501080706080c0c0c1c0501050c040510030f02040807180f090b0f060d0c080a03120603121101061203080f06041505 74
    0x44802103048664002030f04950b400d80b001088100a100c420090300c0c2c4141c0000500b000f083e10801c46004442c03501d00180b01c041201081401400d0030300f0350283d003185024904200f04001030f500300070b056511591083e80c11a48600c007880862820384582c600410f0660300418034246002800ba2210100070141c541c40140419110b00710401400300e9844114024401e104c001401c904921002e085944207031070541c070b008006000101e90104503029248010204251a40512400c070090040a910141515024040010140c01c1000168003815405003d0300c009200700805804543c103d81d400010a400c0c1818000807a21200800350800d11021210034290b5803507020941161134403000800c07100300e0840003d0084c0d40421071b04112803003682e441c0412002010200f00f0703a00a40400307044e80700c00304c03011399025021f00c12510200c01450004500aa038400c1c0100540940da0820340124615a041000300c841c0e00c8046540150b08a908005d11070143c0d6201c1600c64550180c0b07409003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619087248 1250 619085998 619086001
    0xe03040524040b0301060c0b1602030d0e012a0f030902130b0402070c0f060f02060c03060405070207080610060912051b010903020306040f050c030319050313150501140402090303030f 80
    0x985034402c4a0103080040e01d42651303540e59610080000009000907550840d1610100d00d0328544980348545110742079000711708190321250000000d20800c856200d041d9039a21014a82c12030b1421310010003840510059042456500050f0070420100000e204161a0100c2e641c0184d41e040001004042c1027003000442e40c03440c1740843c00a22400300064840701070004002408207668a04c50150b40da55900c0c40a441c01006003a42d4804095442d94141c0c0070030b000140c541d0401d03900407035002c2118412904110f0f1345182c0c20382172100035100108490580002800802c0d00503102c1c80092003060b046281d041c1070340e1203140e2120b100c03020000740000507117440c0074660700c1005100c01454006056405505040c600030000d0b01a0800c100c0e0310340a80c0300700710668a4003005a9910901c52505440c0036010004125481d0b440103103004036030007100c010640444c1006100010340c0300d04240c00680340d418003411242181c0028500c80c45180104039240e480d480100a407600000c1c03492821780e55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619088498 1250 619087248 619087309
    0x50105071b080f0d0f0606021204050d0b09010908030a0203011418070f200309030d080c030f06061207230c031615091a010815040f0c030204110d0e030405 68
    0x1c0c8241e000441e0514241540b00750706002c0d82c0c6c800c0003206c00d20380840b5403000c08954494a0f50040c2e12401b50310520140350800411201902d0983c845840c50000408021655825026030415107203013610f154040010f10442d2800c03482c1d44c001d018202d440c0082021710400b030300c4d020300005003600104082101c030350701c0720340c010312246c1e240c0300c0c1c0c3c80b078140c1c880c4100c3c1d0049a5030381c00003d0164442d06c13803400c1070781c00341e4021380103035004605001c0c14a246d9600c9044034a22840041c0c42150400f100308200d5a007c035030b81400c2406040c4655038541000c0010010340894008074980121480c8200a42910300700000111071a910b12171075051005a4642030410380342c0c011068070781c550f600b0030b03072501c00304224124181c0509002d05005040303030740c8604620f60789500c28100c003002030500d039003c2004160418070b2040038621540320581c0f12600d9a01040c00e0720014540101034501c0800e6480c04240700380541049112500c0055080516040004280314483c3c0386d641d8516a990441c03419 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619089748 1250 619088498 619088527
    0xc06030209061c0e06072d170915040c060305091612020f10021c020a050a0201030225141005041e030203040b0a05041d191e0501090504050105071b08 66
    0xb4107002e4805e80b0224a040440a081c1d4825460344030307a4030403103041d00503030079101c0b80300403464111a594030f0303102e01e142e0b6000020605002c1c203030300717210712a04007001800740c295504280b107548500b0000f035000d403801070007809940b00508640000e411130b4642502c1200601c0310842241d00c5c071101c46a101c0300d1030000c0303201d800001980036000040089001e00c1d054000400c540408186c084115000a0b240303003ca8580d1042d8600034600e0f081102280007643c405d801405546a444002805075103030505500003610306103070100c0c5c2c2d140c074088026804500900407403401405c5500c1c240f0041c80d20ba0348068001e00807c00e00180e5000401040060510030400d0303038046c0403250341d81c60380ca43c1c204001405c640c001e4460a43d6005940d0a00700d4862030068046004840c502c0c0c003100d649404102c041c0c05007855826100c0e64250039401d0034103400e101e00a0358000c10700c0650025039070525051039400e444005241b88240003540600c0241c800b190b00e041c0b205660491a92620391441c2521701c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619090998 1250 619089748 619089761
    0x8090a030c1704050d0b16020a0b0a05071214040203070b0f0d0f020c03030112170408060a0b010315091d0105060604090b0105070f110901090506060a1209020a030f0c06030209061c 79
    0x40d001707401c004002042041c031030320b030070b0003a03401124001031040044000c0f6a14440c001008084d066903001140010b01c0390b4000b0790300483c0c82c7c10880d20010b001d0b006101103800580c0502c0418040e1410b20041d0f05040c0f00f41b101800002c02080c1c5003201d002c2130b000e1b0500c01e0840703848101eaa58450760300c202107254142e60490b925402076981da96521549808041c0703000406442410b0010348249020b40c1300c00446044a04c560054000c0c0c2d51666028070083c47c03299030306814103403940300c10000c2052042c0742c140035050030400042c00c105a040302d460f1065030f4010380b5105a240400380001c556521050f03e0481d00c03c4036020802d011840c004a525000300d210040804c4002c41342e8008000034003240c43c1c04a1810380307009250b6a619007038201941d000350746d03294001004011400a607807203100c030a01d65040310300001c260031404c0d5000c540c0359542c03035100382da40c0802a1042010810000d00002c01003031180382c11350411000b000080d81c24440c10301d5181c0b41c4000b612850003502c00c640c0110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619092248 1250 619090998 619091009
    0x6060a0203040e0924160206190b0a030b070203130b181c050303010e150109050109051003020403080c06090706030b0307090203150301050f09010c090305060126010c0c020108090a030c1704 83
    0x68800c2414017411002d448002d032801e04000f801d01424502961000034254403402c0d06045607444130450340d031094000d044c001c0311660020400700001c400719100120325402160b0070f600541d680d401098142205082c0c940189182c030740304110381411810318803d0261715840468502c142d074101030494242842d41104028001d01021000043c011890804d0358466541c011812a01603100801160514207034091140402c07180c0307000344840e091a5840002d83c0d0040d080051405460b0340ba4500c00d9080341c81911a241d200c1c0c010440781e20760503c1000c00802c42130400f840001e20741800281c80d08814000e403102c0550100c0012894003c0c450840c0c5011b40140080046040098040d000b00b40c2c21101d030b040700d600741000301030150300c10348220301240e40150151210f071742001c01c0700364401800344203540c036020300142c581d501c520288600c29007005591106800c1e800d80d4030014100900081c01e20115170400c91110010907089000a22040d130301c5403510710314500590651304a405140c210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619093498 1250 619092248 619092283
    0x31f03050c040c051905090f1c05071205060a0207030504030b1005010801120f0f1a073b13180b18030a17040606170d030506060a0203040e09 62
    0x205012010070386024841c82610300f84155165908159a2842904101c4042420340301d40c8215031442140a480481e5000705058180c070603600004450290000400240b8898400c2c2c510806c0710810001e0002c0840c6440901003900c1360301c8440c0c40d000010114410960006555010944036200702c034080c60340310682c80450300340440342580c00701300c03406214081084007001003540741c0c503500982030b0903a00000b581445403007562050101c642c810011a6149803500885103031040c0d00e41d1051048040b582c079200c0c0500354117070310030645c5410815840422990234540c1440e40a20008032030892003698a401340ca01036251a200502c145111141c4108008a80c001084484822640a00c03120808a02c4001521810503120311400c20450040380d880e05202d0b010005000300f1a60160007008005645983c42c0c007954942c0c4185c600c0129941c119040e104212a0503100f11600024240c80003401c0c4070217040043c2d6248214000d0034040060240003940c401d400f040f200744404403c210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619094748 1250 619093498 619093561
    0x90311210d090602191e05030712020d0c030e011b0c14010e100f12090b041a1312032f0a020f0118020913060e0303010f08060103051203 60
    0x11041d1680c07046415800000d40c10800015001d10002d051380401e8417540c2e04000b54240369a4607146000c41c298040041c1c0f40320090f41003c90003d00c0500001e502407841d40f170695115602c002d0400c2c3c040345404c0c003480080c0100708003082c0c1c41580c030441c500080c2000341c90102c0402c281d00d4070050034180104421401c4401003441051380310103a04114080c0c07034011000640764100104041511040700004001c02e0109400c0344c404c100910f0f091003008000509140c10f500d4180c600b000465050710485e43d03100c4c4202065400944585d48003d0b18030607921880001d5880d00004180540240c0070503403034041d021449042c0c00b61000c0b030000e201910700404a51103807028400d4202100c2e010260090700b07182d8200358010b00482e44c980c100707000340e182d40841a908100ca8248045c242c0e01c080b024801b48034001a0070b9200d83c1c1c2240c0c00c410000c50702d03589050664a036030740d030b55003203d0401d03004240100005440050301e800d1684294584030b48135a034170640d90b121460500d480d040c00581500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619095998 1250 619094748 619094809
    0x507020f0f160b0f1e0714030405130c080a020309070f031a091b060f0c010504030e120706120c0215010608090c0402180118092301060c03090311 64
    0x40c01610091500740c480141c41da4820f00310706640a1074080e8040d0803400c0040d6640710a0440010080f00a03207042d060404006464521002840e035202981c2c0da80006010310007440d10b50a0301e0b03c00c00c2000320030b01039001c00b01d400410603100136000c00304064020020510b04201400040007400c20240c012080d2503603810800004068442540c8440c000100400c0d01d00c030707004ca024605036030941d15100d01c1c095140240910381d8015050550341410a00110007503000a024090045003e541c80141c4140c80404000842154044410413130380a81001c00c5800e030065040c01806038035140018510038941c00c240c2c103045608081c020700301c000c60004501139403c0f119650240c8018403c8907032624031030302070000700e10981a07182410086c2d45540c864940c400c410940114402c1e400c56102e6640d00d50200080d038403c000b4080c1040301c0e800e945030414074a400c000740144038074a004248102540c40140940c003030f50101030418051002124026240c466000c000109070703c00c031560a66684 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619097248 1250 619095998 619096003
    0x40602091806040e0705100c02010306030c060f110609070317120112050601060e1f11010606030b0108101d0406110d020304030e120d0f02011b0302040f0e1303030507020f0f 76
    0x2121110f214602d000e101080e010740c006080010340b08050100c106111410506a82c06003000108a040540b01c0c10044006804085820010f003080d442d0fa40394a0031000c2c024150000c000010001075011702d040020205c00011443c1c1241c2d00b10000d580c4030080e0294400e91407140282c01c0e059441d00c9400060300d680c003801c01c42c00310f6003d403080d59082c1c0d0722600101c8018401741034072a440007215441c110070044285802c2d800c1c40307490811510040514083c1e5095400a80c0f08502081d504c0180a516580200c805503002d0f1b4039481c0648a54181054070345603440b0207414074403c090030400501001456071144503401c0c154180540c40d00d0890180314083d600803541240012041207165a841c10b20820f03d40c40540b500d0b004d0150381500c07490448040b00f49509150844d900c1e84061000c165040a502d10b0765040c1da5009a40c40d42401c075070384141c440991169141ca060142003050ba241002e500e40b00e180d40c1740c0b1300400d282c1c0b5000001c0f450008459190714176401141c03016500360200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619098498 1250 619097248 619097251
    0x140108060f09120a2322030c15031b08190b1507030903080304061d060f0a0510120c06020c030601080a0f02060f1c061403030930031e090d0b0406020918 67
    0x1d41c0a041803d107500c0c1d0501ba40054070006268481600041c814001e80d010017800501a1b8540040d90501c045230140081d00003c200c840810060401d000e461150000110a17001c6115400e00c01c500301000480e103924a0300102051130300c4003203003038820544106202c0700155048043c840d01c9007400d040c044010009540380540010307051028643c1c54202107105445001e00702e94486040c0d6034060940041d15004040300d50b03003241c5504c04161001501046008180100c11a003406804c0c800c019203441c12940900b8070070f500080042201c032000140810342c00341c1c45441c1c685550842d10201e141d42c000d008819400c0e0001261042e8800e129803040f2907251484807040c80601c0e43d0ba40300c025040c1d9080700003500358004202d4040380781046908460810860f4214030100c1a40b00c07044503480d2150803940b8040d8000142401103403940d1000840424990210701e0b180c0242000020150300540000920704c0214500203405d0288a9050f142009800b805407000100b0703202c4030036000c040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619099748 1250 619098498 619098517
    0x80f0405130507122403061b090f09020a090918051c3c11010b030c0a06120e030f0a080a140103020d080706140108060f09120a23 57
    0x164141d40441604601580b8002c200584681d44050340c140101006804050502c05071110440c2d00c011302000d02c10700c000c000750300a00b00090324000e80e007070040081c1625101c11040001c140c10620094905418000803140e0001005a6442c071010060362174900e60f0340301200151602000780e2034410b11000c00194284242c0907075034001307603142d901030380802d0b00c03112600000c01e011042c800325102c250110790788100c4e2030344d03003a565554658141c900000b0101442c0000e074000a154640b0082405030b58580002100030f000345100c0b6501007808207005215420802c00c050080318441201c0f0741c02100344020200070f8070b030340e01c50300f90300f90195500500312480010040000105e1410a41c842c2a91f200c6180e01d100816034a1602000304007001110180c0b0015800c00c87d40300041d640c7d100c0c1c4410901401800b140541c50680114100b100c001c3c414202003a800d001c01c00781e402c0100d10010314030094032516440c1ca800140c101d4110000071030050450001c00e1a0500840014000c3d005061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 619100998 1250 619099748 619099759
    0x705100c1e030c051b07080a0804150309110103050604140108010e10060b180612091c1e0f050c0109060b03120a09030201030209150d06051507020a0b0a0c080f0405 72
    0x103034031100440440d40f02c8079060002801c02e100300b003000303990342c0400220643c03d00101c580c495222514641040b410b0f5400300ca00c424005000c000500005008503040030440c10104199821519070f000c00910a11450381016525400151b159403154001d1291140020851440c2d41e1540081ca000301120850307010707184191142101e0720151400b030340c0107076007540301414101040214503c0d80119030104455020b10148030000c0c0521041100510034644e1000a01140081a80c500c1c2581030a00d0703468100040030540c5002c00c440d00040060b902031a02c1c0c80144040e00c2d1008441c1030049540d921241d5080448130030a1100717030380200180b100c0440590700b080c40c507500149220321401c4000004550f42145c100090b41c041e5004e4903c40308098468240c034542210110705070b6201001401520356210b10501c0941003036121184220a805802c5113040101c1e000180303242d2485c8074051407501c000429540c628851555003000590100340603441d48008000c0008a41081c0105070190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 619102248 1250 619100998 619101047
    0xd0911031b010c060509070e040c0f090513140708010f020915270f040207050102070c0b0c0705040e01090f0546060908190909060e0c0705100c 63
    0x10101c04100c0d801c007416107891441c0d0100d550b944d009080001c0900d4114000e10000103130034805000b2482c480d40c030a1041c1e2200034280b0300f03502e00701210f0b500158a250314080810494440c000e01000c86a134118a94245200c1000c08062601d40290041c01c055400c0515603000e01400c3c2d006480754040841c1c0c80e0000506070401c508003405202c46840e0f444007081e0003c40d4801452900d0071894001622418a00017401c1c0480c05a07480904200c4460794001040800d014200583c0c2002d4810028241c2c41d20b0503001c03074203699a40c03501070b0724452642caa040b85040d00c1d007544a003190315800707235250001041a0800c2619609520840038642030000c03c8440350210b54000441c0e4015078401440210325156200d00c2c50201c041802c4030080d503114243c10100d416038010f44018049040350081d4003c0c04040141464207581c804280a4109a81480700452641c209a807100c45080010703101c030f4181c10081e2070f2044c0200d4a6910074503202090640b1940010300b003400e1094042e0310030b41c1c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 619103498 1250 619102248 619102273
    0x11a04050c07030c0308071b03050307230f0906130806060901080a0503030a0c2705030c03030903030d0915050f01170f0a0308100305010608030c0c151804020d091103 73
    0x120300c505030b00180010780c600004400030303024603d020b820241510b042000800d070001e401d40f440a064000383c0c041207000c0f0403c20000e41c85032103c8111046030807403c0d1154602c2140ca4000c1c094081c075001640008100b140c0551514401c1c0c460070440c00d094034030b50b2981c0340d4289480345010b94149006200f1100082110503001070545200c50b4000010342c5181c1d40d9101c0038005000883d60901040020381c030700211140d26420903005080d040c400560303820703d001c0404d807410004258075402070300188118592a500402510420714081d070700460800b840345000744d00021a01c80c05940ea40c03a00c0140808801ca850807103068034000c1d180303072150103000c0200e01d0b520000050850003a510a90095000a1080d9003450b0000c80102c80750340002d0b180d540301800c0d510b107901b11011035030021600f103c00020803c0050426a0150383e140644c0c01c3d81c14180b81c1500c1142c1921110406105007008140c84a60444140b500740319010010b800b07007071901207095040a015144a4841d0380c19a406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 619104748 1250 619103498 619103521
    0x121106180312180d11060d0e0f060129030a200c01060e010b040521010b101d060c1c09030b0403020d030609020a09030f021309032028060e011a0405 65
    0x142c1c5030088405001c0900100400c46c0907800007005030300040e1140c000c005081c8040280011140c00c820107812198100200c100c1600d40c2014840d400b8210751140c141800016811650000d2a41d040071445001038070003007070201d6981c0e144000c800340001e00302e0aa104194032a40913100218296003007640e8402054215004078054580d00c6400c0401d001c440310000c4161006403101d01c0c00105403e1300c00000505041a10355041000c6407882c2c04e0f43d540c9000c03030300b031030301500800700c41e06814003107041c02103550f8154051b01800c84080d502c960495146c001e5055200039a0f000102e8001481c1602d0002d443d043c601c001100800c0c2050f00c0401c80e0710050090f01e14041c0e6682c0c1d44192586982c495662043d09580203903000407503c04100a0022180246103040d070007a242e2174114a074841107080c0c5448518a80c8503960041c0f94800110701c41a4100c07001c040d515010440742d01141d05115000f00b4514000e410340d9840c00345900c00500c2007085916202401b15130401160f41d03600080c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 619105998 1250 619104748 619104769
    0xa080624040b0612090a1e050105060414010302120f01020715051006050f0d0b030709021905030f040b0703020c061504061703090913082212110618031218 68
    0x3da10020620000000000100d21280e0048100046460090b11920352006d540380c24844d00d50158003c81044003030240c02d009854014100340c074104503842000201d0700d1001410300000784180c503100c41e020380c0344508001c0b0700b40d0007841d14021582c8198134607040c0d00004402a110003c981883c002828071180502203904503405900c03203928140444030002c0040c1e00100d06900050350b91a0004066281004030780c010740720a180050792a40210307170b09280380031012446d9041010400400104d0400c030311030241c20503404a5040c08039180c500040d0080d00603140400014415a0208a00c01450503080b8080a1080c2c07010005281c4403029a1000c1044c800f00300a03e5000700a140e0103414416000d66101c0c45544001c004030b075040d554012a41d20980c0c00096840c80914500816203529190500800d2803140f8036000050390307070b82c00400080c40750b88148202030202c0e4600e00d031740580300791072130001c0f00405a6440e900c1307281c1030a0050300010030000c00030a1004c030b1500e15081c0f40030440c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 619107248 1250 619105998 619106021
    0x206071e12081e07051b01140606072013020a021b1017060a030507142b0303090206210f07030618020903010902131410050d110a08062404 61
    0xc00c008800d09414100f400d901900140400000b048185600c3c00405040d01c0c21001d00700001c41d080c4407403620003583d04005080b040c41650304104000000d0031040444c045a030780459240c5082c001ca40015208041810907081414000101c20740040e501040395400641e10500c0d411140d030010051000201d01000a4030228505016407400c50380d0442810354440c1c0d00821861495841395501410b1040550041141c08141c1c2c05661043c03030100302c041c07080541d80004120200f61a08d000c01f030004031000c054185940c8401d02020740d00c80300200c69500f001004c402c0b03400110a10030240010b011162900a44980f1002c0b030b150314401c1c0211400c4440303007480380310600e0800704040020741c006aa45903066581c0c03801d1a0040c1c417034420700d40342c440810400144905840c006024210030003480400099031403007086c001036881401011000b508079068001508003080800c00491441e0002c600d20303c20300c1d0411400700c01c112182e4031002d01251b00b00c0d1100c65681c09200030340302d250044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 619108498 1250 619107248 619107271
    0xb010203070611041a04090501080d0e0103022206120e0d090e2a0403110109050603070c0501060f0b09030717071502010b0d0309060e030313030204090206071e1208 72
    0x18400301e8456002030300c51050a50744185421783d00d1070840541c3c41d03008003101c50384030041003c200e0307441d0a2060600610741003000c0c001c50a0b044000034403042c2e8001c0c00701d040c5a8081354154a0108445000d5482c00400c2c1c0c3e4010401e4680a020740075621414041102604213601071301742e0100428880c088501c15142c1080b5031381084440300480750028425a00c0240d80d40642803000c0040500d0900c41d071140c001f0a96441c1941082003441d8283c42401b41408400300c0100810f449400890b40d1003105854205a040542d1034413038003601980e400700718607030343c010b0011a0111020f4010300c2460411000c850040350b45480004128401c140c03107075481d4001031010004a000842c090820280b10710001429a1090001812030703404154143e0000b0203803c01800040d402c82e1070340340da03120120011070400780032103d64002440f8500000f8040c07510303480000115141d03c0207889000790700c05152980c4903c83d0b40002c1445141000c02e5468010203001060220700810b030242c0144076801c070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 619109748 1250 619108498 619108507
    0xd080406080c0f0409060509010503011a190b030906220503090108040303020d14090f2a0d080a0c05060f010b3103050703110a2402010603020603040f0b0a0b010203 72
    0x14103440d07000c8000c04140760140104481c2043c544080002e102500005000040d4682042c05021159605810441c041c0c0e1415509040b030100c042040154010101c440308043d40c00241007401d1242c1640c0030300c001081c0032040c0a0f0781240407a02354459105214041c010302d40304502c0c021122060440030300036400c01c00a503100765100b500103030380c0039000b81005880d021052490104607a002203000b00d00c6c0c1004000d21a1004081c804103e4140105004095005e0f062010b103400d810071b000d6105c18080c200c00034081948503400310081c001d401c960059102c0c54101c00260a041182008642c0c9004480002c0c4486561345282c034103030703840c600c0d8590800194030759443c003405040135200200c40c04102803040c86003104039001e003c1c620070000381c01441d165140506090103103001c114400c21010301c0900409001c2540440d008030740003a034000b0b0046c800710980c0142a1500040e40202d40041044140902220300d840440d00c100c410400d2651030107045011201081c80c07544c0140c00c00c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 619110998 1250 619109748 619109759
    0x604081b032a0109050d210320090a080304180e1f0209180114011d0f01080a0204080d050711090f0c0901021510081e03030c0d180305180d0804 63
    0x2c00d100001010704052102030348800000e4170144060404568217100e500c000d01c00b81284aa50282081081c03d040c011089a803003840e08121541c00781c050b10400c041500e00b90796980091580081c6000c0c01541e540d00c0d02d511265440d41028610501e840d800c2a11806012600045042c415000c4070240e44460038a8840c020296100700c8000b40d2011982c14281845403103151058001c02c8101d0107001c0080d480c40003d40242e251010645004ca02c40d5004031841e2912031101209000903e8084016030b5030499807802401150070030300e1f01e4460041c0130000c40e6000030091040d20b001c1d841c1000700540030810402c18200840720f108020446501003071014101c14040c020001050040c2c4150304184c08507500104000c4542c0c40f6290350341030003006803a4040c0041c290b00910520004140144042110703541e120290407035040d15400508001c2d8455141d02207a0100e1400c10010302c1c0c10303680c2c10002c080e50404040d488055410b2080044540b41a581c0044490362111600781460b1600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 619112248 1250 619110998 619111063
    0x8030106081503120d0e010203060904030c0f0516051807020a062f070b07050309031206040902030a140c040612020f19090905100c050304061a0604081b03 68
    0x2c0c22000c1034840741c2044001c642d500380031801c158007044407901c1e1140080d0704044240c84601085d0103013a4810800c0c003201d81c4502d040c00b644039426040c110300e14601d80c43c01204100c070204000d0440d000b455403e6610900c1c4403814011100111164000001030750103442d8002c00c1999010056481580403000041283c5c2001740d99952501c00341003600c0c40c141405145010203192590480c070005a80400c11100007086a00907119280440c01d61800032100c994034468840400c1d401000180002c22036507498000c2065194083e00307960346000c161a2079000d40180c401c1611490017803042442e081e084c50310505044a003082c1001c1c51000803174080c0009100d41510454010a41400040c8140c171174542d654000d00b11120006020411424250b05001c00e03200341011043c1451014071116038081d05a03504150405400100c0c2011507502010354036911040e541c0087d004900007842e100e01080b003441110b00d40000319022481c641c10192030307c40d502c80c0310340f80d00c0040136801c41c0103034170 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 619113498 1250 619112248 619112251
    0x9230a0501051f1b2105090406060c020306070305130c0608040b0708060f012d020a0512030f150d140f01060b0702030a12020703080412031d061c140405010c020d05070803010608 78
    0x41c446003c814445d0610182010b0402d01450f004118002034604050505206980090280340b0b084605035900b940002e85a06000e0142c0c4101070300c3c0d41c08114143c3c0d8415140040c903030300c408412007070ba640d440040d00c43c3c00d0850b0291450400304e00082c0815003e680d0a07442164000c100c5601c8490101c0150b820004600d0340112058054025101d4804428042e104003a200c0e0010300403001c452070f08a25045401240341c062803c180188170020341c5403068a0f82081c0e406041c400c0040d0b10101080c1c80c0714000b50003900e6a003408a0800601038041610885404000004d010341520ba0580d10f64074810500300a4150f0702040c00c9070045060300780e90f0160a806441503c1d04280c1e292240c00c055000b07508960310f080c442c030036948101500300c611420107845100060541c1f401c1500000c0c81400b411000d005071a1007600b40b40441c1c403c50f4005118110301c02c0c0304500d00e0600e4104240240300f00b01915000d4412003200f2035540e03024809859040358000140c51079a820300404070703040c550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 619114748 1250 619113498 619113503
    0xf051b310303020c090903190e0303120c0c0712200315043f11010b0a0b0405010e1503150637110709230a0501051f1b 52
    0x2000d4500d00514450328400e80c00440c020f9000340341034800c0008000d14030740041c010181c40c1d07004000d030700c0d1424407098000c0e00046160070100c081c000b040b00864258800ca02c40c1c482461301800030000f44e00711107800740c075240c80c43d00102c8100756146e00d0342e40100f8041d030402510b0b440c4a402503a6200300c082d0b500b10400031000e030a9461200c03200c0010746103120207036400c032104000b404104060302c8445d49000507040d584400001801e0084100095080141c942300701084003070414141c0d524401d40003041c000030007408512884e0390704d407003111032a00a4041d03240042c403c8010501d0a01e08240c07240074460203101c6c2d80d03242d6190001403031280c91603a4003e076040107042c48201b05500140e00411002d8080d41c0c0a04041c07900240d607454960a4850042d080c4902c442c0171001000700004e80c83c3c181c4d00d8441d1b00052810078500450280e11325400c06410f450441c0d81006941003298010364101c40065070550b0194181030717031341100404144c480310000b5901c501001c10300928041903c3c0602d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 619115998 1250 619114748 619114807
    0xd020303011806230301141501081b27010201050c0f0304030c0f0b18071a09030c04020f0a0807051c1a04020310050f030f0c12010e010f0f051b 63
    0x242c4d030309400310f8a0f40c0078100018444148019032450f07410b003805495003115000341103411034907000300d034080004000b804d428100840344002504101d803640c4c540030721111900305a5203610000003d10441d00c0710302075040d00c8010a403440f900c1e95005005041c00b0728100920107040c2074606a00d030b841900000c005070b040200c00c403444404200c0d80a8003080e030a01440600c8101c0c904401c0ea98480301503100d1028065000c00020004e011520800340343e00700c408002103641c3d0594000003403422540184888e40148001620115909400024284101507441c0c0d01c02d00d64805c0c0040c0d4442c02100e400c044092205450b8504610040e402a015142e200245803107861000d03010070100c2e041100d01540ea007583c1c0c0018410b9142c0f8aa06c0440300c00120014600d2040d510100e5440382e010503061070240710300c462081d03452042074010041c0e94503048020880c0141c1000140083c00300c1c0c00c604c2c81d40d80d01d448085a00c1e4589403e60081e008030101c08285859004001601c01a110030044103408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 619117248 1250 619115998 619116011
    0xf071d0c07111003090b07020c0303090f04061802071e0c2706170705030105040c171f06150e091b120c0316090e01050d17121005030d0203030118 64
    0x50f0703a01c080b060f0a0040607500050904000d1800d820f07034400180502041d540480c500000790703640001251a01c501c04c0e9890900018030304013240c0944425007140140e03040da0020f0a2410500303a0141c4641401032036500c1e8500325080b0078031040ca21203800076140a41030071040c0540341d00520b90303516010007400034a04c1d8034450100903048031500c1d01b0400c4180d1004c0e0000070204000c110710700c090801280200403504013950340b803c4002d401e100d2519154505028060030000502000140817106022031842d50112081107006040c01d014140780c58089000140700d86200d5041c032001d01c0c501906100194840c005042003c03000d00e0100c14984004015000c160100154840e00887e0252551501c1e4203000980c68140d00520742920100f200303269080058444a040701411910150381000035260306007089a1820002e4504284186000070781c01416032541c44a00e10481c805003c1c2c611442d140c3d0101502c0c0e010404025006034030500041c401c622029854070055501e0860001740d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 619118498 1250 619117248 619117283
    0x30414010906060509090102090a18022505060c0f12060418060b09010b19120b040e0a0201020d0915110309030105040305120604021201180b120f071d0c07 68
    0x2541c1010400b02d5100303841d5003080101d8240201c0f60fa40018424009504184808001c00c10034250f42c80b801203251680480051448000c3c0e0440d468040410841480c44d12864190391300c89880c0c1c0000c80700c0d40710305000507502c5800c0d00c056803186403110503514171345103a08200a000c0b0b0780140c01242e1081d03992016088603a4017180c000c084506c070f0003010840b00688810001110f00580c041111001d081080081c81c10305141d8020600800d030925841c0c0580424200b402410525000350300036140c400030000b0140300250303491242d03200f41d08603507250441d5001242c02000904c24141c003100d400461100660248441498903a101c208480c00d04040c82c1c0001d09540c4251003c3e004500001400b86456135280b81480e0320007010b98083d4a00000b945912444903414840c906800328102c074201080a0650400c140c0390800601d0255001565503400740c8a243c60120105284900c0500003203a9260b00034509003c1c210b01e03518582951100301003422540130303007400c4505507694045a0f40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 619119748 1250 619118498 619118501
    0x907470301150e0405060a0b1c09112e1d030604081e07080d0506010e1306090e0118030e01020f0d1e080906040615030609140610180203041401 63
    0x2040b1100d40031902d9550302d103029040c60352409a081c001c2c1e05200070000ea82d15031040c08401c85042e15000c9659956901a94540c02184c0300c00b9a402d508060b40b25050004080141c240b20500b202d1b01070180d40110404a5150f44080604401c000d14181e48901c290080c1c201c503905424800e00d89c00000002400170741440030482c5c0c201d940380c0c0c01103446850702c148110300288104062441c0307031418042c1d403a0340405004514001c002d607601c54001480700e9102e641451450000580b121062512030403610307024040364040d401c2000d241c000110580c01050140b6080c100e9402c03c500d8861032107480c200c0d1020b4045454a06501c950523800c00303111400c008000f032504032a551241038120030409054041207150a42003005460b400348001a01b0107d2507079007295000314005800b03000c0720444982d449581d032018255525141e901400e020b50b03220b01209003510001a138150781c2d1042e80f4400000c0407070140003128088005071078500720082c4e00039504030b03000c0c00e844210b50710800c1e009030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 619120998 1250 619119748 619119751
    0xf090f150f020d06031704060503040b070c0218150103020715050912030103030c0203061803120619090203010314060403020706030b0406171f023105041409074703 72
    0xc200c980d40c000400030311046c3c40d48804941040e480c0d4520b4070b464020020024000540050321605084003c99500303405101c1040140b58050320b0060010040a04400b03c0e101c221b400c0c0c06414404110410f00358401d100301c0e121140d21031104004c0300d0051303841c00018200240701c4911441610030b800010000d91000c1c40c021446a5611070140320740d171061509003c0c01070680b894140502140f101d03128008010f45841040d010803002082d90f403180010710989141c1c18400710100c007541c008ca480759807600114140c2c1c1c010383c01600c401c0216044560307145012900640140c20014060181c0c07882904820711a182c01000410302c152101101c050500b070038085c5550503441502c05200300f4103a0034141c08005244041181005102c0d4401040020320f90181046810304074402c440d02106c21001e0400f40601800070841c40c0e82c422260306000303109481c002c0c40c904c102080040c00c0f400c0210300000c03d4213107a021400009500348144400e11140e103000c2c20b4031043d40c80c04038418035040040c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 619122248 1250 619120998 619121017
    0x809010207061b090b0909070e0307151d0f091909080a260708221e03090b070201090501050708120901050a1a09040201050309030c070f090f090f150f02 67
    0x1d02e0030001284090000c0b101613005d107002c0d85040c4a2400d10742e855500b0320b03030700c880716080c55132840020340002800c02109401240b0130000c3c106200f403001b070b0700815440ca14a003241a10030000f252800b00003100c2d8015441c00d1303000079007400081001d813613441c0d1080800443c02c9c0c0411503449907600c0100642150b9656000075407103446088204000001c9c1440294614031402d60b50300303140b90700400c404002401c0d580514603801c0314000840c020000360140d0b0b40c0000c02c948959102102201c20061204015030000e44510030100300c44100908840c00154140c41d40854980303004010b582503084440c06441614051001c0703030300306062200d603500c685444c5000017a03034a440403200040b82c1804907a015170503070302c15000800b031301c030520b010b6081502400d06e06c0e165a0741100861452207014066840c40c00b8181002480d42c0a52440b10291005030078203200040914108004441c1c00e08009403a890784000040702059086100000301a80740030041400344000740c0700c00c203a07030013985039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 619123498 1250 619122248 619122281
    0x1060801140a05150621040f0212070602031213050f01240602030d1517030d0f14130c080304030b06100e090a02090120010e0c0102070510080901020706 67
    0xe03540c0914141c0c142540c062101d0004121a00740b2040c1d071403800011140450142e240010320881c000303000028460b00120a02412030a80b410345800900d048440600b240198900e401941c4200d0340403451a0603181a41e0046040c203083c5617240c20b40540c043c00c12130002c442c80381c00350f021400c14010100c0001d500340002c16550410311415005450101854082c522491010300032941d0220444070503190fa0680407071402d2079180104d010126990101c2003140c800da50001d1151408009017840380400342c030400c6001c844580100998280392411446a100180002c840b0f00440003070662031401000c0000f1190784400016185611070f0300240e8448489000304002403500c11241d00040725035150110540304400e01240c1c800710060312a50503c2e4002c1a45402a481440074954294070588600403541c0340d2401ca60081c0703844081d445150195407000d003465400016440704580c4007400d01c0c0914070b44042c08950021014100b00d040395000c1108601080d0140038a80c03280010011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 619124748 1250 619123498 619123511
    0x70f2a06060e0f010515041e050d0f050105090303100e07021612110d0302030901110c100c0210030b01020c040f0e03030c12010f180507050c0604030509030c09090a1403040801060801 80
    0x500c59103c0e00140d1003a8810094514002d28425039481a14101c0d00c6084070040d8551300040359640041e40750704403a811079070000071141808035000c08000e100e402000204031a0f02c40f00c1e4142c3d281d01c03040310340c00c50007200302c2410050707000601040c503800300461040e901e86020310b6042c0c50050102e640804c8841500c07405800510810540c0044421412501ca052030440381e0350107503c0307005050b80141448801d030203841120405008580c941e8400504013040108424000f82c40160303920016805100c40e898401c40180c041e00c1004074021058000304010241c10303007000003900d060300c00c9074829604c840b1581200da4041010b03500414511410070b0303d842c0d03189070351007032007105902401807103e0002d0304000040c224811111800c1c4040804a40c550307075000144c45a12400b5904900c5102c0e40d000c100c10300d64060007404064104400f0748285622150403c03410304000d42d0091680d0b0003404a440c001940c090816139500101e50503a4141aa5404c0150031105c0990049031580d44600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 619125998 1250 619124748 619124761
    0x50111030c0d180602060f180f06100306180c0e090312041101080f0f010605070807020904060e010506010c15050604150f060e0a0803070303050601120603050114070f2a06060e 77
    0x103000c004c0d00c40d07440181420714000380700701440c3d50041c0218588556405d50011074241c107200b0254281c0191089a225040002c449503180c001840191246403414801300b22044036244c00c1c244550300071000c241d4050030306040340141000506070a103148010082c980206415903417151103a40100e03540500c0d100d94400242010740010302115481c42c46400b00903801d80d40031091815a0458648151568803624003816988180c401c06035100b015242084100f00e41904807482c1802e030309000b4070540d1103002c01500c42102100c0020b01c12003000d401c0303c0c140100c0d5030005902c06001000030030040c584140c50740d444c8015412650b520042040103000142e00a004003107400310650320340074064541118282c0301c2c01000001010140c898020846680c0315944039081203054074010405240e41c2c0c9402c5000f01149000c510381c0d00c13442000600e001d806800044400803894488680750040d000c00d0000e4030002c06030440c40724500c481c1e41004210303144034520252990506c80303082800e000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 619127248 1250 619125998 619126037
    0x50405060108010305072114010b04061707052404171902010c06020d140c0702130504020114030c0708071505100303053a020702100810050111030c0d 66
    0x244800c0c140042c80b00100001030001031040122044141d40c21000c1e4400c10300610403110102000d040368508100c0030a5052044d400040501c03001c440400246079141078440841c030301d000c07400300c01c0e0b040840104110b01b0130150140c2a0381046091201c4000c49190000b05a00250000e10643c0c210a62810b044e400810101050345410180b0348190210783c0d0008080e1284640000d040540205030390702d004829810420130700e40f0000da0585140303040203044d1750316080740905911440d055043e24104a035903126883c019a01a9620300300c0303070208d8450503000e80c4043c0001410300300410601011440003005049030764413030031810000b400440080004d03134001a0a580003000e9000702000002d03041412201503280240744e8030b0b45c216141030945600041d4041410019540110020074901642c1c010100307540f01700d81500490501c03000440e0200720860740c0041420910501748802d40c041c11549441007990402c1324a080f540b42c0d055420700075610304000101d202400c0c51407501d51807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 619128498 1250 619127248 619127251
    0x5041701091a0103201c050f1605060906131503061418061002150f04031b0f022209050d020105010602031c11190f0e0d030f080711070f050405 63
    0x81408501c0c055045854101d2990300d0002c400d420008110001e80035600c81070b402c07810316415003011b880c801026040c441d84600074031051350f25600921500070190303011004089c3c19990098403e6003040e02030230034000203600c03e000c1502ca45c0154403000070345d5401c40c03c3c3e0b501c0008460f0f0b0003080309071600701c2460f6005211400c681c890038400d410070300d00040720724a07039038004130860340032110307000403102a401e15460320904141000c0c82000c02041001d508500c034080c038800d50322410401d000351311807c0e1690101d0b1004060f407404440440c00740c940700c5030011061030481d00c40312400c1c180448840440b01d4860742140c06400c0140200310081d02032081c00e00510407400a10f1402081d40003d0303410080c50400c1d000d481e55a103c600c0e064250386010344081c030141c8550000302e201c070380714040c006460410b081800500380c0b824110190510109202e0703000d034035440b00c070b4120000c04005d0321003c00060141040220542c0c2207007034080d003085044010320b22030321014030713103800e180c240003d40c4c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 619129748 1250 619128498 619128533
    0x20414151c0f06090213020a082406030703050c090d05010f0b030102040b040306090804030219080c010905010519030b0a090e010b090c0304120c02032409071a0a0504170109 76
    0x104807203188045011041010030181c2e100900142a0a1034800100340024021312048507501c082a941981c40e04811094007485074800c00001d8210756501c0c84c0a0030348110311310340e04028103102261189005c0c2e000260015050b0ba40f0300c1c2000d070340b000032030386807401c0045c00e032942d07912003002002030095031184111041050300254901801c00341c403150070703208071b11000741075999a0340168144405071040e50081c2d41d00074640c0385d8507030104141c90021141c034010b45000c0d001e00c600701c1d03c003980603000d48004c031303901a111241080c00d41c96a10101080785282d00c003c0c140c841926041c01d6480c0e0131010040c040ea10070010741700c0800354079035003112040f04126003d00000c4003409101c42400069a90140d44645101868190341008035022204070741c0c000c0d0107105850481328105400e140001001d07516860912040e070340e03802140d513100e070148118084070341340d400d44000072940c400080541000d6400c0c8103241c90360b0390320500021000058088510b9542c1c00d100300403c060352140804014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 619130998 1250 619129748 619129789
    0x31905040512010624051c0b030706030b09070c060915020415050c0312040c0b0409090303050c07111e0a0b091203180d03030912020a120f0212030402041415 69
    0x6003417589000c10003610817008203545408541850f1454071540840d00c3c0880c0440c0c2040360b04500c4100b29014011842086119004283c00440c0030ba01c24459032440110003407140189458201c07056070082c4865609440391a280c8035007201048880742c540c2c020003568280181d4451500344450350750101d1702403107020048104403d0b00c0340b0707200100b503030645841c0001e04801521140340607040b00b0540c0d8040e007150705020a001950200c03d51241c14158040c0d00c05100568600c0c220190310701c2404070043c0300c041640001c0c0c0281c141200c0c0381281c85070300c0c0c08050350101c6103000294440a01d50100c1c82034a800140c1003003a040c201c6408242e945003800a608141982d440722001420b031016041c0621001c105036001d062203038008013200e035000303149804c1580c0c1c1c03164000e45491101da01644c1e450381c22402640404d2042200483c0c2e64020383c00b5258260704410b54020980c0040d00990348161601a0b09500e1928140c145000c0d0380048800380008103800103020905070715440b440c4042d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 619132248 1250 619130998 619131011
    0x110112110307121b050f0a301103070c120210090b060a120308010b0f1b06041b08030706020708070c0609060206060901031505091204090212010504020405101103190504051201 77
    0x180c3c0210648811b81080030500361584080b41d000c44854020040d1203042c03590404c04603061203104c0c540c1800781c42400c41e050001c80103d00143c0020301c415100030780000d07500e848840211304103440040c41c0b05540d1040e00c00750f5050094401c1030703c0c03080d042078031000255070901055161141e641e00050250141d025800d2605032000ba00002d0b05104a034008030001800f2000d4200c520304580d43c280ea106201c1380e60904c886c00c2c082d964441110100d5407000da41000f001c0e004030303003100c540c210380140b0001c1d0300e002d400340e603240040e421554040b20800410300180000901000c0c501003d811150b81e400e41803458103400030b14000c0007907e6075003d103940d64011720229086070b03400b0f04030b601301d00c0011401303442d0030001c0c9103072038004400c40351501d10105011401d8540c80c0c00401e00e10303580c44880502c90762203204003c100c2c41907125199101400c1140450081d00070110400800300802c184e90901211b0882c0d05413014800c882030000900000c1c1c28810344c40d080d100039402124540c02004907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 619133498 1250 619132248 619132301
    0x306120f010c180e160513030b10062304050607060603172109060f3402010c0212120403050d0204090f051807030b06041d01050610080411011211030712 67
    0x1c210072417002d00100030700000d14101404419958600541d4490b0420b01c0614025001e805001210302a100c0010100e80964034800c45100564801d111040910391420f40b805c0100400e0b9800041c04075801921078800002003448208101402240308448694561400b81e50200b45403240c0101c0c1c0c501c6c10301e48140080800000303005507000754051440390075501c4141102070100e51202c4045409060601c02c41414803003d801ca4402079040d400a20441c40811002d985450300d841c40140c90b0402484180703040700e91640c200342c1240c001e0a0451410010058245c140ea01c140c000c00322240e00c8040a502c101c0311841015804902d00a44a11900c1c0341c2808680340d640781e00c401381c41030502e100131a09a6850b40c0c480c070550701845442141c081c81500741c040c064a001c64182d803054000449100a141c080e1aa19220f40d41c441e081d0741401c1c0d2030000646024901007001010147d544c44890030050080c03000394016111a00d80d01e9031910000d110390151502e81c42840d0880342d42c8800c0508 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 619134748 1250 619133498 619133521
    0x90120160b06011103031015020712061104050d0c0e0a1a130f0905010e2112040507050a08010515062106040e12070c0603110306120f010c180e 63
    0x941039104154072801d07195400121a400c000081603102c6010000501c6901200f002c9400c00300c0300b0484030490000740010781070342c403a09180310b4a20640c442800150000d00d055201c4800701c61354814450400ea05d0304041045100310f030404131501d4100c6081401403c02644805901c0800c14209112413001010022001a81c043c17045000b0b4041c2d2603102059081074000310880c5101a40810600496040440c080c0500400c004418080c1d810600b01c0883c0070164200f20180e1084401d152840b000c90501030710700000c1064860f400748000c003080542d5010700800003480618008511814812141110080c005591901c2154100212080e220b1240c05401c40003140c01c070301034040c0d0b0340c0c20086400740001c02c003c00f41c98050010b2361000101d22078080c000c910301410003406c0080d22848203070100c80c2e060b00d90100610042c40022050701d000e400365118251a0801c0d02d2004c01401803003400e45503490340c8100070070201400941c00c5090f02c035129004005401d05200c0302d0030f241c0d401c41d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 619135998 1250 619134748 619134787
    0xb0316080a06030209103212070b1306030c170a1a03073201080408030606071b080d0305160c0f0c060f11060f07051809090120 56
    0xa003801804000503851007034503403140c8000c1d60003414182980c5000d031304d1b8103184a1700c1c1c0644203075000081c080c100340390814813111404041c45502c5c44690f5101204001224001c1800d01d44c10344540e030360104841c0045005031584c5089456181e40c036074100040a03050f9400b5070403000804c14002a582d01100662850300c1d000b0561480010701e1480d2514124034880076a15495014407400100241004c3e0310780403810290902c21611011305210750f280c4075103185507200c03d400200c208001c0750100e04103100541c2c021134020542460302038281d580d13039105514a001d50541c0e1204040400810000f440702600c500c849140811152804e848040307441c0d20b4401011040050540f15a810030482c1e544d40c1d69840d800091240c09580e58a000410b520ba8503415140062103561201c2071049000412034000c0b440c3c04450091581c40385821a078607003100362202d540d0007000410b0b044d16210507060a0240c02140000300d01440760345080030169031149003aa0a41001b006024801c0d00d940c81504e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 619137248 1250 619135998 619136041
    0x6060b09100807030b1c0605130506060f040f050a0603110102120313020102010e070e010320030a0b07352230030e070501050901050d0504051e070f0b03 67
    0x5a5200c8803c1100109114441a5008240e00b0740010714201009602e104103803140d81c0500c41942c96a020f440038014801d40104642d2100780400c1161620300d80100d40207101400000c0c0041c0d604114034141c5109070751902140d03555480c00d106020300420034070f400010a00082004083c5101c85069a110003842c084500f20401d800b1301c110fa100303421840ca100c40301002c032103210b511a40350b846c04490030300c001c88003d406800e101d201c81241e078402004c0304c03400802800d5240d843ea2204410300500401b14020000c881c2520f800f0701016141c105104130422045869903011010061400305003e0000d0118401280c0810344a603c43e000001e43c480d071101480e107102640c6100c1c60039061034035030700016500c403200d081442030307034141d0041c43c00b40c1d400302c12202210395450041d07600c0c0c41540803582c00038030104140408024140c02507030304184070b00c080b200b00141c0a80ca600c1d514003030b030f052a001a002940100102c076115404c013000340210038541481c60910362085542c44003a502007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 619138498 1250 619137248 619137257
    0x20103090c03060603050d02010f0b010e0103050711122104170a11060a0e0c010309050c01030218030703050322050d0f03031805030a1d0a092007030c06060b0910 71
    0x2801000a4400720800541c0d2061007400f0305600e070b180654a0703460280e00040103601e8281100062035140c0200c04520344107840d1100e00c0b4440d03100440c003074180242068180100d4500103c2000c004008080001501c07810040d2602c407808050030681144060800100400609000224964801c2c01c00b0b0403510138a62039880130b00c0c05e02030b80c0440d8014021009402a101080069005500300302d01c158070681c1903803041035041006500311510688090402d61060350145225402035004001300e40c0f00800c6800e1032070726070340000c5c80e0079450b80049665400100e20805422180b030700080c81c5280406030046004c0c00c05000c84c9401d15140806410b00c104441000c0915000740e100320b00d58840180c4d80401c040c40d50811030742c0c075400355090600096450307010108042c035206440d419458000c2810b5849450501350750090b080c6d0080045d10254525200ca41c045002c80c002c003401480307501c400c00200f101e0305110040b11070300d50202650b00c104029404040e42d90404114804055041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 619139748 1250 619138498 619138511
    0x20d091a0702010c2a06020a2604030203030f041e060e2704030801030c0b04062019060506041a01120e12040f080f210a05120a09030f0806060403020103 67
    0x41300d80490443d8040c0c012a07003044e50455280819410101262100511480349603440030101d945030500c6402910140e42900c0601030301d09620303c0440034090201240e420280c603a00041d086a100c44114020030f10001030070020103403043e0a2103607500301c0001c000c00c40ba28002000d81601c8011002038441d44000e0142c87c505405100c0c03404070020035282111042c542460007800e40807080c00103076518641076100240781800c00d0b0864050320255941d1000782900c03480c1034a4002d00300d0810318030303d018a0322544c201c201603200c0d14220318003c0001050b80d01b407100c1400112400f11000800719034040c0d07056800759070090704174081c032000100001860f0f101d1415290425504170f65194040e2000640000c01d80b086007803601c10342d6071100076180000d104070038483d038440d80d044425074490321415a012070841042c0180030420b80500340b951821041074042c40131100221491007580355114225005c0c9a0b2141805003556840d092024803800c00e00c0009130b0074002c601c0002c0c10151500d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 619140998 1250 619139748 619139753
    0x2060406020d020409020d1d0d0905060c0f010203190b010c0807110301151203030f0509070b0d0b090c0403060c02070b041710050c09100503130b070c15020901020d091a07 75
    0x3e044500400d42000300715103400042032814081c0504900301c0034011191181a8505003001c1907a0001488648031490107038902000e0003030603003041804041c0c80c001d025140c4500c0303d0038001948205100c1903114003111242034284210340e45003604a0412180c807050b030000859060489082c00d80117046040541c19080000740944180600c81d24405a04000054152800d0002401c02032194405000000c010781411089074003c90b02416164014203003044102c5500b0010000015043c0c00401c0c56503903400401d078100c4050300d800101c114005002c00602c4070501c12212050820310180041c0343c5450010401c0d8051805401107d00040108000041c000c0111642034242c9080034072146c40c000d072084440741c1010a03568090084074020406680c81101140d1107800340c242101d15001d0580c490003505100200050144000f08070300c04081148207110309170888070343d600541c0d11198040020304207891205032409000301c04c6410310540c0c1c03400e80401c01a407540d00040d522502d450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 619142248 1250 619140998 619141001
    0x1020d0e0d050f0301091e0905060601032405010c021305150a09021c0209030a0b0109020909010509010e0a05060d05031c0605040903090302060703030212010305010204081e030a0f1206090f0b1002060406020d 91
    0x1f8100105e6140144090800c8002b1076034134400c5200341ca040160841d054200c0801d250300f040c2c504141d20001005100a42c010824061946e0024220712101c0780384000076021503205480e043d24607030703ca80c0c0342032803803800109450182141c408150f00748541ea0b2900400540f07442d106000d43c40e0040b0340c03200180c800700400754110350000200c20305940c2d500141c00007948610b00e450b000300b1000c000030840c1d0801a42e818100c0d60910f007200351030341d202c01019000305000303002c0a6010801204d400045001040900344000c40d03100d0700c1d00d0512103840b85804840c1554040b0340564148140000481d030484218400c4079010743d44c0c5550344800303290840c020300c01c2d000c0c540340c484c0c1e80a00200034443c0543c0a001525031341c6003100e0412104076036102944000c0008194541c3c403c00119421503c90b0041800450141c142035090140135140442510204c2d042444256601ca8800502a14a02400c0d120403025555850000c0c1d0710800252103071001440600030790380000e00c81d004102030307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 619143498 1250 619142248 619142291
    0x61003020d061815080d0305060d02060a0315050f06121e0103080703080c03010b0f0c10050a09020103061403070614090a15170609161101020d0e0d050f030109 70
    0x1c0301003084107680381d1800385440d8940e0031000c603200c1d20f400850782038160440d44520a481903600208101d9a950404a01030000101401d030040800a014401a180c0d41c01a000718040d0352400f08480c1c4058440814182041c0c2c0000c0c0720b07040550924200d921001c040f6540151001540043c5903106251066103d9401c903441004c1c008110001040c4072202001e081c555100381d88039207550f01c07025881d80440c002805000c5210000304018407041e0480c00007400304c0d201c11005c1d1503550908100d03a03011907808481d10304000b40c850002100310340c0c0c5845480003415480049040c40442040400e40d40e000d280501401e110340900150035100c200350030389080610051000b030303089813980f0302e00c2072344043d840d401d80100d0310300d26401c4454a20302c1c80c00340c422a000b81103010542e5606c4004950b00d042d202802c0c007840054080c0f4044c0f80760a000901035010700800100b100512206030500e01140d52514204002c81840344c01c25603400d1404582c1103030f000c1500851007007039458400e01282c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619144748 1250 619143498 619143517
    0x60f060507050a201221160204060303120f02040806131e080703080f0402100e0604030b04060903110313140a0b03070207180603030206010302040504080c0303040b010905130b06100302 81
    0x7407001c44d04030082030018460b08031500a64800c0004c5d010480455034400b422500d100d44140c07030804d000705410102001e00300503c00b038065840c20600940105080b164103800a40c00110011380204017032400c0e00030190792441d0751307000314541480d24030b81c04c0c0c95900161000340c460300000182e00502400c290144110b80c9014883c8080c0c15107850305910070340c0071110460206001c000006c22580300118143c0c030858000e0a80707200d50750040b40444a480d2041a070300e500250034072001c40460003070413090788514880e9600050780c9249050185c01810000200c80c1c4540c0104007104000409400e008100ea48103041320040c0d41103000050b1030410030b5007018403035007404030400c02120780c001000c404545000d4081800b54101c11405411380714540806009030303114500410050525900141d40325016500b5503007424a00c1c2e820390700750340c03007a5003d50303040e40d016005109200552140a400c010307590001d241c006007907903403203055103001040540710301c250200d040b0b206030082e01103401000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 619145998 1250 619144748 619144763
    0x306150302031b0a120f0209181209030606030c01120e0a06090303090b06030c03030f0d0914340e060d050313182003100b03012601060f060507050a 65
    0x3c242ca103800c1104001c40e09400e202c2e44c8507210010b1114161000102d41d07940244440008410030307000e0100300305002d481e00a40c0c601c60140c2007100242402510401d52031a2021a52080c000f0201803030000702403d00c0c1d00c07a030040c0558030880e0fa00225a900c001122007004664040701c0c1000909041150308007900345030400b4909402c0550541c030203001648070b8200021aa11342d1000c0c1951020b00d0305100703400d07910801c10007030309502d110702a20700c2225600e00860030060a64402c0016000c40300e07400c4440e03210001a1480100c1807410a41f034403480341c2c0d08080f0354a41d03c0121003405092041800842907035000c00c40f05d0b2036003100c1d41e01607504207040765030314008200354502090742c40c0304130b2250400c3c4440c0050141d803039014101040603401c4483c1c811851311905481c0c03a0b44060505c0c810380c0014040010801003136000366008002e40424104551200760003c1c01034005c00440300300691401c1307801c0c0000170258204a0a031101d40c82c042ea21a01186092441c0c1900510042c2490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 619147248 1250 619145998 619146013
    0x90501350117120a110a080705070e0c13060c03051209060a0f02090306060108062d01090b07030f0f050d05090d0e0105041a0d1d0c1216030615030203 66
    0x14003030148428100c6081c1588081070a40001440303466201c400700e1054840810002c0c2d601e210310560900e0102003c1d10180c8402d21800c0e50303003003120350010500b1603040d000814108a5010b00180319540407050224551509081c041062080b4845001d641e040c8410780c2c1c0000181031240b810354910b042c0c1c4041d1000c00c0e082070309a9669602040b10b01003841414105003219201c01c5000b910135500d805001080c064a40740300541d181c40c0d0060802c0d4101d5140400c1840180c02046113092104024001e184082040d030001409840305401140c81c8050401c400c00002e9801251510440c20034900040d80c4040008100d81621503070900a10b414102418031080c2d0002040700125035085480b107000218078040190355600952041c410725254140648141005810007819003807524000000c126002e43c0854400109a40445c0fa417507102a00c1c07181c941c10000000c02c4071504003001440c251a540001d502c4c0107180c6c0c04014600c45e01c03901002d995003000d05407a005540d0080984181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 619148498 1250 619147248 619147337
    0x3020405060a110d090e040b0406140403050c010b010906080a0b060409020a030209131401120609022e030203151c05030c0d031a06071e02031e010608030406090501 72
    0x2440c40c1002480080c001d580c0e8204616008240d030408554025951104647c3d0b00e4641542c840720051054a601d5102d13041e10101e0316207095071500c02ca2180d1a490b403101a40d045680c210b45080c4200790500195000c14001c050b000f50719507a022041600c0070400e0054940410101d000300ea02145c0c28070f001060303103d00560550040c0198080540750407441e03200c13807040d200c04c1d10400a188207010880e900144035800ea04c0d070860301094055400483d101d103170b560102c1c200c030070650003030a0301c000e540c80c40340709103410207010000c001d005250550550034004005070b02c0e1400041598861000882c444221702d401c412200c0390070350090305807920b40c1c4686102c141c40c2c4204209050000f49888002c9003201861406940780d030902508040c184841591440d007400682d0500c40010300c1680403100050b03504006c50f0220300c0044004907000702d0b01340030326425150b841d009500b464000b07020500c0a6503004090000300d800902c1d10110020300c3d82d07401460701c241010b400200c03450405030780d8003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 619149748 1250 619148498 619148507
    0x615060c140303010605070b220f02100309080a0c1b060201050f0711030a0c02042405011d100f090e27150c0306060d050114090106080903040302090703020405060a 72
    0xe0007805020104551003a2589440c0c4901c000d00555020071028045100826a1001c02c240d000c11300103240d44424043c0c1c0181020721024030404c844555400040c001182040844840c1d039500b917007010304c0307440c403a42d55100d410301915212104000c1c802c8002024804425509880100d42a081108245d100c1100a02824080707030340b10703140700742080416000381c49083d4402d480e0080b00003850030711100b003008803030341008580241d0780180c40d00d42c049036031b09514a84a000c0e4807254005c0354000d2800c400940143c0e060340c0078a055000410a80d8816150000d14400d020043e00c0c0c801b03101c0040000c06e64000d02d098025070404402d00b170030041440c550349070150075442c5448000e1043c10010f43c0c10740c2c1c1c40134002c81003608811500041803132410320b07002560b048a401800e01e802c0884090a4504607002607102418101c2c0c0b40c0140ca801e0b080051646014100624181d155442c0494510ba40c134801c0d444000c2c000d6183c10001550b00780f00e51305480207010014909503803152800402030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 619150998 1250 619149748 619149767
    0xc030f0d1401050901030b04061a060d1a040218040504080f0a020f10020a1b03020c0d0507030c0504020906030112082704050c0310050f0402090a06110601060813020904061506 77
    0x100381c0c01e402002042e1450070129103412203520030a00340080d500c654a10303025110f40050044100400017410210f035031104c002d800044a148030000310b600803420100341d040500f400d100c0c007662042010003050f08040100c0d03144800140d4000c25180c484c0e1401c1001c80c03181204100740e13002c01080c5091b01590110702c903200314032604101c5035403801c250b415104074030501e10300c400071424440903421200d101000f5540001c0c06030042d1603a8000c0300011440b0b0003541385c82181c09400070f21052040148201031800507144c1a181142840003010104029102c18028200e451104003900b07001c100e0f8510444200420001182507481c90250038590001c0102044500c12420f12002900c0180882c0c143d83c828011403d02014840c40d10084c05000c5030f101030b40942060302040441055143c6002c00300c0102001e5513840764411481d10740030304207041030b000760040090210074000d640c0c0121104504003501280d0b2040152164981080140030b42108040d609030301e6280001c01607000145c84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 619152248 1250 619150998 619151021
    0x1403070b0c03091213060309030c06061404110a050703231207031a0906100908010c09050109060c032a120807090504051306021b0a080703030c0509010c080c030f0d 72
    0xe413240c0a81c4d0305841e03030502540039150000300140e0010024070f8440d03008440d91070b003e402d002c895540c0a8490303500b0768200360416400d103082c011102401e400e03e84503081c00414004441824611003c000511510400b01c0c00380800070110b00c92546811400400b840103d100da0441e9070302e0b4107203c0076040798802120244086031404905090301817562644c0560001c00410008980e9aa01c0c10080d10f042ca43c00044200082d00c0404544c0c08000d20480d0001d200b66200d01c07041600d444001080102c058114004011440e01d039007000a402c8025004406034141558411610002c0041d4079180b684001600310a034003c1c514503a582c12882041c040d102942d0f40c8030105484105000548000340c0b8104110340c3c5c0200500302149140e400f900c41600345a075451800f01c40d02c0d1040380707056049102035070b18400016108007010381500c034011015100f42001801e0003852000038256690030440680040c20003e49800360301402c1c02100c800c04000151282c03980c1c80030004030014401c85214 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 619153498 1250 619152248 619152253
    0x2c01050105041a03150a27170f0406080a090204021c050901230405030403120503010815090303060d1b0603060f0b0f220f0617070e0d1403070b0c0309 66
    0x103500381090380c05031062003c050020300b40b0b880c200380509166a4020000c1e10841e5580c060031500345005ca0410122402c500c5c400001c480c03060402224000350308080b44030f40720042040701500310a0505880840d0158100301400b03a5800d078044000d0040688025482840000c3c480f0030811041c083c4c450080035041c04124590b290708590742202c600020006044059020001c092005000107c2e401751007582660b00b0503649a65001244c810b64422a001c00d1011005100d140010405140a4400f4915803002420180e4440e0340324480641600d01500d100032060042c07249004290803e4107500d41001c5440381d844200800030034841c02410030301d145141c0001001c40c1c00d00140c40d1543c1d450072025103442028401141d5030080c0b085c1401d5411708400c000a00f07510880b030500010b25140c1c0320303200d25040801d844948010010241e605000040480a00316110120410051a80503038008180d11244c0486859402400d80040107809180c1c200290725515038091030096900004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 619154748 1250 619153498 619153511
    0x9090f1b050c0a020f04020f040f09051510080601030915061e0b030c0d0e060c0d230a0c020f061e01080a020f041a09040309060207080f0a03032c0105010504 69
    0x90031940c0b849403403a48400e69101c00c4161000d0715081ea070503200c02c0d000070001450b03c11741c161003000581040d4000c20609003400d50410810304030340910303940841200449030100181c2d80c001400010b004000c0c504102748280010b4403130b4001d90109206a81101900210100a01c1e85030050700882c0034003401c2c006004001003080803c41403000954132620007141c05c1d5076410143c40129040110051426603c540703207001240070601c04940189041c00c50551358a010801020548251081212550440742c0204c11720000078035405130007031200007012840d01c1c803d0208900d0a009140500140c6c040c02007405507403c1c0c80031201804c000102920101070703130fa0f41d04464451404000c041d41180c0110980c00c3c00340380940c404080003542e409007038244c410040c00702c1c8415000300d804401180b0030041c00d101560301000000024503d03a0000c00e075083c8015400c0da1101203c1800030b06064543e501c14041240a007a00384601003020946280c14181a0340746028120a20510740983c0ca842c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 619155998 1250 619154748 619154801
    0x30f0906090c062007050d051c170c0307090b030a092003010e0328030608100e010b04061d1b0708190c0827060c07030c080118030c0309090f 62
    0x10030340d8082e80d0b50340018041e1703d4500300c01d0108011500030125082d00600306205044007a4180024012003e650f6041d500081c0d464500b800040140054640340002d20070401d032180c0c000c0001d41540c061030013198407620782051760005000300c0840106000e40c0544051646a41241d43d007403950403c40080c42096080e00110b40c49100d61701b448801c550400318500806101848400c0c0748dd5064500000d0340c1c0d581c0c40800e414101400c1c00c00c0e4001d03807a498040c40d4905c090080b2201301c0400c95080000b10314240c120540018185840d14428440b880001d8050b11440b580000e18070000e10f24039a90b00700c510382001e0a5002008aa600c5418001000099071180d4111100c0683c0080068540003103000918241c00380008004074141c0303544010300b540d407075100c094283d944151005046e1a0300314900131909074a40d4010000380d0f031412400111180c9042e0000410380e0301401c01d0340003641e050030b045075a000d40384c11900b00d0038240a40c807540207031160702c0f240d5a14030080401e4100310303010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 619157248 1250 619155998 619156037
    0xc0a0609120c021f091a0901020c0108010503150405010b0a0305280809010c060b040f1a060f09120a0515012102030304061d041b1b020a0303030f0906090c06 69
    0xe002c1d40010303001e500303200700e0302c140c004819216015090000005948420703609000e1280e0300c120001b448003281035041035804002008100c94242000c44641d8146008a44c0e12078040c5008071419110b000070800f07006081d440b0b100c4207039028060514041c1c4900382907079103800790304d41402001001c82812500c00e000003008502503034401400b0f481c120302940110760034a448041511034941d04d07124502d06030396903c00c0905946c240113001c0340c640c0c800b64151507a040340e64000c2c1c0c00380b5001c200d04280700d042c4004540b200310044601100604020030607500d001d0400000070094402c6241c0c11117045071035464181207c8140318980d03019808007681c5070f142d002d00e040081d010751003800107220150184203100041c2003107200300310b003220480b80040c096a10000385980800f04800c0301d801111351006404114120000541c985041d065011444c144594803010b42050340d540d117590740358202904202819078018401703005250450400d89040703400f602c29007000c0f0b22950401c1001032500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 619158498 1250 619157248 619157267
    0x12010302011701050d171605060106030c09081903020f01050705030a0506040902011e11100c020607080405030f0310030f11040b0f1f110d0e0907030b06070f080c0a060912 75
    0x500020100001569403080d500d04591b041c600c5100c00303002081c490282800e410200c2401400100881e514003100981100c010090540805c8002c603000e00c4607038800680c101008003140d6a1082d82401400c1c103c1c203080ca0010714a585509000c07e21134000d038484090b500509a0301420423807510380742d003000101c40460000a0114504032528a50080d0384c4030018811242030414424500e0303610b8101f400e01111078614034880ea42c8003111034507107034104222036100d400c41c10f0002e80c034149911002e0baa40244149005031100c00400286010400700207900215440400010b6002003131801d0030250b03c400da1740b10300076860105180303200e15120001c1c0500f4a80504606500099292103c01522040da03001003481942c025950341840b041012103854902650b4908440f0040d6041141782040581148105401d10b04400d20b95031714102218015507000200c201c0c0400103140900729405580b03160b4506000d5074269105020203030b004000e240341700b40c8080c0d00203c0003440684107080b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 619159748 1250 619158498 619158509
    0x9050103020406020c130204121b09090b04081e18150310030803040503070f0308010905010e060603010b0901091a0a031103010f030f080d0606030c110604032102090612010302011701 80
    0x501c401c1003410014600511b504120030054030341745d20f501440c154443d90440c120307520300c41d81d82450960541240c030180648044442030086002035190301a45641c0030b0005007403030b4400030f105640003c01004400d28283c40c00c051a850303004480407842001060305680d809146002c10b0714a0b80129101200d11880c0e041c10f101c90103d04580310444d0603040100101c85901c02040350034081440400c0c102c074941d209583d598401e6061429003010740d601a03020743c500b0403030f01d0140b0000340d4490003940c0c1941c8508403540d440b5044040100e510b200ca40d0701c17200c150282007200e540841c9218000b002c0b51007180c0c0b0240480e0301c96031445101e82c0710034030807102c02e4806036a043c80003800d14030700502c5103030040c00440d0501e1060305210302200c0d070652152001c82d65450182c102c941c0c0101d00c1d17a00d501000005801e461510341c40180528a41c0c070101a610710f040c03000d08080d00300342d9050715180c000c0a0421034482039452901d1011002c280000d074080b503110444500c0032004c94400324141c40c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 619160998 1250 619159748 619159753
    0x8061302011d13110f07061b02011808030402010e0a181103161112030a051506120106110f010e0618030c03090603060a080d08010315150b0306150c0307030905010302040602 76
    0x784428070368004c01d03043d81004d2415800300400250700d0120006411501d0007002c00003031038000d0b10b810401e2001d26034070b001e06690403e10905001c40310115014162900100881d0b03407a940c40c80101c411210098160380d2112500d0b202058038000f07030011071205280400300b0030001160310700038a9217002c200c81002c4809107000c01084410701c1110340d400b521200c0c0085507120349400103e9045a00200c640c45851a80e94040043c20107203420100c2d42d003d002c1d11045d00c2d000c501c56036020b00704014020790040c040440425503404608015280b2680d45e07000080024150305813100d5203c0341c0607034a5100c00b2000c12043c0e004d41e0750200c110781080350504002c3d0310f426100000d10035030760402480690f200c846107100103104442809084900c1c0119500c900c20b9604602c1c06003103828400421801d19480c241815605c14403c1042c1001c0e5031040c103001d40c4a5551000141181c2c5003080d02000001020611707902428002014101003846511b030b05050f075444d000110100e0003a803007000010f9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 619162248 1250 619160998 619161019
    0x1e1a190e0f070b071a01060c050705010801030f11010e041401030c0803190e0f040e010c12061511030c150709080a15050405070506030903090f0f06120a0608061302011d 74
    0x203c4041d001001514441c1541c1c0c055500480c800700790400013640447c011502405042081000601a040c0502800d0030030052950664480a43d0500f42500084c07810301042c241618584c012001a488104020400e100f4980807171000740300d0950a05c405c8903410754008002c6a400c0c0040140c40200c110950a03005541c12040c0407545d212107949401d4102d003c0c1c0228880a48a600a0546900c240e0b8008119501c2048005084c80501100d030035410303140407000d00a43e001c0f2542401c00154030b180c4161007000e001c40d460301314403410095029604c00c0c00f07000c3c040311171190500361041d0160b4680d5901c0d1a641c4007204e440b08000d44004002a036104540355041c401e65024540042c0258100c2d0301c3c1c10f48803c0419001e900c16a04041c0f0b03944089480d96003464218201c000d5a10b003650100c4555030070703d01081036400f0315604d0103900d8030084001b9201c80040d500c66001008030f0000c483c12801c1a003203602201c54160310a0b400074041d68a40c2141ea950f0484451092402400000300e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 619163498 1250 619162248 619162259
    0xb09090c31030c0f0608070c0c15030f0501090603031b12030c0c02090a0609150503070b1c0606050901030c081006081305060a0f0e0a1e1a190e0f07 65
    0xc2000c0000c079034541c94081e02001c0b0116a105010501901d000403003220300908041020300b0001c0300416110402c400a14101d000840803030502e41160080f07902c1000d40c01c80b400e804d501902c018401c00801c103140c40c00000d42c8030f0080d0003050403070b0700a85501c078000b00e510300e0000c0001c900b484064040c2c015141c085403440d1083d404202c6241c03061820920080c500d5000074a0908242e981441c42c0d91204020301560f80c00d0b02c185440c14201d544001b0165240c01c011945815880c030800581c551701140300003440481c21038140141c000348804200c40d544600b806001c540052505a0010f4545049643c21034050381c12980181c640d407800490700751528200b01c400e503c0052100d898101030031401300015008000b1980a101044408220140400c00210440d401d07049000c0341035003c0c04003100402d0703001c1c40b0402450001e030886a1610210306108003043d0444c188031000c0810501005004c1e800440d884421200c03c04090210180318444240da48040c0c0c806003035113411842c4104003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 619164748 1250 619163498 619163557
    0xa0c1d130804031509060c18170118060c02010b0a0333020d0e06060303120f0a0b090411150315040e0c031213060f0903021009030c0b09090c 62
    0x41562241c48500e00c0c02e03440341c0c0c4600b01804000804441c180d22060240c042003842c2c002d80f0000182844c00c0da103001005000c400041031584189480c42c407003006000421031007074100341d40e009003d0000136002c208030302d0a031004000000000340194030f001e415049034076055103c941144d80089640b40b410400001a18502141061b00b4009200e03c25803c1c1008403d4000351017010201e020004a841c0d401d0007460a003100107000900c01e0b0820003424201c45ca580c8262900170140c15090ba40d035650750302c410002007007007942ca940e01105250420042004000c2100c4100405031010f1021034075a81e15029240019540700041c4125808081000d003042d51210358281c00c0360080784c86149089010134101007120b0403241c0400c1000403102c011800401c00800105494a040d410140c1c21460007010060740d070000a01c1440035510400c070191203111024003440d00900d610700c12590310103446d906a806580382c40e000c3c0c1004000520458400d2080c0c81c4101c050003107aa4900c080717025000e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 619165998 1250 619164748 619164781
    0x30601031d010c0210050408030f0405030c1204090b010306060f030f0908030c041a1303030c0303140a02190212041a1b0109020f04091505270a0c1d 65
    0x141010799072030079a44815116503100000c01c0d1240000682c0110038403009045c205e002083c0d042d000d0030305090100080016080382c0c0d21803840502180f66890f40d1616074111701c64052130811500c5454503032290b040480004004480d90098100011302d1150010b40039a100e0788104400705034040e95209245000c0d0b0481054011540c0e00041e000d102035943c84001e8005a51910800601040030f000c1c02426000010f0009001080c085c24113000403008041042d81d800000c0400c1345100200081500a030440e48110780d800d0503185240c6083c100c050000d40140340381d019a0707050011540c043e41d0020030800341c10f480c08003401c0d15147c1000c1c1407140c0745400d00e2170f191000c0d03c104106480007012a03c100e00643c6190004940c121f083d00402034020000711a80c0c0c855484c140c0c1c1107000803c4030076500c81c0c40c0d11685c1c000c60560b03140c80700201d501d50f0007440c09008800400355031240c003d000c00c050a08901c00c0d284504400e07250740c481441c61754120301c1418485200e40100f01c09044407074081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 619167248 1250 619165998 619166011
    0x914030a2013060b120708040b01091e020309060709050d0b0114150c1506040509060a1a0d0302030910080106050403170904060b0d0509010c0212090f120d0e0303160803 74
    0x109589400c0310b0840003100c035030b80c1c00f82e0841030300802e031071541d402403c01180c1c2003582d07032500341d01078102501c1302d04a504040c401c1542103950f070306004000011601c40b59143c43c810700021922882d100d1145504c4681c101c40c0040001d03c002004650b41c134011404a92054005049070416801c0241401e596980c00500ca0307030090010056100c002d01c114010610401c40030301030080f41c0b055107141d419204001c4c060500c100d003040c0400004480000b482075005112042c041022183c2111102c000007038401031540180b00040d003001455000402400007000a03901c0310030500c0300b650100c030001c80c00e0040d0070010320108410070118440140855864158480c52481c08282e80c0c0024102d40203940131005115012660700f8680d8694800c0c141c1c007801c000b0007400190100341000752124003540d5002e80d4900c0200e0a0055a15200c04070490418090100c0d201c0c0380f07405180595401000c00003100145005841255034100402951408013640da00a14101c116668155482e00000d000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 619168498 1250 619167248 619167259
    0x120706030b0307171e0c010f1824020c0904110108041b2409080c04150509040b04230604021519090914010506030a2a0914030a20 57
    0x20131418070b48007080c2200e90410700103103019090003079540300040f2214640303509030300040d22540d1a0398001d10958940b181d01d1400300c00c41001003030410480070045e040001d8080d008030103005d0325004606070b010000425001c40c1c00e1030021104102c40721004503001044c056407443c1c03c1c4030950140c284e0b40d400c40c0c401c0b52070b1030b00c200c01e00000d03598980c00b50303200f000401090003d0369110540300e60f040011405915000d942d0070304003c1c1e0266500d400014441c0201d981d09002d0848141c0c0d01c44040c0a41001003049a15040500f480444c07914281c80580c0c101024106107d015643c40324090709448800340076141e2035441d6001c210262a0144460500040800c44000780004d520002c400110185e01c5074845141010b540c5422690070b445403510b4281500014401a80c0781c0041d81e6205054171008500c80d1941100d0005e4607005100c400f48103081c2c08184a02c0341d4000125005441540c0c242d244002401410550740b821384100140c5800c40040b0150042200010500c032002c401030320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 619169748 1250 619168498 619168513
    0x22020307050f0d1203140708091b0d0c080138090c040510090905070905210a02090109020d051012022e02010504110402071e02040f0212090606120706030b03 69
    0x40318000310f0030013418040041c2c3c1d5110f800c0002194541c196800174841d1400d1841c501c0e007189900e64502c10361030308010300c0c0700c5550300c440245d07a80309507041c08550224070315805e0366032515010302800c05030304592100549025031565450a11215401240131811298000e6030b1000c01e10201000141503501c41d100d0030000814580c171070003482c17859003601ea80c501c1d90003072905110908841001e05080104104040104219600e02002260100108480003041319107012510b103000d000c2040207401510071000060301c00420f5000d040e5500d2014020f11180d80c64515a5a803034003a8081d50f802066a4407420015040c141c0300a81c400c18043c00088110301c080074400c0c00303d4480c2c5032100060703440348104010000d02140121034910192802d6003044559a5000c45101c00c03056103c00785503400d030702007041d0b5585d900320118140c6c008000315500c800800021b40c1d80c0c00121104141449050049900760a240105c1d100000900010380314242c1801400c5020344040c0713a005500d44204071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 619170998 1250 619169748 619169753
    0x1602130603050c010201050f01080a11061b07060e010311030a0f0f051503010e0a0804150210050103060b01110703031407020f1008040507060f0c0303051f06050322020307050f0d 78
    0x1003810051030094000307001000c2d2640009080d84c0b4010a62914410142c0040200c04000110740e00032940c0f110441c01c06013030000c045002401a028000b0503d8060040454038501c042107080a442481c1d81c3d080c2c0301c040240054065410000e003d2004a0701080090b929140a030f104024543c542180400c0c60030f00c0d00445820348200340c9003820990700820070710740c0a00e804d02c21503036400c41c140d003e0030301c0f903e20751200b400a0060b44a5101c140e24501c58281c4140d100b07000200a240821504100558481c00c10600818001030400c0c00f1450142c4811060a00002c10004a95060b91503408015001c402d05125801681e000c0f60000f82070094204030780d960a0340080d0307905440d6101106890203061903441d01034198441d40902109a2103445100d91015200665540505011640362181c0303d4a000c078011080070b102c41c4400044021a10303a60003002140102c0196407220480d6109050035426840328040c000c1d0b056000d4101004035083c8404c00ca030044e40020300c540c0c40440b964 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 619172248 1250 619170998 619171001
    0x92409010905060a1d0a0b0f13060510180e1c2a02040501061407020d140d18050301020405010203040e0603031b011418060f041104290303090105160213 67
    0x5562480b6000c0c5c855520301d510b8501200520b5243c11640001c00b0300811030703100d003943d280740604185407030f100c00d0340010044400301b148800d0440d031040d4200003524211076203034011800750140280c14074001510149031240d0780510036454004801070420a4038401800d184083e078900c00303405114204402c2a03140c8040303c1e1000080305107600f50004410184104411a203058101000303114040b0707204400c010340d00f001c1e03418441d4180c600d014000e4150500b044000c07200680500e80748525103c1c2c0b2003035648010070b400f10f01802c80b5450300943e260f204041c280c0c001e0f802820b0069106120410003426074a008941090024060700e00e499030380c40c9140320ba170b9258819290660344502480d000da030030320116117501548040344085070302000c6c48000d84542c400b13410780b401c0310400383c041018480341001d5045d24400051042010b1000300b200480308003985405031111160482400c18282000b20840790300c0c50050b0b495500d0720110400d0300c4902d00e4042c00c240d800c40755098a0300c40c0140d45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 619173498 1250 619172248 619172251
    0x20c1b1c060f0f1d031908040519050a060c02070b0702090a0f0c0c051606140c010609021b070b04240315032001141b030903060a050f09240901090506 66
    0x140440c50b01342440c002900c003030008030102c1c120707030003006000402c40e06610300040364851850091030a45650412500e00550907e0044c40d00a034076006c801003100001e18112468814a4140300f240310181013070ba118400d0b80b050a142c16800c115010062030b00e0601c903a0700045030140011186038003c41e2904030380320444040702203030114031441c0c280041040b049141e1104000e4407440541051401009648134140c64035040c90042a400d121074802c1d004680900f030070000854440800d581142d1181000910400ba58040c114003c200c50701900101c4041d600312580c104180541c05040d4807440c10000081e90825030307a4096104940ca50450381c40086018102c1c000e500419181000c120b00700503020709043c440124900c208128525003650901e0600008030550507a00007035040c250b1180320040303030741801000208800505d089d031095000f43d002240c0c100c0995138211078075580e00b40d0b0308002e807000c400c0c40000120103000c41e60345a5009150100201d40c0001d656140e41c6017200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 619174748 1250 619173498 619173521
    0x17030d0905031b060709030204020d02160c1509081b1206040803011401180902030604091703150312040509131244060a050d0501020c1b1c060f 63
    0x1000610a201120500740030341148030f5000502505d04250b03002a00c0003d003444000d001d07540100d400b0070f450546605903801c0c1e41740a5000c510807005031520a40c0344880e8098581b00c0b458440343c514203d4854a01d060645821030010041d9440341400344481a80340c0c07940c103520035100301c00090106418445580264800d01d03150391254105203401000d00c80314400d0701e0403c0050741100c0d1000a030912020219080c0d0307400182d5035200c0300080380c00381058086c0a00694410303960140e141a0340ca000358840c01c0b07401982503c03030890108142d2140788003181c0d02505401408180701a14028595a421140c407090303c00a0f04440d555144030f0701c400041610205405050b02c0155042d6a020307030000711395001c140840c0400740c42c200c1c003141d10070755141e0400158410001795940c40d03011580015000c000c0440282103118a016400b035440050702840c2030141610150050305000720349001d41400401e200359201c81c0da00051001d40d0155000e82d03440ea280c01c0010010786c103500c0340b80700300754 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 619175998 1250 619174748 619174753
    0x1050409210f030c0809060609090715090305060c040e0f0601020307120c0201200304030b06030703050307120905010c0f03030207020102151f0503032505120406050304200a17030d0905 81
    0xc081103018048828504e801000d1040c22020003002a4000c1107440c1e00000845e034070340c0c65490341c0140c10720300b036001d4000d00d1440b1900103250680c00d070041003241c100d030b104c2c104407110340c1ea0344c482901040c01644100d10040da54040824020842c0511956210350b041c41120309241c01601c545d038000181d0007000c1e021a0010340700d0425941c2c0170720600a01d543d002219030303e0f041a417185641d6032180b0300c0044d00941c904800314820360780030302046000319041806c0380d0b113441035030409010300005080890040b40d0744801c0011a540100031143d000c0342c008480c0031191040752020780103503001e600120f046000e0042d020001000c901c00c0c49008906400061448070f1408030102c080e804c068100d0f500c00c2e0300510a60542c0a036098464080201c3c040581d40034100501c3c061b4501003070964920003002c0e000c1004648103900c030015510440c003c107140031600c1a442c0a0441c2d4030b0743e0003686074009000c00c0c01802554070410702e448140090f40308072407900703601301c04d5a0111401c00400710344e02d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 619177248 1250 619175998 619176017
    0x3080a030209130605040b0d02090604020a09031221050702190609020d0819030203040f12050f0304030e1c05210d02030f070e061215040204080f06010906080f060105040921 76
    0x1418244941440c40d1815540c81c0d148e0222170300080c0d098000181010320031600001d120a6291281e1100c1000b1a84003903000c049541207880030386142d003500752016941c200400038801040090041500820558000d85400030103041c90400e00c05900e6130540d00301d5183c24802c0016105d000110030b400e0701628200e80c42d0405440e03465110602907070701108060052040c04003040d40704044000159100e8200c900444d403d580c01c0d18180250311080b54404004020403051681100c64034800700402c4450b8040e40c60b2416140c05082ca48050182c5190300c01c0c003583c0318800d15214504504640900388031309045011014100744da00440c0d00301c110302000414030210b60b03041581d96081c2c1c041110000c2c01c1034265096507462540c0240070100d4032115580e071410a807201e604403005800c0d01070503240101040a1440c2d50740800384039069140e03281c8540061448004a40300e00309402c50707400781c40c2907403030310b0208409003c0c40541036401e440c0c0d1007028414078001c018601c94200c010b8a406206 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 619178498 1250 619177248 619177259
    0xb0f0903160e072a02040b060f0c06010f0b0a0e0316060309020301060608011203051c050a0509060901020a05090415050a0303020a110f01080412030e0d091e0b0403080a0302091306 79
    0x2c034000a0602001d01c224000c031510209003005503e21695a201c0000c800b104c4913000141c06030880d561126000b60000450507c0468030000504112843c80226041660303520010b8030209414410101e1040e4188600c02c03206200f90201101020014204e0307400200d1070080302c050b42c0381640007801083c3d951202c0c404606083c01810000c0c54203040a00043d032601307002502000303002c1c000030100203000881d081c0c41980042d07400d030912503085007000281380101601001300021345100f44a807246900103510f0301014005c0b581502c00a0740c40d242043e240c50300380170103050491700340c2c5286002440c01003082e48862000d0790055009900070991510503042c800d40b41c480c081c21490013083d10119200b0142d8025040daa002a8050050940724000000440c01400c20107102112400740c580c10300c1c502d640c040040b1003a02d1010855610780520071469580c812420302c1940d600c00024013041010030182c1003d00300c2d04600b81805460b016080b0001201c800f0f9042610340c50780d695003018007a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 619179748 1250 619178498 619178519
    0x130303090c0b0d0c0912081c020d0204172523040905011401090207110108040614010b0405010e2704030903050d030c0e0d0209010b1c021b010b010f05040b0f090316 72
    0x40c41001c1c0d02000c060401d44413206584101251041b28a140301002000401c05904903580312a8880c011910cc0342c445507000c1d54110002c03980d0540d0700c181400c0c00e40c800b90714150000d40b00d01c4000000310041c500484031103a00e44198800003124031400c001c40003070b180c4e030040c080300d0752288000003240325013000811413014041e04074521031441448008009000c40315240400c46090a01132169643c0d450118042e251003040c0041c0044c0c6d1600015420341303010013800a0b26400d07201c000f114032808042c4400100c080341480e2581541c2038802482c500364010040d080350091600300c0a82c0c0e240d890b0a4509456401580300107503660092040d5203910200500040350120791720008030959800141d0300d81418003d50f04c11880002c0c0003800885610707072811046108110640d254804010f41428105801081c0307895035003070050b0000c541d84950040301c0e04140380d0b181c89003407609106402106400410b03c20100f46e504010020950b6010031041100d540f14030006000d0500b40700b003044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619180998 1250 619179748 619179767
    0x80c131806140108070e010623040306090b06031002120417070b10180e15060109170604110405040201140706090c0824101701061509090b010503130303090c0b0d0c 72
    0x1200041c46d5001406040d602941a840200305803200030751485034042e6126481c45594802400b882c0341400c101c0410040c8406035104110460588070380c510b401001105a00c0343d00480880010b00c2c01c002000100841d42c644c142c4500720300030904058440e5144490140c00361032341c402031035581d40100074112420300011079480b481d94041c001c1200780c0d5500c40da50300a180e03030700440c4041e40740010741d01c1e4805d0300214010170b06410200032202210054a403540c2041d9002d44003039a5001080e0128141402458003495042e51341110040390141305010700d410000040307a40c240c40c0d41e02030b000b003076410028102a040d0034015000003031240313400a04500310210741c0442c20300c00740200242150728040c84411134465640300c5c400200740d04240b40c0100f0741c503040a4416404101121241030b40480c00000f501c903410030412101010100550301c600003281c4580d070a0000448c14400a44260016a031140c800c22000360300075180c6543c40440d8010002e407450150783e40300348201d4540d0161664 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619182248 1250 619180998 619181009
    0x91504030b0603030712030905210a0201050c0a170406110d020903060901061a0d020f0a02010c0f020109050d27030605061c0c171509030d06080c13180614010807 71
    0x5600e841d101e95a41d0010340003111401060641d02d01a0809000c403c0c2b04401e03070241d1064402c5203010105c52103a8403500034403800c4005618040000d051454410110b801103000c0e030b2501da4900100d00614201d140f4008d0045421540322150f216580b250f050140c03103041c600c400003680300c4080a042c1454010020310081040e0f060107420401e05542d00f90313545500000c1190140d465440e40006400b07403042000d5071129550000b184244c40c0c0d03040d132017499403010f40d40d1040502c0c050303118100e090380c8074424040c0c0303182c018242036070105004205050440d8100c181c0c481106141c4000030a0400302c81d0b10984e01c2c41d44850070040c0500e0502040d00403e0310003c1d015990841603110ba10f159040f03801180310800b031181c84020910710400c500760325488401e020540350724050692a481790001d2000d03518590400d40c1c082402000420700e20302020020700007840d210700c0864460068000b5040e07402041884180000124410303005011905508803850903065150400141c50f0a2995216 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619183498 1250 619182248 619182253
    0xf14042603040b040e0a0b04020313080f270f010207210c1d1005030a030206040f0203191101120204052202090310090c060206061005071b06080403030617031e091504030b0603 77
    0x10002f80191011780410090740100196855204501d24402039105042c00c400340b0029221038402c6d2260f40d00124010500c082e43c0410804400000590b80c441032030003409001c01000c0007404c20191082c581c0b074410750141d85c2092400369200c0045520501c0d5102600003036000408214900d0840c10050000f8071081d4014803142c80395440094032200c002e80024801041e5010000540d601000f50702d0002e8000d406044001e0710038548000010960040203002c00c17004228544445402e101351811100c0c0a004840600e50f003c0c00303451051040a503c403150780e82408000f681d0307102000000c903201c00458000828685078200030704255425440f4000315400241004400c0e15002880b004082c0681002c030344511040c946641d24002e4040c0e984d4910080f09800200150700c801d0490059001c0d440411042e5282e2440d001304d9101c038110495150f0040044c4647d0000102d0011220b40305095480d00b4080500c0001c0c0d140c0090409401c0196004202401881f88000d641c03500314008800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619184748 1250 619183498 619183501
    0x30c23030d050c0f0f03130503040e010e060103050403090501081b03090a170403080f03092e0c09060816020f0a050f0f060f010b09010309060c0f14042603040b040e0a0b040203 77
    0x104011392050250800c664200030000c1412031414068030f400840d4003100f925252920307a41c895540340000d01c200304510309658003040d0303994041d02c581c40c00f031138265544174406420000190384840d0094051505020054415039850480c1ca0245005003a000040e180403d01811f00c4a8440b0140e080c041c05141d00700300c1040000e0a1104031550150400c035810b49960707402499a04001c001d587d10340c0b40102d04418400196012180b250700080e4034941004035241140044980aa03540101804070f060b031b0000c10f488c68004280203604910a01c1110711804894070300c64204412900e080301d06600c00c4480d5049d40300c0511000d02070710072a8000306140c0ca05030000b141c140742c040c429141c1404002900513000c2e4400c0d04116441600441c0074807945600349001802c2da80070304070300e000098031400c03a07503030003265070040382c080f12400260002031144001180ca40300100403010390140c8820480000e80f881c124010704010101a11820014985448660143c070507016100e48504d02c10030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619185998 1250 619184748 619184767
    0xe150c0313080f040b04051305060d200a0305030714031201151412060411040608160306261e0a0f1b0806010914040b04030c23030d050c 60
    0x3901c0d80400c510050001680550034012024440c45400000105001601103030303d0f540076000f04201c1d003068401082c2c0700d58000d000811904280d900a900c42240d04110000c5054100f244008801c5013081241900140e0002440c005a40e40b00311140d41000c10010240b1006000c443c2c1c44007842c00265103441c000551303840c144681405025440d00d1055150100244a0400b1141000010002c941d40d01c4e002112105403090854269210f18180b130911a030003501031050741c0c1202c8154079804225120703090840c0e2100d03690380440c4200355443e0301c0041c8458604902d0a400341e140c680e038107844090752103107608140944a602142c0842031191064001f00082d800100d1074000d41c040f002600d41e4a008200301c5200d41d8205540e404203000803da107980800c030f0074100c4082d220100112906400000c502507030403500500321030300910002e000300340201507400103244622540d071f0b20307801c7c40da0109910221540f03a04040343d0000c5034800d041e02282c8203640d00640b110041038100008503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619187248 1250 619185998 619186021
    0x150b01020f0619020409110c0f031e0c150c030f0901200a0311030a020a03063602070803070c0218060901060f0912061e06080304090e030c0f010e15 65
    0x260030b40e1081220f0120f845003d10322039042d54003420f040301c000e0010042d1003613075000c2900198141000c5003d40c08142c0400360000046507808034092480e900034808030000c2d80c9841c0c010800d0f01440c1d018200c0c0604800c030003585228440c02c24010381c5910b904104040c3d200d80c15005000b515217a140c0440c4420844000500742c060500b0a4400c41e5200c8001100310040e1045141040340d112012050065000b25500502480e00c006d0360100403255841e250502c00307017002451a032401041540f02c0c880d50b03582c4420582f100c007900c500989000c180b0350700d100c0d50b035000310b51120010301218160b07411031038040c611209000390340b40080924105400050f405c4001842107805101000302074000750780c05410b8040081070414010503a60045040100280280440c101520007801c1c0c1200c05400741f5110300016507907480000d6007042c1c00e1803002c00052000802c0d0042d24030041c00140c82c08103040040703480c83c21502c400419807600d43e80e8a00c8c81c0005103940041000c40c80c004008a80142 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619188498 1250 619187248 619187251
    0x603140a020903120c01020702040c12110405060405040c020a0506100321020615010c05101506090f09020313021e3c0d0b1501120902090610050408030403150b01020f06 74
    0x4440c004c0ea51110746440c0a40248102ca5009407c01c0c246900505215000a0032507240086184144611381215511240b2403149000302c95016405000610260505034452602d8000e240100d03500c0d40302a4039860726010045503509420940100180b04001c06402c52104008000401008014261602039210070f00201100c09540400a90300c038168811000003070b003c1c5d00041520001000c0112071f0000c3d0007040c0d411505541e84682c000380c01340c4034441000803a9111901841500e040c02c0002010398006000058405143d00684001d40e95151030740e598200800e4904500080c03040034030603804d50310304c0d1000f171a2500070354a09103c00903543c1a11840b0104206042a4a9040004807402c1205078050a9400881e04000181030180210404448240c03225000b000c580303401b040944404c80c00003904281c883d00400d905041003140001d142c100c90416a007081e40b034007421441e5806c01e80c0140c44810280303003824188030440c4501d1000307400070b10103003515400c4082455aa101c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619189748 1250 619188498 619188523
    0x507060b0f0d0633030609060212150f0f0a0306110c0307050d0e0904120e04110c0109031b110108190c110d0f0f0f0c05070603140a020903 61
    0x4a50249129aaa07074a00420000000400685445145042c058001d01099400004903041440303100c1d81d10350b0907841060b070303809550703801c40e800b84c2160754070f00c080c116420045440c1074084c061107070140029848640304240758459030400e440c210041008051803854024000c0c0c1d01181d042e00340786c4410502c5c1e03069030b401983c081031014542c6030640c41440389140c00b012a000c0440d10000700711001c607240001e54510758a000e04903590340c0405c81203440036100103045090781c940043c001e500400041c003841c08000d1001494110f40d441100003503000c030106804903556614190300f090b810a60080101500c21905a101c040c180e55074220290383c241c0090500c8103840019681e224403a60000060100030802d00c0008181d1401810b900c505840700c02d4180102106440164800d0400d030204440c16902c5807001e000742102500c1042041951404012405140b1000714500b00030f80d10090855960008a01c040640020b068240240442c002c0070300401519089580010b40f83c2030401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619190998 1250 619189748 619189751
    0x3070b0a0c050102040e011703040503101a09010305100e0a0f06110f040e0f01120507051c02150c061605091504050904120e010320030c0c1020030106050706 69
    0x11044241510821041c8500820640c0005004199140f005954504a49002c0310071320350540300485040d00c034003c034001c6641590041e00014580c4c60325400ca8482000e0039a03401031b4a10b80800400c01d184000d80050b14258414a0960488101c91155050001c54034020b4680e480d159915203100c04004040079000301e41f10a0352040c01e050500403600c0e40703480d40380c42030fa449507503030f94110b082d00e422105010b18015240002404002001e011154076502c400508038140c02c1604200b122000c20f05080c0701e20710000c4082d00181c40328050070124810011603961240500144589842002418001200c40b01803043c0c840d2034000d400d4980d01541210804a2900324202c0c94145005650120750301041001c144820b21030007102290701c0342e106941e0501b43c80345c000015820340d0119202017040103002190682416a40340180d03400001000c5001d18002c000301d1a03a1904060400c00a41ca594850084e4040d02c200009204542070300010141503625014004c1e040b400b070002d0161645 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619192248 1250 619190998 619191007
    0xc010f09051005041e080c0609090402090c090d1401200304030305070c06140405061f0902071502042d06080a1a10020c011103090d030c060b04060b0a1d03070b 70
    0x103400f03441510b016040800d603142001038410711100d803150651007019032170b02070f641d80144941001303000c9440c2d1a401810f140e215884940c28441851002002212055002e2044001035501c42c0160140c250065408a80c40002d500301c0b10f007100c4c03d44544002990002d00b01e8a4000501c4081d2544030750582000200313a510413005580302403079018000d0495142c40600c1040c1a020070501d4025409a0200c0300c13560f80702c00315008036242810501e044400502810000200f040d00144880392041c5084503890a2034001035083c0d801075044006904941440444500c0003900341030002c5d107259401404061403d40c02410082c0050a5011020b440300c20858020009280988503180701420980960011017402522010303d80c012600003100340101d188199400003e40303410240041c00c240f20484280c0e41540d40e80c00490303044800980751b058906055030340b0300c1428003c1144081240da102c101c4100104604884c0c003440e0701d00480066040d00545000800030240e40c807410381c05a88 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619193498 1250 619192248 619192279
    0x5060904020d2604060c0b071809090c0e09060103030f03050f01050d050f0d03020a0906030911060a090b0c012c0706080a021210080705091608060406170105090c010f0905 75
    0x4403c074031921240c01040040e000a01c544e0241640c10b50900942002c0040d4480e0002143e00c0244209104405070445200f80000b642c2544103600b03a070310610b40710003941d9944501c6a003d10044840e940c2c0e075000240104103240c0c100c0207c0d00440780d549020040c80c03a1000d107042144806004160140e8a200410010441c080000009241808080751452241540014003035808001c44400007101140002140c5000780a03400002e81d200441811080b2903c05106072600144400c2003084041e920008506200344000c00c032802d0020008580c1aa03030200540700080e00007485010040d02d08803683c1e05610129201c01612110f20b031502094070381c0c43c02c1c0e90181c000c0d65090780030f1001e40c2d4140904c8051801c034490440b03018200746c4040650394010041c10250490303a0102c510b64591035549118840c1c01d0703481c1d219000402c000b42047e1a440c4011100c060450302005503955001440b070089405c204011a103a02441c0c00c0300c0d100c81c000f100410800140c8074842c007841d101d2100061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619194748 1250 619193498 619193543
    0x5011a040b0a0e041a03010c0e0114030621030a02120304020603070836060703060605160201090e010e070e06040506070615150f0f182105010513050105060904020d 72
    0x20b0f240000700b044c410390f0f902e000700340c03d10380038420190310942c60020020b2221340180d080c280704040585803401100d41021100d24281e0006150300d40c441c20501d82209869018981c1d80741c504907200045895012040002c0c1c5015605c10702110914414000c210059031000102c0380d10075514a41284542c0351822010041c80c000d10b054000390142c0303491044551031100c81d481c640300031641100d18541303e42d0303400e40072640c0a000c0d00d00020320800c50203d22004801c810103c603441071500400c00743d515a0311030410720007a004804540c20660a000403194044203000d070106044442e2803032b1914040004400d40301d10600201380c162100c441c2040c0485603101d82004150390607100700301c4080100f0040100701684038010201324440c8080b98058843e41c01d2021404507000f14521003070501c0c4036581d40010a602c0d20300c0a506502c0d800000410038003c10f80035000700761480501d0046450602d0075580000c2c141800b80c002042040003507a5204140142c2c4c981107001c0210b11480e8041602 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619195998 1250 619194748 619194767
    0x702010c0602180103060504020a0503070815040518010b04060e0106030b0a1707150507020a051c051b0307050904110d05330f04051e070f1805011a040b0a 68
    0x1052070b8804510f0707450581e14014100c8050f8004d0b80d080004d641c440d000c0000f00d0140c000d4900020f04184001404a03000740704490f003200038441400329061030180014192501182d011607996080c1d100010040300901a5051a0a0440c1c05000260a04140801e8010140300e102c2c101038842c103405100e038886e4018032002d060300740020500003403c45440c1ea503540030740c0300b0740100c9003146941d200258456030640b24619401400d0601e02840c002c00c02504541003103c0c002050304840540000600403c604100900c44401840407110b5100402d41422420350000d400740401c0410840002c01d400c0c21000741c1001255940c1c160615030400d540b0301a94182c0104601d07454102c3c44c0743c25182c1020200600e0516601080f0568480c49024032150081c4c50040043d4400041014110201c0b40e40341d00402c061000c903400e01d0399542280840c0c2d01142d00004143d1124482800c01c1c004900406001d0301c03c4128008034000e03951110f280c83c0c417481c0314101400d40c000c20b0804043e4070521481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619197248 1250 619195998 619196003
    0x6180203150c091f1403010305060f0612010c09050102070f06020613030e1e0f06210702010b031b10050a020319120501091d061308032e0306050609010311060702010c 73
    0x48079040d100d412100c00526404c0b0a0700c0420110008032540382521801c0b68142c07a80900584019114007401c00804c500c054042c1d40e0041c20485000c030845424416000d280a56665119266191500190815046070450030342100d0080082c0803071600001c415410280309001340d008503025041c100ca5007881501c05903403161a9800030422000c8811481c403607001b040314000300c40602141023003060f21503454880d41c10541c41800c456410102011103034414071900011480441d180006400c3c010b0308016180c80c14202d88040106043c007100ea04100c0354036082051400c400c00002950f40c1c028a442460140b109011b00310030300e440340d000100610942c210074800c03035031192101405460340c007580703c41d65124241640c2c04071400003262400b501070110380044007250340c0caa80b00306601c01400100c2c1445034140035140e40c20071106803840d01110603540c00c0030302d0031441c2079401d0317800c0a0410703403142103044018008a0b44104160240e00350803900303a9031790001840142c90400100401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619198498 1250 619197248 619197259
    0xc0212010c0503190902010815150d0f050a2708071a0601020f010c0f1103090603011202030d02010b0f010c150e0c010f0203070b0402151b01060306180203150c09 71
    0x81c03071107054120020758041c40403100c002034003281d011503900c21108001d0019000130421808180159484401407130311600c0584003a900ca52806074041440c0e03c07007049908415074581904c86000724510440e07170008440c20f41404845440003c0708014000301300d40e0180030154400580400510380112051144d12554113031710f181516410381942c01c41280da081c094055200c000602c40c4040c8036240c0d20202035121142c0202c5c00a008a8145042499024051104209951080c3d40c1d90380554002c01086030a01c0c08200035205140c107101070300310048203580c101110958660f41c1c410722075140150030300e803e054054141c00e10440c0710751081000c015152610a01c0b013940c410100380031440600a884c0e95070603550b0b00c101240d0344d20828501a00d60303d00c00000c10700626224110703c0011000d03034003460408081c400c0c5603c2000060156104030781d1340d1181082044100d0040603801d50041040d0f13400307000c2580109407a0f0301c2808c1e04025030f4402c5000a86000b0302d2405503038040002410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619199748 1250 619198498 619198511
    0x60912040f0e06012a031e270b070b0a060b04030302030d0209280510050a08010918020a0e010504051501050a0f0212070302010e0705030c031f02090616020405070e010f0c021201 78
    0x4035108903e2482c1046d40010b80c81e40071203038414403070903003650000b200d0b07074502c1c0801244d503c521610748002c004030700042040300c9000941095440c058075034a806040c481c006420618151011941c01d80e000c0d14411405000401c0802e4010040d202d403207550762030259880b03a4007000142040074400c4003518090203640c61620315080f80d10401d0559105940b00c440503030302c0c15016034a60003035040d1900000c00179001070142d901150000122230f407007003006201d02c405a500007102c050a40e0030292101e41380400400103442c01c0e00801d5000040e40000c408e18000b4240002e0091050424000c1071100c03407500458803503c00c0000e110131840342000d46d40c64586d0391070024064000c4c281d44600070b00c41c440c0c0100315032502061500400c00700030018659665446004a514400350542203850390f030038400504907441c0c0400900ca2030003070050803103818205104220403608080d1074841004200889008641d03044008914400c5450030081d02c3e0040510008da40070080c950035007a207508288 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619200998 1250 619199748 619199807
    0xd06030b07031a01031811031e030304110a0b0a0c0c030204050a1d301606060608070e060414130908031e16050309100e060912040f0e0601 61
    0x3c1c003080300380304580c4540d1403c40702c0710011020360360303800b1500d10311840140c80304000078080c03221081c6161003d002d8941c8080e031b1000c61a05150391803c404015000041008100415811001c26942e001c44410401c5414981d07844168004e520b00314052068402005041c00040e108010046074014801d10030762400d02c41032401740030140e007015840c0e41345400c1d0304c1b80181e01095001055074044210828103419a2081d0111a1801e020040c18a0100a990044200035030041010b90042001041092401d84010401500140090100300f07a158a11000e9030701e0204507003c0710003c0c00c1c81e0120800000c00618183c1d16094002c100324903040384c070400c004c02c6402a40c030172203192041c0c00707007a001d08603648080c0c6401c441804101c00c00d4180d14000c240100003464000c0150011511880010195003080f129005000c1c0b000d5070081040240d0f98200300002903024191001c120704052038550240b400641d507000344603441320b10310b0000700309901c00c0001c04000d0a0301c0b503419240c0520304 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619202248 1250 619200998 619201001
    0x120f060905010b0a0b1e0a1e020303101d011403011814060702070608060618130603050709020403151107290a0513020907021f02040f06090506040b0d06030b0703 71
    0x1402c61405101c09440000e80459030400380c40700781c024111041c410f1a00c19a41258503030041043d0381c14041a000d912302105500340c100400108940c009560303a042400c0d1541c40e2216660003030400404212003040801407545520341107606c2c0c000081c20940d194000613005d00000e0030342d0541034041c1e0380f20a040c01001c0501c002e0483c0050f098566a445224080740c03108400c0c010400071a101402241543c1841c07402400c1d29400800744a22428003540000c83e44c007102143c52800316180c030800d009208040c4045401411150310852800d440c0d0340c1c03501518041c0d08200d844840d0b0310702a0480d0740e2810011901c25a81c0011404c1c1440d031a10b41380000100c12201644240c0440b0000560040c81e52040c58026184400c806014040e1603081281d10071000f00b0709011401801c806150036000b49042c0b28a001e410400981c031941400001c0842e00d540f40d12410030080842800c00454a5090072a0180c81a05202541d0b801c2001c0d204405402c1e0f5078401408005410100300c110743c0e15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619203498 1250 619202248 619202261
    0x50c070f030e04242d14042a0314060f040509120406050a02070602030f030a0203090c09190b06070b190209130603050105070c050d031d010203070c0203100e07120f06090501 76
    0x5600c41e500b072010080c1c00c0c1d1100302041d58440f00901d440385d107080c401c02e08000c3c001c04403520b000744040340e2501d103e203640c2c0341c0b40010140ba096801d000d11582c1505d5805025071001210620710480741c500d403020004200086402886014a0362100402c1e90040d0070b10501540002c002c036807590b02c07941d94100401c1a4815035220005008100020911902c04822541068074081d48242140c031200f4030b400c003c0d8006802040c05114486d9a80b41c0341e1180018288119002d192080c190107101480200b5030300300c0712a05106400400c001800145d401c00f0341604013003060100c040300303001203c44c03c000344610203016030b1001711049001401501c6405c6141aa03104200a218a4a4446007070360400b01141c00149280c002a10403a9214880d40c840b880b09403d605282c0029001c03c1801403ca134010703511000050203c40d100029410104200280301140000c2088013050804500303864000f14043e104607180002c2e950000c0c0500084c105800d507070840c004000249052070032a0083c402d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619204748 1250 619203498 619203509
    0x11d16030c181202090a050f061005130b1c02030402030307060e0a0503070c06030f02090f0405130f080c060f090303041118090105240604150c0b040606030303050c070f030e0424 78
    0x170756000185240d03100d00546005007905104410b072502d03580200048170143c115103100300b00301032240801d82911a4a040018410808210745d1803484000080941500301030881c02c0074010028440180c070004101d54000303400c88000071b001c60319228164241018460080c03c184000310f012001e00180b54051012030b211a241000191280c8041d8416801107840ca913034400800012204c182c100343e040150312207107109c003e288550300b6940c0c40703140110000c400d842c003080c0812034110400081101d10f0b0042c40c800c0a5048900d0b04400780c41e43c0344401480208140400040c9580383c0e1604085e00034042003048604100d8601703491003500134501101c0700910150451101c114070000358030768880c080b401501d81484c00e402c04000042c2e14001c080c1c00c404100c1054000030101d0030000f0441d0045201d400c0201d0f02500d1414010181d540290195007980410400540080d1275400100892a854200980002c224400103001482d04010003020b0004444d000410f181444030080c042c0c91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619205998 1250 619204748 619204759
    0x403050d020f1635030f0c0c041811040605130c03052203110f03070f030305011a0306090a110a26161202040801060e011d16030c181202 60
    0x41c180c0941d80003611a9101d000342c2caa00881c000026184ca40080543c0130414114500e090845440c0c0704c1d282d50700002c1901000c040100c0d00f0405400240810707007010508441c244421106c03401d001e9103038103c1c224010100c450703408155160f62a550800c0c802020000c041001c50020020494041c0c944003100d480003d1401001840d10142c0403007055004901034070ba40200404c55500762046030561180d0400c80c45981c51005140070100700030621644110724018581e81c80d4a8041c0946406801c00c00c40f03011504810820034503402d060b240e00034421076401c007003500d070450b41070020007107050360740d800d4600013a403d00c9940c1c2100079940501d41c14408800d400c840c1092185d1095415212500c241d4001c03254240400e101d1b40c141c0307002c05543c850040ca4255501905030841e200c03688965084160784004101e244601100c45110b0314011074005030034600180103801004120b62014185030382c8410760040745221301589105011280c6600150940b103100c2002c80500c01c3c0d10403803090f0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619207248 1250 619205998 619206013
    0xc050d0b01091817131e031406042f18071d060901030903020f010606020c12030c0d18050a09090b0907030f0807020d06020d050603100b060912030403050d020f 70
    0x841e028002c3c2440d54012031003000c0f4100b840511000780e800525031240004041e0760100700e10560380007018030031480700c001e9040c0600c0c2d2314204540320182106050550481c900700000304640c0350140d8a0503411031842e449022055503800080000380c804142c04c1009840e02c41880d505800446002e000c0d507841c0c0b110b8a0409810844803052500b0754140c01c003409210b50000795000c1d4118402c898441c0c01914004c0d95180a814211030302c1c0c0d4460001030344441380a0300c450412091000e4005280c002075490a03034941c440c04e40e00c40c8000e01001c2000a000e00400790f4024580300c02c0041c140c0100103601880e5111186000303005159400e66801e0803030740c0803132082d800c00030b035003000c0b2540007031020501d60306c0d070304c1e81c80c0343c0c2d04400b209980000c0782c0c042c1070b000248144028481541c16620010b0320742407a80c141803500780c0e5000c0c4400c41603e0015041c0740c0c0d07500c01007a100d00200440e641c1060504003681c250035030180d688001c01e18410040440b01d129004541500d4206070a011a00c85 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619208498 1250 619207248 619207271
    0x7030c090b0609040c170a0501091104151d030f070e010e0907120312050906070e0102060114040513080c030403150c050403030804031e09030501050c03060604050d0c050d0b0109 78
    0x21030351034401e401e9000744100b007a989035007001d800841014005003482c103445150b041c0d0349080800c040b030700108010750f10401400061000d124501c011000064440d0916080c046480b03e0301c41009c81d640d0511007144802e10124036071042d16007074a00c0250a50309030a1020390b105030341c1c0246025504d000b05012001150396900551074034440d0001c80c0c003d1000e40d140588451180d00301071002d40822020b80841d0710703c5032283c081c0314000c4044100400851400c0d5100622000c5841700c2a411074006100401604005882104030000d00310b80000b4203403149080070f00b0300c008009004003401004070f0600d100c00c90110140c8122401001c1d5240403880c0b1441034000c60f208031084030080340c014017042c40420b1050307520541c4240b00f42809814400c921401d0b03a82d58005104120000712040d106104020702806550703003200d095004107007503007001c0b000038a06000e10302680b030107184000520f0050084118800000b000084c1103014201180d00f400000c003c003d010383c2142d42e081c01d0340080e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619209748 1250 619208498 619208501
    0x406091428020102120319060308120601020109051e100e060f0a0228210204060f08010f05270a0203101203140d020405090c0703030b090f0705071703070207030c09 72
    0x12841c0d0590280c1540c5c1760034003009100c0d410181050001c0c0c400b2001e102840f409921802c0041c600902d049910b440b041c04543d144103030f004145034110390400c50050b0001e00c00140d42d06c01c3d000002118405010001e540d10319181c00404000280d82c00c01d004000c10350f10201f01940103c452a403601c82d507581d248184810383c46071100200306040c07001c104140c004000481c2900301505454908001d011720f500d020803100d401701ea42003c0550000b801c0011a070041c69400101086041007510356141444034800d5030107a20946001e480203c2c100040d100c55101c960b00910000000b0406074106090b5a90094208a403e607010040c081400311305503800c11008449150304d60703500803001c0201c50004500e500a1500b50f041140c09000114240c0d03600c05005102d2161442e0654892520f400d0003803c2d6081c1031541802030529400b440801d01a41180ba5440041d6080495844c4024500b4299800790340461250200000c0b0a104455a001c204881224012060b00402540329400c550 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619210998 1250 619209748 619209823
    0x20f030a08160e06070b190b0d060b040e0303090106082406010e0f040908072d08030705130b1207090807061d040c0c12080402010c080304060914 64
    0x101046000d400110702007102421030352a92110710f0b0078081c2450f100c0100c2c00c1a00b140c01c00700c2e4030a41500030048510b650302c0ca0481c04c40d13090a0140301100e5540301160340d0401e0210080d280d41d0312500804100d4649801c01703408000c801003180d99a24040640c640200b8542c0180e081c80d00403c074007200d01c941e0f100981c54254421090320552501c0b48801500c440900c03c49544d00140d00c51083c400540da20711850b12480d000d61240e59942c45185044170380142061840c0311405000c030001d11004040368180b21010380c0c0003007416901c2e01c0e003400c26903140c0a03c81b40d288108011100220720071425030040e0004640040c5543d5480d00d9013036054802801a00072000c10740e004030010003456200c0c0d0a14010340010300c58412102034201d01040588034512600d0011841280c42d000820a440131560941c3c1003e151440c0c803420141d000900766500b1480180c02e46d44080085020b0111a0340f000c0082940300c03510040004d1444c5840352119103250005130400c00c841c1846981e0f111084954 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619212248 1250 619210998 619211017
    0xe01080f03030c12190e0322060e01050a050906030c0a0e040507140d0917280e0103050402030f0f0f0c04060803090405090304090e0c040605101e171501020f03 70
    0x15040c290109100c0c002c095000300b581d01d0011085d10f443c003a240403445202d0100b4101000755580f410b00c000740c000301001c40c496880b1800c03004941002619406066218142004d2a00c541e07100c42c41c3d002120b86000710075410398000710000a0061085402008102941d0641c035100c2c4e04001c00d00801c03080303800440d1208045469100039801f6801e80c20020300366071803e04800155480c06440301074800e64400400c06180b10000340c18150f25401c0400071a41000c07210190b6410000008002c2001604410f154181500c420104045540501c03a080310881d540c022200f580190050f11503036804402e0303030240103000324060b100d40b6060501810b8140c4c1d0840005600d003040e0310081c04000d01c1c00400050b07842c08140004180c0c112a4001c41c0880f2078000d0040c45580b42d440c081004460440d032005214018007406d845005030440490100d811015040c1c2d50785d510032801c00d440229048036440405001a4108450ac15a4582d035200a070001c0c3d00300c3c3d01851003007121075528450112103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619213498 1250 619212248 619212271
    0x1f02070311010c3504030b07090b19030c110a050604020924120c091f15020a151e061505040b070818060703050705010507080c04051512010e01080f0303 67
    0x3180456691660b8201340740001e408030201110201e00c01040b20342054108440e140b6040c814071416030352002c440c6024220000070a032500301c0404010300a1400e9505900505807180d0380b1181081c002c9095658020201c020fa803009a018540162a0a0300300ca040744100f04e218082502c1c0d11b00d8040c6140d10750820b0382c42e01b01035441041040941414400c82d54028401c0200041c800d8031110180303801000806282c00b18020b03040340704404900d09800c00021002c0728444680b010780c0c00100c9161913500085c8001c494552148888040c214441100d802035050040b0102c80221541c001e40440b0f0b100c2c401c0c43c10081c1c45001c01ca422b8031562044040400c010300c078040100b003448000308078280140c0c0103040b1800f002c1d00400c01581000c2c1e0103a012601c045480000e00c0020f0144075030214080c90010445e01e440c4842080c40c0c000e5000c0d09029041c0f0aa1007080f800d0f202d000c4540e4040c01310410031656a590241c040840d400340a04036440c000c01c5550390103002c0c0001038a000340b0700640c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619214748 1250 619213498 619213523
    0x30c0c1b0d030c210c0302010e01020a0905061303350309030a080a02360307051c06020c071e080607080a0b011b0b1e01030507060e1f02070311010c 65
    0x1070440d5031069518040d103155490300412070052000e54040b2003144c006850708018038103282806800c41d0190b2240700c000341d00410800104903031141140040d90000c42d80350b030711844200d03850387c00392100c0d402c0100203543d81440700c10511038122111070f1540300c8011a04107a03122501120312804207540a0101d640140400c60025004805182d0b002255102c0107051040042c1103103e08180385d8000e1107007040e801c54003004080d0440200c0400d92040d401007902c075150402041d43d0007070707044801d0003540b41941d04030201f0241e50110f82c0d2100040e03007124103850b00c408240b80c00d042c00201d1245100040c0c040040c00e0030000c544544210a80c1c1c85d405443c1d503500048c00050100700f2001c07810801c4c007a1141009801111540515a0042c150104c0c103150020501d0040d03c03c8000000c1d030040c4a200400c0011f034001144429a84540b42000a281912011a40480115a00d054200342801040544c1c660018103203003103900a41080400e030201400542d03084074403000c041c0030007200c400b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619215998 1250 619214748 619214753
    0x10c08030c03070521010501120b01020c0423040506100f210309032012010b030307060c030902060f12151008070918021b06130615030602030c0c1b0d 66
    0x1010355809030013800c1c8986810100d10380607002d00c04919018481d1030000c0c3c014842c1d96172005a44020401e13600003040b034801c00f640081d40d03a0100b0520786118030384a214442d1003400c0286201e100300540044884581041d240c03240e00c0320301c111007980c03508550840010340c3c618070a02100c112286108410f83c010003000c00c202000d81124802c0e420300c100b0301e41c0003002480e41d510000d01c0250035481000a82480710400401800f00d031a144210780c11b0081d4151150340100448010661112000501e0b90a041055002d00504403003e0750020b0013050141c0c045503402c0060900280002c0f1294a81c0d440008007524085100c6046e0341206001085000440c091a40e02d50080080c0c2400038410341e0300d01200c0c0c021180c3c01c021080468010940c0207210000101034000461100040d100600c0c0c00c40003442d00011650780a041d45440d480c0c4c104500781406030f00d0004c0e64001300195a0781c9411448603865070310400b08013445109041912054182d8400b08604002005040140042107074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619217248 1250 619215998 619216021
    0x90e011817130b0d0e03040f050402030907030602030115020601120f06020a120e15090d0e06030717040c0503061b0f0a09050301020a0e0907050301030b1303180e090c010c0803 77
    0xc01d0040000c0004010310036001441000840c01414800c801964410a03c5110025241200c404841c0e96005100c05d100e02d000404c03646054038000da40058336607170b80c90540c80c0782c0b800c0c0d07a2000e05490f20010003c2160151114000c456400907004c8a94a990b40c00c1405400e21030b8060186c9080006900c00c00014031a070000d1141c42da96140c1210340d072450000d28021610403482c000e1450744052183d0740450b6604103100c0e408000440508203c080c5910b002c0d00c101003134108248551400800070344103a009804011000c00421005940c2c0d162502e80945004a68000d0910074811140081c0e60344ca1a0704c100c68420301c02201c0e5504290305264100310742d400848000c1c05109402c800410181c501344041d00032640e5035660346810000200602c40d81c918090886020042e0800c014000b01c1c02c002e1030707641c0224003081e1801c010000c6003000c44160050740c4001150940140340020503c031030440c400d0240982c0010340300d4090f41070005640001c001000101a45004d00016041c006c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619218498 1250 619217248 619217273
    0x306010b09010c120e0102011a030303010303050c03043501091101120902030604080a030605090c0a0507080f030a090b060607020a030b1305060702070906050f01210b0a03080301090e0118 82
    0x18146060002e140ba544c03c4c18030300401d00001c00241041c160340c40c40350b909008462000701d001c0480c542400d000030100c5e480e844140009001d01100040902c3c0400003041103c1c014030420148203585014022000300150282c010701c1d48042840c0c4c001c2d801000184250140154440c5010144102400041da0088043e020000c025680e40980340c0160b1820700c4000d200c4d602c0b0b040c3d002e035035003d440005000c480303031341c0c200758000c010101c2080741c25210801220f034a102107007403568890119146c460b2891158503c00c9e0068640401404460441c54005800e07040c405c0328040040d650708010300509001e1144082e51000c401c40701007000c500104820354000c501000380f5401c060703030364485030700d40751069030800010f90006504100e035030039a00c1a08003401c0c04503100004030990a0008100e004111481e0100141c2c100302c0941001440e84614444403000d410100c525036a0309145919400c00d119415005083c0702d40c2d4580108103104007203a8140c071076045006002d158850006a050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619219748 1250 619218498 619218517
    0x15040c0902070308090114010501090308490b220e030a020d0801140d110102070321081005030303010320191d07021b0f04020d0c1b020306010b 63
    0x11200022602150900040c20b5540c06034441900c5810266075540c00c40d071001000000850360600148038680e440303100401241d4005284a44452502200781c22110188842ca41142c5101240c16800f00515031000201c041e00b49651404503480303210345080c9e810a4240383d5004904042c0482c4603000402281d004191214001615801104040b031a40e845210490007692000644402256003c4140303070141121103082d040c00b0549101042034444003d0300101685582c190842c030f035074420040d00c0010741d000394140454580b01040302103101c80016210002800610003d0b03c0740000001701c0f01110b0000d0019480c503881d5440d5801d4420001c960700816520014881426940309241c1c241a2420082e01866591500341495448401c2e441d580e5608040e80c801c02c010181c012400a48010b400f9041c0481c18111000188507125650103240d4003d00c085030000e40740318941d001c2001c0b5501c5465100d100402c20003400c0301d000102000030742c9a4854001805008102c2d00a05080709 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619220998 1250 619219748 619219763
    0x501110709060b071202070b03040f030e090703020c0c0108011508190f0f050901090c1e24021908030103120e060c0f0c0d0f0b0408041e05150306031504 67
    0x180c88910034401d6034150f5000b0100035001045000a04c9140144110084441d0004022907807800084650380d001c001d1007d0030008101c81014140341c00b50070f64010812008007086850300e0803c030090020b4021403108083d511558000a90795405500000e060fa03040e40707020000c42e00c4801c0203c4844000401d15452030320001c200e48082552401081c41c02201401d000c650050100300f41c00480700c0003000c542260b130400e050300010601d140c00344010341d03001e201d070810441c10800b03c03084c2d2a18280c0c010000c103c88060040f07590511944017104000d01a1b007075410710b812004c07501c0758401440001a2054030b0030001000041c1102c64001d00e01040c0f41080e02007030000500181080e0005a9210b419820044034500007030410301c4030461600c4221002103080e1090381328a0b98020400e00c005050900170b030041400c2c0b145001c1600d00800440403959800d050702410604181c04c0f501c1035038090440c3c00803003040c800d046001d4a1259002400504041c4ca9043c400564150090000e0b14240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619222248 1250 619220998 619221013
    0x20d03020c06070804030209070314060409061d0a060e071a09031905010504030e1212070203030903010603030c0c0b0304110108060f06041401080f06030d050307021c17100f050111 79
    0xd0b150207018103040342c040c1005540312890360040c0148840c0c014040c0c020035240c1600892166031122580350012419140080c00030498035104005000c510815040c00d0789a01105010110000305418918460b1b54140b00c0f02c0b4046481135918460f80c040e82010000d20010400b62010755000f80c040c0300310003411980fa900680f015602140b010040660381651600304020505410203001e0006440507120007501c1500d0700d80d01600e510060840d95031200340010140190355041095448200c4000c000b0003140780c0c0c80c54042e14054402004440044030480c000400790a11804d40c1d01c6590441c042811a540c28801100c04440c020406980960540d40040301501d9000142000e0480222000c0e4250758200014080ea00d0080c0405012040001040f03204c0d1404210116500d0040c1042c2e51680c0715204140e052840ca1840003c40070903c1c582141c01991040008801200480107852151102d02807805541310b079000310807492003c1c020401c002e520807140c1c0c00340c0e40d43c500107950383c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619223498 1250 619222248 619222273
    0xe0910030803010e0f0f150d020406050a0b091305040515071e110c150d15150207030b0f07080601230f0a170708060112020403062a0e010c020d0302 65
    0xd0781c0081e0014501300014004101803150281034103500a00240c903030314031501d088180d002c02c0b8041071032424014a455040041151582e4103c4000303840001c1003260071589a01d03842c0e01030b4010070000b41c40f500b41b0740701c4007000c080c05108240c01581c0103800b4024040c4003803001c0b41282c0e0080c0c452005c000c00d2518107030100020b0009400d011000703a4607280c1c00d04030141c20919103440304201728031540001c10040359210003c82102c080100e040404a203510b035900c5000329a1603580d100241c101590b400800071160b02250082c2900d12034260514261503038140c84214000880310f100c0840c0040c0c002c183c096000d01d0f5030031480c07440d40c40c0e281040f14070b43e0742c40c0c0c915030003410264207801ea01048804142d0380100e07030b06031440d04012060319035140c0440003c0c4000009421079040c4030039842c201100d000d081d0116405036400c1501840030545080801d0461643d0704c0350301d120003003004880c0b0034992086442e00032220059452140c10704d074a4081000c00b0040c143c040341540b08a0207001d51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619224748 1250 619223498 619223513
    0x904030e1017040609050111121614070309030204060e090c0906120706031b02030307120504060f020c060411030c01051b1e06070f020118291f0b07030e091003 70
    0x80f81c1d100d918003080703011162400030300b90383c00c07a0120891800b05001c0c200307050f1104e510207035000212411040c4c1d4103410b0348040e510b41240c1e2502c0c5003c0240081c404050680100aa0084070b02c259020001c581e5544090b00f0840c0090300e00c646590006014110740780ba20803042600218001c040e40340c00e00181c415107117000c21a43c44403006c00d880d1101c1d05000f5101c2c020418080e002c0c0e00140d890343c45c1c0b03041d0090035030300c0881081e9411940c880209090150540c0030180520b840c20045546800341c0e80030301c0d6170b140c00302c1e421075110b04040403250b00d604000c078a42d20147d9041c0c44240c2042c2100c1400107803440103c0b44620184200054407040754807100d00307003054142c414042c04040c10000030080c030311a11004041c1c256810805a6075000302d0034850490780c140c0007030031410800c0701c040304001c145000941e025111600e10091200b8241d8011042c1d9103400c86a40c103503402680d514601007240220f2030040c000c0b8101c402c0c820740f1410b040b4242d13544000c66000b044140c544039038503842c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619225998 1250 619224748 619224751
    0x9070b04140a051c1406040f0f1104020d05060f030c061606240501020f01020909010e04141006090617150c04080703120822032712020406050904030e1017 68
    0x440620702c1814403130920840d24801407140003d00041c142030f00e45501c50928071403002200030300154086d1114010f000ea0a050300c003441c48001c0c0295614510101c1c20000780400390b0700944030307140b200c803420b0b01d41c503002a400060301c3c1c010300520300708031b41001c810741c20303065141c8c0580d000d5881e0082d070a002d800c405144006100c041095026040c00d14000915140440244011583c8104403a45165036440241c07411200da43d52100c0182e0344501d403008041d520220090400d21400b01d91002d681300c140c00500c282d60849074100010f90b40c1c1c1410581111702c0e108d402c0b0710381d04106204007102c140800d0f2242d128481c0b42e090361603e60b03aa80c4d0940741002c01d920640c0c41148603045051500c0e400340c070880c1c00c030301c441001c440c440003071a00b003003015038000c1001420321400d110f481c0c1504208507404904030a42c000c0b0104001d5594a01103414407000301e04900c1545000000305a034600000c1d11030086405958441c0c4420030b44090140504400c1c5502043c0182540088001c1d840f101d03181c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619227248 1250 619225998 619226029
    0x22407020f070e011508010e13060e010f060501020d0207030803130201020a0f08091e0303190315171c120c0c02090414151303180305060c1209070b04140a05 69
    0x1070f035550f150104200c1c0341120f91560004100a10004000510312101c03415001004074041a9628105140480081401b441040d001b175090010b04418111181d110f0805c4510a800b81c920000344548100d80724409030000809004091010035122100080160350300361060044480c144440e441d0103044042005084071700240000e154402801c1055081c2c010038200e610308242d0350450b800183e103a00510301d895400400c41400302844512075000009940401c4540000c006d0311000d030070782c54010146c00071105200d00c44134003400c039403a023a0b0504408031540d100f0402c0843d810740400a0004802d04804201c1c101c0c550502698404016601aa100f5440b40340c41d00304a60341c8604040b0b284501324402100e200030010250b882e15024140540d041c90030f49009042940d010501a00b650406070461165104100000480d640105103d00c1c01416000d40303030b51031400d5180d4441c0315001d20703c0200000d001c03c21500f80c0c030351150b8a580600602040d601c94a0b800230a42c03400c200c0062 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619228498 1250 619227248 619227269
    0xc030703052503020a060305060d0b0a0902010815090c030705040807240206100512030409061401020f0606060906030a3c231b0c150106022407020f07 66
    0x1001094007030703240c80e0410000d002c202c00c0499841e640000d8139040107480b516090641b500c0001d07150303540320841408101e510480c01ca04600302100160002e01d0203800c02c9020800000c0459112001c0c1511012980c600610700c5201341d6443c100c41a00e50070142285044c01410303c000304039072209004900151840642c4141c1c246944640c00c1c6400c80700703000c0c000c02d54210105100125104c0903400040e600151080094034446e00011490340c45241c0c0680c3c3c4052903c00c0105041c2e007410940b56550f04241d003244c000105130b100711a2960415240d9a610210030440031620303007046d070041e50303222a100c2c50000c0e00c106890300028500311150f004902c2d03141100e02e0b282ca00b9021254034513501c1c1c00f00c0810419518030b00c1c1c152a165803d45940300007c0201000600382c42004000325010020498505842d0100c0c03000e100c1da9580c400710806071501181c8008550144002a101c0340361588030150428041107500d108050f01000c0e250400f1070140384102c15902d2001c100460041825020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619229748 1250 619228498 619228513
    0x32f07050f011424010509030c0307080109141501230d1109070302120c07060605060a0509090f190e0106050316030c060806010c03030510030c0e04110603070c03080402030c03070305 80
    0x1d0f0203031a004000d0944500b00a8071042c5002c044101d059251821001c2c2465940c0d0084040042d2402100c42c0d03010fa410f200d001c0340860701c0001900250020740c46044100700310f00300c00b41c01c07540f603400c2c1c224030201d0980c1a100400ac445c2c0e41041d12400508035000c05d0075401e1040010032000b0460207403c0c0c448040004540481c0c0c00c0411640d58001c01c2071400310300300b0320703040032001005c2005041e0061042c004500715050204c1d5912082c02050010b00740369882060940203002500484030061040041c80c000950a030280600c4078441d01c450046030302c2031008035100000401c0d0720390348402990b503a03500100300c1ea1010402103d03501d6464540c0c911061541c6400c11005410382c004804210b00402481026604000c0c2c0c104019414240880d0360380d07810b2518007421400742c2c005000b0240800d800500030320307061501e07030045005601700143c2d5454241408801c3c8400d88050000a510000d184003003445084102e800c544014240d6540c0505040001e161540c90340003903469802410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619230998 1250 619229748 619229771
    0x5060a050a11030a140a0b1c0203100606080108121c0f1d0c0901140102060f07180b0903010e12040b161a0108071a0a03020a0201090f050c040606032f07050f01 70
    0xb40c986c00180420103020006032140851011250300a00901a03c040d07412941150350511040d400c46046010800450b40d50352030041050b5000e2040004501500d480340040511400c2140c506242d842c0b1107400056402c0c490500800202c42480c910b10354503180f600400c01d10030881c1d98400d030351500410b50500c00e503080048041c0c0c182e201048914445084a00356600403803c140d0100032103c81d50555a02c02034140c030f800d1751000d50000c0300903d8000100e00248454064400084203030000c02207101c1603110503944084c004189802d2800500c801c018400c030220007040f05600d080911200348031650348011040d80e01c142505d2101e0b00c080c00602c04c0300740030004030000307281c0702940511f03074904588608100d100d0009035908161b0000340310001c1c070b03000b50010a8000c0e071041031009604118200240c0384c02e100398916120300c4c100840090501c0c42400340900c081c0442c40440301c0c0c4402e03a2441c07003580711122140d84001005000d0140440d105114014940c00d0001c004590b000584 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619232248 1250 619230998 619231031
    0xa110f06070f02010311040e0405030a030c170406021b010f0b03011b0e1c0f05010609060b0f0906070515040b0702010c05030c0306041a040207050f071205060a050a11030a 75
    0x200080380515030034024800801c066107071a01e1100c0e02800c00240e40500e02c0c1c0e0b1400c10b0b10603500200a64080441448104140000101000030075036608020382044000c2c1101c21020508050f000200340300042004291140e008185640a43d1143c42164000c854081e003902c0400e90000c0e000790391500011103a0901b8091042d030300f6051140d40c1c0b00c61a142c18058410301503039100b00d0188040a84034800b01521143d003103007050b000349114210a2407803030601c2c0a040d550052508003404e006000401c2c40c0306105440281e5150000281404048003d1004070707000b80d001900d0520801140080c440e00b031003034960003039001e803000e000946030500000c0e003503039559141e410404c00104100b0895106101c1503030b0308180202c4001c180c041200111408040e80814450b86c410f20005a80f0100640001d031202c120050f1810740381010b59900d1194030243d5100ea022700240c0051002403801c92060303101c0ca500100030400010503442204040d040f0390001c40744440600e41c0c1d281050240200c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619233498 1250 619232248 619232269
    0xc09140307030803150312030c1b121e2b060f05180411060a0309050c030c03120c07030611040501030b0a08031e1b070f090507021b010e030a11 63
    0x10340003030001502c0c66a41c0c1105210040031021202c11110301410996801c1c07002d48500c00240d210300b912070a050442d014035178088106065043c0045480002030080801c5041a6980982c040c605142e0028008480e141e045000240807060821a030300381c40092200b201d1038038183d40d0042802c0040d0300b0b643e00c2142c4042e0402d045118007521301f00020fa840079141040302070100c100000fa40c5861038001c0d1100606201558800c10120303486c4006540b507440801ca0901460403a41460b8900091640316849650966010380005120300b42200c8100010140c143d402c0c0200d030341d40f607500c0e20303098222071181e11120211400054200110b40e414000c15044000854216210600c5c05080c85e03501e108039111001c0d6044050148aa62120042582c107003142c1c0c40d0418200803280130702640c82c3c201a014040d4006101c81020034107040358840c481c40703620303182c00a004542c11170050005042070148114100a80c590903001151424040300c2e81d810711841c40480d0f1842c01008001c881d850 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619234748 1250 619233498 619233539
    0xe1306120b090318060a0215010b27030303040b0615030a020403121b021c0b0a020405042930010f0e0109020a030206071b06050301060f0504030308180106090c09 71
    0xa110641d1038000d6440c4c450035024048070301d181c1c3c48032070640503414854400c0c00341c82d00f0103c142c00001c0c4007000740c0c0148000e2000c0160725040420481c8080c806200300c00c407482c1c05034400c2c0000340000e510150038035008036009014446a80d140d550b03014855004030340c0c1d8481c2c903801090030010802078541c10304807849241008150030b401101c447c1842d03c03c442e0b0180c416011070140c00d110300813204800394100d03041420403840c0d2070300d0ba01000c00380d4818032655010f1840c00c803040ba01c1a06920a4244241140e801c00c96140450404c0003100c828601c481e03000980c01d22200f0ba41046a0b03249488045004400440c64008011003c01264080c3d040c0c16400d90502616000694800200100740c0b681140e5040d10b131149410200032030211a0316500a040d000ca0020174850b800c034010311b04a80181d0307107061011525034401c0f101c0340507500c0014086041000810801244600d00b003c42c01040c00000880541d9824a00b040e80e10400d8140045031082d0018040b6400c00c4071703818401403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619235998 1250 619234748 619234753
    0x70b04120605061203031b0c07030f1109060a090504020103060b0309010b010806090603100f020d060308130906050d08030a0e03042904080c060a020f0129100801060e1306120b09 78
    0x1c03c168030341605c92000516842c84000135004882030540c032242980d1b07940d11030004039080381d40c403403501d0403a81ca0102019241071031005c825440a02d082e007840e9126880c05081c500a040ca000e19140242c000504100d043c192514000300d0220301043c091032240480c01c7c004100010a600058000c0c035025011070300a0030448100402a100000e2920f8003042150001640b0604810322600174007400c1c0420302c015051400001c14000e600015240f034080c626014061940e451002204545641c40344a4111440c0e41041002c0703800314014581c040043e4002140800b9400c1c0725034156440f40d004100803e680d400000100d0500044075260007000852a600d458200107243d55101d80c101411803141400080d00801d4610030300001c2005d81141c40240b003129102c981410703945010400c1c40201e140d0001c007990302803420401d08039030b1100c00d44484e256a4241102211210680039916400150038000205030005500ca440005c0070082180b003004051841d000303184520107410311045a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619237248 1250 619235998 619236019
    0xa08151002060c0d1119020d03020301080d0e03030706110315220b0d15021b012a0905060c030408011104030c14011e022b090314070b0412060506 64
    0x16000a0040d41000100031807903100e040003c41035015062801c69148400c201250300099554006d4502d2039500c0c2c140c0945004400e460004c0b001c0307000034804c0301c645500c06034481c1402070080560141c100405804c2e03074903001c2c3d21380b100302c02d42d05000921030010b0000000c0100850401c0250102c01d00304644400f0801400390440c825030500c45908038026994040c0c0c1d01103540c41050f8038600541c4080060582803e145004000390050140c000c0e100c0c640c00166520a41e062244590600c00c41d02d10449140b05000d8141401c03040b0300b030410500c01105c40110f83c59448201400885d8800c01c000e40c3e1740d0741008074443c03d607a034203200c058030840d0600040c030015498895901c16640c120058000300c0302100700403074061074400c4d20310312442004045403004e140e0109030007a586203600c01000a12450b0030310064003a1400030380308001001c004c2c080c000a86541c00803090070f0304440440710b4064032460098196803090f404840a007030f452410740d04202090141640c07000d0102c5061103003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619238498 1250 619237248 619237279
    0x1712150102120702091b1603080603011506052b1d0c010e0303040e04030c0c0303080402192706030803010f0f0b310305190b010b0405010e1c080a0815 66
    0x2060003601e01c02840c41e220781002c07186001401500c0c84c410444100000c1e01f00d4500b000f40a100044d90001e02075400c04a0302003034954a00d118604440d8155915071510030403503029540d45203d0071444030442c40c05080e0001980007070062600214030041c02030811000140c81c0d61600d95a00319482c1880028801428155408402e40d411204481240000c030f9035146000c440c8064941e00c001c004404c3c07000c01106142e0300000c8107102d0351007501c000152294002c240c0c441e81c1500d1113045100081480c4100d846107070b60004a540c80440c40c2c02007051a281c0e510900260002d0b040501c140b400c16104001c010710700002c040c0289608046c0328035000f5010554400442100054807070402c40d107075401448518141e8050041d900030043d03d00c4140e01100721140c09000341004c0e07070701c0000f660000c280d1504090455007100c505071140e046031011441440120742c1c107000c10084100d510040c030004280c212000b08106442c640c0ca2120703034030703209591100c904070700c0300014000c602c0442d03500349 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619239748 1250 619238498 619238509
    0x150c010b0907170403022d150606160f050105040b090601060311070204091514182a0102160902090a0803070308041407080a06021201051207031712150102120702 71
    0x159190f07580007036101981c0d9070130241d10b812403071010b0f089070b00c03245407115482c03800c850f0319100c840341c0040c29144074044012101d0303c0d00c80140e0b80c06e9400302c2e04106c5480740c1a5079500428140b4402c07502c00704101502d444030b50845000301e03419210100d4a508004401c8808d00c505400b400685c2005c11000046081010090040007030080c0a1583c503005801070103a01c40344000c103005402410b02041a000d4001d40860f80c040d00c0120760960980040034105001203842c4520981d841943e41008000c000d209064030b91402c03045040d80101c421107a0f41403010014076002e840a044056560004601404540c0c000d95000d000150014000180026848030250380c10640100d00c0c0042140380c15101e6042c030744580c1c00b0440a20980300e80c01c04004064002d031100d0901500d000f0800da907244140007822100000440d03082c0c2283d003090000885402190280040d58100f240c200440343d4804e014a50003a1524449480c24050028803981d04000e5298940075105441b41032022580c003059 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619240998 1250 619239748 619239767
    0x801080604080a0507021e0109060e130c031503120f09060503060910090905012007030909021602040e100e01020406091202060d090317070e0612090c150c010b0907 72
    0x1e0001c0e2001840807403c5100d40192805103800400c00300485950418070344455510b80f1100f4003107150788400241c02070054242c050002e00140240000c80c501c262001e00411072820001d0900d95680f000280c4400c0c0560100055441b0b03103e48403201d0035218001d0961000b10103004c00300b181c018024440b0550003410b5a8010b1019203074110527840d00b5800f8134035146903402030304000e442c040b4610140041504002c030302070400d428200d026110300c1c045500034850745101070041181004200a080d006038010010740315520405046007090b0740c00501a507854010980ca00c1d482045600600d1040d80700700102184980001c41c0b40529120018028200342e21038442240d20b40000c400039500c4500c12100c00d80c0c203031320702000b18418901d009004000501d20008506081d07500084040d030041d10727060741c3c200d002420310741031280388031409001550080c440322060041c44030700c2100da10342d005045580340c05804403989412491441b24212000701d0b110314441c1064000344140b080d007090704030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619242248 1250 619240998 619241003
    0x20d060b280c020108070e030f010b09090c06160c05041406030c03010c0f0e04090819260c07081201032f0a030f05030c0a1115132102090f04120801080604 68
    0x41a548140c01900c00d40051f10f03d2a13018010940034684411040d48000c44d5014120f0304101d00d03444003c0059a155584241c0c560000010410940c0003024041d204050306e1240d030580d01a59200c401150603180400148a2082242014802980340601a0b032000c0001500200b2203030041200c000d0170864041c030420b00780148200c0c246c089031030b00e8100c801103540010b2030701c1e62400c960310040442c06103062608001502c02e410001d0300d29428401da131460414282e107000503140e8880c46440c1c0d500c181012a801a020011002c1c145211450907000b0743c014581419801200866004000c42ca601d08001885000c00d04d65000e644910070181507030f401101c00c0d0360441c4c4a18140e4610300c07820a91039540d00c07507182e0040411903008044103c15034280c410659155600540d29a140203640c40a103404411600a00030b0381d4840c4c1032000040b10102142d0354440003a00441c050b00025102031481150f002c040109000850b40c0b40000640d8a1424110790b61520011a85980014000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619243498 1250 619242248 619242257
    0x3060b030307050712030206100f330f0801080d02070e072607030f0c120c1211070c1409040f0222050a0506040c0903060b04020d060b280c0201 63
    0x5991551010015202c1455003c01101d14441e2141a0000500b4030f404003180144601c1002400b6100d803070465200301c50265542800c414144054500c0c007003138000e5440401100c81f03a20445000010f0340060f854191520380000030107840b40300800e079920581119806603c81098429810360018407081240d207072807001c01c0940c850520803941140c0d484010b0001480481d41d400c1c1c1c2940c0f0008a500880ca561070810030254142e13603000540c2c4641d210304001c03480b05010750701407140d540c00060035401a45002c1d12030118044001007202c01c010101c10341124081080000c001c0c484100801406248188034003888440001030041e60000b8401485141c003a1020340440d21400c6002101000d455103480d411140d401c1404001e0000300c0301c0030340450426001c560541014815450268a10782d40d80c00701500b903444039005800449503464126a00b00001c0700c14240a220b407602812001041039910409054006596039401c0e038052800c0c1000c1056802590b00109540c0b4010790a00b00f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619244604 1106 619243498 619243511
    0x6090c0a030c030b1003050124080a02060a18090218011205070f030e0c06040f0e0c250320030d11030105060706200708030f01050f0a0306 61
    0x101406100740b852040c0302242c941000107500005240035401842c1e6039603516400c4a05440e949141c888100c4034040c0c0301e10782e800000f001803001b04001c00007140680c0008040d8440c0c03140000c180700343c01450003148403241c0140c01c02402840ca0864684800c03510700d6001400402c98240000d10080030740480c41e03c107200c0c081c00fa001c0ea030307a440000c2d805044c0a80c01066005e1000100384698402d5107001c0c0e40b07100080010700440da403541300261030180d400c9030a400180c02c1c0f01e0000c0050200400e00c000c600c400006010401010850560b020b08041d90012181641e448454280100c009a0082d0010040080500c0c442040050381c0d0700508400c0580401c0c01a507600c00820000040032404a4000c3e070f018a880008940c01c8003514000e1070140c0e4401e03101201c540744040200035990440382601c5006000940744c41c66511807040008803400c803140401001e081d5102c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 619064748 619244604 := by
  have h0 := BRFrame.cov_init 619064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619064748 ≤ n) (h2 : n < 619244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
