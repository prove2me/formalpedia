-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4861
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:58:45.19527+00:00
-- url     : https://prove2.me/submissions/ad3e25e5-73fa-4f2a-9668-6eee809ddc64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 874100719 ≤ n < 874280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 874101969 1250 874100719 874100743
    0xf060d080c0304121a06101d040b0901030c0f0f06020a020f0402090409060f1d071403160303080708060607031d120313080f06090601140a1503091b0e01050f03 70
    0x8079030415003407502c0c400b0707191140218801c0040005c0401c14604041002c0d41482c21983c40d002d01444400505102241440741c02d554415210410440d10f9224150320301e0095119041050b5800e05080c1d9124440509800c650100c00e8800703810420380703900241601c00fa64042d200c5000c403910482c0810041c0c0b1510b4500c527005030410500c1020805140d10001c00c2e24442442000400090746480040a003560004161036000312824004804680c2d65440e02d0300004040b075403d2402c4070000d8101c804294802c0d80400c02e0307281003250141c0c2054070207501400407605d240c07a007481391ba400b0300f41c900c4624107007407101e6604446628035240c0320348400c141c0241004403915035003e00030711000c4070720360301400c1314038062101c1404c001c0d800040d10501800c0780350701406e043c1e824900c02000c20441c040150354407000e4088002081210700301000f003241e06a40c0c02290041d81030820501d070f5503074040c9690320524100c0f401c011801a440600e03042d03c00071180c0c9409266013400292030031009500d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 874103219 1250 874101969 874101989
    0xa110409081b0f0f030a0e0603090f1506010810032310022b0605060409090503070b0109240f090e030702060f0703080906010e1314010c05040e0f060d080c0304 70
    0x46202d00301c0000031070414000c60001180e0004c1c42440e4626200d000f0103041602045c100700020544d8070f002c0024680c0400010f0848000454580c055450b062040001100c0d4010400901406582c081615644120410070485441d49590341e0703403003101c075039a00748110742c20107121180050300c06101d15150b20f545c801c400d40d120003070a00b03071080841c0389000592219170b18844c84d001070741d454001e26003161030003400d46007070601d40541c800150400303090440300c0d40010450b80c00010b88416043c0e01801020100080b4544448080703059101e030340010601c081c0a0312010030080c000d43e04480c1c140c440720000070a14100c0405003d24502a40d1002584818081004901c0c42540806030502c18080d9584900c287c58405040d5222a428020011080200d00015030140d04003403500c2c00081c030030b401243d011700f620406c85007110501468030000541c0007804100c2c075110010a660004950400180142850400602401802d501c010a68030300404c1d442d003860014401d481c028446800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 874104469 1250 874103219 874103257
    0x11031f030507260106060f08040503040b16030e030f03040911040b0304030e032e0209180108030c010c0e0307060e010c0507140a06030b010c0b10051507050d020a11040908 75
    0x2c0c030f500d02d00880104980c40d44590003060380145814056481114aa03449a8880c0140108211a2984001d100ba100791008100c00207009032124018003159030071002207000d9600d2850300411841c48607600520940c010040540200b801204450450302c0714000028020181ca2020007107019950004820560220400c8145a04070010760541c2e44102c040d541400e401c004c84091031803400b180d40c1034802110780e40402c803401c503030b000300000c15008180d580d07502d82040c100501c01509070801e00f00ea03000440c0e02d07403c14500f4014a1a603207580c2c1000702040101001107070b5224107078400c0c5801c00c14042180c81042c2d000e143d500386441e40001c00e941d2120b485641000316840d8010303071140181442100010898440c1c8600d880321300050750b5980440c00a40c40d59402c8072009804003200200f01e1a000507159a510382d08101d03035142a900640b5940136041c240d04248443d030300300056400070902c050000702c0031041a4041c030f80072500042c1907c0705042c0070050f402000044d410700b81c150a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 874105719 1250 874104469 874104479
    0x6100b0901140d02090312190320070c030308060105160204020307030b0a0f0e010e360a06060f080f1509210c01050a1a01140c0a080304060b0411031f030507 69
    0x240051030754010950403142e5603001124841e11900c43c140308800d210188c2d1128405051098200094201c6544d40c0d880c1441c001010b0b500490b40480011601c0d0a8844810010550400c410907802942400c11906140007840c00301518030001074020702c1150300000051b0800c1c026406150242409401b950030f01e0b848200b6011510341c1801746007a940750190000a00c0020504158407131911408054140c141d499000711100c09501901a42e0b29000d5103071802c518420003540c0da01900401011440d54070300040000254802c0c1c0104c8881c1c0c01070382120b01341400014002c50f4004070b0f040441265036071380c400c5134200002c80d8604403411642d0080e43d4210751002014203005090036000b005030b5250006210100c030008a03284c440052401c000950790b6000320222800826030f100414070384071103003034180d003441c200440c21074640c1da01100b0321050050510540f0000101510200310341200c1007007000a501000b012181d48040100420003241020040f0b20300651707020040321501a101c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 874106969 1250 874105719 874105721
    0x60501030b040c0506130302190302032e02070203030a2106030b011503050f0c2a011506021b0d050c040c080a0b031506101b0f0605060306100b0901140d 67
    0x141c906031812981c0450101345490600c0c01c0320b003100f8460160b03d543c6031440e4240400100d804441d07101e0702c5040b54001003d85c03024050400407050390420301100800307810313000c1b60595581c0d48441d40c192040c400400140c400004540b00c4407810704002c242d40c0039076004089002443c051900001e404d05c54008200070203100d07503a044c2d4541000c0b00c40003280110007141150b408461020a407114440031841100072030b030041842585a00d2081e0314094107580701410780c00c01c200e020403207039544c50f4603843c02e101d00308903e8090403d03403010300080054000b2503a03038000316904141c4544c4176a01d08208110b000c0190080500d8080d10610940c3c0c10f02402402d04981154a15070351410414103401500c0c01090340000d03513049a0818041e502c40101303205800460407404400d0140403801c3c404000c41e0b80680e0300c400342c0700365500d803011440c510307080e0103844015007054002e601a500f03200301da0480c68080010703965400f0409840703e0200b801220403132520401202c030701400299041d411216 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 874108219 1250 874106969 874106971
    0xc0408030a18051207030305090d0c14030f031c0b040b1906140f040b030c071a270d0e01120f0614010f0f030c0314010b0c060705030112110409060501030b 68
    0x58107203070b10115507461060000e0308010720040c220700e421a40007840003d0040002c2d001201d00903022082c5946a6a10070103032200a4202114100b921090501c03980303400c10a00e421002c0d0318028608100411a10b504000c052030312000040e5250320a42c1001d03125544641e00144000703012008045a81d020740c1f0428106029000c002480041c50000c030801c2d03503045400c2a411b100141d0702e41490003071860402e41014006075680b010410002021460030006600182c100180040103410021040706440318000441c8210004041d0059603607a0040f580c0c248117801e0707090042407044130170012030342401c0001a03118004e20304070003454911402da021005131800300b06454850702c4580d0054541c120b5403881ea1000a05a131620035005106e80c0144440111a04001c00da1b02080442018400002d070020400a07001040301c480001081001d1a00b06406003802c51855041089000110900507009010300084100764030050721194080b10780140c05c51010442541c4a180c42007401308 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 874109469 1250 874108219 874108247
    0x30d110f07060509100b030a0f020607050616030c08010501211401080c0f090c0708070c1503050601030b04090c0504020c03121509150a180207050f0115080601051005030c0408030a 79
    0x40345c1e1a202118500511541c003c0010050090140d41c2081e43c810149800107613007243c002506100c1500020320402070b2078000d4036006c2001e0803410001100504803051414100100711144c401080107076044039402c841d18089511101c00d02075100c1401000e0149080f000c000c1c80748a000000e05000c3c04603a500b0440c2e41222035480c400b003528200601c1d01030907070f098a460141080ba09000a4240c00100b80c094828010402c80d581c3d6910340a107450000190400442e03180e000f0042c1941c3d01d40300b51001a8011a010003c480c51521035402121583c000c060140e031740041d08000100e001c005a0b07a280946058090f40c920348400300303440305600b0680700c4c1d001d200c4010110b040c40c1065040503000e20005020500028544140e0b82400c01c0c03008000c85d01c555082007201d0106030f003408105004149040045928600b6840c0403e90724002c1e889408145c2040c001030049a460640b9003141c42101d103000c580301d444010800109102c1ca5105180c0361000142400d032a90300078950f205144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 874110719 1250 874109469 874109473
    0x5061c150e030702030a121215050d030c050706210203090c0913200a1a03070c030504030605070c02100f0c020405090c0d05011a0406030503070f170426030c030d110f07060509 77
    0x100c0030a1080302540e911100274151451502424010350901c9107013034031480e00901d003030040350103261185403c156190f00407900284044040030200841c02e65000c80700c0001c6e2004619610b0034a040e1078403900f001c0340c4503215201040108013416a02c0c041c0c44402d80c5c00440c6a00c0c511301a80041c50320140504581c0e02070704050600180c0031020524a409000c210007490345543e4a06c00203c4850f604804100c2c00d1100504c004000300d101c9200303491052050707841c5c441d2b50b210513004001940006015450400c000040c44018459100d100d4000081d4152004502d0340c80b80c1440e541403402400c911a0480b110705140d8060260540000802908c4c1c03140225114000c0c10900064403140d000141882d4820031039000005c1c0c150744040b081d00d00403101740c2d090f8100100803002a82c0a94800e5030b0b51031100c2c1c00c945224500541d10115070610100035403524041d0032801391030380601061040543d660300b007103a10071801d2404072030707400e1400d62034540c3c0c0b8106c034600940189810b41d061000c1e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 874111969 1250 874110719 874110737
    0x112d03060a05040c1401140d05061525140607270e0601080a142a0406270806071d0f090114010c060603050105061c150e030702030a12 59
    0xa00a584582c90060740c00041850303003941820000511708080743c60340c40c10030100360b0300c0408480340c0a024082000d01102c01188504001c030400c54015001040c03501d2003841000307d990284902c2076a24054109600302c04a8540541490141907202e412102c07654011481001812a0f001c0018005280d80c40100b2141d001c044503690025400360081d00c420b0001c035170105415600404403194000860741000c42e40f40d02c203000d0010f8501081d1411469200801805002440f581003880e1002d440c0d0b05003682098540381c001056480d91007002d120320291203225480c0d5401c0394103030740043d01e11a411198607080002c03004021920500c0350a10001d02500000d0040c5444921082c1f1040018006c1310280d0030500340301540e440d0142e010f0b050100404401c00060b500b03018242c020b500410000410f45414002d03c210038140b07902e500e001600741c226202c0081d01c0d40d00450400c105010001a0105205100c50303d50300c5261303c040e505203e80e043ea2020441030148080c413460300796440030740c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 874113219 1250 874111969 874111981
    0x503031608010b0304050a030e030c040c1e0311030739023c01030e0a05060a0605030604051213031505060109140a05042012060901120b04112d0306 65
    0x101c4d01040e2001805a0007050241010a104984586048000038107542d81901c0080003d022104802d1041e00402c0e140150000d000c60442840c48542085050910180c05a1205044c25210040403002400260700b0100d0042076603250302c41561a2042401c040e9840340c01207140c0d241d49181d01248110a03d03000742d00300c0c0b07291649120340100d94444117007018108114420b0350300c61844030281003542e940762140c5886020050010754500030000350400f403c0410f20b04c0241c5115400903800f80c2d0001d4148400145c0005000071050f08090403641c43c2c0381c5250301200900d00c00e42c0090409000116541038101c06030b80441d02581098031464800366444030000e450b27a001840b0198000c20303150f8200801c0c00c0c103401c6002d0801c9000240c0d40b041c5901c04610140b40c1001c0d03400c40704030780d000381004007a06000c40030710302601e040c00308200404a690340303e0741c56080c0204000c0c12154254469a860b403684502075030a140e8002c09800c250140c4803210745000301c0c0d40003841c460b20409021401d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 874114469 1250 874113219 874113239
    0x9010b040c050715091106040306050f0f040209010b2101061205090615220c0f020118171810050c070e01260c030709140a0c0203030a0902060403050303160801 70
    0x1072250348420301116034907189006000810020310142c0300c500000203420540d991f030b0001800a18414800001c85040c00c40001481c50801040b0b2840c1c00c1ca14018000582e960542e160304648248210a98603040e2141c6009801500c94641075008030307140000ca141a00b09003008540c005e1110708101c281c2d00c408004e60b850b00c0644000021030704d06580c102c0d60381000840040d000d00c07160b60100081794680303080c10888610350100b00000300c0d20780810030a25428003400c3c02d115855482c903005801c8585400101180c21076448580604c0001c10511000f4040d403401c3d10710300300400018007260500000350070f650209800751f5141c0241c000200c1c016289100d010705031948030820056503246840e106220403103018018106101d051140500382c0da0810024000e006084008282d0b40f400588940d02c0c2e000141c4000e8000f0304011b0200d03000365000040c0c81c1d100320b0782d80c0c0105500c442070020070524441c41c0c03c0a402d5000001c208040f0b42d03103980038600003100c20ba583d544207a90382e0728052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 874115719 1250 874114469 874114477
    0x7111e090f070e0105070807020603130b01121502030405011e020d0e2103070219051005070c1101081b0c25060207062006070e131401052709010b040c05 67
    0x4008564200e00f01c0030154440c001506030b2500c161842031500e003072038001070b40c02d42080310303050000029038040701c0400c0740040184e8014411107140b2500f100b490f40e01e40504102c202e00030342103564040006010711a0135000359100c0202032810030b181c1d5000d0b002200c06503200c40c2ca40c1510500301006900c144000190303210001d10603c0350780d0b03403091440d040b41c2990340c005010502140311310407900100c002080d42c00b50540b40b1801c020580180104c9010003901c00052548040c0547c0350f4002021400d100301c1c00700004800d1074403013250780d104050f00910030301600d4031500007000171070b85410880e00043d8440100780811405d010300d40051090b803946030b85a006038001a0030400c010045140103000004458181c000329042d18100d801c4800d02c1c0030022111000000e02c4501445254100072240e00100382800109000c88010f0080c8000350203010b200c0d9a00840b44000741000c1250090381485000e011030039407043e0390a02604017406013402d07800c4d082c4502c1c589045240901e005004403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 874116969 1250 874115719 874115731
    0x20d052401020307020402130b0310090606030b0f040b011e02060103021e030714060409020d0c170618090127031b15050603070302040204151206060e0607111e090f 72
    0x10f500c0c040060713080c003000c1c0d0024400042030313404074a000f04589890074090f5100e2030902140b407002d50b00e0401d841d81030340c10030741c0701c0301c00c2c03600d003d0b000b4002d500d03403070210019090284e40108289a451300100d0726028081921b038010286140703817100103680460303018100d1b270007140c2a4034802e0003c0004001c0000311040113074581c0c8150810800e6400403110040d80c40c41c0140068105641ea49100090780d006101c0045095500c60700c0410341c58014140794850f441303030014006546804404901c64038030a10344050b401412100040c4245425000184500300e502c402111000300c00014289600c07004004a000c9210220110341900800d100300107540c0c2c1001d190300304a480341004100411002c1c1c8059014010600040007689030360008000804441d0580c00341031400181c010040c141041140030810b05060f42000720710703880b0752040d210711811200103a031002246031030b040d005000b0078060f130010740c55465841c202d200c03c0c10707240004030300b0780d007020035030307803480b03001c0c08101800c540b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 874118219 1250 874116969 874116973
    0x70e100e060913020d06090503030703021207030c1d030309041b020d0503040b04021c0212030d0b0d05030f0a0c050105160e010f140a090816060207080d020d12020d020d05240102 78
    0x103032901504e0440705d90010680150740008180c4075507100c035400e40d44201e1310000401c0d0001411481210001003490780300c011491f0401c0060050f410040c21a40c0804603000c4e1b0790040840e00e4810368040c01240c1207100b00410810135003280340a80c041004950340e00c04094042c041c100700c001e50088084901c10f42d80100b51031090343d00e55081210004030785182001e101840c1c2c01400051700c030383c008920604081170045890704d4200242d00d0603100e24500d058081e000100c4c054001070400400c2e5481d4011050b100da07255070010310b0445003a829000090203560829041c80700c0082404030b2006001007a540304503079605070400555206400c0142c0710009268054543c40b540024800b614081482c0d180480c0d420341e03104102444c0c5146031000203181400a4010400c081e01040801c000344144030160140010349074029444010300002c550501c0214100e40390507401e26411a9080901540700b1529001038440c110002d0100b1a00e046e030710b1910356103524100c244d007210f81c13070701160580c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 874119469 1250 874118219 874118251
    0x1e0708070e061b0109060e07080a0b0a0e0c030a030807090b070b06090411210601060306212310150807120809040e030712051201090c02070e100e0609 66
    0x7051150030707030140c0d0322003424004100e00708210041c20700035603010601640000c50030340d0540e11803900342549648119002d6010600490014500d070145507406009804009444c10000c40054207205e8400d0002d1740c5400b5141c00c5030101900540003500a06003640d0302144c2036154001c40107203114000b000340c50f0a4a01000030310b1403814141040e40325225181c241603407240e070b80102d164010b6000e000c9200302a80a400d424038403040090740c1c01401c0500e801d1203110710389644020400180d240e002c1e41c02d4044d034001e400b4002c0ca1041c0c12201910322900c0c60070040001d014640707409040300c00120050621600c901d4030101154040151142a07024289441c542281e03071442680304a000c03510650b0030f021034030a50340c45116040d0700c45820340145580d40c5051400d4081881006d40303080c280301782801034110304107071200c5003815542d1095001413141c1c210382c41a450301100d84e110b42c2140c2c4145081000080303050300800100c6051941a03078450b21040d01700700c0c100a080301e0030310807051021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 874120719 1250 874119469 874119497
    0x1203090306050703092015040b070303050a0b06160f051c1d0306060d02010e1903051612080307020f0601080d20210f03070f0f030c090b130b031e070807 67
    0x1b44d00d0031100400038490b00d0890401d0000f00219000b42d400820005004240d81080c540c05000356903201c0d2240308204030103080c16002071214007407a5400c000d211500c0700d80c1e808100e40700f001c95840540280440700a85600304480004881c82080d4a0008012107030130b84150000c1141529099801006001140d0710041403107901d0b040304030241d0420003c180d1122243c0c4072000241c40a410313140d015a181070450400b42d1030030b080c0075814030041040c00800c01001500c98124500319030721880981d66601d84140c00c920301000c0000c0708810b07014500000507007803000140e4403004261601d030b0540f8400000840390030b04030801e00000c004d8010303800c50b02a1010802d10010110004c02c40c5c18140b44c610001c9414580049584202080c2d008105949594000b841d951100320f8078901408404130b101002402e600c150312540441c4040403036100c490107881c2c0b440102501440c100e042d04c1c0d03d860b181c00800715500108456080001102260840d4440d045c05441520b1a8072900e401003021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 874121969 1250 874120719 874120763
    0xa02090708060105130905041a01030c0b0a0e0316081002040f260307060c1707021509010608150f0c0c0712030c0204020d0e010f061508040c120309030605070309 71
    0x7811030f41009400c03c0007003a50508001a9000b901829034001a9454a40b4003407500e41c0260800e98a058096801080050340d4468240c041e90b607107082c0661151100d0b1803d50740703290794011440e8940290000444007000030620b030b004980200080306d11b6003014080308403c07441a801800c84440003075105100038180b8120f10b8030104440004030b00c201045418190454200c14400c888868035200540b0407146d011503100d110100ca103161103040d090242c406076503140243c200190409103040042c244840070341c0312030f0040080806503401459000c20a40085204840e0740500c40d90f40030210304070044401c01da0340d4130105075000308030041c101410162111007a02c03003142080328801131000180c60ba80080c04212010341c0d000f01c4d0f0711880c17844290075a401c074071100b200d00345000001c02075002d0380820841c1e0040300f41804041030b226410312030f400741d406811158001600018903010590710500c444220f0b40582d90400440d11905d40880558601150261203980111802d2081d9802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 874123219 1250 874121969 874121971
    0x10e120a0203040905060d0501051608062d040b122506020a14100204090605030c030a1214091002030304020a060903050303240a03120f05030c0409021e28020a02090708 74
    0xa11407141c03031f50559034150944a0031990f0340c0301d1880c1c0c4855001019003107200315810603403c944001085080600c005c0c008249226200c00d540403041d0510702940301d591000000c0800034182d1401141c1e01d61030103644804200f40d541c0b0900c0943d12810107482e805840c5000d840c0b059010303204d40607842d101d1103c81010307031900d00c4d01c41c0203000034007155042c244010001000c40800c0441c205207801e040500348900d108840d0300075004181d9200004820684010300b4180307605046800b01622060300c481401070400c1c2e9608042c01001800b80c2c80c0d000005503200354422120b514003261940004c40d0060001d01c0028140d520602c0821280600c1c41102460240300d442c2c1640c0036840b000000c2c0100360b5680c03042e200d54500d10407180c05268011045456000e0505041d841c500380410180901d00c20341c031540a40f9076010070340c0d00d1400440d006844080444061158486110322a4050030f90303240840855101e400c4a0344905903400410003070740d103c1d0000e080e40c185555034207041da903c0300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 874124469 1250 874123219 874123231
    0x180614091902070b011409040510050c070501020301120605010f0b03012304051608010f180e0c0603150414090307060911030d020f100b0a030f081b010e120a0203040905 74
    0x109416070305101c0c0707100d4805081d89500588490059524203000b0401704040034584601800f074540401c000300300c00080344140d41c80000c50001e60f40da0795810001c01030088040040640d40008000580603a207401c400780040e020703500402261341e80d107501c0e101401203071050020040e018401040815000f10205043c89240300041100304002c00000e02294811110401405051280140055030041404c1c0c05402507419145415050a010401c0d894a4640280d281a00c1c0d40d110880d0241c14424101501000380000d5100c0c141904401d0441c80362090041c080d91606850440c100d404004c51801550143d000d1840d114068a806001e4a1113220694131814448481440d949003003044281264890b405040d09902e28501e0a052001060859400134148446040550b4a9003c503008480d44686022800c0009e46404070160048110207400c1140c601d000342c0b03003d00c064112a490690000c1507c4c07800b140012070702403601901400b50300503801840b09004002851f800701d90405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 874125719 1250 874124469 874124491
    0x703110a0b0307050c010e24060d05030a080718120b091c0329010906080a06090213050315150d1104051f06050405030a060c0c050d080118061409 64
    0x980c4072004a20340c2ea000791240e10004000040c030040400003031185107030400265000d0700038212001021480c43c4040c3c8600e1140141000105240395581c40820303004c9603000c8242c1e91540640203026280c00c00c00c8401c0004201059150072006045040d11801e6410b0101d0601c1b88a030f50307481b0030b404c0c03042c01005481c140c89181403070700c0000036000052440069070398001c0303104a61580154001402c0c0542ca100090320701000341d115a80004882c0c003650520b280012043d038600704a5009000268841d0b1003045c8006074803041240c03140100801da6400f5000c603040000110075034122803004440001a94203c0500080340f40303001c0059001d0303030303005e040070400c4000001c000504869023990a100d1030f542c10050001203904403001c0900400c540c3c2855800e0600d4480403070b489070b1410f08002d1040ba40c8400e03c00c451405019003010f143c0e00701c811120f40455520700079043c40d0081c019840342100b044d104c500489000d0213001c040d1102c50b80e021f030601d410002071003000b00d00034005406e15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 874126969 1250 874125719 874125739
    0x11d01060e0c09061224030f10020906120c1314100e010201020d020f031005030604030806040207030c0b0703050f06060418020d06050612010603050a110a210608150a060305070311 79
    0x1e440c06417030080c080e0a80c1694403500100b00f080740c00c0e0b403407071070a0071030300a401c00d59445004800205440c051038400100141c0c2d07461a48001500d0b41c4201010440c080c0c8501081c4080d40c4c4d08074000d0034441c070402442d034500300d0f151b041c1c0f42c54400c1c3c2843d0413940281003100b81c0700c5c40c601c0b0384400f004500c810b000140c140300383c2c050f20109907004100c500070002030200c100001c06101035907c8000384001c0c0c019200782c2c1090b0700c00034401400100200d01868000903070808051081c2c041503c040d800202076482c41c181039200030042d100543d1522140c540c400c01148061500c101121f0890b4043c4114a0300c1c02e115182880203500070a02556071141e43d0400000c02c4d80f904070040c03103c0080301004800640c10503030042d045030006009900840c5c504140311994460070300844800d21800d080921282c0d0b11542100c01d070a005941d14510381d814100001045000082e904c01c5003080c103c443d41207036894050703540c102c980b64031001d021a4001c840c20004a00c110701c410340c0104015003c5185 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 874128219 1250 874126969 874126987
    0xc030509190201090914060a05040c1b290f010e070e041d030f071202030909040f0c03060c0201060303090b1911030c1e0c0109050a05040b1306030302011d01060e0c0906 74
    0x403101b40c51300c0b107a0550b02c1c1608105591501540b00c80180100711001c10030000078500040154648040490301400c0300d410070400d0008005e01c03450300440341c02d10007600080b0b00412105a400a4034091144500d00002103100003e150b00070b4803442403951042d41c0c1c0c1d448042084054040e602d10409000400d503801d42e040b04c2c050005003076643d40b030b0420340d07030710015031401d414059444c0d8140c40864000784600407855440021443c0c1084e0003850382c00c080070113070810100c1d13005c295000030660352400804880c3c0320f406400c00802c880c025218000d2459541040b039806100e10a69030300d149510b030300300080d000e010b4003440080e450000100e0782421868100c0b24035114045400c0210140c00500d6a4800b003000c00000303003515401c3c170317113207408900e4040418002002d82c004c01d8070a47c2c841d1401004c50310f800e209021250612902406041c0d907074100a07009120405100341c400001c3c8214440070b42c81401504d045520300c03070910315160b07a119005005038021050259000c0d0042014203d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 874129469 1250 874128219 874128221
    0xf05071d120714120607020a0f061401061e0908030307030e070815040c06020118020616290606030c1602010504030b090d080a0603020a030f11030f0c040c0305091902010909 76
    0x1611000c3c2001810060b10b004009500da840095880994070400c104a10a640480e0850107591b1060b80d030482000300c1e2801e01c3c0503144601d08007003039020724800040e100764019141505201c804031004034050040b08211141803040c003880f03031a40e20030030110303000074425406910084004c5c02600e41c1d4507216030300b842c141080c00121050280c2001c0a12062200501e819401003143d40020403601200d50403084c0701d41c8035590040d104e1034022071003540680301c0e11410082e43d5400b102540c0c003000da10071800d0703415110310400484200500000307040b82c00c154045070300a0006204040c184649000c26000b041d0000004034100141480008005100c41c4a41030144980e10040c06420340c00040c010030069000f04400b6500341800300420141c1c032007010707170400e60340c0052140300c9900c1d40381070072260000101041034140c414480e0504403070001280314100e41300e081790b050100d41c00c2c000c0d044066890681309130300c8036004207860285200d01c03d01c013090690f1040c10000e800f5030f0b0340d20100f4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 874130719 1250 874129469 874129483
    0x90f140d051c0306061b14010b030d02011a030d051c02070f031d062106060f0412030305101a2a010b093403090c0311040f05071d12 58
    0x482e00c000003450719212241c00d40100e43c040c203451b00e07201c1c0d40700601400e4126200500c2101030460221044503c040ea00c0a40001c4415040a41102d68521040704024000d00300c0038004011044090400681841d000c070711160490303007a58038a8242100c819402e1030510340301320f2501c1d010754200124000101440b113405145402521044144e844501003035103030240010410784030b000300b003220b43e08195561083c072020300d104001c0500355945203008a02d461090094454402d00c0200c0c0c006044400340702c140c406907110750760500458960700c02d0710100c0c40c010702071b01022654008085292a110034054071276054a41c1034902050814a541504498441e00c000c2d00f0f80d444071130000490070308991080d00070351001001c003503080f0310194001c850010202c42c800c500040803da2004103102e070700a01e00558100700a50802c6076a4500901c9801c00300d88143c0c051401c004241079482c80070300c240c1c2e00c0f603541b60f00c414121800441c3e040c0e204007003100295501070350308944010080c600b007003c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 874131969 1250 874130719 874130743
    0x90606021c0e0a0b0c0f060c180f0a03050325030512190e0606030706020307080304120c0b010e010509060d2006121e090a0f02091008011401060f090f140d05 69
    0x15170782c5024008401d42009201c0c1001c85481c1d0049003440406000d4004842c040e46114094204040c1a40005010005d11008a562160034008003000f4040301100400084500310021200015a1000c51010211307825001e8007180c024810080544040b100e0307280c1c0660220001410511102c00350f4007220340000b41c03035155034000020005d43c1d0400700700038009090320780010360400314180d07949805403100500050418500300c445503a56809a142140c1d10755110560600542e1a284241d030602c1c004d10969210307502400129074641050440c09400c140c010600c03140312040c0c40c01c90950440c4801e031003604004200500b811660520340007a01a04000c246640b02005981224103011005040014281c20403c449800188403411143d241907041d00c1d41a41a5a0b03c0314048500e112a48403a4095007860171a0415055882c000340c103840e03094660010b5125400e4048a80a10324059040a2644401d040c0245d603c4014000c001d1840200036400e4142c459840d1400c0410355851 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 874133219 1250 874131969 874131989
    0xd0c0306060305100308030408090a15081f06020604141c090503011d1e011401060206040308072f07030204230f06010c08070203072d090606021c0e0a 66
    0x1007032104603414041e8981096080d10582d10702c90450b02c1da40418400504001d140480008028400340c607010088002440e80e555012000c0400510103070110030100d520480f03155080041001040880c01010140c908130f90007403440e40d0b20384d621888811034511007900035220780b0524075400351400741c0703042020110365034003079003145008189401c1d541e0008500703208054500126aa04e8000265046030000702114144080407011030580100f4031400403060715040741001140d9503400240040c0260b1003a40c5181c200e6440c82c1080303c451050300c9829003042006440c400c51604413420019442d216801920401c42c0c1e01d0380060100c03195141003200c1e0024104c00100d510b20f40c60200396001c40a0f01d494151883c0c0b50000905036404000001c0c009000031680d00199181041031030054068002c0c001c0051400d01280014415400b1702c042980000c1c20002c50940e81902a01d01218a1900209070107401102c04c501c1d102c03101d126503c1007289441201090385d03101102e103802812050a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 874134469 1250 874133219 874133231
    0x60102011b030c020a1415090102030903091035090c090714040e090f06090a0203030d020a23030a240e45030319051302090f071e1707050d0c03 63
    0x1030041500c0007004031599910520820604330300110884405290072203204441c0d2083c800156814404181c00c2070181511848a0510349100c0c00c11903040c1003407504521050792450903180e0346640c54240550403501d480c0200301c41ea4020000b9112456140074100c0c105900c602410030040300c1251001a681d1040300c4140510b002030001d01c0c1c014116030040c00b124500382d00460340d288500c03804d03546490390002d00407803031500c1036140f06482c2c580101a0300805031184804000b6400664050b044245084c620b00314940041e148590030180d40920a001c85140040300440090000e2a050b2014001c02c000fa43c0300d6401c8a41500d60210310300f01c8800400a8280b410980b00078038003400450740308006004c201034144d031100c0200c140040010a03290341d03080703082c0400340c00100020b4101400c442840a40341a1000b0b43d0303c82c07a15681d071421480c000001c1c031040d406910710f000c0301195146c049a160644803a030030560051b0a41030127850104a111250104c81603104000c002a66942c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 874135719 1250 874134469 874134493
    0x40b1504090c110714010306080f0105040510020705060c030406021c06141e120304080a050619020403262503120b060f07020a05190806060102011b030c020a14 70
    0x7101d1008540035618014042c043c40003901c1d0f580301e60600032000189510078100f111030303101b0741080703020307241ca00300703940c5203168010149010b03200580702258140a00d4070717003640b960700174400e60354841c6d04600102855180e6400b10400341e40082d0098600a408000d01c2d410216060741c81d00403800d4000703000400c0c515002c2552106800030080510440c488007a0f40700006038413941c0c900129007140e0302c41c0c3c00c2c030000d07805625500ca158046c0d0203034010200d980090100206019100d504d0703411446a9550a00307125508038843d50100a003000e5031003426503490120201e83c610081c10700e4415501d0f001001030f610303002c03030b400801d102e1550780d02035054002c05602002c000158140342c1018001100001c0008105000700d044146040401013444019585d03034000c024001d28002e40b010621501109652002c2c49150103a455103101d01e41c00708026500c144035100041401041c01852038000950440180495031152000c5118616802c000b04000807807040d1007902d00401005003403075a07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 874136969 1250 874135719 874135721
    0xa030c06020f0c06091c02031204050102070b120c160507151b0c120c090617070819020f0402120114010e271909060f06090203150f040b150409 63
    0x24803444001500400640f07541a2209401e8480d408002c03950802e402200100110b481103581d04080c4d03051042e898503030b465a0901c402041620350030381c2501c0d02c6586604611425215001c0703800b41c4008540c0009114901c1100548003480b1200c00c00110103055413140c520b4003c01da000b9082038020340318138140c941d400001c1c2070508aa030841100c628070320790312034455105031b40c85140c4200c0c0d19401f00c68108184046124040e0030448800c1000c0c6403a000e8604041024800c60103c5120301c2802056007400020311401900040708814909807071036080c8800140001c0c05150426000d12402101100c0040381501070b22103025511403180341000010160201102c0c0700b8080c000840c864070020351a1000c108100c2c0e4040080b0f081c9031140c82040041c10081d2580c030101600e4502c00b0010402140c0201c0d0114065103018000c03143c80e0501c01c0304a120503140c0603200070f138503c1e811341d59041001d00d90a030b95030001c10000c0c249082c000071404036051100d0b0500140ba00060602c56010f00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 874138219 1250 874136969 874136983
    0xc0c1a0114040b09160201090614040b090a080f090a03061e110f1902071502071a0a0509220c08090f030406140310120b04060c0e100804050c0a030c0602 67
    0x4110740a0010040c03410105240c07030801740640c1054010708890144944c002d401c01c00302264402e81c100590600d100440007031103001e440c03c458040644000c1110018002101440c45401c40b1101d8540003907554000312a9000040c40307900040c0900001011070040e02c154540340081198645c07010001181c135900b11040d41c4210015804180600e440b4014104282c80385842214085c07400f0482c48003090786045a1580009049041d110340020981d41c00303e070020031619042c030710449150707020350741d189180507450301640041c2d020b0006a28524001210050701c000305580386800000e58080b00098903101c0816101007040d1b24180040920104142c41001d0081405103050604101300203062000c0c07503110000720304000c004288445001090b001c01041480c401848408441c82e18980c641001c580584016140c501022080360041038801c92114008040041441300d584044d9001030000c2c00542d254030480c1500d580301e4903a225100082c40c000d4810001042c9064802845c203c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 874139469 1250 874138219 874138259
    0x20d03020c04051b0f030a0e01020316020613031403040201211a0406030c0302060318032a06040c091e021303021e1e0301090f230c10030c0c1a01 64
    0xa4442c420003140c6200c4085d45e4111100401d0166aa2506d12a14010b401108440046944000140880d034802c040d9800180220f5400b95401999180d5800c05800c2c1c0d4418054046202a40c0c1100c0c40003003500210b500520504220107083c1c0340701c070000c04010981c041150843d50b1100c80380700c0c1b25210100078264080450f020302c045030556881280004841c8070081c0a25404004030fa00350702a02001e0440120801c1241e0702c40d240d03030811484a050818010102c002d4103141e29040c60742c0818254407442e0044000e428403441c280c604402400040c3e013088001c4803150f4048613006650000b0075102c0d40034610301c2c0c0d542d401c500410500607251609080c504c0e00488800007180c0b1010006c0811901d100d040e860719510000c0424054141c40000402901508012001304226981e030724206980340c403107406c00c070141001500d0741d43e03419104599022200e1000b18207620320a81042c0a80c8000b0300d410081050b6583d90244801844007003448a03d48260041c000614840da401103520 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 874140719 1250 874139469 874139491
    0x501050a0512070909031106090604060b0301140606160f050d02070f060801050607031e0816050702030615032407021b22020417030301080f0606131503020d03020c0405 74
    0xa2090a150b6188014400e0000c62a103440d00e5a082c18001c0300b00305120f1fa100000e541207850460800e546036003003254122080780c03503c21b6000c0d1a0505201e0314600007107580700e03a841a19000e0810081c0c0c0c000b096800030000d102c2d039585001900e032a280c500340034883c0004001070041813102a007090401d8200c0040304840c4038041044550200406044a505890a0ba070300c881c1030070704840da500340c0b010201c2c0d08518a5241c500140e8004074691003940006000070615061500c101d9043c41040d0010798941d02800109007141021040c10056600042c00c80b0b4120109440b00c150000300300c00e00d145490841c50402c01040c0d01402784035640105101c03030b4002130f420280007510184c1283d03803035056010100f40040040d0480e0b4100c4000d003d2020308582da20040d00c490075501d134802d000318885030080d5640c038915000c001074a02e0140e00005c004d10320300008a60481c0c0200410341503100c0c1000062030001c007580b10600c200701c409000780d000d070442103058070500c015105e016003200c0002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 874141969 1250 874140719 874140739
    0xe0625060c0f0c150f06080a060609111c0e010c12060801060510051804020c07060e09060919060509180f0a080a030c033c06080c0f1c060501050a05 65
    0x310f98440c0d540c40c600ba9208034080c0c206041e03848070000410012200f90700c42ca192044c0807803101c80c00103c400d580392151300c0a0007040c1c0c4500d46002611a10307103800f807801c642840100359014046c1c01103e05c860040a000a0802850310b205095803061144200487c00c1c840343c119041185004680140c01000004c0c0101850300300421112156006140104030011070701c201d442c803001c4c10040200c1c2c4000c1007951250b014444135030711500648034400100348090006100d5041003070b481e5210300c0c0010b0103100c1d65900c1c80c1d142c400e1080e00c140c0a0030129510040402d007907850080050082c4134a03030740422031000c00300705c440c90201d00c01c0c4081ca841d4041060352001562010407500c210400e07140224002c5580e210540c007901c10305140d8401c0f0715000c41000710400344444118035070640030007411561400c00c0c1c81c000413200c1b01d0040d070340c098010020400c601d00b000f031000381154201070084082c80c00e441401444859000300200c0d55651281c00412080c42c1484030744002d4281255003a000f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 874143219 1250 874141969 874141997
    0x6110f01090c030c150e0f0301020c010603080c070603152105030f03060a1d0c130503060c12010f1d070512040b0a060503011109100e0303030c04091802060a0e0625060c 74
    0x101b04607803818140728030605140c24a180d207080d019030f02c0c90340400c4000d002c01c503101c0c90050502c0d0844000c51120340301d22100061100c0c0320340280d0404056500d4104403850601c00c1112405880448600b0110800e07001240004d10400090144140034402075031039007001410049182044c4d131200c01600031342807070f10042c40b11800e680d540004440b81a43d03074640512008543d2155564403983d45401007508010a6010000c020003525480030210f403041d0b031300c1d01404070080406018003414240000e800b054400552001141c0210b028201582882681c0c1c411460119085408481d06140c810038820010081e0241a0181a0440c02030001c05080d415000b01400f4400d44c00c3c0c45110401381031031401d80203a50f40c501c440c02c0501070707035907910f80102c5001d0207502911440340103914000b85090702500480c00c08151503802020700b1310f0426904011124050502e20656011b80c080028082444100694083d0105090720003815104241800d601702c0d00130001000038003a0041038501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 874144469 1250 874143219 874143227
    0xe010503060f0d15060602150106181203051e071b0b071b05030a050307170304230f0f0106031a0903071709090114130603080406110f01090c030c15 65
    0x1e5042400d0341c000005103050305080312491403134040502c03101e2404601190307403a40851131b01c92611803201c0028980c0d90ba01000c4605102c0116000c0442d211440705000c00c8255030360342c0c004107000e880c2180c00c00490f02a449014081c030300040c3d0390783d8400076082e010852040e038041c442c000c07207082c2010710918214001029110300000205660300700b904440034602ca45082c2ca0290402a044030700300009032400b640d699020754410b80d00076026403480515440030b20105c91017036030300c0040500c0d410140c9410f02501e80c45003031150360900900b1203080c0002c004115200403d8151400451030518504280840c01c1c0380c2030014415108140400401e610b0000840d03a185178000920b01090540c50410302d81401400074460744001c0f043e000207522200316615400e502c1c41203e05803800c01000100e130007250300a10000b40455010b010402c6100e0003005510280107001060390711118988080700d007155007541d0100d410804e0720406100344401a40c029001d030400c08083d030302000d41450054 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 874145719 1250 874144469 874144489
    0x31a09190c09060e1902030712020a170924040206040e070203040b07060f0c0e10200150060f100201060302031b0a0515040e070507030e01050306 64
    0x200c255005000681006a0454520010030340d0110801c0f015440e280000d86490003964214003621200da00e0071110011031003241d00801450700d490300c806005140307142c040c1d0400d0b0101020704c459282d141c03403120401600b641c0315079034080c0905543c1c03e40c0300a0203c20001d03602840344052102d0300f0800141c0300c8000f104c00b079840d0390a603019507581e05070080303207940b003a6080b400d0f82820201e4000200503e6410032010308412007008d0042d1031901d0030489070080c4000002e5030181e02c400484403014011080c00c2c4141c40c0c00c41e01c00d945540c40a81280c00d441c22400300140310702d80510344461008031300c03508045940d0403c40e20b00300c89400e022140c1e100b1a8008440050407507400c0405c2d003c0d6103450610f1040d01c0b020306501c4418142030000380c02007443e440264000c0c0a110400c282c3c000354103020302d1501c0c4004141c40f04460501090141070040c0308025003081004120101e40e013403501c6902482203410381d49540e99045580f5000b0401c04c00740d8400e46c1405418407e024040d80d896181d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 874146969 1250 874145719 874145743
    0x30501080d05043602070201080717060d050c1512010f030203030a0318062310051c30020708060f0f04020a03020604091d150606130f060801031a09 65
    0x350300712130381900300c055a50030701034044211200c26035514110054002d010581e00036264044141e99101c4c09070784c04100e0b1003204c00a90b6000001501502e086903404034000d00541c200e40c40e0600c62001300306001010342c481a10698007150300e0300341003440e92109025012540050000d41c0c515404070fa900d01403e2002802e060700c900303101941444108a004c4040c1c0c00907004c1c0304441d1920b541e1300503181482c81e8001c0310785540d80014080c0361944400b00071100c010b41404071030300040301003900085d044030f011200e0b01a05500200542d40091410030081201c032903a0071810704c1400003034982007207540b00d495150020810481c112a0320b0440c0342d03014649200035041580c65100298001200d41c000a5001c40c3c081004a0310360170a5002254207400c1c0f1022484142c14008070035642d01c1c1c2454500c9003242e03440d001074828200000070f404045a8030200341c603101e8841e41464442c8480c0e420140000e55030800420920005510300c0c942a074030300b943c8150b10b0404402140d2a43d440b8004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 874148219 1250 874146969 874146989
    0x90108040b0703180f11040608030f13051f1b020108060d1e0506060411070c03081c02040311010f0c050c090709031a0601030b0a0e0105040b0d061407030501080d0504 73
    0x60001402a0828401020204ca000800c103c0515101d42c07401c0c8414400e403105181d512245000c0d00382849150240c0320050020f43c00c0c01e07a06030760050254058030500e04080c0c0b41e030347e000690392143d50001e6021741c8400d07421440c044540c90300030200c0c00904c002500c06545400d41c5400b40c1d8010705090b0f00804251002c40121407a4102002903e01103003c01d440c44c01c428402c0801d100c008504240122800c480c1030000b000034802a10039030240401c0a02400d2840c1c40c10000038100000400d41000d0b10106001a88540c070051022a0019801510306000b03d1040c2c110669002d0b040c40c140c5203440c240034400340681d4031030558417140f0004040c0540d01040104200b01d004800d84d00096034050342e400c40b2a81401c1686129103415a1140d0100e070804001601c40c4c034000c9145401c1d10308411400e15540e02c1c3c04200f001a00b213550085030001c01c45c07405074000c59102d00803a02005605266a180d0b81010f0300000c0403035005901040c69501701e4000041c2080c1e102045408581c2291301d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 874149469 1250 874148219 874148221
    0x509040510080f0616020a0201080f060109050d0b040c0f1214250312031116030e120303040c170706030e070807081c020303010e0408160210090f0902090108040b 71
    0x250840410898014110b14400e140390510700001c0001c0c014803494520282c000100c02a5400744c0e52100c3c5003400a021502200004c0d00e2a070b0010b14440d80720300140340915a259440c0c020270303200300d885081996651820340c100010b103c3c240e1a094024401c00c812032103400e00d80030040380320388034003e0000c1650100c8031404e10f0010040202010700d031190340c0d03012002c801c8108010b0038402c1c40e120884007480803451103020103000740318050007184e074800c400e454254041600c0d9040440810102c0c14444e4034001e501c403c1e04d448080c1603118008400955132401e040c2481c080780c120f154051038602140ca118040291008210802100c16a050215000e801d0030f80c0b29051594680081926219000c1e00103010080050701d00c4030b001c056400c407001c03041003440898a901c024041d81481401182c08500091a02e600030728101041c042c000c0a14403d030343c0003500100b10220301900103180450103010403554903065a0007401040e134211f19050a00c00041d03c0b04000800180240d50000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 874150719 1250 874149469 874149481
    0xc03120d0207020f1c0309090b010206010e0910050c091c05030423090c032403150601020109230721031b0c030510180c03120302040504050c04140108010605090405 72
    0x30080c21013500000c00d0782110138105850388101c02281442500003480240d00092200c420748203080c0b240106a01614181e8242802c1c40c1307250601804800092080c8000c03d00601840e20440307020b1002120319587d00c1d083d01c810881022184c5140300d0009054040c1080040c2c40001150211410800c615141c19122480101624a0001e0880c0c0140d000d104003c042c8a5050003144903400040248416414054852401000902410360198816140700859040d07103000c0b0f6074000300501c00410f0207202c0d80d6803103c0d540c0036003aa5506070801d048090030080c0c418420350300038000b445004041440b4015200c0b07405c1145500107002d1146410320b801011004440e00c000309a00302c402a90013550380e20f040340c0c1c1c450400c84460f40140c40d00340150000000140b03e141045e80001800c40d8040c15074452590b540a440000c009240d0308110008890316103000d01c603c2010001040c903140c40c9840080704800000e40340e69410403000c0381c010f010142d044002d0b07131005c02e025100060113540b01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 874151969 1250 874150719 874150729
    0x90c081306200d05101e03020f040e16082a09101203081e1614090a0e01030b1509070c02060d090b04050c0102030a050f130e040803090c03120d020702 66
    0x948004012440040c8100f42e000703140c1c000c1402444210300c85030180e6545c07504200103003120740000e034003041011410405460071103204503080c0300050002410100070603c481c502546140311902e000880c40c1c08110354141440a00101110142110781c081f5501011a80b000c0112004a1040c3d66410100d80c01e40d8030000c44c1400380c00e00544a0014030300c50306008e04200c2c4200c0c2c0b01c0c484040d80045000810305000d15240c028030b560403000d215180341d00c02c00d4440c020303002640154804140080700c580c6d40c8840f01880200381c3e10844841c81e50660420300e030300440040c0301e812906104040316000f40c45032805640e0101c2d4524041d242d94480344005115485020210183c0b17506041980d0305002032010300c00d000d94454801c8408250380d94005a889000d44080340002c21414011194848916001002e030401a885402111500c0d14640112a2415641035802000120800c01c603880300700266800c0700c204030000e041a454158801c1c00070320442c00c4001080f0340201e81d070001c40d118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 874153219 1250 874151969 874152011
    0xb040b121908040509071812020a21061505040b0a1a0703020703051506010f0309020a0b071401060806180a021c0501020d1b02121201090c091e090c081306 68
    0x405500c11400d040100900320340c01e00104182401007500e00148d030700c680000340c032003080e405803004204c0382c070740018141d114041070300c41040c11504011180009803144148040c0d80e81000e408a116810101070000302d401c0400e0040c0500c601c808288201d80080007151000605c840b51182d4400541c0703401c90401c08550306c0140796202d208042c48000907006c404134450030081c0d03505440050510800c5042d01c401450180d041000302c3c40a21001440c9002441140e0241d0b403c0c1c1c2a0b15011020700d0f08641c0c05a0180c92143c20503008c0c4007044220019901c15914400018001a801500000c025511442e43c03c503012200703003d0801000340a405988006144607020010300c0b400180801a6410207170040c00140030f0070b1440d80340ba41500d07050f40d40c100d0309603000550300e03800c0c08582c00040401071543c8090003050400083c084503164500b0303140c0b44032040719191030361420391a4810b90340e0145541c41031104c0e400820060319860b001071120075410034030115800342e038407041c0310030222 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 874154469 1250 874153219 874153229
    0x150f0e060607060c0305010e0a020a1713140106050906150a030c1101050906091c020307060b0f150705011104150c031b08030f010801060515030604060b0304060b040b12190804 77
    0x20134000400d0f0681d4055000074120f6482d1010540940d82e0901c42d44128814000d81001113034412580d001a80300031154141e100780304400001101b2141d4503805030810880c0d41c4d49150780e442d4807050141e0b081c034801c0142c10900640750003031850307a00d48058480340544018002003564481900305007510030244616480b110000810440c14034000c066290328040b40c0d460070f54442c0c51128a42003000c010568401c4440da0b0140d402c0051030340d625000341101039807141d400321116004810035070b625002c0501c902200c0d0b10450380d403041440c065007980e0604203c50301151003480300300512004082c000889095519004072180c03e20300e419141ca84a14011448041301030b20f60104120740d4000440c02140040c120815681c0d03154206801d0303801c0d40c000c0e9a0451081c8100c0070340300c2200c00c06582c00540c004d001003840c039241e03484541d070740e041120181c036201c1c1c41d4180140d66003043c1c481d078000c0040603904084014900d00005075036400200c42c041303407114070f50100014050600d0507100500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 874155719 1250 874154469 874154471
    0x622090608031206060322290912091e03100f020d0e0a020120010b0d03051245030703270e012112030f150f0e06060706 53
    0x2a1038044003503482c1c106140200381c3d0f502800100307565182c004180da108404607049103076055107040e0070781001c0c0040c0d802121a00070210380042d008141860360400c540c400c085044091030404140c82c5405c41281c020903150230104030f507094641b40c1c400401240c4001445041e0f08429100120385001b4030900203145051270001e42c840c100400f44c0052902c2c070709a0300c007409001e04a880c4a83c0fa110108802270100f412400041b00c840c0030f10203c5620014900000070300e060030040030a150484100b0704030000744000800002d40703190246115000705e801030408180100c403034144e44025400482000200390241d80c09901c200800204111050840b01941d072203007103a141c0a041c2e2503180c0d1409007044401000c5200010808802d0301c02c071805010705c41441c1e442c0040000c904550511400381c2a1008072061010500c4254485655000da540006202d10000c0b015030444810012494542050760002c100038680782a50005807130f0440403010302500c8040020b4801d20507440024465 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 874156969 1250 874155719 874155731
    0x30504050f011e0203090f06121513050f0115030509071703070507030c030501060b0309060f04030309210306060309030903080c01090b160e01140304030c0507170304090e010605062209 81
    0x1684c040083d014600003526440414004102000300c82d019106030031505082d40c2001a0703287c100071a05000041c000f8029008804d003003494102510b0040b01c8080518040400401c08504a0300e0000d940341e50030f06d4108124102403075101c2d1540510b01c14142da684a840700070fa01080140120b0b2078130307030303111085035443c540d241781c0059154400d210030369a075440c00000044130300784c81040b0380c41141208081c000c1940d5a00f1a4a40d50201400542c1007607070b50356208001232000d503412410b402d01003c111703040700005c010080955541d9042030b170805040c8550000001d0300300c1424001e03030ba1300200c055141c2d40c1c0315042500502403204090b000e04004000c0c00840d01a192425040c0151980c0b11048540024010740d001c206d1040400306165040001401180c49502d101108520940580b240540e42e480440030002c8490b11201003038000240c2000130741400c1c4103e09040b00a8002445020324010000d405030003007202011861128004151010480c40420400b8000c181000c01c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 874158219 1250 874156969 874157027
    0x140405011d100f0e0105030f01020412170403152c0a03110111030c0403060b0a1a13170f0c0307030302030703120905072304060305120c0a06020c15070c030504050f01 73
    0x1385007400e1141030300074024082c04044040041c001c0b98251070006c030030401184440d40d1043c80d0b04081e402141040f05044c40301000040c107480c0340301180d03e107640f000310383c0d20320081c0c41010100245603190001200c00c01000b031404008241d070702d809501410800454441c05c5000c901408084019864a40000040156249504000e00240c4c2c0c010203040000d521002c0600140c01d41038090440501602040c001c0da0810f50001450410702000080703422a0f500c90707200d00c2c1c2141c1c2c906050340384c0d040851900320002c000c011070445a40200d0041900c985181c8000e900c0744030f09403001e01080b90048940d9480d096603040080900c2d809011521903650f00c0044040350700221541c1228201d00c0e0219540350711b484c2c0240f005403a0004064604a07101c50316080181d800380c1c00d03075003050107802c01800101e103092014100c100c0030b820140c182501080002c100c001c0f4010075120a0194204289010a610130251026680141c40c845a00b01440005940b4510341da4035a400383d108260362401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 874159469 1250 874158219 874158239
    0x120408031b0c10020f1303150c14160f0b01090c0f031b18030804120b0c0c032a010f0c08010b04060e0913080309030301140405011d100f 60
    0x4440c0242440c1100c84850401c507008180c03162082803030859001100000c81c00915900a0452075940030369a0b00c1d110a032200c40040354580d07170056840862111204401c00110b004004052900c0d282142d0800c019405030500c60080410032110103907003411001c00c20810200040e80c0325004405035040c0d42c1d40b00c0718000900380c100e9a00e40050503001c009808280a4020024803a20009446140180d803800072650070404010200038894904400004611f1580041c4058806144409090b00140c00d01051211002d0680c0c000e6690400c650780a80b8804070540d01c48040c82180850b6902c00d8407000723181036440e058006c656510b070200c4200d03040340c15030000b5443e500946940800c6e03030380d980b01101c0901444c031441e0041008001d004805140c0034812035404401c505e41c8211446143d154409503400c1254121000c0d800080103202d00d07182c00e111103d0209040320180720640c14064100464415001501e402c1c450313503000306184008155001c40540f0006101c524455501c4000c64 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 874160719 1250 874159469 874159471
    0x130803041514091c200a020f0d08120406090818030c0303090109061202040915060e0409080d0b01120e0a033c141306080a0e0709090812040803 63
    0x4010b8507040b040b11140d00c0001080d803148943d0b401800c02c5528440f01160400354904810040010341c03406041034681446201100d010540b008000f40303412403041c80002c1076000c24079407094240c0016000010404801c07a1180d0310308510a40242c0c4442c0f504d00c0203885c2c00c8200601c0100c0c046106c860003030781b01030044014001103003100c482002400506482e80b29180007240010b241d40000e214180c0a0707083d0707030b4062046d100010b1904d59210701d46411290341801c0080352030f5107960100107141d40244c00080071501100c04200d9910b440c1d50f001114450715034500d000d130f07072900d02c4206168040d08007050840a0000c0034040d00100a410315281c2204410032000b1401d1102070f23030080e01140044030561604001030074074108218049448140c1840c400d0030403c020743c41d40c2000c10b0142000381a0116004009848503030500e140945030810090600c6042c82c501508281d825100259441c129102c12000040041c0f01e810068420b00c1102040d801c505850014030040111940042d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 874161969 1250 874160719 874160753
    0x90b130204050a2c0a020a1d1f03030809031b01050915040507050f190602100e010e060a0c03060909050d021507210e010f0b150a02030706020313080304 67
    0x3002550b5a0b100c26500b00c038107007181c0794134140400f080c030039100740302d92000070b4101c41c000115803140e0a190300107079490030640c010b40e600d03002910300b04645410b80c02219030003a113102404840070308030340343c007000c01d413002e10001e801c0089600c041290050b05204580d110000801c04498810a4205a41c0030780360a8030250001c0c030494550340c54442c42010454012503000d0040e10100d8074000c100801941c14501844e402041050b07504404950109040010000398028142441c5178500e108210f8004c61400c44443c2d041200049400f600482c5640d44001e21039000250389068203070403001801a504180901c929100c04c500070b1080010b400c5191820590885401c1154175500210425050b030361200864192220304810100c400249c40c030b42d044140d0009045000d98452a0130b540044400032440d558860660045003800b035070382507106211480c0075180154164009640348600600076040c00d60104c042003250790750017403008196400c541c05035140d046c00c0c249a15024080295 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 874163219 1250 874161969 874161971
    0xc071a0c1e04261b0618010e0d050a0201021212280c05040e070e090403080901090b340203090f180f0f130c05010324060507030306171f090b130204 65
    0x20308103100c0d290040030042030a01030a000d0510f00041c03c0c0100e450300c90701e48541072068100a18201c9e0b00c0c0c444842c02041e00030401081c070410180000b9082c08800350400d44c4c4404104001458402c1095245801c00038010050090340c42c9170b81941c100c909140c0c030161215080126000b002640300000e0800d90702951889601c0ba00d464805072131176403072004402d030400e15040000d404a405030380e1081c0c5c005105c4001098894896980003030360002100d41720035200000c1001d409003403e203d442d840c10b20080b981e0141404000c94040d542c0c0c0181c8510358400c4224080c0d022b407513225a07074408119601204180c509040c0941d404684020403140e0303003902c0b95000000703501c061080342c03071035186a0000b4041504904003001100900300b203446481c0807015548070400705015048400b001089103598003a215100d0380340050039542c0580c46181c2205d000300010000e84c201040700803020359040c0070844d4846882d400900a007100f280003610309504401000150400d00480c040e506d4400c542c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 874164469 1250 874163219 874163233
    0x71106060a05030705150f0d0204090f141303020709020307031b0203040b0d0c0e10020607141312150203071d010c0b0601050f120c071a0c1e0426 64
    0x50110510701072044a40c584d21081040101c1e04210020006090b810a00e881c0307000b140c0720030200d05a11009480c7c1c02d140d4000390030001506203125101c1070181d904000c0c840e4800703299294010001c003400040119191410702d10405008001400007881c0d03090017551030385840d079000390040a191030310710000798803079002400c0544084100c030709076400040715504280424011100510001407144140280030b1307498213060b81c4508101aa00680e640100742609e0151401814007101d1052440d58103001c1c0300c03d2002440b03401840b42078a0142c00d98040c010710078146030000100c4e152080098a01c0003041c4081c140e0b000700c0d074030304001c0741a04c17078680280040700440300c00100300000f40807000f11102049140d84528000c1501c002d00201c99428070a014403402d090000c140c50400c5100d00000e0300908002140c1005d20101169881d411b000d0301d0301480342e0165114560020b0002a44081140292400b0800741c501402d81020750b100007070740001256002000300da007103045600c5070328 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 874165719 1250 874164469 874164481
    0xa060807080d080c031503013314040c031d0706020c0a083a020109060513080301032a080c01030e070f03080c01060306021204210c03080406060b03071106 68
    0x251901d18010240d0300e8800344d9a07040e04446081d04081c00da1240d001b22052401b0f519902401507250403150b241c0585260f846d0786c80e05100f508481200002d01ca01041001c20000000e510303148240300042e00d0100c0c3c11508100d0407002040110043c0749903400203800d03061203480020f68201550403507022164058032081c1002101c43c51407182c480250f01200741899800c406242e05103200001c40701002d13204a900c01d00c030200040408024005030364a644040c11302c01c040c011107030800c1c51072984c0301e980290380e2030300900d510050101903d0410107555002042906c003002c024180060780042c1e80b00ba490303802e441d8450094540b4135000a0401195005000c00402c500c401c841400e11810181c3d443c40e9501442c50708909501240c6558519001004c140c480c00200192042c40701da54045282a290490f45050b0048044422052440d0f00801107031700148400c0605405041620103039641d454690043c101036000704141c03082c04000e102125803c80b2075610000200002e0740c450756601 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 874166969 1250 874165719 874165723
    0xd03021305150a140f030103290c0c06060d03080609040c050306070e090603011b2001020310061202040f17010209030f010507030b0d0b040303050403090b130302120c130203060f090a06080708 84
    0x1600380c1031395045c001c0004100241c803e03080005010001da04100300f00c030b00c01c407506110180845220f41300c00000139440400711410b0028640c0820704403550040300c2c01d161802019010020441e5000f80307082130103e01031154010340f21008000c014215032081c502100024030000c0c4184070300303001c1c0200300007069980c541809074100b420284d1108a04655003070008a5002c00308010301e4458040c92172030394254480071b000552142e08110750060b0707418600280184144203004580c0740f00d0384180014404403201451280880f00010084160084101802402032084543e619850710801000c00130080040d04464031505043d201040444490801d0050110144000030824600740c800900081c0c066030204e500700e4060b14018040d03e84844e241441d543c000e124100c1e031085080e00030000c514140c1c0d04603030404009009000d445036100045584020062040c13085142c0100c002543c2e40c892034004851007800400799034282c00c1074a1701c03800500b098011a1814010f000d00400c40745c0380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 874168219 1250 874166969 874166977
    0x709021c0b0d12030e1b032514060d09230120180a08100f020c0a12030b0a0611011103010b0d0e070b0712020c0a05030d03021305150a14 60
    0x4054180350400c0c42e50b544110000140405160070305036140001505004200f1101401c1d900c1031400103410b00b0300204042c17900d02001c186107035803002d00784204c4040008400c1141210100e106400b03041d0122000100c0340c1c0104149440c24900d0024401c041c45541e0711811503070355400c1e50501021a00f92586400c1e190007281c01c01d6400040e00021101700c0c06100101800740c14002e03a28400f03c2404001a413540300c03603000715201d034007500c8020006482d500c1841c64a0103100f00461616400058150321a007242002030008880804c0740d6200030b010b500162100303807006100c000c1c441e4503040301800c502d844010f480c800350b01e8502104442d0308003c0440b070503292000e000c541440d900100c00e0300a0904003050014a0050301400907138440807002501805100d040401484070000780024601191155003521515503084100f00d00d89003c01d032000010568030740980c2c0c03011032042410611300c1a40c44950030045521a081000d8401070180000900c26070b038683e1402480d144899182c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 874169469 1250 874168219 874168241
    0xf0a050a0b03250e01060207060f020a021012091b08070503123c0c0c0108100510170c04081207020604120203010f05040b07140412080313050709021c 66
    0x4406062038089450112843c5010585043c0105600751a007040030020042a40f2240c09680408002e1105541020030400d590045100410754240c81d500083d50031074031070000c001489442d100d00421003042c0e4200c150129000890581040104840450340b91214825444030b070154070740220300e516003c1241d49011020307284180c2011440c00080c01e032201c070340400c000a032464a048404007031524016490074091003625076204c104501a003030130302c0606050181009103003010001c448131014154000d503101030340c8001c00c810040c80d055500c841c1005803992140100350070020b04040010007030003542c542c1000c1c1d6a442d204140d15600318010000002d510000520047c1f004484041c288403410740003e001251890041d00000700319001500d040c1c4001010004111400e0b8100341e5040031403207454a0726240c01e00d40901c00340b266841c504020b20044000000c100c00f810000c00030344e44642c200040d205101d03a20302000000f9481400c29000001001c0c0481c6410b160910a06000714 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 874170719 1250 874169469 874169473
    0x1801020705060c0f04030f110109090506030703110f090c0a0f0f0e04180f03090806010f0b0d020a110d02030a02010506010908150c040b040f031a2401090b030f0a050a0b03 75
    0xb4940c090a81c0440d08071601d0418a26030034440080403858000002e02118014075848c84407c3c54000011310110182e0010301e030341400c0c6400d021140d140083e00310220781c0c000004180013440240003401b01418204c0c035680c03250010040c0b105002542006044909042d12400c03c9008049001d0360107010464641022400e842a2484c040c2025041a0030350b000c1e1743d48202030f14005507180b40c000c06052009800007544010b045c480c2c42000c001090142814400b16a645403508401040303501c5a4000045165004600030107070a010b02d229003900f81d50b440a54820040f11a0700035500d410400f0b03408010742c28107010514031350041d01000240e5041c100540044100c1c01600f19021101070f1059a0072a020400003520900f084c0c00303003006c1d010b5000e008040340d00c3d600b0500b03019403c00705401d22a045030003c3c00b06402410035492880c170400e2001448445003180165a40344191344407421810340081002904940f02c0c07003140c410700d8001c2c020403854031882d04402c00c40d01d0b81385c1c00d15016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 874171969 1250 874170719 874170721
    0x1112090f0c0a0b09030313081e06011206020f250510050c0306090711030d0b01080108010c050313030306050402180103150b0f2a03030723161103060f180102070506 72
    0x843c5480c008001e0400c000e0300b2a4078007241074501142d6500c06520091070740c0c00841c00e68900740c480c40c80e1000c0c007546050003401a54103160307000e02d080480d0103000f401d003030340002c44034105981c820907240d0031818140040c10884040903134441081d101c007c00c444a005014540b02e2846940c03003820b025200514095046994074418015500701c0078101c0720600c80751038102c808040c002c02c01072503161020315021a019106c5c0b0b0000d00715040603000008203074108600c0c8800c4a51100940f540419801600d01d501a01d41c10f00341c0040541e90001d030f4020340001210030408081da01b00d403090104c2030740c0030000343c103c0c11a01418100c2ca07004040000000b00710980d00c0c2d20a1801621400002d4040240c40030040417110004850f40401d00031190008070030070480c142c001425012408030301c060b102c4411048040e1100600c074176210a852002142d40000902101244d020522040a41210040c0c100700e8000308040d50225a038406091030099442c00075481030003900c01c12076000c0024109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 874173219 1250 874171969 874171979
    0x90604050a0f02011b120207060212090d150603030804020a06050c060f060111150a061a04062115140102030a2a0c03030e01020d090608040b06041112090f0c0a 70
    0x709021103001681040f5a00070f54862411907440039003403003032180801e946c0c203803071642c8064205130070b1391310410640d008005175108503503485c4115000eaa104441140394541746290011001200c2708888030603900d403650110804d60810602802140203e4010f2a051f81e41d00c011034040c0305414588090703030030041c0410114103190031210782203003050414000300c149444416151003401a907a200711880c103414081402c14a201300406040707103198000c44420142401d41e020312179445400100038a030203241061071030102c00c41c040000900c10902001c0c0100385283d840041c14000c51880d4141c07085800b180c4c7d800042114095041505d9007042c0d24004580100034403c03003101100c0ca078a00c0000e1740d001914148000015501c251a0122640200c000091808084130261710601c2040c00381408101d40160f03070681e1050b4041c1d5031070302d29950000410087d007584010081c06110128640c01d40a091080c6070740305074090000c0b69240201d511a01d03035145543c01c141c64000295034810b00c0f03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 874174469 1250 874173219 874173233
    0x10302031e010b0d08070204050109060305030703080a141501030606050313060e0f12070516050d0b280b04050a0204030c030f080c03031e060405010b0409020c0703050307050c09090604050a 83
    0x703516800d650000038066440400304a58040043c1c08071000480095201e0071407400380b1540380507001c3c89400708101d07410360751041d42c0ca100d54400a42800006d000180740c20ac080e8020003101420500072a035142083c10314807070b00c01180d107040c41c0400e08140b03021903100d2003503082d00e00c22444c64001c42442141a00e501000741581810a6841c0c00f410014009001e41000700c070320880e4503144072039500c01860520600700844056142d0781008001e0701040f96540c0c080940031016040341c2500400c0d101c05d0400d145110620301c1c00c0c0790400d40708101350541800c83e4040342405806940c14805070361440101012403060340401800242240003d00101c0c1880c640401d40300d229032009458031400e4040381e0310f95001150b480d09900d40c454890310b08801406030391508400c0503039043c4030f254113004003003c0900560013203c80544d808108020600d00130405540110341100681c0e40c2c2d0340c1d0608204e074450a107a1440d038026034500300402c42800e8002a414481c90304240908840302c04d0b5a1910 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 874175719 1250 874174469 874174513
    0x4050f06010206011226071202010e03090126010314100504050d0f090b0c06041e030206011e050901030503030a06151706040b030312061509090c0f0f0d150b0301030203 74
    0x900c40c04d40c1409400c0d502006d5091032034510313099058213529082149000421280f04400c0c034030131641800134503440130100009540d21a0402d00307220f0300c1e03660340007000042c01040c99005142200104000010310002401004c4207406040641da014158564040c1c00e4400645000349154001c4a48002d001d1192003604480ca19a140c1351000075954801600d0341d400c149101e060701d1b000f01050008005260900d505a40606801e00390020001d032006912244148030350010740500b130201040e0104010b0100000d03041c003d00840095840c0d042082e5039030004c46d0910314152800c1c20110f09402a601d04001c000f100d5580c1401410100c00e100084c0c041c040c11442c1c10503107401440d406039400b807005d04654541302480c04041d10b0410104081d0301296413400044010412940f151920303540300c1650310202c00c2031200d075030304490001040d90344a25640c02003848404140940c000c08190440620a11080388010016450300002555440281302c0203501d6130141020300e01303840700d0300000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 874176969 1250 874175719 874175723
    0x905060106230c0f06152b2003010212040c0f36020a1101060b16080309032802070504230601020a05010f0b120703030f1103070501060b0904050f060102060112 70
    0xb482021092404d0b4500d8600250340d051440b0720500700310000313400c03c1070402100100c05440c1d9900740d003008080c008814200b2102800c0d1030071220b50510f0008080500c6902d481010700210340d1007007100401d02034008140c07011142742401c1d01c400680d4002040c41101030f1150f030701c0c0c0071912840d04c0c5007203032008071141d00301a0444c0d450301408051104502c0a0500001640c50703c40b46041950309050031900150000700764440d083c0406141400c0754400c0242050f40413044958030b464001030107155010304103001d05003102c907001019011607003882d980003000d1103800720f80e0031545807010802645d0780060982c0a500c18038180c9080c04642e0107880340c1100041c0103603090245681c0317819003580c5220f828510000e89404040201d030030b0180ca0101071078030980150100e1400c41d0b0340100ba201416038841c007040f01091000090400510480f11b180d940301c80200852a61085602c1c0710750013148040b44102d241c0000034032861441d0b40d90500c6540b059020340b90361b07800c1c110700d082c3d500881001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 874178219 1250 874176969 874176973
    0xa03021521010909060e1204150203040905090d080703050f0610120e010b0a060207150f050f03091014070906080a09060e0f0115030809130b130905060106230c 70
    0x94030344501d003040d16450192401400c080b446182d01e04000e41035030380312514402c0d1a48604122920b4402d10b01c1640c3c01e55440c898090750b07488028400324658016900884030284c90001446a030690020301064010003640703c0581720343d079a44082e81100ca00300c407180b034225500c1d00064101c3ca00303420b41c100c03102c8150030680b0031310030b030803030724508039054400184820ba40d00c00e4903a1040c5071043d03081006090700d20080c0709107130920440d0500200f2243c06c0301e0a0025074500b403180c0a018000350b9880807a000301c015161701d031050798180c0e50343c005044440010329246103559070500300705a0a1040310140c0710700d14414600042101c080c070006000120311960f500e034450000e9040d001d24040d441c420301c02040d0300c1d11200050b41c212004608174080722450408100005070f401019207290450803100c94440b85011021103002d07100c040d4115902501460510b00320084561041e44024040d0085400e240e898a40c240c8108401c40340c0460340d0021040c1d11031803807403804e0007002d4060000301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 874179469 1250 874178219 874178257
    0x9120c080d02031329160207230d320d0e010219030c0b0709030b0c0a0c062d15030212010b03060103050d0210020f0301061b0209010605070c050a030215 67
    0x80d031700d48029840c1a400001c2001d14049a0102c41800303180341c200407038044502c5001311040020395101c80d1445102c50070140136101d800e200807075440c030707082210001d426544007200d64a0004004200121203902e51030b0504807a6006c84103241c07040300d140d5103460091000700c12206090300c8814010080e81e045120300740031482c00800c80503101944d54800d403076070b00d0180c8040c40e1100f5800401424801002191882000820382503070b80303d6080f04108490903601c04100c0700884081140c450054110350a0003031480c040384140d095a20120703500d400081c10030070b80c01c0805c01980d00c907031101d1000c461040801c3c805450700c01502d15544413000700000d811032400001c40d0518000f6841942e080e001900d074103001c0340e010701660450f00010791046140060120300d0710302034003042c000c0c042000100326100e802030841800150f84c6980042402d06a580c2d01c241c001c000b0340c82200c041311002c0c0300c403d00107418100031740120f0030389034000c083e444501c0e1185002d11007504521809070320640300d02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874180719 1250 874179469 874179473
    0xf032006130602010f020901051207090b0406090608060f010806040c0e030109062003040f030804030302130902031602060609040609020303070c090504021e01090504020a0e060d09120c080d020313 86
    0x80041c078100d0455541c00118030301d40030b406401c44880c00e4650490768010440848a681e000080354000c2c0010304000c189601ca0b52002c450802c002d80100c043c0c1800080e0100f032003174128000c0401c942103580c4464842e912034082c02040082101c510340810840c4012503c0e515060b0400b5400b240280f40121161101e980041c1c251070111a042c2c6805690320906001c251518204464880580c2c03045442c5080c140c1e102c24682c009414060104070780c490104040504c83e40440700403001d416061000c582c1c984e48104001c1d801541d00d0103100c4620305118000700e002190092007217100804003020ba80e42c689030800a00f0320040304070fa141c0020840c08000415034800013000d4403c2c00070000d1146043c1c81480382c41200c3c1085054550701310900071120f682e0041d185130945109403409601c40300c4610081c1c81c4c06d180c41042d140d2200d40842c01440a076460b0b44043c1d0202d0182000104620000700c1c01d891442110360702400c11a81040000a2000207400139600002210740e030001d586425 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874181969 1250 874180719 874180729
    0x9150d0e03041235160f0308011502070303021504050102090a03030203030a05011a090f01031512020907050306010906140f12090f0f100f090506090a030f08010f0320 73
    0x3a0000711081e414078640b4014040003c0001130302c03180ea44e001e00c04003400c0c00307510341c0c070b2029080c0105002c00c0c0c001002103001903144030185600d94881d01081c8981210300e0090304441007400b452040888001440301f140b8400107204003181d4068000d0704800c0e402c40c11080c50720100801c152441d40d0200004903994541c820a50b0041d402903004d140c4a00b00781c0c08580603a5010ba001200c11100b070081040f00084607401c6840e0130200b00d52a026081d9203c0042c0c0c05040ca0900c001d14041c03040c04002510031040c9081c44a4600c00c07248400c00d5038895100b42d0f854002928036500040e444082800034a0107282126500701591880506002940d0b003c0400765120380801c88680c1c04020030700c03000780340030482c612000c40b1140c0078010364207003160703495920640507140c00d0310035071611040155248140e000f49403081d008415070350b4600e001c42070150744411201007100058060525545281c0c403610105058411005642c01c04516584669120b000c1c20051a030b2240c12440c07003202c40e0b50751 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874183219 1250 874181969 874181977
    0x12706091e051c09031709010e040f1a06070f0b040c030602190e0409050303150a080a12080f1e2e05270c03091c0305160509150d0e03 59
    0x407890082206280855001501000c0040c0c3c1c00305003c4545800c0c00082c2c4110f401401c5890007084007034481d2400d000403076202c01d00e01e83c0d107a0460329140c811035001e11a60800191b0310502181c02085440309410b0140900c01e8200151121882c80201c1c00003a03805001e864002c1d015016810b4683d4882d181e81c1300b01c0e480740c030200c4080c17842104d405900c0c40d00140100200340d4201c0301000074207116201c3c01c0d282c0c40007d1113224042c200d40c0942c00903540c1e807400740340035003c1013084580c15446403070201d001d084c0d0302c0e034528049950040041e442064200c01c05219040300c2c0c4030094510702d001002d4810389400707090501c0e01c42052848a8201c0c0074028001003400b140510030440500c0e100a0001d03501085140c4070142c011401007487c1078a900c00c44a802484405e001503883c0c0d1080c1045051071130048071142c850003100741c0d1804082d850341095024040c41d01500d28881025581030701c00c0d01c62034044e15000320f2101034580b8442d0b5800702600c0603415080010030180c009035041411544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874184469 1250 874183219 874183223
    0x901061419170603060411060a20030409060e0712050703090b04030905100f05032215050402040b0906100e0f10110c030c010c0b06010c02090414012706091e 69
    0x4031010301d942c5402c0c0c064092500104298043c2020f4200354640d107011607a94192607000740710014003403080900c5200503001c6075264081e80c1044d224000803060310b86d0721070f1040304203440c103081012a900c00100300160103402c29440b00f07a01c6007000200b0002602e0020310740024559940c0080020030b290514907803046101350348550844c0c2c200010004002504905007003005007a40d51003213101e420104803074028214000c13010082c010401041e01c0d610704600b0061400c171244102200255541d013129015501c00c58061208a61200510a2543c800c036015580701c65200340050100e401003089015409000d04400070b81b60268012070b00c05c910740c001c40c20014180340030b9010200c0b411301000050850481c058415201258002484c042c40380d10081d08042400c0c0104d10f417030f8050102401100e90140c201c0c00149003c1c10804071050060f003581d2900d5080502e0740d86400c0c2e20314118244000800c00c20f00c203040c0103440350801804d8500080364002040f4444a182e40c0c44112030b481194 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874185719 1250 874184469 874184477
    0x160809040606081b180603040f0c060c06060605070c18090209181b060307111501170105090604200102010b0301020c0105011a1603120902121b0604050901061419 71
    0x10814441250541548480660480c4c41c144440e041602100c07643c0b1001300070842c0c105031a6151424110710748180e4482c020980918050300040c03868120011030044d9004400c100411990360409455512901c00002e1981007000800e0107082890301c03020f1607501041c4000280c040f000d5020452409040d00c8074564906d90312440c08010004202041c0141ca10b868484420300154012401601000c0c003800b083c4047c1000704a4003190402c1404071030351a00080c072600d565114002444040020000c50307255080c0b8001500c42e07800003880c0e40c061940701c65900000380842e0380d84035801400144042c11552204215101582d090000e810415112000000da5516100d031609129200c040c9151528506200711002c41c0f8007281d4151440d03401d411300c1280348c2c62038851680204040c0e40000d6200c800361034a001c00c8040060b80c00030401803600e0030141540000d04120b00c1e03000ea84101c41c0e001310307200014020389120340c400e417049008207050796051222240000581c00141c0d02140009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874186969 1250 874185719 874185721
    0x40302030d061415120403140d06060f0f020d0804031115010308041712090d0f1202010c0813050a02040c05120f0906060d020f01030e07051909050a0b0616080904060608 74
    0x54075044d586184039141000b4001c1c90300320f92100d15402d00d84018009410300143c040d22070701c14400300c02242c20140c0155400c010441e2503004c06001c6410b0403003041d000a0b503c455080c601400006c65204461441d00c40e50644d548982d411a080442c01030b0220140c0140c1d04008201e500c81c003512070186218081c03540d1214140362848101c440710800c012561352100c01c0407904611400101c1d0b000b10b0007604c0d10340008895083c44107548002420042109001c1e465040d1101c0d8190b100c5061000c0981d22803140da216450301e0b000d00349540c074000c0c01a400040c812001490258010300c2c5601c0309062407030030031055100704210014100c4585051141003000c010366500d0030300c94945d0149040700c8644580401c1e03000300780302c5440001114181036441d2000152008100030b094014080107000e03010200ba5001500090f003401d01c103916801d810000410482d0005000303214481c0c201601241c14001c040405410406540c407054440d51001c02c800903040e210390007100042c1c000c41c3c0700d5443c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874188219 1250 874186969 874187009
    0x190b030604151d0708011104121e170a02070602060c12150d051b10050409020904270203060c0304051c0c0204020a0302090913021e01030b0409060e06091b0108040302030d06 76
    0x3d40b00103000b04a03080c7c100f00070501c000c0310b983c80340a683c13a40001801819612901480c0341802c52860068403030011178901c09446521000200710703507001e41e401c0c8c480345a43ea0109a0340da10701507981401c20002800a0441020a40d03001a4000748465079008a4070142c0d0105103403d035040410350b03168000110034000b6203820700590200780000d85601142d14146a030050040c0954003c2c405245d8001440c1c1d24103503616004004078007110701c0c401031001c100380c40c400e1602c1d591042c2203001e401307080005103002c1e0110058910490b0401c000e40040620404024914800340741c100c03080c03041c6c501d0042c01503150b500c060a281c03034054500690f40c204031003c202c45014024010a1984900040500107894070501001900420344d03038064442c0001c40160b001d028101c405917081032030031031034000388101038015015299480d4151641912030086060321180c424054100c5e055002d60346600c25441001c103140e03c54040e10540781130007164641182612460f5102c0055210741c0806038030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874189469 1250 874188219 874188221
    0x219020303040b010f080c01110c0a0905060420070201080601020717010207030e0d031706180a0615110705100c02061206090106090501020c0607060204031703190b030604151d070801 80
    0x2001d006500070455000d0319081c0c6d142e03038070801c000c81903040005201c10039040b00010030685100d810000c01d03c00c2c905403641803c800810301210011f120380d041142d2019044400040322111801012840e840c004c041c1c6c00540e615003014005038110300c9001400070f0384103a08006c030510740d8000c40000d070b41c401c200c0c10014054107000340c0840c4030321580707030441002175000388042c400041013030108a202d40e90f000000e04000c1c244000303404e00d0883c030000c02403031078016480303841619813a00030030342840c0348030408644081481d0243c0145a201c00300901c1a8074004000c021800303c03900d0001c4094546601141803078204a0350810070000c80b13010b108040c0740000281d4050400341c60b190005900c0d000c0000d50300c9105012090107000b0004080f0188800c98046501468000b2071250b659012150400d005900480300c013103000d06500d41c010290003560280c1160100001e00a088540b511340b00d00748504460f5000c0300d04159140d200072207880001d191110200720550180001501d4075080354 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874190719 1250 874189469 874189471
    0x1b1e070f05030c0d05010e0106060507140102120a05150402070303050708061f050c0c0d032c090103060218131505030a03080c0c07120605041506270219020303040b 72
    0x18004a01500e000e00c02610001180740c0e8204048403411407801d5581407a40c010660600c90b110b082d400e002002c1041c035040b80060030214480c40c0c1c0c00741048a1265400c0c200c1c050421903910241c545808516605c049801958200720300001c1681c451004e1000242280e02c01c0030b080f00800c0c1c07143d0820501c1604481502e600c01410b85014401c0080145080e1000c4040d20550041c00408550501110307130800042d0360401d03001c0c25005048106040c040e0a00c1c400c105014552910a80c0d00c400c12007034407841c2c3c007030710b64058552901e503400c40c0d840030041d40008074034000c80714554210200590303034001c1f00c890102c090040000c090000020030406000ea0390441d6000f64814002100003d038403c0e09140c6c40000e000e480713910340d0758408048c0c0c14400c2d180d10076031481400380740d80030034049503034401402240701e203c1c2a00000200414841912060b204900d44290354500b05da15408000c50071441a20540070010711300154003d240c81d01021910f841401030384003100308010400740017191 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874191969 1250 874190719 874190729
    0x30c031a0603030f0703021c0c0b0a0207020102191e11040b01030908040509040317070306050901240810030c030b040b060105070b0c0912060a0b2809021b1e07 70
    0x6054500c1d2400110743e6900c941c00c2c5492034003000003400e105161080c0907150050000303c104d150301038900500200b100010a00650b00481004013103042000103208880c22180e046e00a4200002452510200ca5181c0341040da94003048481c1d0315079000b0006152501c0611610b0f055020b404070b042031104941c49408002d062518224000020a09503c181c070300315442100e04080550340e82c070b8110303030103103500302c040c03010300c020a060080454164000100741c90302a94880c0c41ca0387e8030000a140e11140c10b0303c80042154a00e540d000d40ea100360381407a0720022030000043c10325034940c1c8141020a003640151410180c40c01072108005e03100032019003200c024038140e0305205254607050341503080070b40528001c610009509000780c80d50340c10000000e81c02030964100b4038040494074064550a20344034800c0d645a50400042d0035003004500305042c132505100c0d046410440f0180007540319200110004d200745074010a00300b020441604d1221421165002c0da40984100d03518010140c0c00c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874193219 1250 874191969 874192013
    0x71e2a060e10230901110715050c030f0f07050906070c08010606031b0f120c0f02070506180f0604030c03030f09080105040201081f080708030a110304120327030c03 72
    0x1a08419030070a031151900b2003060a10f08200b500c410400b036006107a0a1802c142002000c00d4080900c60328036054200640c00c0300090000366945002d8103a14071045520b800301d001c0000200368803c0740709149561160351030070000d1500b249140003036503d403c90301c81122003120038a41071040e4102802450024961414180a4005085030030381d0050a2880c220003007000a184414469108480000c2c01e004d91040801c601c04c241e4034001d101d00d150300c01d494050300c102100025541882022280c9090051005d080d5001e5084200402c141480c0c41455205006000120114041e1003a280c000c2d44a626616117091a9041c00b40018100764440c1c20140d24090401000d030360130030b070903a500400107c00c2100120000310003921030102c54214038400c2c415181c0224504d913000008120302541c03901d41d171a484d00401603056072840303a070181510302074091420346c0010f40180704a6030b984603610b0070500054440d01d400b09161086034020b40b00c404560604000380040d8000001409c507100c2c0d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874194469 1250 874193219 874193231
    0x40306061a070308040510090f12080603100c02120c06071101060506040902161a01060e120d050c031c06061716050c0a14030d05071e2a060e10 63
    0x36807071a50307004480b4058103001000300040c0070000b090040c44002d882a05017001300c0039082c206900328820861084506403003d540008056000d28000c0f03220340360003801010250341010040c005007031102d4950080d8801c0e020f11400450b44036000e400c10000700401000d10707160001c00102010802c1505d1000c1d64500340c428406078940d0710442c3c00340d07850b2040150743d0f400c039030035084440c1141c101c0141008102400110a031865403e80c1c074122060b036030f503841d00426540c040082c501c100115034a07803076201400001d0128000c4003e48280701154007034900b001c0d400000c03200201129010310502c5a07444400380b080c680c1104601c00541e104000e400043c0c90304c49030881e140e0403808031032004e001020580305121402086800f005590058a2014820582d5000c2c0da0b00d8201d050b40840392410b040025103028800d40d00d080540d0040791420b00403a006250a030340c210000d15080c02003034884c03802c1003131442d04c410440e40618860100040c480d1440316005050001d143d0602c0503a0741082 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874195719 1250 874194469 874194509
    0x9070506041a090109120c030204050c090a05130e030a170c0711210a060203100914010b03040804030605040510050901060f03080f04080726062202040e0304090204030606 75
    0x10034000b03129018942556550600500140d038103494070b40c09611000b02c4d50940c001000218080d5a084030710980f42404252a40c003220091030144114507078100d240b4883c01c10103480d009101015150b100b8000048190580040c5821544240c442c080418042c0655410100504c25040c0c0c1c4550501072040c20104183e540c14010348400881c81e105007204420300410000700380401200a020000700c42840d5070500d02070300a500100d98814545228104c0000d02d1281802250048000700c41003031b181ea030803d1039100854101420540d0865002d100120001d00c403803184500850040c0c00800400c3c00742940c250a0701c4006220808903418400100038592100c417441c801c0d240c1c03021070b0079140c01003140c007100c031402168098401c520600e400040d100902d0103044071140f00c01f070307803024404a40c901529500c00c0e0a507088040200101309201c0402d69040c1441900e42c801480410840d0350342e030b40c0c18956045030b046845016800a0100200203151044000801e1001c040e20007140c201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874196969 1250 874195719 874195739
    0x60e010216030b1b0a03150f150c0321090b06011107122f180702062205120d060503011401050409031101020703031e1401091a0303120907050604 64
    0x1c0e1100809404414000c52014014004119010181d0056550700c2d2044000001c02804d0030344031442c58125030710008076010699030010b405441d81d151004240b620300d41000c46050802140650030002203540c1c1e402c1a420032410708414001c0b0710b8002c111b014503400d08800700e0b000a017580e07042c00500000e0003542c81d00450340704111545071403c0c01c24080141049600c06e00180c0c41405c20400130110001403010054414a110100b6035110341a040b211b0501c00e0310702000e5070083c2c0507a00ae04006056440300020082e4244817020b00e1144d00c46c1d0a596182c43d100040504114150f8041610002e90750b03a4401e0030b0050004400030301900007140d40d28409600103008042c0a5500e0b000000c09040c000c3d02d0440c03240300800000c56441c800343c2030007801070204c114405000641c0b041011060340c0b45000384000700840d107103180c5240e4a018071100080020700c14005101c40044c0702c20216a0742440504130911407500c03c64410325021042508288164119602c5180c00340018800340c410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874198219 1250 874196969 874197013
    0x10e0c130b030a0e2b02030f120c0909090106050118120b0c0712080103170a0509190b2a0607020d0315030c1214012702040f020c0601060e0102 63
    0x318100240c0d00c1c0ca030307041e201000e0038003036a1201c26481082603012021000c00c20301001c011004240e12690015151708076203d11410340c0c440404803060246a0754120030900c0701350040707d100c11440c9412020b0012480511048400184a9540b038004010a5070080010a0000300345000c8034001420708250000c4c21034840b4014206102d164002800040b130002200c0703646d03811110302c0c8008103810380c0c0202041d109000403144082e01c2d58402c0c502042d074000340c0300b20b10283c0d112542000107030310510801828501e2500c56400090000107000322201c001000c011241e0044003209810313182030b00d55400c10845407520f01e0341c424010040d000e503020620100300042032a011805140c1a42c03400c01e20441da0300040c1c49a00d00070000030394450290000d2500f203204400f100744241c0800050345c02c8031502c0c904500d100100c030f000b100d075542102d1010385599200410018101070f040000070101e070482415519241d214030018440b0301c0c0c00141c0318041040910080030091201c07a60440315240c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874199469 1250 874198219 874198229
    0x190c20030912010b1c06091407031202190305030702120301120303060f06080601110a020a090203070806090402010504151422090506060d0f18030306151403010e091f05010e0c13 78
    0x246070360303010081030781c01c01e00f56250405500028031230998422030311081103120803190859001c0d80e14070707441e00205500e90144805098005608096141681d44d030348000c00e908114043c0b03603440d0b03100503001ca001d540a4400910361881210940c58084d00711109904078501e115010740d0100700300d81d444405140e004000303282410441c030000c036040d8034040e50310100a610840181c07000c1001c17901580514840d0a00e40c0c1c90301c7e85600c0381810f001113140155806030014404200c284101c0e91141400e003c01c0d4921701c0d041d001c030030795100418500d0b003060420311214624050b030701d80150404c181c44005007810010800541c1480310024015205108504000984542142d508003401d60b100342c0b186085941c400c0401713501e40c54010f00502480c05650383c4d03084403084000f0030300e205e44210007400486c005118507690034a9610000c966004043c0c1c10b403845440b101c01d51040c940d2904a00390544206c2c00304855041a100e00310005005101ea103050005003c4041180c4800e071807441100c2c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874200719 1250 874199469 874199509
    0x1005030c031f0306020708090a14030703060519140402010f020601230a231309020d060504020a03051014070806180916031104060e190c20030912010b 66
    0x1000051400c00c40d046943c40500b000e440460701c1c00c00e00028100615250351b007100e402e05000d440399004045010401c0d01c05402d13500c5107005000165a40e030182c6d030821411142c0358090406218003005440e008060303c01d00543c07810602c411540c06c08400210a02e440c00903050560500e03d480d10751101003000345580154103501c00b1001c2e01c829444402030288070665882c00300d0941440240e000d0340c4201180201d4442d042c080c28820b55100d400c80007540127000122103c02c40d02c0c1c3d8005004098030a07030f07008008040c00800a503081180d2031241d4400e000125090500c2285d00b60480c100424100a02c50542c0c10813806544490901c1060190034268004e107032201301089103418603400b0382d02c060081d2a0404010300c00f6111041510310021a01030180c50380720745540341444020307540e0007030140707221300f149440e41465000b40c5608901450220f51b1002034401303204501344c0700360700c015498000180c8141c041c24141040302da0351000400034448030001c000403d02c0e02100540c250b80300d0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874201969 1250 874200719 874200751
    0x304230604030b090a0507060e030a020609031006030b07030b010924030f05090705120304050a03080a1205040b061923010c0602070c0f12080409020c03090a030b061005030c03 77
    0x25035203400980c0d014680052288080303181008440784d03640354003c0c06580c80d21401030b0009072030788a10541c2d020400f019014050b0b07040680e0901001e6041031090f42d03410b0107003e000d03000c010241e204400c01035021b03c4284046080c07070100a400c444629100c00e040250b2403c0510000e9048045085248048041508444a4010218020504604203020b50b0342480e080c08003a001c000f0f204825100c040303a5032400c0e452000702459a038810f51280680000205808001140d14107002e002e4030401d505240319a128100c00010440e0422201113580400d044148540d42c1003409400390003511004500484038200389a6000f4000f00340c0403a190061106d44d0720300264424242d25503125800341083d5121800b87c0740005c2c0404142c09403840805601200040e000101d40198001d1038000b501da61070030b400d0010b120b010350b0107409015400c0c44200f1805400f912048040c3c0b009600840c459001ea00f4035004000300c1c0700130190503004015081c03041c42420049003040f290450500c2d4240004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874203219 1250 874201969 874202039
    0x22b2d0c11150306090a020c030414372907050a0606032603060d110307030b1e0601021603031d062a01090305160f02280b0f0a0c0309150c11030304 65
    0x2038400150340d0303c2c0020b00404400d00c83d03040003070b00a0533980390450b40d0080c4580321224180b50b0712001000780c0349129252840c0903280e810790010050b03031340140c0540344885407a40b14002a42d00a034802c88801407003030068040c03110189082401c240351028000d285044c210700141e1000400d22020b409940340b501039800740d5404200401c015544115071000c1e604d44002d19488101d0300c2e0341c0c58800d405400c000a5aa5840464030705c58142008101684007800c40e00c0807561075091001d66440d00184181c07480003a9107400141c188410748800700074584119400a014441400c2c00b80111681440e00e4000043c0c0c020003900c4e500407484480c900300c11141c1c10000c00350b86001038083e4002d103000e08049401490941c000e05001c81c2d00c240030484a50300c40c0d40011a00c42c8005880d91b1a5041c4100c50b401d80c4940d44889869000c1d26002d0400c1c1d84485d8240580c030861080d440c0803800c1742c26004100502025907250085c070842c082c40c141450030801c40742030543c100c0046850a000c07916a00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874204469 1250 874203219 874203229
    0x5041104110d0c020609100501030209190f0e2a0f060c21030106020d090b0406030209030a02121f05060916022b2d0c11150306090a020c030414 63
    0x614a140b0010900407030140c400d01946584041d0780540860080581026003201103010f034074120303079000d0640100c9903101d443c1c440b90400f44020446149071075001c031410414603400307480c94000c001406400600542820420154840ca81d00c06400344010802000c5d0755a403540008803180c1610100d0b41c0d0400080f8003418144c4900c04200c43c0c50b40c054000031040300340340c003640c140c61042d001c4400d84800d4450603221254988105250182c042106121003446900a8982114017a040f545500c15650000d11450114820350035140d000c90315649411030800c5042d014040c491740304000c9800c00201040a00d80700800b8055030f010480c0010384514400c000904080805030111208002203d054a07c035400030b4051400040b204089003940321040c11002c10f1191101c102c40c95481140c100585000c240104140c1d040c03c500c81800d055622001002402c044104000c0b903540c0ca4014200301200c1009072000d025a0310501c007500e038021001045600f070381c00b0b24448039002c40c50080000e03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874205719 1250 874204469 874204477
    0xf01140d0207081e120414010b09181029060d022808090a17090d0c0608010f0303020a030e270612010b0d021309140a020a05040504110411 61
    0x4580d6100190007414080c03801c0c0508140740603150441205400300001c000c250040f0b9500c1c802d14003205000c0b40002e1156202840b01d140c07071100101c2c0410b00349001030302c40c0c5401c0780c029000c5420b40c081801101e5003030042600d05103031041d0401081c801c160401c060808441c01d41c855540c6481440c02284d5180d030180d0b0b42ca00ca1417032040d941c800c01000e168202c1e0305d80b11008500c84921207a00d44015004032009441191311710024401c51156444914806c3c191a0501000700740c20020000c0c0e07a1a07207110149024011003244504a01d020340050807458140c0c0001e50f030074048082032000941c0072070b403e071100b6014075180036521024400164585234004d030117001256090310000c0000c00c05081c4a118203400c80c1c210060452001400742070765050946107a0161901181500600c0c00b9246007000ca040040c001610130700c15943e4010516010b50b4024440e4030801c0d0341000c501c1c1a00c01000600000d0f05d05009a08050390b80340b006604c900800c034403558880c01044241d0055000791 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874206969 1250 874205719 874205737
    0x6010b1b10020901031401050904020d0c08010f06080c0907020607120b1c02040f05011206050903090405041a06030715031d071203080a09020307120c0e0c030619050f0114 75
    0x150340041045001c11000390f0148036801e0210b4241500240d050300e040c185503040703840141903d80c1680d030701d80c02c10502d03000900e0200d4201c843c400c408544035000348200b0311820b00ba104c0004041d0b00f4020800c5ca06918203000900c9446240e040000240d408a40c1907001002070404000c94548004050042c00806903001e40060784400da0b52607a82a09080409860007500c04220289500c0042c1c01680c0d005d005101c030320071031850307503c0010b0495488660300081d070350103a0f424000d00e40c000400342d41d020743e03040d41c0305005914040c020a1003c0c48003038200c00308a00800c0701038545009806000c1b1510800b03018140e50f031101022004080803081030101704203007640c15650b1108040020620024000d03400200c2c0f44000410400e550b104260409800400034845a8603054003e581001018030403140d15144180025090004a005a01a2992620b195103a183c031505108103003404145802d07001c41d24550810850720b440d04010500c20080c078061402881010064110344116010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874208219 1250 874206969 874206973
    0x1803011a0915150a110a110d0309030f1415040302060f150901060809070b0c03340b011403010c0e0f180a050417070503040504022a010b0901120506010b1b 68
    0x14101d1510303610f001001c0c4041a40c1752800360820101c0c80c0c5a50b030f0340c14000200202000905004070f80b6068003910400e600c00d28200075440c0d166510888450280402112007603121031620040003001d20160320007244008105810345040e840080d03603004041e01c00744554002c4804140441001d080a0510460150203140613581d01c400017000c9650486103490180551500450841002d004032840c210f2120021800c00c0c801403d10842441c590f007085045002c0c2d0b066402180a100303a2806800380078202200c06585001c2c1c0825142c05005845031199142840000400b500400300031200c0c0411f41e50020298520004129001100620b544041503e502000401d40d13881e00924400ca00c205182140c1c01d0712a0901d11560040e044028001d4006120500184c00c2035805000c058107a610320344035191740c5c107a242c0c3c1d10704400011200e07584d4444050308614104000c080e8014010030480610600c42615825151101030040c0c00302c40d0000140c51900395030780c00703110441d0307414030003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874209469 1250 874208219 874208239
    0x302220203090604050705310914010c02120c0a060b060906040801061401020d080c0903010b091501180506121918031e0c060e1507051803011a0915 65
    0xc41c2c03a910541160225410b1207226000b240d1424102400e00312040340071001040382e00003210f1a00e184500800e0912142c0d5609000e2000c520035030440c0a091500d417000140350b03203540b600203041034051212803e00900c10000303011864000101441003c1d0000c20000340708003040001001c51040200c5036034401c501060200340a103041d4456011113214800c14080088900016619054100b41000c0446c140d800020b00c2046144024884214000c000050b10600c2600244e010f590954400442d5955820820429604985455200854142e55400389403501000600a00c00c4070514a18041c0c1c11010614444034254040f410340300b4500241300d401d0120a4080d075002d14100c040e0001076000150350480510313418510811002980e4070070390b6500c40d803109409441ca11030542c841780304601c030000110040c008002d0080e80f032030340d4183e62080d038900c0307a1056a0510800701c2c840e924041d8241100d0a0440c81036020010540e446c804690380e007181540a0b04001c8001600064140303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874210719 1250 874209469 874209481
    0x601020c19230105040302091009021b101104090f020706050109022106010206061215160917060402010e0307090612020109351615090e040c0302220203 67
    0x41c0025090725520440c1080012071250380c40520301d0080c4049020500801045c809420031034006940807a042c2c4010304160f584030943c0049a002e40001d03141016840003410107000c051122494202482000340074001c180030302995188503d204025485a80760640380440c00985c042d24403091300580b040040b50307540c03030032040a035018a40d03554040f44401101400b40c00d014801c1401284103030700a00e02603503010203110388006003403400d520303900c80c03409010701c5038032465075841c405e80f13600e41c0141d00c1c0141a02c01a101c2c22803500071400c0d02e4034450100011220000d44181c1c0250246005100030941c000404c1c10055a074208046aa00306500491840c0000451100843c401c0c0d07034030b255955841140c20b2082165600e41040d01c8042030400000652031241d80380110440400d5403020240180502600d68041c1d020300e0809a05810144045030800b107014004c014000c510502c6103000e07030b2140444001800024480e030a07040304c01c0d4090b04c400a02d0b165a46100c003046580382822 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874211969 1250 874210719 874210759
    0x10b0d0b0a0b12060603040c0b0a05091c03020717030d0218090106031a06161104150e04150b0102060c13181406040b01050d020c1c05070507050603061003050601020c 73
    0x100c4442844000c1c941c003048045c00c00313000b200d10850700458021001c60420f62603203920f6100a07410000c000f03042c408080036603a0015000e40b600f07084a6920482e91032403030042c1c00c2036620b034840c5000010b2041a040d01040101c11140010840d131001039480e043c041c4125230028015004540260180d000850126010b40c81015402824003074000c038044880700f044003610480d8607181a000c0140d166000140c04280d20050030300000344081081c000001c82d06840601644c840000c0030416802e01050092418031050304468591060004401080001c0e40e9400302805000f11030000117a040c2c0e000d8030b000500c9005e050a68031600346051912030310130241002e034000d07a0301f545684003c161140340034801c80c000c881c0181c40e82030a00800c20302010080d08015441c0c02240610f846242c04040c1907041403a4618140d01c0e01c0e5107901071410720503c1d1003059004503020740020018850700b0b50b100d40159014211525020407d2c3c1d031403100403802e18400200311a0481b20204c0b03101c4104100e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874213219 1250 874211969 874211977
    0x210601090b0409030c061805100c03181a090304031205220e010605071e0b041a06060403080a02010e0703030906030e0610030605090f0a1505090a0308010b0d0b0a0b 72
    0x51081c4050300403035040004480c05614010040b403802c03912000003032510341101081c0ca090791010b280d2245e041c2c596508008a0300704003134029a80d4000ca2070440c0d00351041c198000d090800d251144e8040313664500b00c0627011034000d0602c40100001901c00403042007141e029583c0100050740c444d003041005800c81e0020560840350707892440b0b58001c00c104c54400c50701103800e08004102070782d107000c50580d01503005c00b605481d155280f9803015006440703450714010030340c8185540304031481d25041690390340f4407402407541800c0301c2506102141c1e5418050b1400da0350401995a503c00c09017a0aa00410000642c810580102040001407580210803201220b8154905000090060507459240d4030104c41e200354540b42c01a090010580542c0072507480340344202141c002240140e40e40d45008c82d03a9408403080d449841100d42c40c5500c500625070040c03445001403006240ca42d4000e025200140581e21201e035001c01d074040900a541c00aa00341d02019041c2c0c010240c03145008126a80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874214469 1250 874213219 874213229
    0x3031303060b0907050a0206160e091906080304080c19081906060f0b16170409020421050d080703060b120103170309150a0906060e0f07030c0c02010e210601 69
    0x903d1800285480c0c0c0101304031880d03003055a0203040c00d5601c840c4401c2c2c800c2e4050314031204028440c1081809038440c0c000f00ca004003521449815040b5218284800342c441907040002107800600041098100001e90500d455408807400180c00344021030a940a9000d80c1c40312205100e070907442112a03115504401d2141c1c02010b00f448040d448030000b103042800e910681483d850100701075035110a01d5101d0059540c402c8510359106252155800040e03000340e0002440c007076001404004a41440103a218080c25604208030302402070307150b85407a00901c64040d400c0c001204c00050200d840b81d48200e004d0251105402d49a0407250b83c403141c2203000340403c480310405000f4051703041181c4019207205282103401001c004000e5450300c0c0341110080c14032903605880310380744d20005085000d0301d00542001c42c5036280510317009148100d034490180406080c9460302220100c800d5020b008c880d1407980a0030031042e03100d202c0f0003241c401c2081f0704040c4091045d80340701c0c500889010a50504841d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874215719 1250 874214469 874214479
    0x3211b02010b060903120723030c0f060c03060405100503191a090304050d050f0a0609060f090803010915050904030c0b01080d05030103171b030901021b090406090203031303060b 78
    0x8694581400284e11920000780d606034480443c10b504000098000c00c2c00130701c6441501d4084280e0340301f0a0600480d103500d0745250308081014020154100100600380240c60000c0c6010305010940904510001c0d00c114003441c1c403500003400d01001038191000810018007120f41801015030110419030920300201c8050100442508200d01003203079860042042502035480d10340f034102000b010016244003211140078034110208204070500003004624020b20003c07421004620b49041195407200007141d2203490080300102042c016010342c4d055941d00ca10000740101c000215045a03030007940710941c446c044070200810980c0c40281d500c11140702c0d410b03007001c9036202c800c52034448207010380c203030f002440c00e00c01023000c03485410b0200752216019640c0352500e5018100494904501c50342003c0c1503000044054003940d0420400e40d107000e4890120101b0150000003401114010300003411310b03a02d803140320342559424003c8070081d843c0540c9521030265a894898060641984503910034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874216969 1250 874215719 874215731
    0xe0d0507090f1508120a090e0c0d06080d1e032403050c010912030f03061e03050f03041d060103020f1305090f07020a02100908070f1a0f040303211b0201 67
    0x4011503000d0000e131100f0b070014003000c400002441d6104e803ca4143c40c001c00c1040e850006030a41c8100b441f6008480c00000542d1313845500342d880b001d542c40d903409122031740d00c10362160203082d5000701d030b203842d6000914000e4205a00601c082700035085000da15403194951075036030510403003203100c08002c8a00c100c003036a18070f00341c06005440810603881803140c02603404003868002407003410303406a039451303a0400003441078546005400034122003801261410030f00380f0520500608106001c404805040258545420481200754481d0306c028a02c95107501e000c00709107903a000b0340541e5051b0031501c03c19511500d01010424841c061403013280c4c000c1d091140440d00c0945800101403003400b45030000d00124441e5070900c11031244180c07103c000c01c01c10135804514410f00b800f40b14002c144d0300b18494041818001d8103848070a90392403140390301c5810021107013842c0300f40d07082c1c1e401c0f2500f42c00c01300241048801c903024200c00d034a0358404064035082011080c807100703040000c0d950b41154002c00407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874218219 1250 874216969 874216991
    0x181b2704060806010306020c1f021819060311041703040611060c0319110c1e0d08041203060503010212271c1b030206070215070e010e0d0507090f 64
    0x12503040e80601542c50300914018404200346030001c00c2886032650488660b4000c10418032a05c050010900d040c082e00010175040d00c449801d40302c0b0012100f2562511401c0c0c24000c100700114091183c4c03401c0c5901c0d5030903011801003103c1682c1c024002a0006140e9544000d5030a84950160085102044004550405012002940d07900c0f0369140768030240386445001824224a08039098400c07420f85139288640d0b07100505000d00001000310b00100103051403d100d1006c001c10000c0e14028690000d40301c40b0160351710003883e80c1c215030090440b0700a0489210124050b01641d00309581542c00021000e046016408255210341400b845070610810764281c807040f1141007446942c00c3d9445801c0006845e0074054803056620194101071502030819078207859141401c8109a001d60007074010041d5240c1c050004020300c1090300c15070640b80c585640050144d80d16820800d040041c000300f03014a58454004401907142c2000c00c842643c0c0c2c4c0e900701d000240c03207160540c4c81020700742031417030705 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874219469 1250 874218219 874218221
    0x1180e07031410020f040504090212120c07060203070b1614070f0c080a032313090209030d081003061107021905120d0c0b25020a0203010c0e181b2704 66
    0x40d01d541780d0300d1031a142c98070b05170030003010340100d4509a9000103a6452a144004200080044400c100075040c0d15181d000d6021424090540d0100056400c200a40000640c9400c02c49501ca500307881c1009680551a108550340144800809012540094400140700c001c400095040744584402c20185446200850b10f51202d0b6034000e004c60509007000c409220091780c42c4030066107520b0103908120a841a0140c2d01009601c950200c5600180003004e81c18248403001c00c1e82d156081046407410260303402000581e0a22015006913036030003103181c803403c41c5001c030f44140350020000780c4035041c4140301248a807190701c6075070320601d018045a0a0910301080941d03244000351610511280d5903203405040340342c001c1ca01006955284010714490940ca028002618840d03401008a88964030525003109d031415540700906c007000208110640c1c41e052035079034000c04184c2a0081c1c0d01c403602401d480c3e08032032480c82c902e4400850004480008440548410320b00841c03000445d000070f8003800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874220719 1250 874219469 874219477
    0xc03080f0c0f071103370618061b0813060b03030d0c0503100e010501020a0b06060c0a03020607080133020129010801090509120a0c0f060c2601180e0703141002 70
    0x1306c08826444660044030f042c00c4d0854100e90094001140034940c02c48092240b4580106c00c960307065a0b002c20003e403000c400140d138030800300b40c1416841c1d4105008244003600000000420060701e034103400185071014400d8801c40386800f08140324203200c10342c0c06005500125820103002055401c0080d01d812607000c403904981c0b042e000f810000f817054985e041c4809004140d01e801040801c0b03000042c1d0f00420100b27183d1030099000d010541026940107201b41c9060388018440600c24070b0020071001115403c19001112100144d0640042c2000760f015054000c0070a02d40c0c024070444400095010000e1072205009984031906aa01c5001503000c40c0c0c0b040d02c90b1556548615101101c3d03921103802409510308905204066520030390341e110401008000456800340c642142c0c1c070001e90010002d050042c1520071142c504001213681c1404408140f1030308101c4541103880c6409108250303c01a1401a141c058894040e124103008410b8043c003a00309005215421852000716018801c4d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874221969 1250 874220719 874220773
    0x60f2711101d220f11040801140f04020102030906180a0e06030d050304080301120317071e0c200d050109140606060325030f0c0815010c03080f0c0f071103 68
    0x40b084031198004158001c041c18181c44c1021075071042d0200583e81d22901800090080b500085000303903200c003e20018a1014040c102d285260030705010043c1e80100c01d0740d90600c41643c0741600d07131000f500146001d05c08100e070300c0d07000050400c000c0303410024619120f1140c0000d604448900c05809000c031000d1104031005030010b81c040c801070004103071042d24072032003500910300548602a122001002a03105070b510300041900300d061f60351218020300903640b6056560401107501400d9464258001941e00c10300a103801c4404a00701881d13803142a9404004e400100810a0810a18000200030343d0341c0f41701c0302c02c0e114400003d00c6903c1c1c5481124401c80c4140d141c0464001c0d90a1103055029902c4d005000741501d841510700c8455007882810140c1407a9560180d0b00d0514803000007a2040f80000c00d4100a840b80c0c03044046900302e4203550b00600102e41c0488147e0301e00c0c0f080d105500425001000f107a82c00260402800400351a075103407a40108c0545014122407148000812128910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874223219 1250 874221969 874222009
    0x2010c020f121206150d052502030a031512080c01060f032004090b130312200702030c0607080409180308042319060f2711101d 56
    0x10190081e1000b01c140380c02c202c01078240e0007480044e140076003041e0060812203012982da0010802315004903400d000701044143c0d0322a180c2d41c40010002e4a034441e0183d0303007040c1130b142d0301c4a4107400e415000400c014060700494043c21005450024510b80c00640341005541c02c00c00c02152502c400c0d010081221b511001250100540009100c618003a107420603901581d076030b501d0303008941c41c1c0180e140303e14400817400c0520202031074003611903400d410801002602d844400620116094600104414240a060f48850540c800645082040310ba42c541182021410104101c001005001903400301d003418031031034000b607260071400804640e020300001c2c00d030400308020520490310591200103580c0b0300d946511005080e00d14207a01c10f60a09414040d41d02c070482448064400c00ca4100c04404050003142540300c0100e18420b080c0e81c01101c540301010103081045030b000da0417055910301800401349250000e01c06040d034022070342c10145551600ea1100c2c96490005400e050321540c0c0f402c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874224469 1250 874223219 874223227
    0x111c200316021c090e130b191404020102030d090c080708060708010909020108010603020918070504170105040f1106190207051206060d030327080903010615140a14070302010c020f12 80
    0x4078240942c44090400342c000101b541e041c0f00402c50005d0317885e20801c0f08a0341c031484403881c08018411505c0c00101020381e44110007d0100607a804000c83d40b030206400004100c0340070310300700003146240c2a40700300d91a1050f5000040d40c503001080540c03290580361561240ca80c1d070b6200e950103803448101c00900050b00c0c1c00050101e5402540a081c0401001e0410f080e07595207500445d01c130a4003130b03c5480215001007820401408a003401c04103005180c0028400c03030410750341b60446500ca95030f000f0082680102e03080342588030141501c04440d0400006418220b000d200652141d070340c0d000d49405003180b0030286034103220000d0818040c490181040c0c0412041703850840c018000500c2801300102c028508010403040f80140140c03a9000308519a5141040b40416085a8140e4091000e81d401c00ca60100300f61b4002d0041161250b0b021600765840201c1d043c102c1c1c0c0c42d0000529045150340c04250318007030580c154000b1070b904a1036002c8070389210403220150b0fa15046041c1c80c0e500110100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874225719 1250 874224469 874224479
    0x90d031b050307080a0906090b150105040b03060f041410050307150e150904020711040515091602071710050f0c04180b0d0b0a111c200316021c09 64
    0x5240c4c0d5101c078541100003420000d90350754030103903400b0900641e40351210f6010b00900c401c0341c83c20548802002d080c504c0c5060f1074200b40440d103000040c5144c0c030808096007500c0c510f84958004081c0c00d0140456034409290040740103901070210f02516000f4860f540022812941d907501c202c1290f01a52112101014194100103224900f01000c0e8585030050201700e00a8a071400036020040c402c0e101c802091518070700740300440b20003c091040d045e00d510101402c03500c6030310006400c503400c1c604140c0141c6202c1d10076481c10705164045010500d5444210400c114045400e60100b20406818045074458841404c05071701c05465440e4040702c200010002d0807400c442072404482740c01d101140f000d04001c00145c0e801c2c0004421744010181c4010800c0040c030a00c1060200007003452010700b0000b00c3c00303510400a42498021120650324010703090040400340e0300c10715106a50000701da40c1d14240124020b641c40d0386004601510a805031040d0354110240b1a0a2a215540d501b4907030a20708 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874226969 1250 874225719 874225727
    0xa0209130b0117071d0607020a0315111216020a020a180f0216021f090e0c13060e0a0503011107080322030306140913061d06090d031b050307 62
    0x103a0007607042c0410708000000c501c03904651144540165102c08001c180a0180e45080a41e8400020700c00d240030042a801640e80c51070b49001c2d82d41118140c460300d000c555441c070040080301030542a081010414050396404102c0c030030300c00e2841000c030308220706c2a0b050903a40c46201c2800250301c140e2070b190038448800340e8421903500c0420440c000c00c0000041040d5001c0343c2c040200312a0b880c08100c0e0f54030a5003014402c200c0c1440e4008807024031160b86110090a600090142650366569900810303949013030a010368003503251001aa144d03480d601c070000381010140c40441401000c0ca10b00000703c034a418400d83d08882c04400d116407420406982d20303c581d80c130050118150301201004a941a00181061900c142c866200000e400e0309041e003005401c02c12961440c4148100c40800918840071950b10040c1c95010002050076440003140c038036503910b01e64407401c080c41580c041201d038150001d05181d080c42680c508019142d903591451b450541070354010b0300411002c20201e50004c1c85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874228219 1250 874226969 874226981
    0xc0503090a110609061308070e07080105130b191406070b1b0c0a1104060906150309080c03220e04020607030c060b10020d0206070503150910030209041202060a020913 73
    0x100809243c6004407400029040c1d801820a1810320540310300c00344044003080042c900a4401507141c1c20362703498614801401c44c90140605030081c205c40503000c840221035000702e00b21003c010303d8051748044000441440252a01c12032101c80b158902c100c84a09001040b04d49441d0045807120b000da4030010710b030403940d40c0400d08016036002007140a403404070034403c40d00c2c114407540000c4031024a460811050b503c0c1a0803c4044910b018020001010302d1409480070107214280440c101031681000755180c0503822440c2103e000004d03444840c400c0440e108a5142d14903004920140e4032040003100302541205e0094018030300304500b00120780143d9000c1101d0380300b5040851500341130f0010072803081d008590345025a1028025004090301031000c15448803e40c9405400d40c135020a008864031030052113140680d440002090580e0420940840610b402810362581c0c2d007030a00e404140901d02c1c1c50311200500a01020801002050003180c2c6107041c0140b00741a003c3c1e0f8201c20000030300c0c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874229469 1250 874228219 874228253
    0x70905150901180306090503040305101b11070902030108070521150a0e070603090320071203020316031107062606180903030105040c080903040308031b1c0c0503090a 73
    0x101d156000070000d170b01c0b400340c26005071003040910346451440ca0140c0c0b405141120f580303201070618004d503003081508041d410801c40c2c0391510b80082d5115004142c00d0109a4110300c0010303000100102d0748400004840c4d01721a000d590700036001000354200c8140302c00b40d00c89490190803011407060042240002160040305500700000d0754411020030318541011540700d203002c40d840f9040c900078140c00100c103070910b900150010040310030326106180c8500041c00343c5900d04101c00559400e0520070429140c07405000004c0e0411035003c0d080140200007220540f5042d441001c0000c18524451154040d800d03c0c01e561001c1c3c5047c0040300c030018040010304058100c031307103842c0005c4e1003407424910a0142101c000a035030390394104400d0200b82d500301d0140005000f65078003800f10045001040798212600003081c170b602c030740314160200060b03a0b00c80d8800a8504001c1119038455007034580c0a40001101903003003101e0f000c50325040e42d15020895104c01590807022040000c608224101c8034685 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874230719 1250 874229469 874229507
    0x30c090918010603030c03121407030f020405091314120319110a080f0106020a21110d030e0c010e100e010216080c040605181303020c100503070905150901 68
    0x4070000480303508554090f403042d800100783c210458180758000703114144403520b1900a00950a44c6d01d071140032044050704500030560b0b0b882050140d2007496040e50040e200c001d0400300e05040801d031440032511858015a900c441c040030781d8030465000122000e14241d210806070842d07507044800c13175180500da0200030481d51aa90714142e0100400001c1405220340d03150b841c02403e00d00d440005560058012409640c00140b440340442d01d94100329107a01e4045c11184080c3c1d80d508170032100c0c2c042410304030342280f04480940c1019034241e0070407242e60344082e00300c41c6250f150000440321500c1e08d03100160000340030ec4500d071344284120262031740030f076041c0102d91804411246401c0316406591140c00380c4e401080c4039030b0340c3e0700e494080d60006080032100c07907141c801440c0300200d0302800a0121014401c603003440c4001c04d3b00a020b02007503100020010400e0604510340940b07a9441282c0b51000112410b1002c6041d05d003006101d180c8000307a07a50541000300c0400159a00003c1d18420074440d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874231969 1250 874230719 874230751
    0x70512070f210b070809100c0c06110904060605070302160e07030c03060e010f030209010905040803060d14010230010803030a0c0c05032115030d030c0c1a0615030c0909 74
    0x2c168400f84040c0030302e840c4d0744d1310152880e0400e4030505162084940c80c2030031341001d019a00c4640d01a10001c80b4a0f0000350010b100b120840311076540303220340040c29400030708041001800c41c2c0c018014040706030081d02501d0022003c03004030f085855042c004c15084010110204e441140704e98084000480b045c00c0000d180c50b15403a500007445004d0348045042140d491007070085042c05680039004041d241c905001d103060a6803103411500004221a0083d460b01c0065400c3c400d04030400c440420300c04008654a80100c1d2118007140c012a411480c2101e4030100c910106c01c0281d40d490480d0100d8001d50b0454807071a00700d0f40a0000d0384898030030401c10b0000200031803824030080091445003450000084024041c1700c025a000030451508401c1e43c1803c2069030310041400d41c4015014074000400b40451502500e404070031180c040d080b8136016082d080c4ea01c02d0301041d40c0c01034000b161000c0c501424201100318500c0111040c2c50218401d203e9024641406020170b40c10404180f40c0c141e81d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874233219 1250 874231969 874231973
    0x11031006080715030e06010b0a1e030203011a030402100e03012307030b010f0e01081b180102101503020907020a1b0f0b04120f0320070512070f21 64
    0x19100c20341c1003078500c2e8000707103020082070002e0820704049051606080c082c14204983d40d58480b00140b1405080b0200054110394162091854826151002c3d441c0c41c0c134203001145c014000e410902030035652080c1d506e411118440b0180a0b24482c5600030279000d00000613190450b90030000c0301d90142c043d9210b00381e111015101100c24503501c150003005049600d00f41030000c00381c401c400d01045c10b02240303001c451052540300001d0980e44400303007858011a250301b142c041d03010446122000c0c91540208000c2000f01002c1c071403400e01c0f482682125006400e110f0b50340116010250728078164405840104018105000f9065004645005a07000300000d030b1115410b48254400c15a642c451010091145250043c201c00150031141803480c2442d041c0361803080501c0c0c0154001c2c0488c3c85800aa004051244110f11502c003070481031180a01011200c41d80c3d18152400b0302071150b81d140c0c1002542040001e07091080b01e05c5c01c00550b40d298540380400c90058030540082c00c044030070605100c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874234469 1250 874233219 874233221
    0x201030f0612030e100e09161b1208010e100915080610210c0e1005040c18170a0209041b0e01030201110a110f041506020717010506010c110310 63
    0xc107400b035101c640e132440c056400c028807060440b8100040c04000031590016440e010300140c0d2052495034400031580d0421010341c4c000000602c1c6002c0d00b03003030384981c50401c016402c00d02030b10b01003610b6a00850340c070340c0900d00c10305000312400000e00c178107000108440c00132038212580f0a01e0b21401031203140d84540c21542410822070300c4141d654560780040104104e00601ca80c100ca0f00081c0c0c05040941d01e03a140c7c01201118031a410100c400d043c08500141c001c0f495010003814010020820514100f0016000780c05005103600081e09141000441d03140b201910fa840f145800f0242001180f0cc3c0d003000b10343c050241c01540c0495a080e041d0011070300780c004940144c10300e1481a007107580345100040c070f0000c11459440321034000c00030607000540440c0d030780344841c3c60499240005c081040080b900074a030b0711714044214110950001101500030400e08240c0309144450581100c9000045007603940a0318a80e0005601070901b801140c11904600d0004000a040e01c0320344003203c060304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874235719 1250 874234469 874234499
    0x2d12091b0605253804141e070b1e0304050102030612010c0806040515041401090501050102121204060b031c180f140103020f04080a120e0d0201030f06 66
    0x4640b0010b4043d07509202c0141d0801e0a07140111580242c0c040c0c1d541d44440e04c1064041d4401414801e00e000391007069413402100409864040d004082c81c140c00d10b0403204007a60202095406645200e11440b100415440c00720485103000309200e61901034203000356401b688514400e1012400485800c2c0715440c0250701550082001586906022003082400391018030741c40c001c1d0385407c0d00244001d4010100a034404400c88000441c1d0796204401800c7c0c01e07219034900c1d481403410241007512010741483c01c1c1aa0f030381c3c8d00304010300e0381c85600599440004c6a84920446014040c194080340c0d1080c80552241c0b2840001c0369030f0070b03c00080381c94004450070a92202e23540c0203105a00b1640305403181c501354541c07403458070170710700e40318854030b450142d4040c00b08007000000d07014400c3e900030740480d40108a4030000664641e80c6002c1c058981c00141c0c03084800c28000207045400178494041420003100081c072a4903100855401540200080361090160035141d5400040401000c8408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874236969 1250 874235719 874235729
    0x5042f09010e07030e120706050609042301110a02060406060e07050d02131802070210180e040611040602070f0807061e0c06020c03040608090d080105210601062d12091b 74
    0x52501c1f00c400d440d2074030907200c0040241d0701030a40101004080786200e400f00041c804d41e6100b0110306460318a84034050140c1510f60402a18006094181c0e150300060152142d0b00a400c10080710751160004600000c00303455020006509220308003801c0d18030f500505944510003640b1044545d02c501c1803210308010800441ca00358041904800c0d0b0030610308070000b1421614051071482040c680f04a5034001c1800b65041148500c1d002800704011b80e4001035a412410f040c8645440e905c0c4e500a555842a02903800220360b10880000c450400150030b070242c4040d43c0318058103403951a480c0d83c0c040c06400030801080340c4481e90001241984c4000e08201310b058001e0b6656034107000d030203803d400003d4192440d540c0400c1c0c107407a009a003ca00355055481c21100f450480c13080c0a11800006805905201030b80a61000000c5964100da8110030b03034001010b10006014105010480483c0c222030aa000700e200080042d0103415994021541c640c0f0840080b0006001c1c440d250741c511000f9009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874238219 1250 874236969 874237003
    0x109020301140f0310150b03040c08071715040809090a020d0b01140d0c0c080a1d120a0201081026010605030303040c030b0c040905042f09010e07030e 66
    0x500440b040024001100c01c02a9291461080000042030351185980300e80568203580384d0126a444010001000c000d0143e845d80d9601c0c2c0c1800d003010180c1254038420704811380310b00c1d01c0000c0c60720000c1c06000c92440f04040074003240b03000102500b4021400030021500c095003003280b1000ba0342c5000e009405a0900d540050f114100d0301e042e841140c4000301f101d8180042251002084d05038a41260107184204101080b40b9941a078140c501c0c00740000010000000415102d41480e4003819120281d1100c18101080c1d406880c24850420881e40001da82604031241180155000d4107141d900141504944400c1c030342e54000105103070200015100c00281d0080003000104824002c0c4400350030201c000c0c514604040c1c1d100c4114014500c4014084007401001800044202041d20014100351400707000c149001c0c600049101d40007406000c10745d1031707210481c0e15a0354040204408050240202071140d091480048d00240e0080030703881090344134004c000b003080e414001040c03815805c1e08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874239469 1250 874238219 874238221
    0x1b0903020405060f06031b130915141f1101020c0a1407081b21031c051005062a070f0e070c02120a08160b0901020304030c121701090203 60
    0x410041070300c501030b020f940700ba900406202c1d50380d6161402c8075084030003040b1050380c1070a401c1841c449400380c1c8443c841184a030300c00006080b030258000520b5541030001508485480380c050034090740400d14540e801c48180721103001800c0344d2035507407802643c0c0b074101040ca40310f100c0406400d9030b0003030680304442e811108000040002c6031081407040d801c090302500c2c4090425141a60b5840d06904410070f00d10303010010710a030b4803014105602c50841c4001c0f01588518581c07195905c3c0e01c44049104a6a040061480d5101440c81001e02902d81040081c0c1d059113890100010754018801c80301402e907002c21414081841190200c903191a04005869294603011502040820380c0c1d0015240c0441c210070454890360110701600925411540e01d002130703026046032854217007000740047c40c2040c002024601e101c80074240c2c400b070501c104100c142d182da8000e00702d820303800203a0f00100480c4003200d00c00f00060711211005459240c0d03142c100a9958451540101404280e20903690070754004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874240719 1250 874239469 874239473
    0x5090903070c080312070818010f0605030616050a12060b13180501080a0209130606080f3f0f0a03150501022d160b0406020f061b09041b0903 62
    0x68000188140f03030207541404000b500240b8914801060f9408110003c00000c1e0802e41006040310b43c0c2c000c0d2002001762000c020a0304000305001d0158506c644240c00c00245020b20400400904001e150385190800503118401c2d13545081d0345c0000c4205584409020075047c44042c0a00b040598000001310703114074003e1000f8940702045a1944001d043c00010701481d5400a078084007568180c840f14450707594940810268074440c1c0c4001c001e1030500c00c000881100006404001d0801303038040e10000c2285091180240b682e00700070016846040003030070034900c20440183d0900c252a64582c4c80c05900c10b0f15003d10f94407007802c03071020030b0b035030a0003181001c5181d11716000f400c42800142020004070704a40040c01030b01450710300348100103240c19240c04080c4421a0b0f00c01102160030394444e00e411145609070030038004c94006110700744240990320800140140079148041c000c491a40f110b01480c0d60661000415503042601c07541a42003254140e42122090241030383d48074120b80c114 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874241969 1250 874240719 874240733
    0x40f1b080f0102030a060506120105010c0f02090711060a09030215040302010b060d060608240f04020405040608030405040c03110a050c120703170702030306010f0309050705030607050c0d02030a05070f0c0509090307 94
    0xb074114a000f24814030560102740711602c465415140d090800318188041c03403500394480c01c00c030100250003c0058040c410455003080b003084810043c1c03800c0c0c644560b20901d0010482d581003501400591088502c80c82c1a00c0403650640c000340a803001241d8409a0400b15510358070400c070180200360344550800c500da51140d81c0786d0b001580341000c3c000d10070b10014500ca402c1110b100f000e108007400507000b03105540c0c981c11035000704006403044c406c01e07994090340780d100d420500c201c2c2d0095051000d201c80c0eaa10901c2103500000c0003000303044c01c22098000c11182600080c00e0b04401b40325007240c2c0e910030046940549a07013032207aa68104903007540c01401d10300043c00b400c030030195407045c803d00c0516a00401700c0c020b042842d15000902484500300b8519042c1c5a52050742c142c003518041c030600a50040040c10a004994100d4140c8042008126903910604512400003042800315000041003110b00e41c0360503006059542c01d803a16400003a20f4020309540c0c0c410154000149035040101c6c2d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874243219 1250 874241969 874241981
    0x6020601140603060127080703061503050d0c03050c0106240804032114160807140304021519030b01090807210f060c05030f060603040f1b080f0102030a 67
    0x1ca060032410320090840820454040540340ca8148800c4142e0080300621488445c2da46052540352494800d60f60050583c442d083c0e80000c1d00c0c01403c2c15800315032028421030400850781e12100904019034131500807650700b2145801101000401c00610740f010900b40100c1001c0c000c0d0710950f80f50050001c5485006406084407602404101030401012a4001c0208081c061401450f916603140448018005080c40359207004031419110502016803d400500180d5902544600c0c20707540b034801090300d1041c3c042004880c000c2013000083c2c0141414040000b40311400c0d080c00703051241030240280403002c4410304000280c1c2d03030b2180382d1496a12040e003100030a9171034068603159050039800d60022207880c000000e4102095041002c224221590160180d000042086180c8941e2001440d503407054440b00c804144200214005250000890780a15403181890440802c55510306003080c400c5001038a5641800d1000594414284112081040004001a80d80c0b40c0700040c0011241 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874244469 1250 874243219 874243229
    0xf010509070f050f21040308130b190f0c0809070b12060607030207080d03051501170f04050c03101d01060503120903160e04030905040c0504031704031b06020601 71
    0x5500340c1408611600b0440002c407014071850715644d6000760109a0000b4401e0b0000821040014485550441d0300d1000b81409a40b09698881064840242550900c5001e178800307054464010003256850804c4100c6e000c4e650840e0070007090103441d8a0300b020448107000130040100e00e034103040100007070080c00039002038150302804900b4030a040c401604181c0c002801640034100009494080c9402004894020441c00d0300b1500c00c03040504004001d003000303907100140501ea0480002456025108044480e60b44c1402c5040d02d80d103005d9100b510382405001502c480c01003042c5043d0986041c04605800640360b0008255281c52558000306141c00001059440e450810180801d40e0b01080c5883d0096000300311640300c4d000030300082e040080ea1032031442c20303010360f03080003424006d1082128811070107603d07480300003551070042c00140c0340c44030202000158100070510004541d004c4405040426500560400d074803980c4501644c01100c009400785404104200440c40e0f0400005001d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874245719 1250 874244469 874244479
    0xb071704080d0809211e28080708070c021f051314060a080c04090f1d0705090c130b031f0b040f060f0c1b05040c14032d040b0f0105 58
    0x1113001807240c031195000b2600d55481700d03800558580c05a090031548508090a0070b010385d5a080c2e2101c0d40c504400c2909202c00b8240b450f07100300c03089540120103140c454540c030340f2041d0043d0307241c4408851032108103208a0740140c0304e46007401c0010140100c0020080c1d40d45806640d000b00340380c1c00d0380d030034a9503001401c141c000c001031f850300c0e4440c0e1042d500901001c1c14240d02c0781c0c886090b08000f9004541203104000d180500b0303100c0c400d89580044120100c0522088041d40200044079142e03020742c000c2d1500110b01c2c0002c00c101d031840b00300502009aa01050908840c0c4444000c142c4e039105440703c000c031584001c4411035003851644404014510700c40c40d9890076240c0728584c0c211a0440c442e00060000c16103041d0755590142448082590313000b42101010014584000c080790054064240518036054014600c180a07850f50f03440c1122010095096907181c80142100c8650400042d00c250308003402003114459a02c10240624410b80001d00346141803071080c0c59855059120f0b900c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874246969 1250 874245719 874245733
    0x70513110d111b1c030c0e1302040e0f100f08100b3d0905010c0b1e010305030a0813030c0b07180b13060302040806010b071704080d0809 60
    0x2800400c401c5403403280d018000810340d04002c80e4140094043c25103804a26442083c1c0006140000b160601d508449100d64400e0710018a10440440320621442c1000c214a584000203900c0d00d0003c01d45400342003a0301501c2c09454140f0780000070425950421520400c106000d0f60094a4040c0409040d43c8030000c04603a242c02c6040e03594103000070f60016616a04c1160361080d4580d182c8a1f180e40c242e0800d10000001d41d9034000303140d400703404680715032900d1520424040d81d100b0b040394021604143d4404159840315103549031170748409030050801d003c0e50904414604040c8030903600a50043c8003440d11540c080f10003030880b0030003c1c000000900034584001c002a0403000c0401200d402000914041d640c5e9901070b02d0020307900080849806c0d0040c8006404400302004004844088040a00c402c0d42d510b03050703050f800b85005d00c0c040d0b904010018400c3d605068003803c4000d006803965032400740101c041c0550355015409c80c03c0e0340d0300000c0700d049140350806c22154104030004014809 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874248219 1250 874246969 874246991
    0x1401030b0a090209030106091b12150e0903040806040f060501060c0c030807050a05031903150302060a120605060a0c29070c140f0c0108071103090904060f0509070513 73
    0x1d40e1081c020510101d5000c2140042a1001d42c4100c0140108900410510b071040b1026003980b0300801c052000511419980640c3d48028001d03101c80300c008070349004405040a0411081c014001c1c1560002d02c014400010844420800b040c00b45005903807022000789141030040660381c050304030800388111507808200298880d000e00c41241d4001182d5611001e1620704641000041500034086100100b449090f14680914282c4440055142000382c1102002c0d42d80c031550103880003075804801406440416801401c01000304480c1c000c0008113541c0f24400500950003001e449400503481c050240104180f00c1a48040641400f07034104042021070039410803c0001808101003000d0a00388804201d040c40c1c00043c0c04243d10700743e641c610030403000346660300003004183d40007840050109445038090841000c8040680001d50714182c10042400084e81001e00f0454807256140300c1d06c400744c40c00c2c6c41440c0c00b9000c1000a00192854401044805010075035002c48451034000e070000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874249469 1250 874248219 874248229
    0x712080709080105071e12060e1509060607020f15210702010203091b040f11030f0f0c1206011e02011d01180605040f05030a090824130c0b0a08011401030b 68
    0x36070314802c3c02820302403020b208048030b21247c2030842c1000b182c2058030202c0c40108107003529203d503e86035003054070510010108420b4050556042d074000c0401c100d42005030800c00e94807601364001500c6d480300044a15100c0d01c0b980d00183c000700d980c54801480010310880040c1042c0c110800744020b50a5080c0840400d48401d40401807078403400c503000e041011600d554100340c001400e000010000e404442d01c0300d0b0f106500480340621240d03000e000050506002c1c405840c015820398200c1d506040215030f201582020203001641401198020020441080d40c50444401c1283c0d0012410030200300888a040c240d110f50a11a03906103030f00d030a11180d80500450003190015030100e46a2103504080d404003110303800c090160701000074030021440e041a607040031142150115100c04d0104241004044900761804a15500c18404144442007240c18001d10602a81d8040c1e522903844403102c7c12a8031074801400031801000041002124803003840103100e0080c2000c3c005c00b00001c0000d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874250719 1250 874249469 874249487
    0x5030c0906040e180c22092111070b040b040e091c02010209030c1c032304031a070e09010b0a020c060a02011e060806071b0c0b03040b16050d11071208070908010507 72
    0xa0600c87d41d80084030103002034491031a010141000922060a407030f82030082800c00c2d2014038011510400c8000100d0100480c2114100c55018040500303080c104105c00c1c924040c06002c0c41040d00c5a01c03013a003880d2280103210f00b5190419000140c0c0e6444003030505080030900c034005449980b80c000c01c040561002025405265030500e000c01050b0f542240101180d010360f1800c40e103c5401040c08007c102c2581080302c02c042c680201105a51b4070b070281154903e41000b902604414900010007001401c10040c012000080c0151901d586003003001c035065400c08000000181e4607038407000e10480043ca206c100c03038611138805209860500c2c400c0740d584c035006001001000070403c4020b00b401601e511469020f039004a100c3c000d280c0d140500401604151010784171103901c03201040b20000c605103110781038822a2603260030302028504c7d6070010708202d8525201d01008003c000002851400c0704142c0c1d0642d03850728a030380d0410080c02804142250048034007a0724000600c03500d06c0d00041c2d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874251969 1250 874250719 874250779
    0x30212100602062e0611070801050c0706020307050d0f0c090e090a110a0f0803120702190305090d05120a03180f120c050102130503010f060605030c0906040e180c 71
    0xe00f11484148400d80118201200d003104e45a0300750300e0200c1d20b190f10a41e00310742128444104da07075954803210381c14200c0740140c40c10400031000b0404500000e6440e006141c0c80302d41c0d820041d081c00800021003003902c01004038080e04036039540754600901e401203010310203892120142051172411510f051341d503443c82800646065600b108003842681c0e00710301c500141881143c16242103940b5640d05030f4a41080600444801c400400516042d01c0017031075120340181c40d00c0000501d2110346080d2000d900a56105400000030002540800c00c01c10007403184a40016500c0e0b0390310310302d880081c200d03101c54020380b200001d10506200030445256580c00d00a40224082c540030035035040503261007a030200700034070550011441c3d00c1d0b5080441d4003402202d5041d0000c0c04040114900c14040b6195806910701043c000d001240050540c54090b02141001401c0189401e46400419240720b02c100e0380c0c02c1c0d007442c017268035400407001841340030b030081d800f55105c05981903040c0300003111840032100c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874253219 1250 874251969 874251991
    0x8120405090a020c1605580507030c060c0b07050f1201030506061201110d0b031222090203010b0702010e0a170a030315050607080706110a03021210060206 68
    0x80b49041d00c0503811a5100079003441103c9504441440424400c1024801c89204040d400000d802420303600c02a4a0740c1192110030008140309281d003094004030303105c1408040d2a000c100f44804002407603a58210500880c0141032183c80c0d85007181c040e480c5900800208444020000e0029041117000d50b040310711800c105071107020034082c2074124050005001c0d42268600c00000a0050125803540980000e580c44c0c86400080707a442e5003600d1040c0c4c40024490401c0003246035100203030340440c203030b013000500742d5040d0140000a01103503000040b4035500c04000e0203082000b0710142080000801403480190700310741c942000c031707040707401074280c064144908103030084216550050600041d0207140c0b02c4043c1d800e0307001d0302c20395260080c101c110082890034071500b1f82818243d142e0000c0f181c000344000e1818859070307038540d855005501c08682054548143d0250341a0540240a00d08016940141c440910781d00c000d250304400f50052228200091007030003451350110314194420f43c0044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874254469 1250 874253219 874253221
    0x1207170321130f2001030c020712021c08032409010303080703150f061d030d0c330605010e100e03030d0f02090a0602120909041104180b010812040509 66
    0x582034181000144020300c1800015094810000740200924012148044c0d094140c25000015000c40303205103281c0e405a030000e00b0411400181d0030005000a10250900c0941141c07901c1d4212030340c103c0007088407070140102c1001841c00c10001035406840c20b4040e00c0640d0038100b4082941020b0600005e030411100ca00043c40d818069001401404021b200046209076503505030440411940103440002d640c0e00c00405060301c80312402440f049005019000007051014107403240e15030074408442540c0300e00682c140c25004150030384d089800b101c0c2c5841050040117a000304072040343c0c22543c140310030580010000d484800040c1245909800d100e43c1040e03010002a2a40c0100c0700320b02242c5d0f007040800c003c528129006811009020f03209107018940b5900181d880b0001c1100030b0301c5841041c01050810702c1d280c48076540040c0500c0e0900d01981000b0081010744503059034908189079074654034010003c20600d424010040900503011b1129154402c04591249102d240e1044121070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874255719 1250 874254469 874254481
    0x3040b06010c021c20132a08010302090604020307021504020f0607060204030b0a0c0c08071a04050309030616091206020909070c0605090102030c07030309111207170321 74
    0x4156000d040340c006041d20708954443e0400711028800b070500310342150340622101400c0301d60500200e00000014540800c80707012010000092001c0c641a80a03844102e010040300147c0301050842c0c04c4265540c0c201c55811401489850078015003c940624070401c1040301c6030b03a000c1020348010a01c0711170042e0700d4440703000003148031100041603540301c4000241c0c0410025654004d0045a20030741980126554550804044400a08101001c14914503403800010f200340c1c02000d0301d51066204440640003981843c080c44001c450844155100041c540c01301d10342001916407103801403c01030b850036819180107002d40583e12840d00f94054805040e0100101c0b034041d1012400c029008100702d03d402003000305034800100c008c0d152145800085800e0400c103000f241e10a150103200781d840e0007005e1313404400a0507800b005580003802d60800341582d44d94400c0f00b10f8507402101c000c162060030031141d8000f0f11101c0050340c0482c0e01c01c0082201c4150704280c4240700c4100809115026030b114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874256969 1250 874255719 874255727
    0x108060d02030a0213270206030f07030603050607120b0a2403110a0f18081f0905060906060415030f420b04090b0115030e010513121403040b0601 64
    0x11240003580541341c1406821000859803098440c10f4440c03901040000340841d1b4040e1403001c201019400a0007040020401d140c0c00e0301c0203400071030f5403500007403695580e1902d5040200c2620b588002544410364000e0914250140041080303044502540d40751801c110300d80048070401d00388010320b6940d4981030140340a0b500c414400741c940d061141d66504a0300c4000c02110560700b481010889071561203d1154001500100b40c038001001008070343c090003585100b00541d1002440343c6a2910074810000b030040c80218020402c0500600690501c00d007000309648040361038244044203c071040012404401c030001ca0781d030b00200da20a44080850210549400d101041503242000410440c19402a022503070b0700c00703100319020094840701c079040000351605503402130580c24012005200c0b610145815800c254602e0070300040c0203680c04003035401d58100303c8003e8801454086900b0900030100088044030390305190170200400301c006c402d5441d000c084d002030440e41199001624507402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874258219 1250 874256969 874256983
    0x5040c020c1818030a050a0507081b0a15021e0c01140106050903060a0c1d011806050c0f07080d0f0e0604090906150803120c040306140f070203090108060d0203 70
    0x41d01e41e2094000582c0c80503404501926070300f50080c02148120394025001c0241d07901c5144e00d545562034034444120071a035681240c401a9500d5404000310500103903003003003a4251a0500b0f01810302c10740507091603081200350245000100f80104280300f0344000040c02c0f080c944100c054516103d0404000c00e500414600c0c004004115400b400400c6450700940917100071039045044501503030b1510a24010740b1408026400414048440c540c82840700c01c108000c0503c040c5800116140f00d50590113000341298001c00100d40001039004200c0c406005c41d942d600c00200003445894900411180c0d00c000150400041100c1c03103081c9100f051040654040c4040010703c00343c3c4594903000003400400d15520210f859503c1d0001000c00c059010040d0740c00c90364140003a60421280850064480c08018401d503503000b03080001000060b001c0c0300f209030340b000086920303030649000840d41f4141e11015150805542c130901c503c07000b580e40f10b01c0320382d0303c03150907106042104c9140c808a49440c1c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874259469 1250 874258219 874258243
    0x9030406020d0c080c010207030801080c030a0b0105090a0e0303010f06090b03100b0c0a0206030103060b090a0c08010603020d0b092701050c1602060c100209100903231f020901090e06090105040c02 86
    0x100002d4012309040d840503046059030b8003d820341d000310308688101f641e00e1209000041502051000401c83c914240e40b00b01e07840854160041204020782c0c20640c01c1d54000d1b04481d110160124041c4052a4402c8a98002d4840300c442c1525604001009000c40b05151080b2403a410b00014000314001d428007941141030341c0945001d449584925285000e0484a00740302d0080303003200002410049180124180c10245171256082c99081510031006544040031144005446004ca0070680e11130000c00342c420401e40c05070240300b210f5807500050000d5181c00200302a8100018064000f50440071207205940c800031074910080e142c404526107000340b4036100c50601034012011442a42e0341c000b040f41c5074045400318112940640251800102400090a542c0300c0b014240a0b850003520700501000500e4100d0384070505c0d1061320440329815030302c0084841d070041b6840d001d0b560000c05d241e02401d02c122034000540380040100e5940201489100c1c400c5450b00c81d801d40c128000c3c07000c0b1006103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874260719 1250 874259469 874259471
    0x6410c1b1f022107020c090c07030201060614090402090114070c03020411040e0f07091509080105010603090210140f04120c08010b060301140312040801050f09030406020d0c080c01 79
    0x1040344856140e9070103050000d0301c8400d411001c1c000c094180308880d042900c0301034000b210f0018482c40180300d00001d003500194030405210045540d02d20080d284103600e82c0b0b00181d034a1510f460002c0c2556415070295080c06140031116500e80554016100c402506940060b02e4100440040390300807044000351015600010b15502441352000e1b9000c16a8000d450078800390181c024244210f01c6030b0b1042d000601400c90102c1c401c030304d00403e02500000107240c0007103915119103e0604600c2c40b4940440861001c41040042c82402e0003014010201410f0412000041d90080390a0a0115018604001c0781d40850894110b018080d901d1841a15075255141c07500c1b06608000c0e0680c05802f500c0b0034803a02400115804140902d006500000c0c0c0814216403a01c1d44410341d05011b00607440d8580610f405480d8006c11001c05130004000c202c002145a0400c021007042d101c1c4c2c050180200e80d0401c02051024035000154070740e42082d585412034001940f4101a4a10300031a0351031090345d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874261969 1250 874260719 874260757
    0x708030a15050901180e28030207060c03050909100f08070801050c1303081606020d1a010e010915020304081005061809060703050406090f06410c 64
    0x81a80301044080c0c8010740844099103590400003120003d110390103030401d01c0311076042c440c182030300148442e4400b00c003114041d00300311104004040c040f0160301e0038a501c1200300c805155041042800500c4c0b0342c03c02c4075002e48181c034010018070030100324500800226000c0b914144d2905401001440610041c44185881c7c040c0e50340c4071a01441a106a50300f01000700340390b0312095048403005032074803600845807403a680d04e2480c0d64103e0b00711000075034580360820012501c83c2c002401003c161030400034210480394426850076014031040da0400c080d9074920b10960741c000414a003514141d003101750700e0111b180e900702d140d40301f95081780b1041d000742d40b41e000c4640100d030415070240404903040c1c20b002590210400030700e2421201c90350258800b902040c1814042d0b805071360414010807002c1060340494132150322680e00c1003005c0354403a581c1c40c807071401004040703901e50303044d00c808070083c03920715030062078180000104142411700c10000d4003141c070320300664045a006507000a20b40c060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874263219 1250 874261969 874261981
    0x20d050d020607030f1811010c0515160e1305220f060c1b11060f160201020d020f03030f091c0509040606050c0a031d030f0a0204150e0103080d02070803 67
    0xa500069503d8000300341040b80b44201c0c05403034080c0c0160140241c54000d1564a01d071100c0003200d0b1080300c0c5d54140040c141d0120003054080c070001032071403848c1c0400701180c03c1001628100002080a150800c01084c40301c0480e9998080b034560703c13441c030210103c0c260300e9000c403030134102c14001d07100b04000c1e007002c00c080c08001a407075580201c1801800c040140d601000c4090b240b8129074128000b40642008103000050280364001441d84000b800e040d0424040d00c043c42010b41c0305012020078054500703009800c660341001710104000c00f41c80a41801c0301e00340545030b601e010190807101c031400d1210000d80048000c05c03c0c080000b41903100003d40350440180031b00180c0c0f180410074021800d000012503100e01600882d60f03c14091001416660044c4d18121010782010012030f408024420300d0324015036003003001c0c0c0c01e80e41a40002e07244880540c8100000c65002124554040702402420008402c3c0d8046071130450b40c100c1d01145d642d4003882401d1009115001008207a16008001c6c040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874264469 1250 874263219 874263223
    0x414070b1206040b010801060f050309070e04140d030606090b0c101b080c211302040c030c120506060406080c0909071d0d05030d0b0a081203100b0f0412020d050d02 72
    0x10080300e050f10308200442c451001100c40820902440300440c1103598504a03c5118200540c0e1003500c0307405079000f40703444070860401c81d24107803000c0e680032030001c0000e00d50341c3d810b20071011044650f0804104203880d004000d4004503d0341b2541d2a0b0032804551080801c005000e8540030007036040c0104100c48000152419850900805200242141000035040c0107220200c0300381148050303180a41800a01c1c88800c0c01e01d0041819886055802280d401a21207010b50720492580e510040b9007007048180051421300e145407045d000a0038001445440c1c0c48000848080c0d401518290039155140340c1707101c01d14460480400d40000c000c0c020004c0003139205031a200601c0c4030300d014907480e42c10300c010007c0069031034801602c2500304001d4090642203d920985440e64080c18104866517a01440c908201a4502e1610001d0000007006208c003800c24004000e44200501c3d80c0c00e050784882460036074019400380140c081c6451100c2d000b5980c801d541101c0c82a400002c440700c2500d0300000079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874265719 1250 874264469 874264471
    0x90203010b03010f27050718030506071418012f15010504020315040b030c180a0509030c060c030402221b2d03020c12041e08060414070b12 61
    0x408610303060b540410802d0040b401c2220004485e1403003000d4291400341d210090401408003404c0c410648000c040c40c520b5107120100540c0104090304403480c0041016100403401303640841c0c8910100301d903058003902e442003441d19040a181080850070002d100700e800000140b0340c020a41508e504000900200150880d1040100104402240d07a100f041c00b041c1e0005554842c40b40401c41007102503421300d648062001c0100030116031000c00c2070400304040d003090b00c2070303d10f60034080c00c00c101d100205801203503007007004c0500540c640381031a08040d82700d00025001381103120000000c03800b550307565141c0b01c0c0d00d0000050712071180ca440518040040103004100c3d0380104250143e2100745025260002044200c80001140c0c2d401d2111080c0000340c0c02401b580505a007030084000000040014081030046c6402c0c46507035500f09100d0031480d100840b410300340c00c1c1c010041403021000118006411070380c41170301804050707020318603a4102203c9420040188401240000d510a804a581 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874266969 1250 874265719 874265729
    0x2091309020112020928150c0506070503040804092a030b100828090c17060610090e0411090709090f0e120d0b0d14010c031505060a020106090203010b0301 68
    0x20b400b0043c492461038043e4011400c1d01e03580300400040f0244c00c3c407070305001c0c88880e90090142c040c0c02074444003011003141c50100c800000404d0108001c007049002c1184581084060410600b1490550b0740c400d818844d078002d4408050f114544c40d140e480b0307900f03540200070b95040c840404440700da0300002c00414005000920038003e50340614050343c06482d410b80101d0a40340e0440f82d0036054800e0340460029001c43c4900941d03510b131000081650222404054950403800948565035502d41c0c601d4038501504a9105e01d0303108051203003079070300042210212000300c42050126039882c14160703aa10030718601540c01c824013804205036a035210305034005644001c0d0f000c02c000140c1000980442d80c540c0e00202484d40943d01e03103c0c0188001024280c00d660039074010070a80d56120101e024003c0d038400c01c60305080b40007208851f12030f080c080c3c481102383d14074041122001c2002401c041c1811845814003505c0c00242c4d100841e4402c2d0800406040c501d10199501e581d1101c1400c0c60340d100340301c1c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874268219 1250 874266969 874266977
    0x1807050c0123070f09050f0607020a1208091302031005010e010203120708091605151c06031a0604200d0e060c0304050d0f0207061b020d0b070906020c01140c01020913090201 76
    0x4002c410f00502c9444103841b0040d022503410b04995050000300c2c4c1c0054003c3e64070100402d0002000b11410402e1f908091141007860348903210101401301020105010710040d500500400c4003600d1068268000c903202480e090b40c0202c070100060b030452084503000c0d8511407241040090158018089a00a2000d00f00312044440c41000d0715203900f48900400d40e000110040c4101160400e1001c0c2c40c0c0b40c443d000e42204034045042081c82129115401290f0140443d101030240b51644800c0c40c4d030118064405005034400110f010f0707406007405e0303440851600081400c2c482c24613550b200c0324140340504100c5003d401c05407155101e03a081100c00716040e105506a00003e00d2188040c061020616001041114181902900c03e060a03002546911074000460710143e0307070702d55020b07100a009504007a51402c0180c2d004000000e107400180565004480d88901c0340da11000c8044c0c280c2d01d8103042511118111066400b911031644415806400b004006841281644c4030402542c0b00740c82d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874269469 1250 874268219 874268237
    0xd05010608090d0c1202010e07030b1024080c16032a030f03020306010507320f0c0d050a0c1517060603012310120b1807050c012307 58
    0x650b40340c1d1400c1c2041c110703000640e80d2501078009646106812690905800046000d0002c1500546080480c0d40b0983e00c83c1c60200c2400b04958104000b039015042041c0950300c0d049400c262011813051480c8042c040148920004c1d500d16041029035010507000c2c41c90110135082c0b41070091020b0142e03152030800058142c0010400410008002c5d81558192201c855840001000707070025000240788a061020402140380080c41800740c1a0b05409000b09012400e403441c540b40d041d070007000811011582c00b00c6541e424100c40020950710f0b18008868141c01c800704c03407510314104800c0b83c50041c90310039903c0000c41c41c040d2025443c9018003003580e03500f0140d002c150400007040c0c030075181603401050800041c0030815400c10300110402000749181d0142c1c06940108441c44001103070400000c269803010580031001c0c1c00340311550070003160b000c003011040d140f00c2c00c540700000c1c011400b480030004a00809220a40281d200c81c158014100c0d0502501c0a458402420840e004800101d40b40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874270719 1250 874269469 874269481
    0x3060b101b111e1215180a0b010320010f09090f0f0203010f03050d021b090a20030610080108030406032705010f39110f0109021206150f0409080d05010608 68
    0x170300e4108000000c030907007070755106d02002c0c1d40004051080b010060140c25910782c04190b06186150013580f00729640310803c459124290204207030708042604002c0f81c507200040c502d91006148080d203800d0039000910928107a202001817000000c4074055900110001481051410006044034020800d4500c1c400c00481e04a882c2c445502a80003c4100038114041d1401e1901e80d15501901c0e80038001080c2070142851145035403d10400415284000204265820049030540c0100411308041d02c555061820301500c81c042d07400349504055451056499800c03079101c8011102500081500b800030071400c180f40a45500315010500324140b403503501c14542c11950913034000014001004001c03c00303407580e2400481210810b42000700c85242d0543c104418002d4016603900c4100001707180c007a510500a0005082d0b402203c0d54005404006102c0c00c1000718010280c02265084420048000002c00528041e035015103461700216541582e00c0d1032380c0c02641039405540311210556224 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874271969 1250 874270719 874270723
    0xf060506070f06050703140f04020112090305030a180c230a0e04021003020d0c050309061b043b04050106080304140d23060103060b101b111e12 63
    0x741002001c21541c01641c5020071502e502040e04644507240210b1103072248005010594801d8580c281040c80c80414001150f8103c1680c51010300c80384818005200181c1b00500b85010050000b02202d450f564042c400400031010f00301816441078010b02d405840c5c00c10101110b17440701d07030400c01d0f6410141c01c1c025480d180021000302c400c11700d00c1644913911a400d00c00400140c11004052640078400342c0211a418083c4406070000d954889890f40742281c1c14901d4030383c2c064003078601205c0081030000320b5058a001c8406890307200c5a043d82c503040540000c0e005000703c0c0b05a0400d824600c2c1d10308041d03000c0c030340d90502980c0070380e0082c09981d40b039411507a2644143d11403c010601c6c0010030b40040c0c00e201d102c3c01070450250081c401c040c0b002104141107100002080003094100000502c10442035114210442c7e0068420140c1c80d00c000a029140401404a00158108800006080101005000c14048406481c0c840b01c001d4489203000c800e00d20011080c842c0d000d03010501c1c120a00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874273219 1250 874271969 874271977
    0x215090c0d0303180503040909200109030233031e09071403010e06070206040212010b010e041a03011a0f04090b01150c1415070807170c07060e010f060506 68
    0x801071000d00090340341d81e420750080c60031300c0d031360410744540001d000013003042440503000910203090042448842c501d0700c48290305400c00d0f07010440b101400d41201c1640d2124500782960b82c107680c104c01a20230b544040240320340070b5202c0f032031014884e0b0741c41450445a002941c002c0c210102c584000c000f001102c100b031180c0c2120149640e80c4111401c0083c1d801041c1c20241195001e0000140b004c80403201c14148901191a41c002da40130005006c02c504050504904d100d280380300810143d108800020048000386078190300c16030701c0b401402803c183d48856070010000040013084408425621200390924140d80c1070f20546c0380001e00758072402e090280e12441e07980661414150384c286000c1030f202d031420001c0d140401254a48000c0020400940d890180030500300500b2220b50030294051410002004901007000010a000005801c1300c0d96401500c9002d010300030340d07921042019054002d10324090201400c2c18460b801e20343c810b5009485000c802c2c00c060210136100c4c1c00740070341441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874274469 1250 874273219 874273243
    0xc140705010b10052d090424050a080a0222180308090111090d0503120709080709021206120f030a21181202011104140f04050c0a110a0f03021509 64
    0x124024403842c45440170f000040103541c0d244280b5003405d40542c0841c084070145480501500301c00340042a40d5040c0e600d0300801840100d403014511414201000d850b42d5401c000213009410100c0e80386d0000311201c50303103c129100103004100c1d0b401c600740c02c4204141d03602d030141e0100380c8a2000c1800503030103024000c120340e00354034450716003240d1005100d4503050300c09040d101800140f1148000c40c94142a10340256070950700d006116040104241c100000da900ca10340c2c0e24410884c0809248076072032241d6000d0002c40d02071010b580c043c10014180700002202e41c49501001035000031480d000801e110400c08141c4140880d11111182441182c0c21420100e1a60743c60070002400600c0354401400c0d03500c600c0c4004203c4030f40000100103540c0103a000a8581c080c204c65075591800d019460060246003290148094100f01c1483c0609206106c0a20108945010700f2603c682041007000c090a40c8507038a91018841d60900a440b0445410011114038071030b00811130501d400503044d4584a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874275719 1250 874274469 874274497
    0x9070306050d0b04020a0306020307080712090c0303052a0d0917030f07060f020304060603052a0d030311031006081e0721141603140103060c140705010b1005 69
    0x541182c48441503c000100f00702e038420344880d008800242507002860080c021501c03845103030b0600890280450880301d1603a404a860000e40b400420702070313200310701100c2c9c25040981e074410700a00684003094200410308103c5480c0311060342a0040041c0620906c0f05990322882d076180c40d61521404482c0110001c003031a4418084a0100280d4000810a0764422040003814032090740e080700a80c2c0040f541512030550351001003040c00420722003042c08a072124040b07803950390074501c82d66581d80f60307001c468002d680010100341054080d520400901e943d000c00140c9a161030403040d1080b503440d010b180d001507400004500d00070007002002e070101e00300510912140da0b4407141203c828000144043d07000c0d03007c3d400300290800911801c1c1240560220450151620b05d25920a081c002c2d028081014907040b0483c240d4941c0300079841c1546c1e401100419110100ca50403200140540070841085100080e0701080200540c40351800b1101601d00e40403034211800162041c0c0682c92500c2e10380 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874276969 1250 874275719 874275739
    0x1b180c0a050a020a12020a030914031b0307030503030f060a05090c12060414070210050112050a0f020126090111030712052a120c0a140f090d0609020907030605 70
    0x80c80c09403000d0141841544125540e404254030385454036142503243d1005078010420071024150701c81841d50281c00115900c00c5004560341c080395581580791a42a00c000c01c4032280951950140300410080d43c02c030301225144d007404641a41c0444041d40d600d485000c00301c01c00a000d00f0328440c210700c940c0004010340e0400c6050340ca146007100c001400326038001c3da6100d40b03505004165100d6801510b080e40207020f081c030340c15945000c4445c103030820080074200071003080c00a031000038111003042e1710107402d62650350148010b0340e228115103103003504e000250b202c030b00d120302c0c6a40241c0c0c450300701840203001001c010707007180410344401e40d1100d0010300441940140e220b91500b10325040f007290b00080c40d00c00180c00e0b4940d5281c01050712007038170210005181c205107002e0900c55400031606180c26150065040f0040c00c0103000e00c00361400300c00d01040000d4881010426207a010300d0107800c4071428203075464680024582e150049201c0e030740d03803408949420b100303100e01c2c815220090000b03070039 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874278219 1250 874276969 874276987
    0x9020a0e040f05091f021c09060b0f0f04021e03043507081b0f0c09010f0605031b070c0f081524040e0109051c050c0c01050a0201020c1b180c 62
    0xd11703c2c3d060038408826000c0200082c90200761150405860802c000000d0441061500d94151042003840d64894102854071900544d5030484861651404450040c1d682c4030906010b64002c5940d0720241b02240080100003d200b0f180401c02c1469007040080d8000030602d1941d036407800c50130f6616101000c0c05014100006096100030609640e03030804201424440207030f943d01d0007031007074504081a048480d8203451810074642d210301400384010301c00051402c00e132008241c1c0c04000c00c400c2c1000d101880455071a8060b600300c40526030001c10802d00c042d00c801180c80f600103c1e1090601c1445841841f41c180e960001409000e282c1d1003051301c1c81c0141d480c0b60701104000498001340d000756140344d01902001c09100d50f16100d44560003a01c50b2025200c403030034a0761442d1480701c0030702c40c08119007034030044089a2103140b80f200742011601c1d4144c100040f4024003500400c10014400e160308038407103100441c40011002f008a0782036200440741e0076104012001501c508640d00001d224000d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874279469 1250 874278219 874278253
    0x14130606051b030c0a030f17010b04082404030305060d08040303020a1e0201020a020103021c02130f120c0608280f18020d02060a17011419032a09020a0e040f0509 71
    0x1e03140b402ca2030060b000403114210301444002c00c1c0d01424ac83d40f00014108819201400989694401a1100350720554401c080218031200240024200355681e40018050360b10307070150514064010b00156191601ca01d8041d6071f900f01d055064034040f02003e400f2501141c0c02711211029a810382c0035002041403a4019070281d000722241c0d010100043c2180d800800305403000d0110150824400510b862414256404d4802c05802154207102451044004140c00354201821204603190a03810355950060030140c044010b10015001154030082628201c4160001c03010003421400070803211a0758000700851924901000f0741207606401d6510243c901103001c3c100c0c903015130400071400580010340c0c80226200340c111000f104600c07141408541803038031045038122041d210580b1214216250403402c0900750360400d601c410f00e070340640d600078035002c02800281420743c015034840422440c00340100016408040c000d52405800d280404c01314001c40340210808005002404400080c00d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 874280575 1106 874279469 874279487
    0x301020406050412020301060e040302010e012a05030603010e0111030106080f1014030c03070f0e06030303040b06150c0a030c210914130606051b030c0a03 68
    0x1c0302042d0800d00320390540304421800c0d40b155503a840040d0140070903070400313111404103109000c01c0503015080a24600340a4009200d42c101c0018040403680240d401c111000c0940c8100c0c07568240950020f6411101c06000419100d41c014880d50135102c0c90488000d031000008010880349034848065500507900106041290418000310042c901030f0f40140014440d1414004482c1e03542003219071252400079041d1000760360b613061180f583c100148503100b841a003040c006480e130300c3d0100481b8070070b030344c8441c0f05003850703d4141c14040300710200015840c00445c10000e00821010410543e00401d00c00d80e00c41480340c01501d8510407920800202c80f00d6400620310503407520b40c00114a0080e0b030700d42044c4542841d0392200042c054580004200c411601c0d03c071001c240154040018546002021041c3c1d1380080000c0b026940e074403d211600e561a00401658800603103d04120 = true := by decide +kernel

theorem cover : BRFrame.Cov 874100719 874280575 := by
  have h0 := BRFrame.cov_init 874100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 874100719 ≤ n) (h2 : n < 874280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
