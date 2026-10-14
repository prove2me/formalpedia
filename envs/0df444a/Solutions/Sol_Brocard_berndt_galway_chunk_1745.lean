-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1745
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:31:33.224974+00:00
-- url     : https://prove2.me/submissions/5b0007a9-a881-4dff-8db7-0186e436718a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 313669064 ≤ n < 313848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 313670314 1250 313669064 313669079
    0x170403050417030a0e1203070614010513020c060c030417040b0a09050d030e040e07051309060e070e190f0e0a020108070c0f08030606040b070515071b0b0a15 69
    0x41c00075240c0a41d1030784141ca41d2410340d075950780304005021010a600c040d00f404c0c54034107414144181c00c1440140d074074101190740c5840844104801c0d031007100b40e000005200600b400c43d00d9103000d217443c841c01c510705480035a25035643e020007444540201400000202007004454082d0b4045488008180d1221b0700c1c1c181d500351541107059a94002944018006054902400d0303045141b500364407184041d0910100707000c007510b44110300c1103070f0b0f01c40e40740d00150b40d86a1110f558074a20b04020002003000c0c1d40c1c90709106441d55900c00349076a502c0700c43c050041d240c800c0c1d00c040d0440042c0f0001d800003100c03101c0c00c0c0054030403014007541030f601e0110160170035180031031605040c0f4401d136507640b015a00c0d100c0645030228040405410001700448050005050304025908001d0041c2070500706aa40e5210403080d50102a0450f825000851070640c00030042c00034640000160805010204c00500030102000c1030340e4018086004240c082400310700c0300c3c1c0c8130104513207011803140c0e18140c0300d0030b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 313671564 1250 313670314 313670317
    0x307030308070e0402070f0b0907050d03050702040608031314030a06091109180a021315120c060503150103020a0e0910170604030e01080405070e0708070f020d0504051017040305 78
    0x321480400d4243c40c900e14145060f20807120b03250b40c0890749030010b800d540c691072400310006011180c00e100d0682c0c085100d039140c0c01e001c11074078442c0c2d0321160707500a14070600066507040e40c0b00c0c0c607150303005102001804280c49210003d4404c4c40040030304c89c10312200081d144c01c500000140c00686483c9020092000c0160305003e1003005a5040b0110785902c088244520407502c00f0b21410381003001c450005282003042e16650034a403c2c404500030700345042e010121100b5030f00c0142c15070880054203042010109808004150900f0894150f10304405401542d984a42c081c50415900055811082d80944866800034901070150701c0607290214984000c22014025165054a4120b44c44240394000480310f1046905554070307100c98006200540d5507250140045500303004044002c510102003072045071196445a544c03040717600f884d0401414070040c1c540c030a0115002130b40d4401595820804031401c40d0401c0c1d034030340c1c581942c900301250340e0000d48000c403141110710340c10310060642c00300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 313672814 1250 313671564 313671571
    0x1b080412050c18070c050c060c01050601120b01050406050c19080405030c030a02060f070317070305040b090604020102060705220e0103020910140616140a050610060e060304050703020307030308 85
    0x70201c4408a1040c0104004490300b02c40b012241d20303829001a101501c00c1c0124010248a54111072040d0500c20000304182c018000212650399190100701d815a40618035640652242104119055105000234143d00c6603003d12418408001410a44183c0030849000c1509140c0c41c50700020fa03841c40d045446900a200e0207109104181c01891645008106542803d44c0107040134a8401e4051700b40040390404079060b810b00540e424200c00761a041103506228030740540d00081c140c42c15183c40e41c011007000d002070085034400c004110060342c00285054020b9a80c0c2461520b910f00c0c410491f00d24030288844820340d20240c4000200c0c901035810740c9050320b200300c030140d4032903a17007800b00120345000d40b28803030810111032845030080c100740c0b00904440310001d40c0c600b5950305c40d8071140200d0300030b51511101035105151450a02c001445225041341004400801003842c16030700034021002040c1c003030301c244000400702d030800c882006204002c550141c1a120825560308010304003aa048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 313674064 1250 313672814 313672823
    0x30c02030f0705061c200409150302130e07080312100819060c020a020909030304021810051c05060c1803121204022206091112071b080412 61
    0x29010700c00ea41c0008035040054810240a150034500b0103500700d000c0010304034030494901d030b84100401c3d00d001074035a8420340440c000c10403a41c0782c5c0b80810020460780720f40c0403034800c004500000d00040e520040300040c03d645403034000c40e0907000082c205080ca560360f401507180c1d2100140100350900c24100e21031144d8810800300700a642d6664a0b00d0301c1e901c0350030302e0742d80e00028001d03110005400703640300700d01e94a6117104a45040234940c1c08901541400d0741c41c204240e1003c400c10003185040110b501c13003402c003079442c407049041621702d65017030b10240d004851103040707070350070869201c880714001c4490240c1001c100c5009080040305d130700b66070b8014000410704240070342060300741b418001180074503850008100d5241c0444135003200c41d00100075208a0740300e00d0481040007c48441e545440030444000c01c00103c151508008074201c0d94002005081c1f44d406101d140d01106210140036070002c01410f1015001d0f04a4000340c024209141004084917030101e0041803400841e00d40110080c800d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 313675314 1250 313674064 313674073
    0x10f060509040c15020c0907120c03060b1606090206070c03020102070b040e01060e010c05010f020a090e190207050a08130f0e0405060c1803070e0a110408030405061c09030c0203 78
    0x100d9050199620044901501080044004011400d070201c14150000e800707105841065012a00003420600d040d80c00c6000229840840c0c11080c0080c413a00c09055183c0c01c00704001860f1203803160080c000c0603181e115256003668900c00b442281e400506106500808403542c1e24003a24051000304241d0000744d00500c1074610100b0b111038403104650a42d00b560b60340b200c3d540e1030b21304c0803102d0b030410507416410402910346540015200740958090002c00c1c41000d61039001844000305100c040394000b0610144800510500710012881d215004e1100078000d83da5040c00c2c2021454884032000050030610300290030f0044d01c40d0f0000b5401501c101403030051402f541e231040610130b92000c0d03602500c0c2c1d400540c007185805191200800c0300c111580c00079080c1e000b0280000f41001e410764020304d40c41044004001c5603100c24450301c0c2c52407031400d884604080c18045440d64034026070003920b0140074002104922841041020b40048050b200140803d9032180f42c003c042d4410848100d00a204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 313676564 1250 313675314 313675319
    0x60406050f1e0c090103061e06080606130b0f09190302011b0206090405040c0f0b120a09080a050732150610080408070c120312020403030c020f12030a02010f06 70
    0x48081454070b8040298508a030b15401c95080d075651044d81282e050543e200d9000810308003070700d041c8a0b0548010f07402007009180c000043c0951200a03c51403140328104244084800440301400a55a01803681d80d119560000e0000c0d461152081c43c9600c40c0e00e0f0260321005041e00340f200800c0c7d80c03003a40d40401e0000c00302d0780881004560040290b104a0074000201141401c3d440564024050940780803071aa5500300f01c071090407a500720541c060400505038007001105c40f86a90041c507103d904116000c242c2d1a82403150046500004c00c102002804106101020304030000900700900c62741408540e507003400e404941070041140c5940102050400d200e6401c5020074420100a440c0e0500215403440480d010500204101c3d1499000d02c807840216811071006009091104880200928142170250100c508200840c03402d81c010442800003982c001701440280d981562140300c1030071004009a0090080103000c000c511000c1202e0201a030305400c00c004600d4215401c100554 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 313677814 1250 313676564 313676581
    0x20070f090c08130f030e2101061422060b0f07020f041a040221040c0518071704080c010e1b030304150c0323041a0a02071511060406050f 60
    0x3000c403940310f04004a110450003044858a001c600b0301c0c440d242400140211500103608080204070828946c0145500455075039000d00c1858040c002c0c0101000b6200c0352000005c04060840728900c040800c40668a0151036464010202900640e0203040e103e030000304a190b42c0e501b00002c140e2040060008468950402d4801c00a60013114aa0020041c041e401404082d602c4003117203a4000701d908440f010191210800940501d00c2082d840640d41d02d04020001045ca44451841c04900c010091020307aa0300039801c8000344102040351710143e82c07a424580310900070303400c0e8003206508040d0300b0705200c0d030045541040d005003400d5000c00f020307005080c15901d0140c1c2c064022540c8000a918502900132141d41d14001e200c0c1c54040344c11564105224114029003440d80b841500c085402e01c5440e020300508500354250945080c240410f244009503110070380d07c9a48160203065114060b050310811040441c44c84082c215074540c1804d02d07150006100441e0703c0c01e0900301081c041016034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 313679064 1250 313677814 313677827
    0xa09050603071710050a0b030402010e150d0b061b010b090a330b0c0601060f0302120417041d01080d030b010518040204031401050406150b070320070f090c 68
    0x2e01c0d0035070301d9051100d1101030058810030b01414207402141c5000000170155a4041814054584000526264140391002501c84064941014070400e140000132409a8410042d03403450301d640c810104000700b2040c0400c0d802d2240e81090310034040640d21044010105401103400c144099070160f80c5561064800801c030389088030f40408010101008032600e003406144070001c0e501c81c00601038a507a030340541c03810301d5218489055007908550010880180c0100c51a4203103240c6082c15443d04018030400b007414100104000d003840e00340403150360162003941c20b440281003142e9800340031002000081207065400d01c10034801d4869103818080c11480b90260105540e01a1100340c20000c40e0f40c3e0707551200b140d0b2405d50b5001982400000007082c2c40702e0b60b9084030b014503030002500b401c0500300b034015030b0701c1c007004401d82007080902007100d480b0800484451540524010386044101610035803d5141403040c007074203115510000c11000d00001c04002125110700d0100f20411041c001695207 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 313680314 1250 313679064 313679071
    0x90b03060d060b0402091207030605100b0406030c200a05070f0608010b0304061404030c020f0904080a0f050d05010f17010c120e0102090306100f081b0f0d0f05030a09050603 76
    0x1d41501e0680740000c5043d0004403a49074000c4c0050700b04021140405d0018000170020b948681c0600d00070401d020140c41000e40100111407100d80d0a4240049440c0a1013144520300416503a07035005000140f01700041140c0445a01c000184440841d4605031b82d841848810744580c040c00038006201c110099802d01210156150506281c1c41c041c01740300c03550001002a2120b548905c1ea60a010031124205032140c1e2080e100c14980060f64010b1000701280f03044228002d404100c1400007040343e440c141c0d60084100e1038009006945000220751500403060140c88481c01d041c00840d1003081090001c003503450540000c000d900090503403070300340d56820307803030380c0120721040046ca01d0051a83c1101920601c41c1002500d800380345070200e4500b030421142803034480304a40307044c0022084404108002c11a103801008142c4450300c0e00182c0b0118040010f100b400b410311101220f0310307400c40030b910041c0c10000e5500200c0300e80c240217440c7d500041c20394002592400307003c286031900c00d069900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 313681564 1250 313680314 313680319
    0x81f181d0a03030506030a060906140703021809100b07120f02031206060714100c140403110d0f0209040f0c0f0608070309140f0307150203061e040605041803090b0306 73
    0x1c8901690b1010340c018540034101035054000d07064881d003c07440600401c4a201d11886e00040c003402d0100840380e4048018007030708101401004134502a03592210f080e501503a0480303400809868200580d1500a0550310106881102140b00801d100248804e80e042089a488120700c101d1124412a02d92180c5038042400d164003601140d038508004000e0981c00c0c1c400d281c800c00b20100700880300d1400c880d03145010320803500c903e00d0403000d0303501c0700d1644150300301c2007001402c0a0456803010003c001c002095406860302e00040014444400074070814a50007603d4400a414107042400010208100580309071200c8900095014403080b031410071100140d844140703640390500c0450203050030420a4800c03422540312104006c2003400b802380169290001103955402e0703440d001000d402041c0350314401910500c1000007903207034190b11035004499110382c50148440080054018a41d941040703800c54071f0000c2d200000c6441110715860240030b170312071a600c05da4600814046200840e80d054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 313682814 1250 313681564 313681573
    0x10911070c0b03090a0602030906150a0b0f07020f0a0b030703150308180a03050601080309040e1209060f04030606090b040b150f21040303060e0112020a06081f181d 72
    0x102c5204030280d03811102c0103059600c1c40a81d0748418059070003c1d942d5545030f4210800340f000c07101c8901d085010304002561204800c41c500030003036610740901103054007940c0340014807000319a910550030b00e00140080c007201280340c4504c0360702099003040740c0d4200440d02d004dc008440112050108040700d5000c400c01e031410702907a030504c400c52403880f00c003500041c1101001c800130b0f0b01409400d01808000006503240e0040804000640300c034a48041c6403600b100c0c101c0044441c0e044100c0b90460010740710a50b80b41060355860116209960014098601e4424042200190354000384c0c0315035000c842c00c0c043d0359500303030802081d003801800c400040c0c2e00401201c0020791030a006000200d11000402d030070444510860003034510100c40c100c002030f5607440144804d400e042c4d41c4a003d44840600108074585950101d007544d1801c1c0203004c1400518000582080d201c003102d0440c0c06a107484048000b42d1b04d0170b1600c000882408040030300c0e400c001403006164908051040180c84510040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 313684064 1250 313682814 313682819
    0x3060103030c030c06050f191401060e01120c0e280302010809070e0405010b24040e04082710051201090e01021e03040209010e01060c15180308010911070c 68
    0xe0b912400580d004030203028110f0840e0b0045810713881214882c54140300200a145082c40130491821100694101e10342c3c9002c080940b01c01812040320305441c86410b003a8095808500103982a80140500d041141d0a10300c50f04180b035440748401c1480b10060711464501d10403004110613440c5171211a1031408000c1808001540c071400c0d21540010003403090b00c0001d500c1d84d0206507614011641a502d0760346071210040103007840300302d9800d540c00303140c0059010361811880310030a20680c801e48014007004000b06050001020031111003100c03006461021210600b4003004500c17144251910a550240c1000c0c21680039a00716420031507580b0080e000d586c2820500c00050600a40c0d813a0150b50030322510010071a01900b1506a6a05030040e64491402d8810048114416000030a140600800412a998002188540f840d500401c04050501f94804e01070081400d6038003603034010381104503982415004005076041e500c180790300707011701d200003c880032207841800401005011005000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 313685314 1250 313684064 313684067
    0x50a0b0a0e040608190c1203021c12090b0f090d020a0305070c0b040308030a050601030603020d0b130506070c0c050a0305071a12190506090609062418130204050306010303 75
    0x21001260700c000e00010300c90351201e1a41c1d1070b0511101d014500a401c0c4041442803000755804100282440b0070310f03105c00340f141d82d4001e44507080d0a0100011580c54081d41c0c40c26406000070007941c00c0642000c010081c441e0810f000f00d10f40035920070214515210105040301d2011454171803040c0c00750000c00707903148169003c0b14a17038064001500d14214140c000703d0b00c00321400c020001180500691510380c00d0000b5860101e8101070b24084c18145041030401c01a180c40424840194021201d10703c0d030b6603078104c1440c000c410400000d045000391010800c0c2903821003644441b007401a0341084125468805000302450b09000140855002c014200411101c9030241c0c0e00e4491124001804e102403014081ca20110945138641440c0144d56010300b01d100d036100341503101004842026260070840c2c0490881c25000c0d01d414001c08980180c0500501c440a04200c82c402101c1500d60f40c200c2400c94030103410151810a1042d111001c01c0191a5000c7c02036900350b60004028060076441e6980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 313686564 1250 313685314 313685327
    0x105090102030d02030c040510021501050d060e0109060509010f060b070b07120606031409030a08010b0c03041206140c03010602030322021c150608150a110307020a020a050a0b0a 78
    0x400c0c11440100410100002d50740050b40c02490500b03441781d151400d01e81000030800305401e1440448d4030280050320b01d1880c400c10b0074110750b410b5a4060010109050850241c55806001581582492484010440c031584010b02c04c4100000070811203c20480c40b400341d60355841074406032181440120040f952203480c0c0d030340000a504140c0358003031003905020f00366a20703a072000340403a1b80c801c22201440314003c0050303441903c54020b9844c0507440c20000e01031490600030b5024824000c50300e0111003400b0012079028110480300390341300340628580107020f800d08034210f031000c2841e0004510f40b984102c050380d040c1c40994000c2c50550796180b032505100b004240510381c09a0003203004501584403000b2280d030990000d040c90480345100d062200c0300e21030942401c03192616100e0100250b80780881d070035000b0074800c100803545444134044070016041414170004082000030278003134100c0d00010003605d9244250391345481070341c0ea03001b0001da036040c512641d015510104507881b405c521079030303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 313687814 1250 313686564 313686577
    0xf160c050d0b16050c061312030209100e03070902160c14011728090b0c0c0a03030e101b030509010c050a08090f070f1a07020d080304151404061a0f0105 67
    0x84d00c503040000c142106450840c007611010064520403240e2814052003140c0014120b007281825458941d4001c0481e03440a0a248a0303030030040790b1003070030070a9034042c80408018420315238250345595001e0100b0010100200040314514642400080c4483c03004032908a0150161130300819034131071009280d403440d0020205121000c0f04030500038000e0269600c5841c24100c0000000e0b000128034002c905403c01500c0e8130207511090101441e403100c0010700c0140c65500d45804140009030f50111031030142504d4480c4181814035082c0c1801c0c0300c100b190740365481000c3d5018002e589442c5841e81c03c807408001003400080341009000b1000d8043c0603050741050754401145c22078000c0c185511305000d11a0002e126000904200b040000310980c2d05003500392070303411070901e003486a85c00280d038010703171020003401201c000c0b0000301800700e8100391388170681c00c842003803050f1305022014039504581210111100c615000303802c20b14070034101140110700c0d409085090350204220055a80b60802c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 313689064 1250 313687814 313687817
    0xc0c080310081522150c120c2a170c0c150d0e150711120c030a03111215040902061207021c0806040c03020f160c050d0b16 54
    0x40500040c8444100301154079041c4800803c0000d04140b801000715000b8039456801034080341004601044500703149007601c4401040029000102030410703244001c425048075107003841d00410002d21a0041d01c00e60880c070408c0022102110109003d0129400c20000a0210034640702c2941207445031700c6c0100f602e000f840341110172440150002940c2e0380112800d141c9191000325128210f280240219480b54280c0000750401c4092084d85621491000b0414010081c480e81c00345a0300e1014001c90150032280e040989e0358946100d44142d580d4040c016140c0041c2c03404190003000082281902c24510030b03030115141c2502c814241031580f08804d400181d1003552600f5180c010396a1400400e502e904503940c101b03592408001c0641455641e1003004400118094000e0406500c41c010b164070090858001405d0100c0c031b00704800900071204203c214620008810380326030503017100070010610034008210171a450701d0138841c1d40705440d100240114141c0e404a200908200060210032829 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 313690314 1250 313689064 313689091
    0xe04020f13050901060c02030a02042703020105010e0f04031b02010e130509010b0609010903120e15030907090c020309040b0d05010c050403030e090103020108040b0915100602010b03010c0c0803 85
    0x50454100c900c0c1d1007203000c41440d0503400c400b001142002c520f00c80c0100f58504114648005a4000c680c54001c0e0b190001e200f10794501512401072090b070031440102c041e12003000e400714060326010380240350a0241006000c5644002010310b0706403124944074990590300c5402140000c2890050344051110803818000e14000019240c1c072100782d06e180080340d8031804112804c0182080e4210b6400c4920305003c0c00d0200a03544550741c00078580b008032030707000c3c2c12580a101a402c00b00c4446840c0840e41c3e07801040c4140c1d8402007004030014601520944040d84d80195035541e640045851303c206110150f0424043c9440d14034060b03008290041000d4143d032441000350f602d850031621b0300f05000300030a6011400f030080c15406242c8040c0325178151580c21040d41140c0003c2d140c19402000108840900d2000401101060103c0c00d02c03014949841040f40c18050048404541c080c040c140c01980b030b00740c000c201c1e0301d0140100f1004030398a444814460001e92030b00c0c0c2c815800140841d012100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 313691564 1250 313690314 313690327
    0x406060f03020a0e091509060d08160f05011104031a061e060f040902070308130f0f03110f0c0f1503010b0705070e0c04060e1206070809070f030506060a080f030a0e0402 74
    0x101c2920172449001d0702c1908420300780c0420204040c1c1c5030040d04050160a00140580002e03907100201e4020b00e4008400540d5800e1603e042e0000c80550100101607508002400c50030540b4074001e001620f20590440d41203035616907884034440c2c0102c1d00c2582c0501082002100c80380c0000b494404032001411451404114a10555066000c0d070f0158003403940c0060b5003014140d01c0305081e82c00c00c1d0210100c8101031031039152844a110709640150040041841c4501018002c00d608408a1aa0002d461a041c3c6c07025501380c462042c42c1c460350040d4001180c10000d4507009292004003824a0916030540c3d09110407c50103407c400421107091049607004510b80040c0d405003849410320920595a031400c04c1c50041031060700500d81801750042030600440c2500100e00700b50322100382d14240c03c1d40c1d9560191146010510b50040700240d0360460084240000884c0aa20414040d542802c2d0140e90b80a0240d58030031700c80c03800c2d2031500140a403c40c0c06201c2d10300040e850200900150030881c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 313692814 1250 313691564 313691569
    0x1090f080c0a0b0f010603060f060f18180905061501021905030405031506031e0a0210090b0f0309060907050901061803080412060e0106210f050d0507030e0406060f03020a0e 76
    0xb002c0c0c2e440c0b05132850710342c0108407007070745130007503402030900419044000d41c500340000c1c00001100c031800c070030300609140c055013000c08142084000c1050500c50b41008501d00902002012203a505031800c0c061100041c1c08485400782c003a12202d01a4020800f81c0c100148854114140c0c0100f1074180c0000c000c0081c8603035080010602d0300b040301e4149841e90405008140c9020000c0c011070140da07444c41948400c1e100041802c82d2443e406407541c5c042d000e4111002c4603159078030341104118600c00300303501c100500024051842000c008040b0b034801c1c0c8402c00820b42e030b039109102d050b83c0425454018484188506500305a2008507103000b1381554481c3d540703811a402540080380d4000c69010700d8400e108150249900d41107484008024203414880a50402c20b1015100c0c0e50403502c0c00d0951041200c883e002c4401c0580140569081802c0400c0040c2503520a400690010300c182d01c8110311494a80714403401c4420580300c000d505038100506074069080103800c40e080c00000e41135040242c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 313694064 1250 313692814 313692833
    0xf0b030303041a070f080c13080706050d051f121106161a01061e0e190e1005060304030c03050d11030106020f0111030105120a051005160201090f080c0a 67
    0xb10320450441e00002c0d0103c2980701d60030401003100c41000603160028840c0d5030011581a002039400210691721004032090f010040c0d0359501841e410b11517075600040041c1d00c08040e1282000f0028140300b1911402103207400540715003101c00200310b150034200300c00d000451070720040360f00c1001d40100c0d41c044040001c44580140383c000005080100303115040000c882603900c0c0d041621000c2200e207505004004140000c0300d07801c0c035001c02c140400729008500601111b40d00e490005c1c8140c6082e40000c0b0303a071501540912603600309511080c04100315086208404007580d001500c80d030300755a16a20100e8180141103002c1e030900100f0011403e0640860198001c01400c031720b81c4c01d5136075162610003458001068a032501c2d507450704c500c48075108048801c030390440740100e4a095480c0036199143c0d04040e90b04e68004c04a210341825440d500990340c101c0ca108001440d000e0031008d18081041c1c0c00c1c0c51454400900d03c1c10300040400001d03400740080c0a502041030b044a080d03500d05d13925550b1310f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 313695314 1250 313694064 313694071
    0x20a030b0108070f0902130510120911040c051c0c0302040e04060b010f0207051c03030608030a0903110a06080613021c050402030c030f0607050f0d05041a07020c060d0f0b030303 78
    0x21500004000e22010144421040007040000b80c1103103071601d00c070010f8480402c4e13401400d1103050b09c110340812061142820601c1c40c6032001c0304000c4241c1c18a0b0540c0107803200302205004605004c01440c12030300420548006180020780c0380700140041c40c001004001e000c3d010400e050b4203200c08a400441400d5061056210306800200b50f40700c403001510084036981242c0465000c0b01303051010b034071103440018061503a406900e24040d8240f609031301a00140c0c2002c21207201c0455090b1003640c0c4000760b841241e0081c501600340104641c10301c500407000b4015800854104804500d150820000c0a85a4820b1640050404404121601c000600ca0090300c4506460740103000942c5402d002c40300c0000070490041081c0744070080900c0e15400014000c00503c0008220703110000e1104081b944e501e8100042001715161500e080b490740140d99a15880302c0344c4603400074400c0381c00000c0f184600c19009002908085140340c40304040c141c4c0454040e03400e901ca01d4040c1082d201080590301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 313696564 1250 313695314 313695329
    0x100603060c1202090307050105090301020d0507021f020f12100306020301080304030c140307120521030a0f0606021914060117061b030c160203070b0a02120c1504020a030b01 76
    0x26810680c00000b014881240761440a003071040110300301950380058401d04955003804e142d5103c03100c0c5400039009008014140c0c0080d400d06040221140d03000c1100d644540c480340c07a4540071140c101c003000072030060a50340e200800d41041002100c03803c0c0307805107a008802c1d007040c0c000070340c50b987d078034041c1d070001c1c0e104400641c00407400f841002041080000036080d507451021902e96200000cd40c0c40442d0301c207110102d00d41d0850201405000d21481c1c13103c194105944004030342c00070224040d58800c0b42d44141c06403411b181801048598011801100d503164014032544c0b1040b0340710b181c480403809040f103d41c030400c1a48e00c0403000601c42e0f24006e100e01101036106000c49200d45050106c001c014101c4e103042d05031a404008a03041c103a98009628810032511040781007e0440810342e110400381d032501c11841c001601e4a02240107244250b200d500380c480c060220200b84145001e40d07404d800309a00f100c1c0050f040f142d181e01c00e40f580240010b0032500125560348600700944c1081c0c12100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 313697814 1250 313696564 313696571
    0xd021012110c0307081b0a051c0e01020c060d2d110a020d031e053103080a0e16030c0e010f06080406051504020f040338060310060306 59
    0x180c1955500c1100310284020310042c0c507080840e401c8640340c1c480d07550001c0c10403401003170100902090401846915074045d04aa1aa82e85810250b0b0350342c0840010400f2070321111400521035124295802d0001c43c10f80041c500000b090b000c202d003540102040d0050542d035200400d60145400c0c54a8041c0d0090740081403030008251100025100700b4401d411011608018290600d50700240ca40d107410814370300060400c4500202c0e1012604a041801010b81444d0510800b141c1d0031440c09044900b8840600c440200d0b03a540c00c0041810b2040a00416800b100242d440010b03038120403c44080e0209a0f0f0100c0c2d0307000404034003070381c407508191691130745190140000c424a82c0e0581c094410800c3c500701403481c3c4034006244200c010b2009081507151004502c4000d00c070040500302d0322000f4405e6499021103007072840f607500140b2040d20a080080000c815000c090ba40355050900444246080301c40144201900c20801400340e80d0903220703c0010030120034103031145001030351040c0741c0031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 313699064 1250 313697814 313697837
    0x301020a03090c05011809110f070803060111120d050a0f06080a03090806010b03070f0e0a091a09041e030e090f01140108160e040f0216051014070e0d0210 68
    0xd01031070051390001ca0500200e91714016401d00390341404000c43d400b011021440c084401c00e071140038005c2820b0090032003800704110341001110300c003540c07083c5400c0c0e903007070f46540f11481890f656807403024080c03a101d4070802c040f9802d00d402d40c21140d4040719060f004514880e20b40c003440c1c22125940c0c07103c2150b800440164080503400b084bc3c1c3c00515500e0020041541404070a030030340e10010b08941d06004003030300c1d0880818010501c1040c0c6050041c1009456a0b031503440001400c0d4412508140503c1078003480b10078588902602d02480e04143c0c0b1100318410060301c0c01d2039011504060703007031000c9003800844640d50780c41c0c02c80c41411541440d00c0594500481c03011703900d06865a03107041c40b8100e81000719050102c82070b07080c514003034036003100d00009039408a40107214030005400b0f050300004208480050840c6002e03003062268040b6880204544100001c0b181d040f9103511207141e08101007155039102e00116000940c2c000e02c640442941c1d41c0c005010003010300c4008004c2031048492 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 313700314 1250 313699064 313699073
    0xd09080d020105160c0201110709051e010f0e0c0d020f0702040b01030c0f140c01050c0705060105190306110409020703081f051810080d03062102030303040b04060b0301020a0309 78
    0x9814000e0550300080c46103007441c8540026503032000546200b040f0000107036805680c4900041c1100c55480d80030b45522580754101c0d4030151000315900110148461487c90100841810044c1228900e40c0b10090b172a00301203011941000141010000038001e005604c091449440100702ea01449000c00e0390783c841620610080d07c400208140c181454824400314071504040700341c4051040c0d00c0c00e4400340910300e000c40c0c40c0d806850700702a80d66203800100082000c0b48002801d80364050303011951140c1c2e90300200406a540148940d41252402008200107241c0e60480110517044445040c00c0c16100c22450080307822080090300041c0194080c4504003029101400c90301e451240e41411090a00740491082440c8003030014141ba440800603401e82500c54107d00074211110540d0701030b400d42d010060142c5030500a61411800310042018035445514680c2072907640a4061425070340c5035180c10f4130b0b0301e100500a580d081c1d10340801c40040c0c0d6003071000380006003c0b51000910b08840d07090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 313701564 1250 313700314 313700323
    0x1407212d030b04060803030a0509071a0409050f060a030f06090f03210b01201c08010905010609030c05041a0613060e03030c070e090307020315010504051003020f010c030306080d0908 80
    0x2101ca010f646056824004100040101ca901400c80c40780880c41d520350303c03000d42c40c2c103034640d04c8829241030100d81651240060741c020800c4480842091201d41c454070380000080d00190b41040d0302000142007080000c00300c0c404160785502640c3c00041c0016192944545907540c4101107000520040240b50058441100100720b01d81c01401003000e10b03505000600441d2083d901c0007800810511484040142007190884698400c0402400c103108041e001c0c0040f0800e00410100720305140c00070940910652070f080441e50454040c5121610740740c180700c001c040d40319402c4c0056070410514a00b43d10342a00800e00003c10780344214007103181c50001000c0580100d0380318400d80041001d00c04044000074504180d400c10f4440c0260b64568140c4140303148982c800094040c0240450342c1000c4a550311100d04a6000361000d0241d680c40703000710203103000d06002c004e40c000c40704c02d8501c1195200e0b40500424501c039090014146031900203081c5000b004418240000c0d08112003881442030074003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 313702814 1250 313701564 313701581
    0x70503031602011a0907050903010b031b0307061b02060307051209030a0f2d02240f070219060f0e0703060b04150305120703030207120f1407212d03 65
    0x504c1d1044e41050001980344a0140050701001404121180d450350290310907250241d0007800c403503889100c0f4030000002c0b0001070314070b4424040d1000010303041c1e014007241c01900507840300011155500d03608000050704060308040400c601807045d02203410804142c6400390035140300441c1c83e0400c149000700801304600079201000116607081c2040c0ea0344140003440515040c5007841c4070460210101e1402c8003024218061100034480310181c00c0141c803142d4001c0c028458050800e0f5142030013a42d50341203600014862650b660703c190b02103a2540e00040c046c80c65103001003011607141c0102c41c54010140c100703544a076924518012b0030714180c45400f080c41c02c0300c0c00c0241c049103552141511a10b1071011040040800030f001c00405201e81d0449081961202031400c603002e01d004000c0111503500c80341004541c03211003000020301da0700c040e540e049a00c5004240d000035031418003624995610208020b2014000705095940f400340b41e40e04d40411402211590421f1010000b0150742138135 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 313704064 1250 313702814 313702841
    0x1050108070605030a021e210604020f031311030d030e01050601080709120227040b0109021602040b0a08070305030a0206010f03081617040f18060f0e04030507050303160201 76
    0x307001004559001001d80e68444c040d55001030701c990b0700d1403411440c04e02e4020310100c0d400001400500b01c05000070140c80b000310324003032808142c4e50321042c00120b2040c1114004403080600015840424030409504145e12035a80000e5000c12000460310b07010790819184042034484c9840106c5480c00d104a035403120702441c003401c1c641080603006c0e00031480780c0101642c40454000a10542d241c26070b032040c003882150401008044002d0b281102084141c0b01201c046419400010764032080d80207a07240c1c0341c103031400780120600650800008110b10140240c0020030365900107081401880328400542c0600c02035a922070501400074200b02e0160440041c400b003c84040c00415640804e40c0c070000040c000c22a100c9016040980c11a070500c0c0c50200719040001d008907050100f4984001115602c24485e00039101d02884070060f02e030903010741e405201f4010020085034800d4950240c01501034100035291880741c4d140d4904550044681403840c4000e40c0c4141d41d0b055091041c4803042410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 313705314 1250 313704064 313704073
    0x203071a01140907090b031005010809070b0412060603062a020613031d031b0a06050903060703110f0a030506090a02070c09020d0f06030c060305012102060304110d03020c0301050108 80
    0x4002040c1402c2882080b01c0d4024410100001d454a01410110700a4404100c20b03e440380707454400307000440514000c0c0ca0000e0b02c24404120514070025884091b10b000088840c00c3c142401d90b141d0b2181000380b4240c0d40f0a80711900080410042e10420161101880b40d922000b003005070120101c14542244404641c0198208901e8030b0b01c034018a0141945860128029000407011848100d5245100ea9150040d40c0041d00540340405a0550f02c14098416401181c0d9800d01524103014100f6143d402d40c114400050b801846079210b0b001da01c800c1540b20f410114000c81c02e1410b80c100d2880400829075038400d00005261014109511001000007903240c54407030f07079032440021078038407038204200e4021880e6041605a600030100809e454041003001a9513400c00010050052180802191602001103810503080380c61020502c80c030040007858503c81d03400d010059000034000c1e034a40a070b41080c803a06035a0040307140c6c142e030700a42c02407c20950800c00c0508640042e80715280c02d502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 313706564 1250 313705314 313705319
    0xa0302090109022119050703060b0a0206010905180a1203110c0c03060105060a0e0f2d040f06081c0c0807050307110109270f02220906061d0406080105070203071a01 72
    0xb0880e180405c1505000c8010035151900802035000e00129000320501074400310701e4940d81c07640014141d0480308032610500980d100d44020803a034130f801c200c20b0281500410800c0c80820100e2121081c035402c14500001c18410804450050303400c55980b149054001741c41401880c071301003049501501c001c0b158145085203c01c03002d01299002c070a602c0c096100032024003100c0d0b540c2d0542842031000d00d655440740c2d604040150800c0c4251030280717031046191904810721a00d491007100c040d124454010100081d190806221001c5172040000410807080c2c1d100000490510251004910030b000841c0c072400c85142c141403004c43c0c50703072007410090320100c10407228000c00c508045031b0b24040213440c96402c0ca40602c00140c0841c1d4518102940009081c80010003150901110381010f0102000900e03110031001d015140540308080c0000c8052400344005080c51020041c1d40d400100005649540e03207a25609451084610501582020174210140890313029500e021141c054024400d0b0b60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 313707814 1250 313706564 313706581
    0x3060e0730050105070507021509010903150f020d0204080607140306061c060609080f06102705012315030a0e030c0a0c03020109080c0901030201030b0a03020901090221 74
    0x1005144280c0c203012142141000c2003a08144401c640c0c0040c024000c038549000043d01a81c030030b80c0100c0c000e8058041d00c03a00e0501640545900400517510241d4241c65902c0c0c0c200e800942c000c0302000c00341d07540401c041c010b246200414200a8002d40580c4031441d02000c2ea007440c000404070420300443c494072004000040c4c0849500100440300304c1e4492001000300814243d441010f814018980320012036603135041031040c03040340d08840444180880740d41005840d1142924000102612510180130a03d00701d03c0d01c40080c94019032502c042500503600f002603400c00c2c0c1c0a55003113900300851014000050541842c480b9043e92178403101c2e00020102c00461000030462003591381d480301ea02e07c64040074001c0b01c0742c503803039181218544c0c140c504281341d40700020300c8220b01040b0788500c0022410f90104080038030740401031064007141c1c82c40c0c0042d070180455208003640060b00220120050b603078240b800c0c0c06800f8005c001612080200c60040d804c803080c032840101350704460100551031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 313709064 1250 313707814 313707839
    0x3150f02090f150409021c11070b040f020d060c030609111e03060d020a090b01030f060e04030c03020f0d110c030f060c07110402180316050109050d111903060e07 71
    0x2c40c01030310b059050010030400342140b40603e030420380c8801d000060400c1c0ca480030394540200502c080070304220401012801d030070a03214925000340340d1140b003030004001c02c84481381c1d20207543c00074140c2592014150340742c1017241c0b800e40902e000701e607075a03109019a00710791080200d00301c1c4644441d45014a0141084030707502404050824600380000007070300355103903440ba00005a6000c1d00ca180083c0e159070f01c080141000d80c502c0c41c0001d240415210140c8580d0080c0c1c000c8401c11150b035201501d540d20205c5407200790801c26410340c07046030549004594204800c0c894001e0380d5441c11040d042c030400300c40c1020000c42e4041e204c1d070301421039000702c0103001c03032030580003040a000710340c1c3c40c5c00740e10340018141051280d2070785c46840411130348080c5000c6215038050b41c1c012021389110024180d0300340401c25131030040c180005c401000510040c01d02c0000c452480340502c5588090354004000201c50719000540040341d00e01cbe409080003084030303a00840d114000c8480181481e98103090300d0403000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 313710314 1250 313709064 313709089
    0x6140f030903040f0602150c031b090d0c0603060e1602032a01020304030c060b09091c050706060f06140a0509040c030b09070908070b0405100302210103150f0209 71
    0x59400020110326100000c1040350300802200d50071254243d40c408010b0349404e101d0503a000e6400721040080d10011514044901c544071a0392441c02150440100c40e0681e00003840083d04210150403820228104030700c001d009080725540410000c1c240800b92070703001d2000e440f12100c00015100405050340100607203401d01c0c02c5810303540001c2d040a0841d191180c0c0c03800041a107500c00030a000615a000000296032801800c05028100348a01448240071f002c0b5409842d81d00841d420704682d00301000003000d0004980f8200e42840c099848080888129034803048120700c51003820071816422030302c0140704100c0060120b052050740c000103001413007080200c80c42590b13030300100c00c004d0380a0b50000c2c079014070103000d64259190030000500440400d005001242c40340050000e0070a000d46c048070240c4401406a0700d0a1000003003e40181d0000c501d200c275111064180c0040c00e88200c03140c5030003140280d14621090703ca200380c4c01e0031113488150100440703004102c10581034a403030310f182c070382c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 313711564 1250 313710314 313710337
    0x20307020d031b0333060f020a05060106120905011503032a02090612010f05060103150609030807050705030a06090b0f0402091803040b0f090907020c18070909050703020a02070614 79
    0x292804003842901103002641d10800760154400408031014112003022001e44046d82c840c241c0ca00d03504c0409036511198142c008107554000401800424440c1208032603001e0240c0380071442980c5541d5803825103600085011810600b1320007007050590007045174070346000042d6031094018120080c1c3c5403120702d00390b001e80508996008101c0340e40300c103026038030200d0100000700f00840884c4d20450103460117803076250004c0c6c1003581050040c0c414215000c100e804940351722078200d16658580d102500400011748090050820000c0c035a10207020b10101d00c0e114800c002200f408610f00035920344006020034290f04502020880141c0f01c65042c01c0c0c11000004040800c42041030342c0c0d0341f46124070380100742c03102004034000211940300c20103400d000314215103900c2c2c00d980c2c094040b6550650301c1c6403140d00100c000316800c10201980c000680068080c60007030201038690b08010151030050300c802001940c0002d450420540c1481114003800003441d0403000d03094042d06c4070000c2d0107082e440d1034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 313712814 1250 313711564 313711571
    0xb030105090417070b040b040309080106180e10020a090303170c0306010e0328021516030f050c060c070510110a0302091c050f1c0210050a0b13020307020d031b03 71
    0x1003160b40c0f1201a01d00c880d83c00b1050b6030040ca054901400a406c00b82d40442c04220586800325100704c0c180030705000d507908200301400105060300408082c00171060482c0c00c03400307001c0d81d04d80d0b02c10300345c0020103e03003440e92030b28840c807861850000c114001000d6000c25441412041c0081c5c12008001c494214000b442d113203400030040030000b42044d00e9868034a204035011049881a07624204107514910f00881d018500590090b22100003841483d0900c4a6150b0a0700d21100090003601e02c410b4400740c0303182c1242030000654150303203080d0b03058640681d8648042010000c00c07a0422606d00381101000041c0001421080014054081c000004081c1074011030030407075644840410f00d03c1511601440900305840d428100d44540342504188401e0180c0c143e1000c14100e40c07003d000f203003011540209414040c15030380c6c4c0c0041c48080c2203110f905803224803c0d07451b4ad66a40300040c101c1c01d8990010b0741c07420100d601901c0c081816032200c060600b000f483c0203880c45080c0710750712507501c1d508020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 313714064 1250 313712814 313712843
    0x80409050a0213060815090f06012001020d0f1a030a230105180d110304030210210b190302060f0f041d040201090e190e1c0503060a0b0301050904 64
    0x850283c01070000e80380d08810703010800511280c1c414641c5000360345034040003040c0fa084100303200c12001e040340d4889001003031740301144865115803141148003010030704a0610741c804018050990340301501440c44261a5491140a5900b5120383c002c00c00c140c003034201400c801140031a840702440240034040d001c41415000750f45926020000c03102d02c50900030000c502d46444030654080c800f10351000c01d0310a000d03070b0380841030149415051030817680006505181c5140d00b00300702840200700f11402c114421407440740901003861849070f9025070b89004260b0554140c140010002e9103070201e26402e000020410158454004036413120780b0000f54559a035074051100c82c040d21465201000c3d910640c01e0300c030b2a90700d26204080c0514400d84c1d0f940c00a980d17400e580c00748960306550381e8881c0784085004450482c102e0740000148064901542d9010320510340700011184103c9518010950000c03c000207460103400120141501d06021f90030b5506001c0844c10f2540d000308010110188074500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 313715314 1250 313714064 313714081
    0x121407030b1207091509020f04030f151b030e06010513021605030a1d060702060909070e1201140a06080a0308090a020a0909060e06070e1e040903020114090a08040905 73
    0x2c400c151540108070b48541c0d685943c0c01000b051102d103010f0142d441c1c0e84000c12150000c1c02145c0100d202c0c2c001c40ca04260840d02c8020415010000842d001005051381c2c3e1215002d500400801503400c10032012514a890f0014081d1b4403c82c0d403c0815410402c0180950b588440151a03001003c080c01a25500595400340025400000c06401c0e880041120031110b41d201044114000b16200c8440201c0b02040600030203009640e0001d6100310140200042c5042003060a5801401c1d407425044244003e004125424003020030000310780d45540c210b03000c904d0315081c1c0a03049200e01c082000130b139107400d030083d0300c030f0b1a8524001d00b00910800410940c0301c00b0400103e8598008241d09a040e81d6006124010034440c0801c40e03040e0708040c50540c200401240243c4640000d807103190070704581001300110003203242e18604038034080000092407611f4038411800020310076000080e080c4807a0400c0c8145d0007000301604c00640c4204d200c980041c403288141c804581a0b4080441d032515070001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 313716564 1250 313715314 313715329
    0xf0b01140c0a08030108070f08150402010302071a190c020a0809040c1809020a030f0b010e12031b07060e0604030c090c09081f110906030f04020d14010903121407030b 73
    0x1010f401204084004114158042814001c03203c0c1c900c542c0b440c0b10b50318000ca40d1510b4281201c5842484030b4400200507500a4008103000743c411114000403c894500e0041520700590304080d00d42518004481d0885061084481200c42400104401e40c800d5a4181d480d03ca1103000703e0046480ba403c0c101c1c41c0b402000c4004100f2040102d10b803c140c3c03039840c62030080d0865200000082c0c107001c4c508080750b4240c4111032003000107940300705d8041500f20034010701c011800c00856841c401008189013400c0003249000380c9183d814042c201c000d140000c010035540700c4414592083c40108401c01c00206c0c0c880442d030413120080c0b00401e071700441350002e440c0e00c22103a200d001c00d40180190b1490080e2010030b108441650b00101304225041010400b0b49805501002d940190341000880c0310291a50b41c2190f110b48010140038140300c65039515104c00001a0506030169104c0c01200100b6420180c44411000060010864001040310031301c41c03460302034172030030074190b07a080d01291540b110403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 313717814 1250 313716564 313716583
    0x1a130b060f0303070215130b0910030b0a080102040303051c05010e04030e030705060703080906010609060c080304051204030506072c0904050f0106140a0503010b28120309090f0b01140c 81
    0x81030020b105140c01c07088002544064801076801f0000c0f08003040c0d480b20700c02520542e940282800c2c240803c690305c10380040400b4030038264400e1f04c050b0000340a000c240014806903100e5036419031100441a00c00e0034903c0350400510f07280d8109401409070901d8650b100d580250903241500c090031202d0040303800c10160350815900081c00007404020b140d08503807030030b0284480c901101d80680e600d0f401190f8002103070180b200000c0201c6c454502180300e82d000746811034014401e03205001116001a04030398070035030040314542c124404200c507440c0c00046103194032030005d85042210b44000700741c4002441004030b0610402c4620003181c07e100302002012840c00800000b005002d88508600c100661850701c82c0740716110240e4042458207041c01a010004000780030f15900b0945000032020704505180c03100b4940040070000500d84416140c0c0000c014040d44440140c0c03402c280c0007000fa41c0010415162030380c208518490180d0380680c003641c0c20102c880182e078955046114190401041a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 313719064 1250 313717814 313717819
    0x50913200901060f0f02010c0509060d1416020f071802071103060a050a0606020c09070e030a060c0c02040501050d0c051002010f09051b100509091504091a130b060f03030702 76
    0x28004a0f8264205001d2a80002541c0f541c04142c0c81c500301c100d09a44044541c1070000d4010300a081c0d1605051015010301c901888011803621040c2c401003e00c0c07031007201e0035000501c950742c0b01d008113a0103008022910038039074050107840c1d0034100c00d0ba80f0707401c0c044000d40034954002240c0f07052000c8810000d007600d400078140c80303860403ea01c001010b41f030140c850f1a81e0038136116000030054000a485280703420b01820480d8103a44040040d90060444c0402613050b0103645020303000104544102092029030781c1754102c1601c194010300007112416000130340550021560030000ca1103c817004001c541d01122002c4050006820480c0940079424115480d00e090a00039001c00c180820443c0c841d84101a540d406190b50030100680841080b180c7c5000c03035010842c1c1011410400001d9910420600c1135070082e585940118044540440c02629456404000d0600b0880700c208001d1308070803a07403400040508113443e0002490000f8005611030f62408401c0035640d2814820f1701d404c0d0340c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 313720314 1250 313719064 313719079
    0x602030306100302122a0711091e01060f030c0e2103090a0306050a0506061314030a0b0a0f15050a060c15020a052203120c060e030a090302010905091320 67
    0x42c03501c4508201070480c01b2941506000240c990320440042510b44141d0420040b07a02606114140801c1d004050800321408a0030b0003a0034600e02904526402804140d03070300c089203007039010004c0131104119540000c1210b100003d14483d6528500c50002c0c8034401c203014066280540150315620404040036001034000b8000400d000c100d6100502c199504541880f10b69070305800c01681c1d21450100242001220400b4000125490400013881c42c015044031802401622004420304040320304201c002d48400c503043d0110b81c64010186c4900642d44501c1c00c207410400000c11352031240c0100070402031f0001c514020b01091600301c4001d00b002d00300031560f903541401d00904a13481681c0c0c00d0900a0304814440350810905010340440340c00c201e20030424007000b8422a86145658400c4d40e0054581c000048641d906000525201106880f00100d280c41c510024040300e0302a80314603c60b4182004021103100560211446150b2103441c02e61903c2502d0002a0076800001c6c120750033011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 313721564 1250 313720314 313720321
    0x90d0807270504060f0305011a0a0e0405010b090c0405100906020d050a02030f0708250b04020d020d14280b16020304030605010f05040501082b02070306050f1807060203030610030212 80
    0x32085001d086d40d003d00000d006400003101e510f10003012805000d9000300c2510002c000010b001441c8642181c03042c8000f20b50030b07100d140003d5240e40f080c1e03040356072103034001801c1215103413040e00c8400e64025410440e0820380340810194460000c04940c0c000e011002501900c1c0501c244102c5030f1031070300c03482c0d02a11504c41e4140034105400010491520301d80c1c1c8207007082841381088804844030b5100d8140340055640e5400d0003050f5480150882c2c014142c0651080024625101c2403100b90920004000040721020440c02d080451009442c2d06421070201d071010031101c5400740d90207034244c1409640003075144412840d51045900141801d407820700040b40101600300c40008442c0d088400303010300e0340c0b02c5e58241c0d1a408907210181c8042020b08071304a0000b412030301c100089080d40140e507551603407900c0b00030544000700c0d28050381c22181420040c00190404c020070104040700010b02899003480c00195484c030025110350f00c18a0014a24690a8441c0c1c0444610387d42c44c600348030301c505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 313722814 1250 313721564 313721579
    0x20a09031b031101050c100b041d16060c03020a0605060609060f0c06062d0114040b21090703080d0f0c020d122d0204050a030308090d080727050406 65
    0x60307560004442108024000d400d40d0f600c62030a403030701510114042c0180c510426030300300c02044001c0780c50783c102e03484d0744101d490794820178a501081c0c4400005007007500703090a8840382c5148507420450a04c40140b090001182d40010302d5040d8981c07040002842d030b03c8040000d665401000f801542c040d0000640d030410f900190050320503140040d04403551500e90000700301e28540b05940c8102000746283c40c0a2b0040c0c485131071100b101e0741c1030520280b2002202c0300e010741caa120390000d640c40b4a000999160b005a03030b5014a290040350030103c4450300708408055110341d101c2c032024248600218a000c0c850800b17034480c100c84005060200320070105010041d444074082c50441001c614034501480400c2c900c2e01a4145141c0001c01a84c1140340381140300703111790f50804203203251035070034000420651141200a27000d14001c6c2c8821501e854898030662503c1140000300f001c008000d01070050a64000741048130012003940d1030703450505c510080005480b5540c0c80030754400d00301344000400b030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 313724064 1250 313722814 313722863
    0x609110a020d020a15021617070213022b02160b04050c0301111e12010305070e01090207080901033c060f080c010e03030f030406060e09010506090406020a0903 70
    0x10250242d58030314100030340a03a191402c0b01c0c0054400606a4607400b01c2d100141e000b0b22955810710a00002101d40f81c032141801c14038000301441c40f20000a100d800e6152061550740203000403801946009480b0290414600140c802c80e070084010b10400306a00e10f0740e8050b00c401c04808030094030082c20b2818240403808007500c4c190340c0c038011400d030b01c110307401e06014613501c07029401c100c1c40ca0702b00c030044115405005001d02d110300e01d40c1445403c03942214001494001d50192004184007810025818008903040c2e01480302c0c103204021010010342c1c10010f07074000c941c090a00240505044841e41c1d03141d80c2402001408406902805500804000d041280100d911400b00300710ba40316482201e04d500f00f400744220b250700c285400d401942c411910145c400c10041c0540c0e09102901a000025820a0b10101c900d2911500c082c04105140d108440c2d01010f03540003030195051480102e00100d102a05c09004544c000030305801c0203004035041002180d21107000ca1101e4144040395405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 313725314 1250 313724064 313724077
    0x8100317091309050a0210020a0c0b0316051333030606110703030207051203040e01090204140f01080727090e010605120d03150b0a1101060b0f040506070204060911 72
    0x6280e046594000b032582485025002d0350700100600d25403100f6000c1003003140c0800e01c91803c52207140400b074000b07100740da101402007204010441e03ca040c0040480c2c22000c0081500341080401e0150846022a4800c80e200b100c90790407004848410701c5550041640042d00343d613400580c441d1844030360b294540c1c4101300322112540c41400f840c031f84d004d55584401c242d00c0080d0040e0702c0700358140003d28000d14440034075089142124509513440c419490f070704000340d00c0800121ba0210301003042c100740e649030247c10241190300b00000c01100c00041e1000340007415010801010600500034244c42c030039242014502602281c0080d99141d14030009000300c0140710215500f066800076050400c16107440c9011707035000151541c0b54580c01c046001304003121034039020801e07180d000a0229504801450740030f6955441d2001e6448100509080d00c000e80e10052040d04104100c9455507414020b640035100b045800c00d0f83d840c0e83c0d00024028284039003110380414031b800d100712155491403004100c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 313726564 1250 313725314 313725319
    0x41e030218040605150609011416200105190e0d0b0a09170a09030b070903120f020d09180b04020c030d020310080c1005030702150a0f29010810031709 66
    0x240e52204045001e241741c00d000a81c0110301401700268541c018200f0031559244034503000e05041c1e00b4a40a0403440c40380784240e4450b40c0ca11071100316025008101c4419207401c0c00e006240c00760f5441c2d0342e640c2200484e04003007048404901810240d48003c000d542168001d22070660a00707020000c003000705160301c011219484559002000c804206055800074040758540309045072554440c810b11030b100030b2039a030400a0301200070002801c0001c0b1120045103e95451420380c92001c1d001c2c0c90a0750359080d0701c00380a1988000c0089280145030b100c62101781d20400700d4241002004a0041d0182d040c41e007456000124466407031132503940c00380d881020040240c00707146544158003a21030385031405117604058031003442004103018000640d08419640b044481d400780d505071031035a000c1c003541c1c40c4044588800c40000d1111f140d004044090480c0c1d6040d41c26000808034031450300d502283c4e17450620100500041c09424009110301c0215040001d08013504032002c1c910780c40d5070140c80d13880e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 313727814 1250 313726564 313726571
    0x20d06050118110a05160c0801050703050603010b0a031b0807151b03080a110705010c020d300509010227010f090e061201110a050c190206041e0302180406 68
    0x2d0354402a0250703400d0440ca8800c054640701888804650652104814103418070300782d81d21300c00142c030f0a8584001044c10b600009403070b0400c0c100003415140050311040c0300780e0510340104038940c4e0390940003040325071103840c0c450480c3c4480506601007400307a02600850003105000102920f1006075203281d112145d9840c0703034010038454200c0c8958010800600081d8036580012014a0243e00000c0c0503801e0405007030070517070b07199a512b003900c0310450814010780040c00741c040d100350460780019450445451600b407007950684c140c04c0203424501400c04881d140c2c0c010a079001c1d820360494220781d002501e20710403460f0702445261100710720141c25001070306a48515a4481c85903a040e000d941c09041c8001058030781004004810f09a40d500c29401d5607a10714507240203880740010312480c1c1140d112030b51620b20243c400e50501c600c00d810300007107244400e60480103a48580440d800e503424008200000e440010303030204108001d40000b50040b042045240007185450581380c0705511514091 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 313729064 1250 313727814 313727849
    0x140c0f060603210705010902040f0f0b1c0605180d0c12020303070c0f1104020406030b0405010f030b0402120f0d03050415090c0506090d08070807020907030507020604140a020d060501 80
    0x5503403045400c3c0c841c0c122402c036101c8000b441400d10001e00360342d4000d0b0008a00c12078a900041c00b165400c81101a003145c0d1246403510f10f901500817000c9043c030840e03056410188030301406150380001ca100503d101e54031030003e10f0b05141018100d5040881d0b10171101c900c5040c4d2000381030210041e800303449581c0300b1a01c4a58071440003007100d2145005580d605203c51003555800500414000e0844e1039a0034001442141d446a00c042e00080c1074540d000304503880f500d401d100c100c2e501a040b20101d803806081c01c0c0003080321130001c0c0d6009a41680c120420381e007100580340c10000b181716041d407140540466242c81e5980350304458003031406509600d041c0b01c8841015021541c044a008010000b18201003180d40b40c140050800c000001e4004d11050005039104022603120700b0007200d14460100d94181542084408030754041905d0504000714140900042d40d0b41100500062042801c41c1894482850910101c85115409800c445844016203403040251600f40540005244000800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 313730314 1250 313729064 313729069
    0x80a02070602191e020607060510140405090a0201050c07150c0b0f06030604032f07030501060e13020d06020d020304140d090b04090c1103070c06180509060103050601140c0f0606 78
    0x1c1401150f00c1081200551a1588030501301100300f203042c5d0b803140c002d00104020a209004161045610300341d0f81c1c59450401480b540c1c0c440407082c0c124003a80ca44010131211709000504c0e203c1c0d10707809003465030703d40000182052502c6041e411914048030241010342e101500a9505149240702c1d0f0200c0903156141c00c20074442d01800c56405038198411070204000c0384c0900b4621203840c00c0c40d0300440260294044450f5009101c031049c0a465104000800900800b031054501030101205103403038608000c1d500107178210403d240070784620f010f105070608000c1107038112403415500b507500f9500c91a250822010308050641c80c2407190041d0100341000d180f0070440d041c00ea032200362101d800c107400c1140040c010f209070522035091241c040c1c101380e0a11000c0000c0d0010501c00e19451707800a0406900500008002c40412402803010000740029580c0d41020741d1f0040c005c0c64001410758070380c001240c40740b5000381508d40101c80003c0c2414400004284818200d0080040700ca20b81c84403800d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 313731564 1250 313730314 313730353
    0xd080702040f0b100c020321030f010e0105010c030e04090b07051207020f2a1f0314010302010905010c0c0302091602150402091f18050612070612090f080a02070602 72
    0x4500360311043e204000d1354954007070407049000341d001408503800b41c2288800f84641d1005400c410000c91004401c024070396000740011400b400d41d0320802c00c1d5552601c800078066042c250402001d01403079101020713554a460f84001c03601ca4201d02c4841c0c2d6400d08600c040d0840d400f1200c0c0c002c88842038800101240d0001900200400c0540300a081260885010494103244494003d09001d6000d03803680305640e4415412070700b1551000449103103540b03000c01a049424503402d040c00074010100410240c0e801c100b144007202c000b802c00c420300d20f919280141e02424213401c000c1d030210b090400e004040004500d40c12065156408890003499a0710b0b030300f11041c00440d03009502c0b030044400940c0421841c55401b0542d000c0b208240607007078569111620094100412600070b56688040100341d2030045140d2419100e014058855241850002030660b000810415500c0341c4514a030020011b0b4100d220502c183c22040d02c07601c8050f4403400a4440302d05d441404011310600f03550742c8008810706c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 313732814 1250 313731564 313731581
    0x801150503060a0e0c040204091410050112091b0902130803120408090111010c0201020702090f060a0905100906030b0108060711060a0b060c0a0c0302030f0d020c060c010b0d080702040f 81
    0x800408041da603000a80d800350000882d41310305405020800310058032240003420140441d600046510501401010f50b038a42c010191070b10b403607a0030b00c1086240d802030341c1c140380b00c4c141c0d10000c9050f18803401c24003080510390700d03241c05529a04800003401800d03035000d00703031481c035800140d1009542c42c00002d6881c02440b1100c3e207204086804500003514000c0204140c40042c10300c2c00c0c94903005506282100c8100e030000c40544d4000529200718501000041d03480304130640301107020704110000c110b0344401d070300034400b05036034410204281030120b86010005000201c0c090245948900c1c2002c402407007803044941c54801c07540407500c5c40e030058400c1540303082e101c0c0c01003a540d690b800c20480544018510f054004008020205070340c04144000004940181601c2061600d5803041c10f10302070640c4d01381100c07900807031302140c4602e50101c0c409421001c1100d80c5520303626141015401011401000383c0e00508410114040200d21006403400368000c480c104084d40189004009561080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 313734064 1250 313732814 313732819
    0x405090102040602280c061101110301080a02090402120d02010e0105060303040305151e010b0910020c18040215070b09010605040b060301180f1e0510050a0e0a020d060b0408011505 79
    0x3c01503803403c085c100c14501040d18003110000d0203509180c403000b41030045038004400041b8114520640c4031024060020f000c0300c0b00c0203c510f15071520703940ba034680301c82503270082c46030107607a010405560318100452250880d100c01d44190340c0303d029019000780311000102c82e95500341800a1441d00d130100558080b2500400601071250000001684410004044160402d584a440525580954900350103408000815643c903901d035170030880381d107030600351540866101308150041501c0e004100c04030380000c01e4040c50b51f40c550b8800200c001d00356038043e074010306012816009101e4074529150150042e00001c000c03450325982800207840c4860003154021100f00b004200341c030700318450400c0200c40c8001c00200700d004094043c0650300f000c20032018051040001e030802d640d1030720440e504030103915040345c882894200811040882407007010030181d40c100c00200e50b08031035011203c0310704160307004116054032070020034903c1d0414020b2102c00e43c07071b050300c9078000103003c1800d9040d10f400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 313735314 1250 313734064 313734073
    0x903060a05090a0b180703141b01050409180203010e01020901080108070e01060f021f0b100507050c0402031b1204120f1715060f09040b0603070507030804031119020405090102040602 80
    0x1140c8600341303007800203003820902d11640358118607004802c2c84110080d6108010003440703e00e82c00035140c81d041442c2c00040c20080d440c0c80500c1c0907070300b1004460484000030000704021070321400e14010940f00aa01030b4065003000718081d1200c1042d801854040801d0f2610112030762120700706940d5070213600603607541e1403600005200c0c4074050a05444019014070480d18081c220400c1e4054480c09815400c13106a00d038820450302e03140541110040414514105d801d00000d611801e41ea41c800c400d000b80601e078004042245101c9160800300300c002e41d408030580c1c030306041e04200850442281d0580c0e5008002207100da209100d1018141d03608000d0341d444d07a442c50b070340d0044d00d10030714045c1c48407109089000003002142c4450740906401002b220800d52601070240901c000d450440c00302c0e0348109020000c000c80550031a090b02c08003601803400d0703241a03541e0701c0c0a65202d00d580504104902c1603100c50034440d002c4050a04465100b40c42c2448991114a445420b0b4003c0d070282c0310240c1c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 313736564 1250 313735314 313735333
    0x206160611031303030902120313080c120a110613030524131719030e0610030302030a030506011704050606041a01020705010804150c020604051605010c111201020c030903060a0509 79
    0xc29003046c86054001820316408550743d04a5911315409481c0c802d911201d8881c0400031a0780512210a411109840351002d903840d8001243d16100d960500401c00c004c0d1220305c2906488140603900d200c0180c00c03084c40410785034107210f55920303040b45e180100d00700034030b000200109848010b603000305480c5403100040c050f0f5036980c0b0035514004400d00d141c45030034400f4404888491201001c0f0703c1c07103078a00042c210705038202107041c110001c0080c0003240b40c440c0b0810000350f0000445d1030010707140c03600040f5900c44000403a00404200040c510100245052101740a4042034090051900f110104810146201804030810720f040310130380940c0016004214550017049015030003881944c00c507940340c0150380001708071002d900c652001039020404000820074104280c000640e150518003032400d16100008015608490000741502c8502d01500c0445d1a66080079074980311020017551103a40d41900e2580d240c014060349442403250b04040780f000c1c00f4a204480c000c003c00c5000e8610031a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 313737814 1250 313736564 313736567
    0x1d030309010e0402030a09020613240c140f030f0414040b0a120f0f0606060f0302030103080a3c030b091902070c0f031a0a0513020f030a0206160611031303 68
    0x40001b0102d441c100d8541c10340800503543e500c01403060555001e00e040510b070400002d0b0400580882c03a40303001e50040c81000d82134039001124844c03039561210410040301c10250240c2c2c2044812941c1e80070030f10010444140c04001d400140c404e0b26060200c1144243e1a101004183d030b84c00c2007800d4004012600c280445100c24080b02081c9010f4180d5481c0c130112950b402d010864500401d0302c80729a81c00080c008141c0c0511042d090130454038043d411941152212443c80c8074000702c0c0c90a101c0b05000070504c0f800c2c410340070321500b00c00c5640500002c01c06d2110403071494140918400003850900b5000b40b40c40c0035072800b801844161010030a4014201c413580003503202d454146c540400121001a1406132110210b02544c400d040801c1150040041d6103040000070300a4484a030a080801c24109410b0342c0b1440d80b00e404540781e5003d0010900400d0030303c0c5c0f038030101a40212001034400325001ca500a440c0c504c0c0e00c91481040b081e0001100c52111b80000d1710350b00c0120320f0407491080803a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 313739064 1250 313737814 313737817
    0x90c0f0907050f120105120f030a031a06030a06050301050705130b0901050405030609010e011503031e091d06030d02120f1c05010608090d02061005090a0e01050103031d030309010e0402 81
    0x4216810014a400d00840940c50319400818000e41604d00030401030001d42400805486c0d41d100c404024141e02141700b64660300c2e40602d08442c07080580c4e401581114281d2039102c1b120b0030001400c815645d0800c04030040c050205400303494041d600f0030303010034030f0310780300b2000c458500106d1590600305c5030500501003825480b8400f001d040100c1400003080a03a41400550700075541000001001080103a01c0c03030035500303918515a8038003101c110030070100740c000414101080c42841d40d000c083e91030010940d001031164009a421010f540303c40c0386040502c031181760142004078211441d007140f10304102c0c1e686c180c1000204d0920014008460040b10b544044c1c1a101c403424240d5100038881c07815502240c80991050300000c0300c280901c00490014024008050001d101501c605c1c5481c120031030459182d031164500994820001402d00407140c0c0c002802c0341c904038001d01c80d0356540d050007401824070303810100b0b030319100070540740e01460000211070200c501a1100c0a0103524075080200a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 313740314 1250 313739064 313739071
    0x601020717010e030406050a0e0103020712050703030f06080a170c07060c08090409081b070b0a050c03091f08090601121211010903030617010e06062404031a090c0f09 73
    0x142d0340791520070b100000103002500240c0720070340e00c0b641c9a6000400c014000c000d00203015061610400198010980d00c03038640310855281c0c14915950369003460201c00900080c1e1100c090b20380341035800300c0d540a01041007070440b4094403d00181c04490030748100b441c410582004859800800e0810006d4003c1e50f15200b00c50091aa250500702d00c40049419110450b0003121422000100300e90070705481c554845a6004490050201e00d00300070301924203226440101c4113010f8041040d4400d00000c000b00c0300c24001c003509204c15888540c8403c42c50051840115011414400018000d948002401412201455030030f18401900c0e882e1560342d101c84001810400001d004055800c00b0240907291a461003a6030009919243c400700c0b0182403c220045006a4140b14004c2c110680c0040d050382c00c003008480d86405800d4200411442099105032100401d501040c00401e02c03005600d40d44207100c00480910785039848840b01615000d0500300301e0361140c07a102848809040118034980d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 313741564 1250 313740314 313740359
    0xe150f1314070308040510020f1027050c10110d0c06020c1504030e040b010801181806020d05060108040f0318052e14160201020a0b0a0506010206090606010207 70
    0x9907403501c01c0000c0c10090b160b0010343e03090f0f500103010405402e0686841d81081e1240c40a88000750100d41e03c030f5203610891040e400201d480341d50f00c81480b28601943d805004200400e10030f05102843c140d5160203420801620601a140e954140b0f603009080302c001c840102e101609480c03c9030a4259020800d00a01b40d6680c6c0c0d01744030b410000c10040040300100f585500b9112914505440c000340601c0a002d446c5018504000843c21a640c101502c141900d1002c0000880d0080e03441e40380c1c008082c1003000b00b0620031034240000a0191a6005011140300201c00b4091075440000565070000c098500034000b02003801541c020a11505603800700e069500800184556204005210300880e0f6052060341c140c1155240c040f026070300314800c0d20b241c890404c1c0013081d041d0031106a20380180c61500c14090310042c441800c6a20900500b140c295010b01d00010900342484140020102140c000c0c0c01f51242d00040b620803000010802e10401e016401444001e0512440c0841541400707034002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 313742814 1250 313741564 313741583
    0xe06040314031908040b091b0f030109120503040c0f140f040b040606052224030b0402040e061e031e0c0603130b0703050c0702090c120103060e150f13 66
    0x3c24101030407841032522540c0c2e13159614141070a007151014400f8001400c0e40d400f258611901c910440351540006c002103030040c80d071001c10408280585842c1c10004e0018170b00c3da9814001c943c0200180d4051409a0401d00b000764a401c0310700502d01c92030003100345691202d80320240500d000c003225a0903580c0600082400c035101d5010405603a1540c10034004240007141c107400c008544100503481c85866240c8184591500d03010b1022001ca041c000402a00102c101030f480e280260400c1406007006082156199036810707140b405c0c034400340c03021446201c6c0080301d0307041c440281007030070302c00c800043c047c0200510016016034248224040c2ca4550b01520316680b0361076036003a010718411590120100300c00406464480003a102c001c001c030007894517242c1030050441c007140580b02100c0e8140d640c0d4085449142c1068414016401c2504441c4100c40000c030401003107800410080401c01e049a03048a45603000c1c6480c0c0104403103006880304200c00042109080d540066901800f4081c0d44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 313744064 1250 313742814 313742827
    0x2040e0609010618051b0f120f04021201090c090518010e0102070203061006090b030408161a060409080f0304060207080a0e030601121211030c0708010f0c0e0604031403 74
    0x24144103086500140607503480c4420840706240444003001d090325001c0030095440c105101e4882201144030410560394045041088500010110351440c111100b9080142c606034514400300e400c03c80b4128004c51410700b403800032500500803204407e82c020140c454050400d00004000c00c1c00134400c121500304414103c401c120288161944000001e001580d900118014586440d00142140341803403020075003045201e5001030200103403408484100d64a031114100041c00c1c2c01151899440e25403c40821400c000c0355031a070b18000300700711f8440746d055650001004116599648040c11444003000911030011710b400046034032500c1407000500301203294692442c2d0f500080303502008914800700020561404206840c01850724001110040900382d843d44c580c0625107185005118203409000102c84d424429a003059082200716066556503140c414040c0441240e055002c4d4505503850703800a118081c1c2024404021b0142844c2900e10380e0b0303141c8120207690702c41c41180424041c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 313745314 1250 313744064 313744091
    0x901060215040201120c0e0a141c03121a0103060609080c04020f041d0a14011202190b0d0f0b03030f0a0804030c170904180b18150414070603110d090204 67
    0x10f0405100481d5200204c071aa0002409415540b54102070600e5080d41900f076001e544444ac603c2600418529203840c001042c0317001c1e03aa803054900403080b518244012152051000b02d400944040c00366018024180d4414080c1c0d070f0102c05010f4542c00d60031460f141d064608107a001480003030f01d040a4185003555078001002c0d0686140118002c800074001484100e0ba0180149e14002800dc240901c00354500b41c054000461405402402070000208001300e5002c8070103d18001c028000c0c4195495010f10748490003040e1200c03da8001600d400229503060a001080d500701d01d4070890100c0c03600c002da0350162260b02c0d008200700e0030401070044038000034505a10b0703c01c24030101200a91030740342d601c2c00c120a807012440036108084c588103013040031816520816030814004140300c120003a0700b85009060040b0100c29110000d03514003480b0400c09802d45204021400d481540d01d620b40f110070031019038a14442c00780241c2000d2154158030b0b41280e10005089100820005c3e8036207040f000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 313746564 1250 313745314 313745321
    0x9140d0c1701020307020d021f0902190312020d02010e0a02090c0d2a0e0d0b1801090506010927080901030f1b0206010f08030313030c1e11090106021504020112 70
    0x5140c049a5004403e00000e25010060b41f2040a45c3e80084c05281500d044c01800d00a89000c00008480c0c0307554091095403110200d1055424041c2e20f56040641c40f420100c0444a419903460300601c81c9001000e00f013481886082e0010500801a0642d41c01c0d9400700100b030030780540070b0030038143d040107601c510340010303c2010030f0201d008003c0c0c0c13401482e6020724030503041e40643d240140129401c2101c049da986480c4000940c0d4084014521600c540c062400521800d10342e5a011750300c0e141c1198140600010514100c83d00208103004450319000d008500f00c3d400d11154004088403603031840099000d001402c450b00040c500055200036000740d000c04e95452540e6820480380201d8803800142e810321880340075044075002440094508a4020f60300d100052400400d405400024410148180ca28420103904016010071081c84102c14000b40c82a1100881e0110700c1c20f41c000700c80d030908040e5103040351442c3d00500501071181c00d80d685226002001281004031219848041c00203030311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 313747814 1250 313746564 313746599
    0x2120112110a080d18060f141c05090f12070602071106070b1902040b040b03040503160510050f0f010504051503060109020a08010803070c0b0a030608030f090f0109140d0c 75
    0x800904500203140005400145c1c200404100b0419254017800110303040001450b041e142c51808808a080070030f1400380c58040c034001c100f21401d561102034025444d0390406030080f04105c080c2d824101070102001d980d01c0c84601400d60040d000d003e00c0004c14125409004418055842d0300d51081004000400b02e40c00b00204588000c5c099040c880f03a2900d1880500f00282815000c51400e400e00c08000703514040e80c4616001c8000c00400941003260600503200d49003205407960b2000580c40c5040b41e10b0b11003440030410206d251800049a49426108031801450026040f040e56400d01c01848085c0800504542c52a1041501c40c50760b5101000001d00910780700c2d90040c1c4031000784000a04400043c0d0010071903a20510840c404602601002412545200c040360b503620080c0b282075028104591107040d041c0404101c1550070030810000b4841c03c0c1089940d00700c0384100c0001034882c03402e24010b070041802d40c4200c4004e941450380c040080d0700d00030211494890f2703540c0d10081c540350003007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 313749064 1250 313747814 313747829
    0x200d0e120d05150f061803031b1b0f042a09060e091b0a0c0503161502070b0c0a0e0406090903170903030a0b0f06030403020c120102120112110a 63
    0x141c1e000041c850348210340e0801803d265541c00d82c0300c0c0ca000609641e00a001083c405e40c80001d031740040200180d000c003244800682582c0d02c4d20300900e490309400341d82c100403248600981c80f05903900003403400ca050100314000c005803020542d1a0500000340b100107101400c0200d42d04032190710054080c2d00c000c810503140e403842e0307a06060400061403038042c00141d90040880405104204100c0862141e032204e949110701e84402058004030340703c403a18000680140000245213440700e01d07404220b5203082c0104040b0494040f04155001248145072000e8000d075007000c04a1038840b080d1004004107032492600c0307208031038404001411140f041d40a00840fa554241d0f8104140e040a20100c049504546000351464001c01039074a905c8028140703000340f5a0341d10070550750343e9600d2100541d0b00014001a07240d140c0303460007941e6001c00851b4284154a004400a1294014001c44000c0300750079060162070f9207440c64100c1200c020b1300b402c54a0a401b0080504580c40b000000e40c01484031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 313750314 1250 313749064 313749067
    0x3060f0603110d050c0d020a15050706110f0703120605040204090b040c0c0c03030f12050405030c0615030a0318080604050703170a08040f06140c0901030609200d0e12 73
    0x3145002d031000140c02c06414012030880c004200403840105122400ca4816101000029814400100b05510710b03000003101000060799a59560390102c0030300075041c4211800c0180c426103501214980c01001280343c0044001c0204a00082c0b10320240111901c4150011a040e44c0b01c400080c282e0b0800c5c4c2128070517603034403404031800303241c140280141c000d0b050800c404000404d4440141e401414080901400312013241d500c030003407056030480030034084200100400d0400303142c10b03901d0f030b445a4942c000300d2043c50007103208001990000450101e0041c01002094190b6905840d4168103048640b0781d18500000050035140a0101501c00c0b84aa0060522541149012006910311103582c1c04403030310910505501c15003140301c0540090304140c44000f9003000d441c0178000303481e80d0110031a0640c0060140013000b403601000c1c2803896800d80b810f200d0581c907485000700305c03840004880c40380118400201c3c040c0201c00020180007110390b1011604074403480880c0e240200036101071100300300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 313751564 1250 313750314 313750319
    0x5100e03090112110301030215040b0a09030201020c03071511070b040305010e060106030b0a0e090a05070e18061b0c07150e010e031f0203090120030103210518010903060f06 76
    0xd0046294603169100c074020028540e100e84c07504014001408000c1c05804842e8a0040301078901096500810400b1300455482d038841c00d00821a030181d00c4201d016100303142030b02400b0701c1d01003002020b603082214101c0c0ea8a000e10021503102811410079071050060381c40c040b85036141c0c0c0b0001c00145018100205100b55010300305881c180c4164000c0c002c00d450422290312907a29620000c00326856070892400b0340d05c920350b03640e05003440203000404d60301c1603650001d210204800d01a12030042c003101106403481052040380c442d401196040f45a0340c1402801d9559050f11015100840c02a4211401107484081c81c0c200e0483c403600c070130003054520300702905e1036902c0703000d015840c0001e074050b01c020b1039000c011a00c02e00000d003e01c402d11790007000080080c9070941c001451402c8136900784c000391100020b55400c9900a0200791040411101141840a51440f030441c4d098401d545852410008052423030b06c0c440241c000d641002801c020000c04241180a40a0100d4661000142051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 313752814 1250 313751564 313751567
    0x706020309070e01120b0402042a1409013603082502010e0d080c010606050306041404030206040b06210607030e19080c01090c0b0a0807092105100e030901 68
    0x2440307910a2000b0312030f5400500240b034101001840542d4001c50b142c04a840304d20010b00036000d4080c0340e500c0311080f106581d04010b1160514801e1034595103404d40c00259030303c0c40f03608510032540207034041124800c0781c5118101c43d0010302d52041d11340d0070048521850700020352090b0103641c0155a502e00c0407404240c842c1c80da4001c0c81c045626000d40f100034000a50001e481d4041d5180820321a001050b01e26003480a21001c0703e250300900002000102d8840b68007500e260015241c680c001d51401d15512440581400c07180c2c09036825400030320003980d403503588885122006141303030b0308803130100114419030758805003c4460300c040c1d0340540118a0245401011244405e5109a0941c03103d000000b0041606418640da290800d0142d0382d1142005009805001710764001401c07032007200c20000b107031003940000d4441c10b01d2030327500c0d8101c13510345800c125040c0c4d0050181c1c83c031b1020800c003500c03001004200a8260f9504c98826101e6201b403040720703202208d200146081c02d81d0000115005550b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 313754064 1250 313752814 313752823
    0x80c030f21060d23010f1506020c0625050a020301050a06080d14030601110309060a0801050111030903060c1612050408240c0a020703050d1d0f0f09060103060b0706020309 75
    0x442a1150300014506444e0944841c0c00d5408a2030041c050003081c04002c50207411151000d080c02509100d0b01849001020140481c0e00c103c4005005800684000345072010450f08244103104030100f0030881145d00a8139a03c0d5001d04888034801c00c880000141c81c2805160700c034120449001801c140382601081c205501c1e00014010051000d080709a508203901c15030303030021000c1c40d03c501805c181040d05481d61040a1219a01010100383c2161066202003214140ca0303080c2c1e135241d01c0710071955141e5a0b82c082e07980c83c3e6526405c44800280028194805007003d00000440c406111034203031a0400c0e444040240100092000582071001788001c00080c1e041c55a501d890180c1d5580002034111507040c003601c0b1100c040d50002d807141166200304035140c00380d0b0300481a2600d003c1c00c4100038129204150700c41c0d50400144440341c04626009128010900d030107070110b2100c0d00510100100c5100c0200b400c0c0c14540d8408001c51014040300140c1401c9102e00401680c0741040310145240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 313755314 1250 313754064 313754071
    0x303080a020703120b18041b170a110103020f160201081006020a080318060f01030309060c050606040905070f1e080105040302031b01180f0c0e13080c030f21 69
    0x41078010442c00c00080e502c010000309501d210040091100000400520700d1501c4408942443e141c481c284030030f1204a40c207810001d540701840c85400303652403050030100200c04040c08150f401614018000c65244040074003540340c145001803422503046020102500070110040f1104034528003c011960803544045d0040030584121142c0f5241a8000b50348615016005011180c0400800d019041300d80b0084c038400d081c402613807940e1070610a404041b240920007580000d005050003c2c04c0d40c050702980c440340350080701425041d51254203020207442c000030120340d03d00c2030b0000050181030303215450014210940403c00c010100c0c0704a0f072034524094101002c42c0c1d01d89018800066000000c840c1703584000c41c502500030741c03428003c2d80148048074808129181c9956480304012000d04034000203845101074151254a034440e4000c0e8882c100c0c0c8041d400e804c8420500d02003003180c406442206003c42c1120328043d4a81c0528000740c001144107181e540707842c600300d1442c0f102e072140a5072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 313756564 1250 313755314 313755331
    0x605150c070e090a081602030321310c0906060309140303061c080706051003021021090606030c0e06120a12050705011508031e03060a0302062d0301030308 68
    0xa403e2080000d41c682c040e0110081000c000043c0c90791140d01c0055224200ea81c00909070b03034480c0c104407840c503100b03840e00518040300e0007283d00003505486544200d070281321030192009c0c0b800c61080f034a003d2071055190140c0d0180101d140015020b051401041e0292001c0e580104c0c03212614900300c0364282c0780380400300c0c403504140200a09522420b8030314503c1446242a0600140e8038242805140318103103015064034104400c000740ca4152284802c2100d200307903820b0640e1008120b01312442d040966154424020040003c1c40189443d004581c0140c00385c0c0001644a0b681d983e421402000c83d403240c11820070402c1008880d14091154650482007200603180c0c0f2203842c2c2d00da82c10301110a802200340300001c6403c205009003588900b110346080140700f002192500c80e5595a60014034091245115803030460303042212032801d4a00a543c06449403020b0703411942080600d422081e05c448040d1000c0c01600b0010000014200c0788020180f5072030ba4a50460130020072100e001804140e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 313757814 1250 313756564 313756589
    0x2010b010215040204020304080d1103071e08010308091516060e1902190905130221060408280903021003020703050d0f0f0e012901020d03020d0605150c07 68
    0x481c0c5040075150f109604030340040c3e03640e5442c98512407a005008001c1c165900d00000c0c8058044040000c6000301c03955110524110040d11350b00604c0703084408007000050546c0c00420000c4c1c100c0d00a030030f04200040c61080ca1704400701582c0540d401901590781c0c0c0192074481e450910a091042150214001020b400000c3d007180c00d4101500c0c1e0300340000d0180b00425020502280d00a9110001d010705034024403950900c83c464000c8859810403e034845d82800082114080d41880002c10081d1650f010305815925a210403070242c20040382032407513041031600d54421060a408640b04122192035140c0d1540c1035005002c00e0301010f00f480d00a043c41040241c0c00f080c5c024003541c1c0324559500022031140d00201c40c05001e0300c800004030703008a0410340c07003081e2588103400880d0141c0000d083ca01820314280c070020200d10084000c10302503001440c810384103900c81d400400000ca800711001c40c5280c6d5980103d000e1100040000c4040c00307000ca500754802005000d5003004290798031800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 313759064 1250 313757814 313757833
    0x1e090209070807300f0515030313030303050a0209180412020102090a050d0521072001050703080405010b090703090b070804031d0f040213081504080406030b18010303020d02010b0102 80
    0x60041c40c4400044801340c440810a001584030b00e01c060180d00004000510007120000380c11006031200387ca00c001c240c40c6c0a8940703031160800100760b601c0c103600780450442262071070f201940140342c080d10b6043c21640802101f0304603203400600c1034500a0070800d20040e454030b400e00766040c82400803140110f90041140092554507543d0034003c0d104101d880600600d8075191080c6003000c03c3c9400c096407507042413903000c940b0050003d051100c0c000d00c181c040114002c1c40200c203c0d9040807210303010a01c20701c00d407404030f4403803692194007500c500d0000542d1001c440000740030110840705400000e0300c69180d07108004c0f09894440d00400075040c0400746003070568010307044100c0d0040880c840804441c1031065961642a500360704507001c1c000315501c90090300100d41c4041e01e4003500c030a5218440c4944103000d810a02c40d40b19941240504e4102810070000714050b02150104c00d50011881400141c04856049064000c608c2038004003c180c1601070040d081d248800c0a55040d5000b94501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 313760314 1250 313759064 313759067
    0xd0c08010602150108060402150c070e060310050408040e040c1a09010f030b0904080a14030a150f0e010b0a09050907030b030f070308120a180507180e03070212011e090209070807 78
    0x402d030441d50480300c1001001d40d80b109e040481c058441150801d1040400014901031700e500e60501600041d019078000074000c89083c0c040c1d84007a1401070113082d0400040102c0ba101600c4290070a12a60720703a80459620400d40c3c1c0c030344051080a0841040019000400d580c00c07240b900d03542d03009401c041c0464200600003c82008004102034240003001400305115481003aa400103403e1001e8001c0d101d0404003002d800801ca2118505c2150391000e1010aa10400e2420041180e007882e001c50364680c01c03c1f603c108507400a020031824000304c1034003c1010f40d541c1c89524801c04076540c002594138882010103180c281081107011300758122540500104140500311404000d000454000c10345545892000030007885041b0340506014030107503010880d010881904031110181148105143c10046004a070420710646015500c1041008e0060030a4038140518000880002030003030070310313005113000040c840c00c4101e0f8969035122030001c62030429100c0341c00020f140b07030103512403030410070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 313761564 1250 313760314 313760323
    0xf010b09040f0e0d0e0a0e060a06120b04090b0613050c0d02090a030f0506011a03070905040536010f0e060601110307060204030c06020d02010902100e060d0c08010602150108 76
    0x5141d00071616040c0360307580b0056640001c10f0a219210480750700c0750200703c0013030417040120034061040c622402e00051800e07040c0902d07070040300024542a0303160325000c1c0a49402080c1c0ca507981c0300540300c1a000440c1e54541c41010806030242c841c50446141200030000c0c0b070030b64011018040c500e8102031154503502001960039035a500600180d940442100140350406c0715031008000d580b1101d401410800081103442c125035101d08840b80c000c042d6240c0d20380500084450358009000030108000620700781e00080d0b00151341c41c0e4520a442c05030000046400080d11038108002d084c551640902013007442045803c00c9954000c01001c0e424014940c0c8a40015000078100f08000c0d0801a20344410b10440b03002d5035100c5070856403140e8130316202c1600b11340b40c41060007501035402540e80203030040c05504207a5a008000c03501c407040ca41400c1c0e640c0c515000c045a0455000d00151001404a2049881501c0c0708c1d1103401c21580b504100903d044040070070901d22015900040242201c00036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 313762814 1250 313761564 313761577
    0x309030f050c03070525080c090730020a0f020a02061801020712050a0c0602030313030f031e0e010b06041a0f09030613120c0c05130207080a080f0f010b 67
    0x15245a590b2030b5002140e02d140a043e07000b41045c01160744808144100c00001202083d0b00e820342548560b035202c0c40758071011b58001403a04070002d540019000762144c0b0f1010041c444030407036051580b80780c01c0e44c0201e2010101c0c40b13101c40e0b0344c00281241a19040700c45240c0a811510040401010b1a404103901d4040c00440407002c0c58a250780b240240e00900550004c0d180988180c0644505401c00c155604840d2409580303185030b400700424543d1020040380c0c41806054032042c00c982150b035045030b0f60414454080205540c41202d9004500c0e1207c080c6041d0704a8180032801e11004000741d402c4031000c04005e449644200000c2100350a1841030602d00600f59495a0b19602c50b00f613418028801c0300c004aa140c002d1108100c81d00c1c0100c841201250300803413080311451405203003550305818800f8040c0418454034010080c03403410205204440509400243c01c03c3d90f0346c0e580c41080c0d000030001c500840c00841c01c000da03d01030022000d07403190301e8040322207035545000b502800358460742 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 313764064 1250 313762814 313762817
    0x111909030204240312050705030f0319091a0a1805010509070b2502030109020d1b0602010c050412170712080c120a05100e070201020d0b040903080708090f060705030403030c0309030f 80
    0x541740c4590084060350b0070540c100e0b0640c0c1d521034040110980c42e61048404298216140c02c00c03120f0220984107005096501400c0c0a10288030301590000c0f500000f01389003031843e00c505c84607419003810b00a003010148140000704180c14500c25041c240394250b00841110032051050b200295203035107139690602c01e003407000ca443c00042d00109024207601000030390020002d80502041002e0803070640c00c1d091503240d0044010f61105c5080b8203076455201c0240018000b8002440008040511620440e21400381d040c0c810307200d41054a42070f00100c02c00e5a80c80035483d01070b56030301d800241050340401c098070070502e40210f202c52091040800340000103150341d101c001a400c48482ca108002034141403c12581030702c0d02c8140213010707510407880c09200505100041c2103505150043c11b40b2290f140e244e1851994651004441c68580100169000d20885900380c0200308240041805919141c2c0d41c5030b41c07451309080c003405640f4a1030500d42018900410840825800b40c1c9070810240329 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 313765314 1250 313764064 313764083
    0x108040302010f0207150506010807050d1d01050f010806090d02060f072105060102070e010302091305030d0204030c050108011d010603050702251d07121119090302042403 75
    0x114241240108443d481c92600d080c8002650028002129519a5061141d1200344915581c1070011030b0045416290740e4082401031042a01c4400359030050116040e0440f4248000091456600d0039034005a840c024074148080050000c0d0f48140401c0c0d44c083c450600a010544a0180003540c40000030802004a1019404545214170948a0784201c0c08240c0801c09505000c81448000784010f0310018058071440c0300000c1c042c504066103074101e98006008403800d079600c52002003c020b10800031641c9000406c201c41900984d0701c06000a18010030f240d4003518102000503054000680002208006444010b11851032281d14035064807490301e00402c1c10b80302c1d0320040c1d24006071846920341d1041c140c500240c4442e11520900221101100c100d00304183c03200030b00701050019141007002943c00340300d403020038800c0e810030400c083d00800d0280ca00b00ca403000c49210600c424000100003198190100103504c0c01d40181282c0d04449512101e1b0007007130a100e0020042988002483c40c511f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 313766564 1250 313765314 313765321
    0x1703030c09011d030f06010807050307140d0303060315060302040507034803021309020403021e060913051b0c0a020904060e03030c0a181208030a060f060309050c0f0a03020108 77
    0x490072071486031014094211880301041742d108548079002401200c180c0e20468000150900e000100b20040b40d8922400d00c07120751003002031000941f0700001c01d0b8140b5456000c00000a0300d113280200207902103c0c030008010b403d40c410002a44c1000e0001d02c00c05060136842944a01081c40504405003601001072003101c04110a046544000700400c0910f61001c00d0302031301c181c0640083c2244210b00c02014003958880381548224011400003a400200c080c4402540c40140452001c0742800100110304141940700040e64240c40141454006a155030610074560300103e00c094842e07071030a60541c14680781d4071103140e46a025a0000c0c0c81070200c04041018000c2d41d5102d05420035245090340d55034600b000e5103a00070f80c889102c1c44e00192100c508112554108171020302070300e11000c03d810158a003901e5200d02608060f0404409a548910004074100020703540780c010812900d0115042d00d0b50b041c030b00d09000d4440d909500589100d004440550f66102c4002c050329030908040b0b80985 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 313767814 1250 313766564 313766597
    0x20108150d1704050a080a08030c0f0403050a0f02010f03050c1608090301052503051009020906160c05011206030c0302210607180b13090c0c1b1703030c0901 69
    0x7a030160701500c05201180c1041059003000c0050054810684400d01030554a651180e0b40f440322000250104809002103000c051048000301006046505035506154a0303850322820500401002c036400065035002c1002c65070030030004c0041c0302080c10204140e1a1140e03507070b5202c1c480e40b00d00d8000c05289804640410585030152180007901400800c0301d8030b0f20202703c4111440e03000700700e801d4000f4968961300c094840c5c002d044c441e04000c01c0fa48030b89450000590044d4000407200d640c0b190040c03000940c83c01b40060281c003040e0203a44142c0c00107143c0800545401c1030315206082e040c0c2094400c0c03000c11034405001080700d5064a03818500075061284030000480d0111840e468041c14040c0316955600c0100810040c0c0105503882c666a62003007006881d2041d030047e500d002900143c00c0009102d20341c0b0801c042d8110707041000e01141c0c07a0352607000421841e1a041c5510120880a11a40744202c1c1aa04240c2e8420700a510b941030009442c0c2c0750b802024041410010701030780281240c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 313769064 1250 313767814 313767829
    0x90311010504121a090d09030204090f080712030b0607020102070e0c0f0f220608161101020a0207080115050109090b0a0f090b030c01021903050f130308070b07090302010815 76
    0x40280440c3c00e814030080b860061503002505941c100080c00080224200c2031005c110f80611810507180c00f11110320715400d100142c103110109880c0c404442c001d0801140303514008240302403040d814549001d40307850004c1d00703c44001c43c1941c0102c2050001c200140d800051031420345429205401c000d03070391041c9520a9100300c614885012a011909080500091000d09242400803100042e4400601c5001140c03e90a03c00d14000615000c00716066590b03080081d6542c00c070901e0607007440039020000030300b07a90180303801c280142d2010004000045003841101d540c0f09402c05015440b526003000280303e80710b80c0c02115030a950345e25401e100d55035005061002030282080c48128599070700f400900400340095070300d01034021010040059880442c0da03540e65503e06c404540380ca20152400c640c1500084129640003000b000034610050300c4211074001144901105a40d500c2680341c0100c544101a106074140034014806000603030300041e01581c01605200380c0d00c42d0100500c0064000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 313770314 1250 313769064 313769069
    0x21070203062a0d0f0c050717070b0c0d0e1b030705030703110112020c0a060f0b0406080d0c08120f0702120c0613050a12050306030705010806090402060313210305060f01090311010504 80
    0x4d624003000302c0096604100035182840c000d00b20399890040d0b01c0024100ba110361a0003c080d40101d030f00061051618201518410014000018a000c00d889182e4a00354056210120449000d000a0182e24081040101510700ac0c0c0203441d556141d683d900c4090300108000710706000c6014000280ca42079541036620b81151841200c40082240c14100000e19030684600c0301241440c825021b81c2c242030040400b210782d9040241b008020310081221000f40510341164005410094107615110300d60320940521440750350944036041604001e407a00c9291662140407040910103080c00540220740c091380407040400009200d4068900103090000c540300060032001b88542000b0340c2070b03100e00694450b81c420340c00c54141c1a12200151402042260b1082d4800c2d182c500240c0141071050240d50024221507400e800105180c0e240064000700340c0c241c01005417144825a451941030040541200c1c081d1465550301c01d8060000300b82c00243e0101415035800340b1580340440c5d12410890f0b00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 313771564 1250 313770314 313770341
    0x1308160803180d05030c100507260c0915030108030912071505161509050717060a0b0607020901081f0e06131407030312050906220521070203062a0d 65
    0x11106030f81385c7d16600400090300e2103000a41500184030b0b2103840c840c00059011100300100b8030342c0c1c3c1d5090105500d42e1110071070326000400450b11740c5601501c000a90302a08000020310b803200444001d02c8620f49003107035102400c1d4010300c03080200e0340092600d84a4400340e40381460395102282ea0702d2580d0a10980005c084a083c0c06140c41c140b0303810380c03120190500c0b46091354034860380d91845000324008247c103c40d55420010100d51107203456441005504005084e203401c0408070340004110f036000b40d21400700f03900964414007001c0d82c41c0d00c207055100c2c90329034104141981c003c2e003250b0701c41000b0300864132120195944400d1241c4201c40180442d060001c40c1c1c2125140e01e40100010b200614144105003400d001c600c060401250700f034840d55800ea02c0700c01680c85142d100c25200101c200554050045101da02110844090540d95a500030300000e40d076940648141031030200c000300089120048400d01c0d4941e4001c54000720110403403861440d445a1108000800030050f1400504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 313772814 1250 313771564 313771573
    0x6070f0302011b050415080604090c03030903110306040b07080717070c0516080a02010f03060503060c0702090f240f0a09060612020301140103111308160803180d05030c 74
    0x1800c26905400c54010300400c2000c011900410302002e039068000c900070604811074800a60140e00d2003507149680c030902c0280081201340250302d84644040b4641c2040d000510340d000140244804601c16415028042d03000b09220302d040e0700c2e83d018003800540341000304000c0101041680313200e4140d480c104080b120100a8a08003000007401c000441c0800300c070b450248190703103103404168101c00300032100d600020b440c0b00121940111000001e01c1c1d490800e06544001c086501c1d1408c0110701c1c031031101200388a44d40e9050340104440d1100041016000c601c3c00e00c200310581c0326041c3e6000f0403581d260300da040c042c480540000c001d08541c02c0d01c6900707c102202c00003505042508180102ca4075519141d9028042c44038200517407200f40601040c1000710f070907000723065200b60300c40031070350003001206c1e41008881c03411410700c400f065200d0101c0340d118060840c40340384041003c03401000000b00031468518485000000d043c203102210340f05100154074034003404420b1045030079105d854403d80c8c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 313774064 1250 313772814 313772843
    0x9130314031509250315031106071407051201090c06031d0102120a0e0d050a05030408041205100606020c011b1103060910050606121504020c0a0503040503150402130207020607 77
    0x4204d40c018442062120480d03042048540b540648621440b0403085082c1c100f40a043d80c4441404c550f40d6a00c032a0040420030040012031841d107480300e03000da40c81014040545c0b505041225001400a03940c12503454241102d00042e9084840d0342111514240072074113000501c0085036046440d948a081940002250303e103c691000004e80f2810380300b20100403910b0048492540c404d04002841c1c04940100034200095000e140a964001e1203150003628080d100c44511004c0300040000300d0301a4030a03240c140140c6401e015902c041d04e103d100a008525042000909044610742c0f00b8514040c08181c0005212075503071100c602074005400c6855906001c00d60b6035a600f070001d4849400380c41e080108000b0b140400841e40e501e1034100c1100741c0341d15440b02c0310a0b4008044503c0380d120350300b041002402c0c0c5052081206150040003c1d40d1107c0c940303801c0c182031603610000c20a488659800300710040c0d13075503c01c15902c80c01080f00182c8400f454408180c0600c52110050030800444e040e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 313775314 1250 313774064 313774081
    0x30c081b1b03040f140a0e0f011406070c17060a020f161104060e01090501090903080412020708060703090b0603070f0e0403020a0b0c09040c03050606031605070c06020c09130314031509 81
    0x545070030070140c5a83c1b074519034500c40001700890a842900e40c6000c00350040041c411203d40140f22000001e00580c5041c0160ba81c0141a00055210240494843c40c1d0205010707014010745622181c00902585003070383c2042c0d200800d2041c0c40c007008803540301c0c84482c1c00340310800014030121500a031003000b4140c0c803822150040c03407007440703400801402e26001190500180c0110400070703505803640803171600e850303888120b416000c1004000b140306114000508076410021280035901c143c50000e0400c2d1705080c03011a03460010441802544000c07400c1014040010500045981d00c0c900e9007100d1311a031a0803403c100103107030b01800940868052024580c030101c000c0281c203208480403c03d2400180301a01583d074100d41c9113a0002d030610011300303444448003200c111402d040c500395103001e4440d594240c4815098010a0050344080a540030904000304810f41000103003885121800c0b003a85d0003000098603c50403803045102101280c0001c454110220301c10b107000b4125486440c0c200c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 313776564 1250 313775314 313775339
    0xe070302041701020931090809040f0513030521040302011b0206040f02040b1c060b030114010807031b1d0601030515150304020d0f03030c081b1b03040f 67
    0x19042a00d1002d01c15000001c2c2c1482250810b54001e040d520324070141c8034040441d25038001079801e00e4903956108248405440c41200951817040c0300f030a4a50380e100c402d120495103c01c4c80564250314003c00c3c068100c104c0703081001201da0514201e590342c0e070010030306800c00c6041010310691041060900007016010740082d4400c080ca1a0761545904800c00101d07039540058078054410801080d628000d030a054000040442024250301016840300e85010300035141140150ba919a44080100340342c9401c0c00351000c4454400d01d802c2c1994181818103440c1c01072440018503075039030900700c400078140e04242e581c010590325020311040701140020b0040385004540640c0000d16010018840a1200401c020a4074002c0c20f4092001e282e200101c0443c3c1c00600700f80d0340302908480450000380d46030b000f005000c0c4030341d501090ba081c500b0000b40c0b502502801000300780034050000c04500c4c41c0c885c182c4543d114540c51243e00d20070b00103101403c5205607040303034035138800d10344010800c10070200c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 313777814 1250 313776564 313776569
    0x1805070e100b0a0c0201020c06280903170901030b060408030a0e010f0e060c01060e0c040905160c03080709031b050a17070302061804020d06150f0e12070e07030204 72
    0x4004294a580754000d06a415416000301052100e0501803580351902c034940c600309140c03060045030b8602101000241c0c0350340280035a1189031a5850f07107900b00b1085480e030340c2d42400b80350800c510114150b50355640c1a000045100606c14000f24616065070b205c1e8014000000c0040c00160384c5644072000302c1d44036400340b540b4101003031400b40c150080754443e043d24003a04e4026030395902e88500032010440d15500081d1000184c2d074a596000c50710b5103104951501405c100c40c0d0b065500c1345000308010035941c00610420700c0c0b40da142405690250043d16042120380e0601e0102c180740d995002c1a80e004005410140038a42c004000d401200c1c4066a540113442003203440e5645c069440c6400c900405080b00620060b4020020410050500781c01400350041500c81c090094618a000f20701240c110044003009036458150030840d20107a2400401491260f140004182c080a03001600b0326250b000740390301070800722803400091801448032001400d044440f00c5050b04042d00c0080c080d400c2030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 313779064 1250 313777814 313777829
    0x6071b061e05060906060306121c05070b01060504030b06060c0a1a01050f12100506060d0c0f1209050c150d0612050610060f0e0120060a11041208030703180507 70
    0x402042c0309282c5013a0651007041d0040c200761540d9504018085806e80405400c0c51a2040c13800000e07814a0800d5803a5403091a6500d1a488905900b00480d8804040e4400c40500c80e0412050001c91101294a54020340684001d907075865140c0445160007281040680051184070715600e14106034001103041b140d044a0200509054204202480d4060400c1101a50011843d0680882190440c0742d0009008081504042c2d0a50000c01070314001c04030440020f07910382c0c00c0102d140d000700712003845540000701044503281325943c0c1517592603a407182038410b4942e0318505100e160000d0440c0c01ca081032207400c0c440280d4540c030381d4903000100541110140201070016041d602e08180140c12504d0a40e9203003200c09034494161400b040f4415954104030410340603104a0f42075100c00d80c0710705640c900a20251400c000305108032500302e00800080300040100b00410344031606450842c507009810240c2c2c030784a0f07070800c0d4010704c1410005460740307103944c180f01c09002c0049200003c44000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 313780314 1250 313779064 313779071
    0x1503050d030504210509040b010e030a080c0114090c04091b03060b10020105060901030b0903070b090d020105060f10030f06030c0e0703180f080a1202040b09120a030206071b061e 78
    0xca2000841e01c007000c4c000030000030300a10000c85980f605812039200140c040c10480c04019201010908008a0341e0702034880c0c0c4400180210200700074400d81d40d00e08400710520f240c42c10141815510340e0300060200d17100d19114480c100c00e0108100441d150700380d4402e0103446595482c0303007600c081d20302c8010301c0d44940c0301c0d0700c0c604441900601500c0e10a034402040da021a80c299910000e074100007400041c458413042c000c440000d810416001d0049440310000c004800440710000d00b540e8000b00051b0103590340c2c032000956520ba054202400d9001801c012403125040c03500d000c0188081d80c070182c00c3c000b00340000203206622805e158024a100c0d40e007031118025050750300b8800d02e40004000c1c1420030300c489107000325041d0000352202218503d008406092000c0c042010b0341c0254015a501389030000e1045494649142c900407024000b00185c820241907840107900c3e02002030550b011311981300e035200000079031080b000c0000d039400700003041510596101c10b21074515056080c03100700d01c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 313781564 1250 313780314 313780343
    0x51303080a152c040f02090a200903160b0318010b03010c0c0b0a0e19060216050d12110d050c0c0d0504260a060c0512040b101a0406031503050d030504 66
    0x160403e0540c815508400d000300710060542c248100004000e00d00040c441c0e036081c40c0000c04031800d4000090003c2c11802c99110004202010304050b00481003003030006900004000ba01006e00c19281d0294224178105803c4440e1840113014003800081107034035501c1e02c40404e54064106904400c9980540a10b911584d03030500702d103013214080c024654942d03001e11201900d4452001904410a00c0741001505101d0440e1000b094042150412503c9421540102800b0b03984410004070207038228030306100c80e0a940750003035502c3c40340c414400410b5403103400103900039400d2030440780240d40074000c0f104420645003004126400074003a5251042e4826136040c544c0d04c1c1d0b04042c030b50700c86070440030300340c450075a541e50320041c03415064080910109011446500080700f040c0e0784154000c0246800915014003046850300d4103400800b5450400444a6030700c1d22402c2c282c0b02503420798103002481a031504900600100b09900c002c1c201c1c440c914001e0f50460f8103070003e0f4003036403080781d1102190a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 313782814 1250 313781564 313781639
    0x7021e0111161406040c0308030c1204060e190c260d0201050108060a0c08130213061814040b180a080a030e0c1203070209061201061d060103051303080a15 68
    0x11130a60b805462404007640c10700c00f1603811401140c010a9005a4038a040e0203421682d02c403540455050761401d560f554851805002808250074000740340e0403095400c1000d070744420528802d4001c401c5019100c6071300256024a555070305440d49051002c0b111030304c07180c04000340a001d09014041c071600410022402080d00d83c062100743e01e45507140c1d0078003070351803c00c4800c400c00f4010050741d02005000400840c00310f80d20540b0060400c401d41c0201c0d0210680c0001e044c0c0c3c2e0040b0304100e5411405041001040744001ca994100c0205c031041030007494503480c2c1303071700d410406036000d01034a4002409202c5640c0603844240e0118800c0e040d0390700c0c991506c041002d55408141512015041041008018a81203400c0c03076004200500c0210707200d900a0540c0d00f1915175070403c001c2d100d40804000c1565001c3c01d940c83c2d010b482440c06024504d0a14041c03000b030406040001c080c40703140001301c1c20007004c64200c45203005c901e11100300031640d0340c0007404200c2c804440910550f80400101d1030002e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 313784064 1250 313782814 313782823
    0x6070f03170402010c12090f080106230913142407090b0307180305010c0c020108010b160602030a1b09410d12050403060f020307021e01111614 63
    0x2ca4050312403441c01d58541d116500350380b02d404410400c0000d002c0001c01c0d0719071041130b503401902040b00002409810440d040c2400d07100d1046811211241c10300044003030b6600c060b04c503401151400312420700005494a0402a000040c680045014441d950440443c00030808064031544040007140b58907002d209450040160056540e0030320100000350090b03006103001424102c2c4031580c0da0755140d807a240c09003155081210100001c442ea44402c041d5030740400414050611b40c55001e19200e8820008c0304600307643c2100070566900440003071303095a1503510030500c804c1d0702d01e01a0508541c101c0000d1074503415018684840c0d40700341000c5020103144a0000451000000c4900070360002030050221081641031280d11141110105000034001d40d030079071044000b610f4203500d403800c2d494008242e54021680d02c1c0c4640c814810000c2c03041e400030391040e0643c0020519410040114513540c01341924000350802c1081c00589000084861810428107e0003041c469004c00c06090b01141c46 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 313785314 1250 313784064 313784071
    0x220509090c010f0e1801050316060e10030f050403080702060c0c151f060f02010609050601021b0a0504111305120d180906170f06061e03070506070f0317 67
    0x3903600040499030310754042c0e40603003850460340c28540d44000e94000010003031550314400c45480b40740b00d0010080307030604000c00b4a4148850307042d0440a81003040042c0300e001c00301d040740e00c64402d00702e00585442c000d034840301540c000310b44103220701c0c034003410047c004502c1565020014415140000c108030300041c1034403020701110010b048008404c20204860b10409007031703501822148102c0c580340c1c1d081c082e12440100303109c0e1601c80301c18800c0e03000a401c4402951185d0358450801040140c40eaa01007250380c07450a11590041c0344110380030210348000c043e030300202d410514015211130f0f03107100750004c2c0107079080d1119107110300d81c0c4403c288000c1c0b40401c3c80300b0301142d011001f00c9400502400803c000c18089144603c202d075a249040d4042e548a0f501c420b20441d1500311051900006104182280c44480018426400c01c1c4020401902280d001180f00c490b0502c01c030485a5005d0108800900340148515101c001c6d230b0078944215604080c086001c21042d602c42d4065644004a4910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 313786564 1250 313785314 313785331
    0x19170f0c09010806040e0304060206150d120507050a060203100302040f0c080f0c0c07030309090c0206070e040b0a05040c090503060703110f0306030c0a09021b03070503090f0105040b220509 83
    0x145080c03007005540030440070f4811a407198031482d0a40460390100044c4c80180b0035503001302040d00f4403240845040d01002031b020301a0701400c034200049000200b944203001745502c3d089a8610450406c5030504200803c01084540000103208400e4020803a050030340c0d000301c0d400c101108407074600204840c02442281c010601d04400100b080620349551039203c0c0a03800c0480c94501589102c1b4103003681c1d40c004070301180840c8c6090001d109035201d40310300981c80c0e00042c0303a1402d0803c0040d01c00801d003c0041c6c45607484104103030080d2104040900106406403090101c10140807015250045074041c181c00303403142c0d00000d42034a00c6800b036403d020b00308003035041c90114004c2884842e81c1c40103100940500c02d810384201583c40740a469001000c003c000161110409080034580f10070950098890f507100b40600d0b00031500100480740e0309a012a25005004030a20069801d401140e0215100143c00316031075100d01c141e00c02c10004403d0012250500d035449208003d03010800707407070244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 313787814 1250 313786564 313786567
    0x30601060f110f25030609060f050c0c120c1f09110607080a0810050d06140a0902090a051f090b010806060f0d0903110a0f06050603190803070519170f0c 67
    0x103000c0b4840c5184142110103001503c00344945a1b01d400701940d200c8001180d07842d070303120040c01e000b10715803241c1e035000429007440c2c614201000200660710481514005101c4400198012001c0410401b01087c5c90f01054443c150740031080780c0000515038240c0541d824540d00015a20619200f0110364489a00c200301c28240703219414122131440c401081c4450188204d0f80c0801c03180e68003419448582c0c864440401c0781c04080d070070801d2190f0003501480905080c10100c500503903e2910240d803210240c440021a9600e40340c08200c1c070011035001c02107424801c80c002c00d00c9030030741d040211240401e8030341c10002d444181c103000341c921a1a007401502c1d4414030042190369426004102c000d8013925002d05640c0c40c00070b4450400c03461913800c4501c034800c0f0300c4150410a050090952156040300030b429050480f4a00b1981484080c10044c04110000300180105001e01e050700c040c200360302c00b0403c0000c00407101800e11400c04041c1d441021030200026882c60100d44407501c590750061506 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 313789064 1250 313787814 313787833
    0x3020c12160816030e040509030f030c040302040c02060a0c1b0206090d080301170f0f151f0603020d0f1104140105120a021b0303040b01150c02030601060f110f 70
    0x14032a0481c00c002084020281c10200c04506040098150740ba01000d0b510401c012a160180c9050700582c0018000c0d4140020410300800210648014814000803144e403680c036020142514403139900300070342c010b142c180350000e00380c0e000401522801c0500c0c3e04110070500c00d0030948815a106040001040701100507000606042014044210014007185008159030707940d800aa0400d0300710201c08401c03125070314101502002141400c90701000642a081034520000780c58074030b0501500503810381c0b0700205290130348840f05d0003440741d140c100e0301844039102d81d0028081d42c040f102c07101026040240d0b048040800b84035503075400c00c0d0400703401d140a19000803054001021007070181402000d2050561280d180203041d4030403044d02c07030010380e00d200e40c07240e804040040102c44d5030568400c1c000c110010306842e4500d81500c2d40128810384441c1c60f50400c0301d0112080718000d406000f04000024980e8028646e08040081611354101001013030b00c0490b0788885078680d8148031fa000b80d840c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 313790314 1250 313789064 313789093
    0xc0f020f060720010324120503040e04030201091a0601120e031c2a09090b040905010f06030303050105060a120b01110f03040312170a0f0f1d0601050103020c 69
    0x4012200320301030180c034200800d43d283c01c4603154142d041c11100402190244001d036078148190325860440c0a0000d845089100c414105c0c503015000e11440c800b0702c0d00800d03090200c02c000355002007400350300c23a07a420b20b01458008e004c0c01d454401144c8089198004116088000450621440c01a502d1852185203000312102501500952052500040000c5180a812071102c0c00080e0f10107103020a1170a5042d050301c0c0c41d05081100d44008142491240554541c0001001d0031151840408281160788800041c001c1006140c000c10171340c6001c4071000d48410720b803c00d000311782c0030303031001c10a60382d03990103005107841030811210002c4c1e4005070f80046c00095034842140c04d941894400715200c20840014540312040040501d182d01c04601042000041e840c040e0001c0343c3da24210130700040c9030300c9254106a028000d840495121072061000c0c035003540c05550000c5c0d207440144400d200300000e8514a6030803075072580640c0903c8001041c0c5500900131104d1101e103d00c010700a07040f44449 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 313791564 1250 313790314 313790329
    0x607030e010f0908070e061002010203190905010b09041a07092601200d11090618010c0602190e0301020f1210050d0305040602060709051c0606030804080705100c0f02 73
    0x11090910203100c0c004202c807101004170001034181c040f07202c54a410f06604000d080c400040c000700840e8010010000c244411904241400c0c0305000045000241490f046014201d0a0280f9812948a80410041c05001d05422458041e075003041c10058440c10000c0754402c0080c0600182010f00000010f4441031044080e40042c0035079000080f42c400ea8490203401a003010000303403c0400c04038004200307003805d200d0b200c00081a03100e03040c501400c210105009015450000d020394010044000241c0d019280b005411f1742e21900171980c60003648060018a00300f14006400100007000032141428144219402032110a00c11418100304109110b81c07010010045ca2010703248010008081d200c14140c0200c6510036100c131a201e44c2030140003803800b070b00101050108010700108210b075403240306c00e0140b0a490040c21082500c0c050501c01c01070012640300038200c050008002030203542c086688416640304071508d000c03201c82c0744003c03985282d9107000a08200c40400d20317500140703850b03030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 313792814 1250 313791564 313791587
    0x20c060d0906020c030310060f140a1106010603021c09020a030b040206041203020601052b03030b1909050604051f140f310e030d051e01090b0f0607030e01 68
    0x59010070101c025980c1d20099070082044050b4a900110612aa01e0b810b000341c000a0462468444030154007060f00929a245110407401c40000008004030036034455004403c0d50200903003100c2c40c551b5140d10060081d40315001035541c40c02014821056004680030301003155400805002c103480c25625542009800075104036480f030f2080000190400008181c030260034001c0e0040d240c00d41c501300510420308000000141c044480046060007844d20380c030790054a641626001480a01c4c24000c6803c000c00c1c0c908000806110210000d80841c044e044584141e100351810f1240d0b031245d90109580080c0b40b0315101c4281207800c403c0c8070fa4082000d030941194001800030440220756004503400004100c80308146420040c031750541000101c040020104400c1810840042003c00c40740c0c903030240c45d003500785041d1150003141e4013003400b01150f03c40850711020a4015627541110308000c1902c512001d0040861404070031140c5050001e03200c08a426840f50074840c604c82004490159004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 313794064 1250 313792814 313792837
    0xc08010c180b28080103020a050130061214010e030313320102030a0b03030910140c06010e090f01060501080606092101090201021501060915111c110c01020c06 70
    0xb102901ca100425142d0103e402e00d648404800e54194014842851002d822403814800305101042c1d40700d031030003180600c6089007448102d4201d80100f1102c00340155500220300c000c0802c410a041c05417440c01124441a500000c101900c030a00d0a96286d000403110018500b062410302004511454110f51850007843d903600a0304c120322101c0b21401c19416201d21660b0340c0401044100c4109111b00c07808203408a0085013021f064000103040500740c4142101003204507004820111240b009a0304030303e0242003902d01560310f82d145001c44040032901070100d1301c100aa1039008000c184a500c040d1901a981c000301aa610814080c0f1035006600c0d02d0f422845240c00d1025400c085c0b05503002d40b0200900109551001e07000082c50142c5d04d802e4000300b007500700010003005070004081e0046031013100c00003004000045c0d00785c0c0d1542e441340c03080240d800359040c503042950703107210551b043c0d03641c40d04c4a045500240e071100d42c0d600100580d5501690101c3c503c6c1d015841c020020340000b9080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 313795314 1250 313794064 313794097
    0x807030306050301110403020f0312040513020d02070305120705030c0a0f02031c0c0909050f0105280807030c080a0c260102182d010c030302040504090c08010c180b 72
    0x42c0c501080c00c480c940381c01e04400355408201801103181007d2801c1c080c0a049004000e40380110441d1301070f51151f031244074450041640d461440c14070980513581e0140700014111748481e0380303080241072a4852540904290190400680624029002e40380034002c0355803841d00b084000c580603520600002540c60a520080c010b0503807a5030b0401041003600383d20000419150001c910140000e225600042001410801001b41c4c03002d941d00810b04440301103510860101180d0341440d08030348000c1509804900c15032000c0750321100041e01008580c4505854100940ea582d07402e0344400e52450300818540082c0b401700045600300c102c402e0000289009242010107003405135003241d1099509802c40c0e0300300c1d00342c5080307454071020300c95200480340042c0c8046440d81d034a4480920042140c1d60600000503503200030300d442035050350081c20020b002004508030505150302e040b03032980700d8503490703608248841071850f00c2a0050b02c0615040810030100b5400c0c4104210b407a001012000440da55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 313796564 1250 313795314 313795319
    0x32604140409021c0f0b09010b1e0a0302060f03040b15030307030e0a122409050703150216060506040c030b030703110411040b030a060b0f040e090a06050a020d1404030c0807030306 79
    0x10340d169042901e0300c1000241700781001c0389441640480001e04135400c0b43d1501d03c0c5d102c4d480c0c64100b0140928407260250600c00840074001500d6444c4941001c0c2d0400743c0401d01101ca8007800c401940550f001d034075041100d40d1100e0715200d511a00d21005900b6800900c080800240250805114070100a10740c603141500c40d900d001e109030750b95006840c8445101841c011240040405803141e1164680074003801d00f140d1a10303a940e90b210320000f0b0501100d10346503c144006030307040c0c54101101c00d01d040a080418100749010305001d42c0c0c041c0c46149410040d082142c0030340700e00b2205d83c4010f8007808006245450b18011303d116600c040760001d031940c0f5498402d6081c1d07001080541041e440340ea440e404e044040d5012610250011b085405c0f04200c9800c00141c914162004c480c09000c83d03601c0c5980d4400c80906116860b50020320041c142010b10000d080c40c4c2e0050150f02c07141880070000108450b0702101c211030162409004150744000070000b280704180100b101c54042d08010a800d603 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 313797814 1250 313796564 313796599
    0x7090302040f090b1b2512080405011a131a0904210302040b0d0b010e0d03030f0b0d0c05121e100e03031b0c07080703260414040902 58
    0x48035102e03140035250f950352050701008800603400c0d41217021948620440c4940b85650451885454100546c20220700040d20140340d02402e0386c1402c07580200c880907491030001d006450b400b015102101e140d42461001901800071552140342d40030001c016000141401000e03200a00441100c01d9171807141d001c880740d86888030305819024601c03405030350307148452002c4420f0007a030070200580100360040008100e0351500f5011384203500030721b90000920080a4006803250740c400507546400000803070f410400c1c580c0590051200e40c802c1141400f44850700c0c401c00107c100c3c40e001c000c006001500050080c1e042408801424502e41c60480f820046810724023000003c01c400d0505481e0300c181019207158107140581007006840b00011070950134280d000c1c0040f003a04001407141c0d07120110307220100003400c000300c80041c0289001d03100826241e061109200c4095010070a40d410b031017010701b4000540c101100c08841281c00543d184801c06010407024150025082e40d100300081710450040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 313799064 1250 313797814 313797821
    0x3050f0d0921022403011409060d03020705151b0706030c05041a030403030603080c0604021c1a100b0c0325020d0f020402040b03010b120906070203070201080c1209030408010623090709030204 84
    0x83c4000b451040410300d82c0c10401c1ba808800602150203544ae64016600181d00001c988050b0780ac01c540c150a4220703c19242e0400780a00195240e04e000c001c040310100702c0d400301c0c101c0c00381c5916039824803d4802d04142900c1c0d500c6148980c1c0d0810b004a03800000000b07011014582061180c035000c1022a507035181d41c111074000408a45c415040307a03040c4800c620303110155210072000140c0f50304008104d5100d1002c0700755217040a480c08950500050007203034054443d14013802c41440c0d0542c5941000e908183c2e250005c11661000b550308075401c01d182c4a83d0500b240001d40d0051603040c504580b5031798401490075490782280c00c079401780b002041003060170010394064003003040c40720b460704030400100e100d01c807000d44002050b070441806d0010455000c01111100c94080c02c024685031200e0031062018828078420714954440142401800f103404001401200c8408009202e00c90301d8443c45200e00c01c1210354111040340381c002c585004d00380004d405900c00418100f070030340c00d5079039000b04054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 313800314 1250 313799064 313799069
    0x1050604180216080a08100e010e15030f01060807030213020c0601122f1309020901051005160c081b10030b01020f070b0c0706090308030601110703050f0d092102240301 74
    0x3050711b00080041d4202c0030049500102a00b10a03803160f940b40c00002c842102e0b010b400c86d071900050780300d040c04a48041160383c5041d10100300070040300317540d64842900c4400c1400b0892140b10003500101c1f540140d4000c0d5002880c1e020003419142c0d20303042d142001007030b80c4030302212182071840c841d40c51060800031a2004003050781054050444101c1000b99041e5500d800d201003034607014221b80581c56466507a0f05640007958151188980d408040d10a030003410740345888058400c00340c0c001c0001c07480c4400c04036444241211030894004850f24401c10f100b8070f1a0750421158460030799254400d4016030804c44060040e500d00d00641c44502e814043d042c2c105410785a800169161409801c00c070280c0184040d10f403420391399003582c1d0341820600c000b91010381004601100003880074401d104a038000c5a00000700d0f1803103900000c0c1c098481c0300801030180410850700c400a540c0c410003c0110782c10042840d426203180c140e13401c00c0304405804d1828014a448600c2c8440ca150545004501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 313801564 1250 313800314 313800317
    0xc0308030408040f05120d050904020d2a09060804030539100e060109020d1b08060307050a060225050a170705060405130c0c020409080c0601050604180216080a 70
    0xa550b400c02040741051130440c0d20441c051000c2c107442000c80c00b004103c0400d202da803441c00994071042000050301074015440d42040c404d20705064055880320a02610108078014000419181020001178455909a02c641d001240e00d000000d40024407410041c035580629250050200c6203040000c1e40c15203680d540383c10a5400300d00f07480005401001021680100700c1c0b018050b840c11410410f4481006204882c0c0f500d8000c121202851210340250036080501c424013a5110030284009018400903503155001c1c0c041c2d0980490641070028030340f030984a1540051040e1b014886591207001401d58059500032880c640200e160b0342c814103e0381c014000c50003440c3c0070301542c442042c01e0802e075074007451144508020400c142e4907400b4501a40b40818030001800000061080c0e03021148464020343c40361420244804105942c40640a03001000f4101d906036030300d078414003d181c4078030f000f140c0301c1c02c031034100c680c0003030083d60000c01d11204c00c0d044105010b070031590f801d04c803500001c00100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 313802814 1250 313801564 313801567
    0x30411010201231017030a110f0613140601050916030b150714010c140c030d1104030515010317131701200405010906110c090901051605070c120c0308030408 69
    0x50951000c07101d2000d0031740341070b90141143c015807610380e43c0d200c0c070341448041c014401c502844c01101444407000700c3d4100b1047d50454581035a0030300c00c0d0380e00365400300c855921070904080070000001350607040c0e40f07021707001c800c840e240c03104001c0d880c00502501c0400c1544454511115441c1c02c0011081010b503c1c8005866142c28584400b1109192020f5545a0b150072281e14000340d101084030504800307040780130b544d8080ca400e80b44c154494142c062080038200b1810b8507145651800500842c3e00803415200001c048400c0c50104001c00e110143c10001c00850f05411100701c603004004014008620b101e416070f460466800395070741d116010300b070f99543d124440700410340894aa81014207e00712945050300b0140007810b41c100030f003d00070410294102c1c5081901d41040a403404a4008200c5405854000b000501a10080340e007282210500d4404180d424094026520303555482294121954100700d0500040c400140d400d031141143c200300000460360300c000840c012405281c1c3d00d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 313804064 1250 313802814 313802821
    0xc24020408010e0c0907082d1e070e01030e03040e09010902030d11060c07112101060f0608040b06010314070f1e080a0b041b0903050106091103041101020123 69
    0x10781c01c40b400c2c0b8281280c1500042401c0d4071965803e80c0b0300b43c5c084001c1c180a0040d4603880042501034046c4050307a41807a03c0048001c2c200f22581e50410301c40d200100c000580e030548580e250780b20b41e00a9800102044d4450401101c03580030f80c2000700e03480000c2045909040e560655410180405c0d106240c150f5516100b400c250305041c00040c403400045d00380031503d440483d03200e50391260000d00c4c0e0410f004000c50014100715600d6401e9400e0300b00101408164414212031040f660b0000001624075880c0101c00218050075281450031250245c5541400f5980d42c5c45001c804400140941e04040d521076560003003103004244d00b4010040b50751441080b41d002e100240224081c1d60510344080318944000d43c02a0b84250b4240d804038208001103005812080898090401040d085d44080c0d01142c14130030302e40c0e0101c80c14089174042ca00922007a03070f4480c95101281d807c140221a005010000100400d40298606044880610000802042c403400300c4510b00e00110200e4601003401090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 313805314 1250 313804064 313804079
    0xb04030c0504180303051323010c141608070605070908070e010b0d0b0a03081917040201090621050c0306040506010806030316021f03050f090307030f0c240204 70
    0x100c034003800e019102000030000c41da091070250264441c00400305a00d41c0c0002c1d04108050401c20003055004001c002002d1030031198022103640407903640220341ca06552842540d22a80c00e4151640d0107400f22450710140c12400300d08003da054054032050340800400300017901e0b41c800c1038030600040d80c46c6501a410090401d040000a90160403140080801800b0301880001200d20b41311014000040c1110407402003903000b0060313030000d0440003000c1214100c88074800410300c100ea500c0e556962a032601207000790750440007601c02900164030007006001c0103019180f4424141e05928407840020103004c0103600395007003210b200380c1c04013001c0184019400c10340036203600300e0004d0130b003401e45140c03a1002c00e680c2d004e0b8500c00f001d0031030140040b000b552101c8424078030302801621705070842c110704840074024000603120240752000d00800164a80300110543c5c0401c0d0303043d90362007040c1a5040d001c655011618400350388010004208900c4184001129100c41081001c003603126480c0402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 313806564 1250 313805314 313805333
    0x1a2703190e0a090207110d060f0509060601020f0601030b0f1909030c03030c230a03060b0318070f0807060302180301020711010f0507050a080a020a020306010833060d050c0a0b0403 79
    0x1005410f02d00511030000060444c40c4008600001030f0380359a1000c401d800c140010702080362032048801d1510041c880551400309980b0302c2100e00381c003202d14420000200903a184400d2201624103003181b0080f960045a8602c0c0035080100c44645007107510004132250200c414030081180480d006082d0802010b8060241c03801502c0d0741e080441200b55180c0294012183c00c0d4001c00d044600000d140c00450300a9212501070042c07400855103d1805000700018210110300c00c00f0940304202d800142245906261015111000c01400326645000c00035000b039000f0468070814120326420042182c2c900744080c0c050a8040d80002c001048180005803030788901c1c0003001700f004000c004440100300000b42e41504907510840113951100150030807800c00e032040c58020b50600400000007100480000c1030b20060b440c07840407a02c01c003078418645090906a0b250300b0352020f1614001003e0b031030304d03a000320103050240742611071038160700000072041040c58000b0000c400e004079051042c441c2040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 313807814 1250 313806564 313806569
    0x60203190e030c12011e060315020703170403091518080d090302010e0d06060b040e09010203060d0f1109070207080c030f03070b070c0501020d05041a2703190e0a 71
    0x107024081848160209072201404403a0f64015012481c1c8050300700000d5010390355542c10000050002d5081c00d0960001d4002c51005076089140b200380280316403280d208603003d031541900c51141719480f4a0101402402c010130580601001010004215040710400d080b0052507960b0034080c8147c1c111a0741d80c4200d01c0c2c20044103030f030004919008064000207180c05503a02400c141c0c00e2030b0130b80800101d10200e0468020f06180c2400c9000403200a203c014000740c52200c600701040d50350303034a440c0d401c03800f00716081741e0b00c030303c00c0016a07007c10240a02d10030014024012000c864810b1000b04411030b0080c1e0305140140d100d40742c00c10000e4000d00000020340000c0300036010b440f06403a01075a0343c0c083c140e8060a00c444032004a8000d6000d84210b0010551180003075440d409080c805000130030080f50b05480d5811026150001a52008110380c4641d0201c2d403004c9002298a040340034410800f44410344501c001c20070000e5242001c410f9000d20001c5550381e0144036684d10900030740b03410380da = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 313809064 1250 313807814 313807817
    0x80a080f09060c07170c070807120309050904021c0506060102160f0323120406030c03050907060f0e030303090f07080f0c0609011e0e0f060903070b13080706020319 72
    0x30410700140d14008200c00b5040340502c1d4103281c40311101d08008490b0185007281900602d400600950130748804107007803045400c20002d4031006584c8030030151314030b42c00da03070001c0010700044800c0c8002d2501c0f00040381c0043c0064082c80f8258180c1c25590b10b60000003001350b4559010a04201c9903682c100000c1c60050300840640c81070170700d04108515641c4035800000c2c2043c8142810348050703141d4946902e5207400110842e5601d00d5050ba408126610034011580001e00381601c0301c200a000f4020103000340c1607400100940c03850000202d07400340c2140c1c40d500820444c1065021241d03070030805107000f81c0000000d000c94060003100540b800140b03501035440e5030800c400c8ca010b1803001180c6400d4400c0e083d6400c0c0e41d5a01d0890041303e41a110340d0106407401ea142943c420200d500000b0b650303031040181e40d501c06401704081001038a01400c4142c80c0c0c0350707021610910541110710082d2404560104685c01d4054a03611203a003080c0c1281c10510040c0c0c0040f86100c1c54011400d20310b00c480c00103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 313810314 1250 313809064 313809091
    0xd0504120903021525150c090311010c051e0721120f0207050a031208090705130b06130b0d0b0a06080c0c160f0f091a1905040207080a08 60
    0x1983c0c0802e208080300c1d82c01030781c0140c011400c8014048461030a500c00f0701184003500c03490405241041c80400801c080d45030315440c141403003c0090140701e4641c2520307001005000240c1202e0011960354200580071940b60044500c0c80540d07100c0041d52707094000c2d41c82d019104990070008000c10310440010076981c031890740b841c078a003c103000315864441d181e501d1424800007291132006a00c0c0c40700907400150881011013000040c440c49140228800c0300980e00d0800d1516001c00c01135440c045401070701c0d4410952a00e5061101190388000c1ea8910050005410000c11009000c1c0c000d441e640705021a03071000a003086a12000e10511424110441c0c41407125420600005c10241c00240444000d1200041b5018213040801c042c4007240740e82440b4900880d2500180ba103134040c54401c207002035003002c001085400c0580030301c15240d09038040031081c50a4150800c8400524614100511080610003086035203407800100002405090038568550b40c1e8035008000840041441ca4180d80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 313811564 1250 313810314 313810319
    0xc0a0810031a04050f0604060e0d0903150b030a020406140108010b1e0706020c1606090506030f070c1b03110f0616080d06050a0f080d021f021e0d05041209 68
    0x807100c1d0500c0e050001c142d03404405544030b2a10034501050f14041e00500d11405013008204644ca0304004004003070103080d60a440450403042ea8220042d0100410b400a941d030340003052911780c2c0c000507110800904481869800d034011500315100b0350440e41005c0d8124813050015604450340500401c1d00c0758266240021281110740c04014003c6c0300d82500c030002440206108080d015144003600e80c501713484400800c4980c02c1040c070314900c9480d0101c0e580110000d10340c94180d0980b8400d400b82c0700f55101c1681c81440498000101c00403ca40d02c1c500313070070b05660340c840b07089080010f584944d5078880540424410400d00c0c0d03554008241c4200d100304070103020344451900120360507910182c0e090f280c1411500940141220303070000c607080120707a003001a1300e00c568005e0303404990204094a0404a5000c800c82e2501a07014542c1200300c8400d0351900c821085038007c1c00210700042c4140c00803001c40c15040d2070784d44499004492107460b1000c1c0410b01000014141c0641d90300e080081f0004d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 313812814 1250 313811564 313811573
    0x80c06070317062206090506030109050601050f0d1a01080c0a12061508030c07090f020c070308280c150b030d030f0b100c050106120b060d0c0801050c0a081003 70
    0x18400080010385100c00b00420740c02d03140d009508180c0d2105603080344024201c81c0c4010300034101c9104072000c2d14240070110f0b04130700f0188034841005810070702030030542e070819003403210b02c9401d503600c26040764507100c0307010101c0c1c22240101d10704240c1c0381d284002540b50004041c50000c154120a12455040004001d40c1440700c11581c081540298042210484400c203038034542c2c55584869258040081c0103840b4610209502742581c0801400300f00c4481c80181c5d460490184410704d601c00c1e4405203003400811003c5004d08009240b1040081e050404001c1030402541442031040220b845160404100504c8400060a43c3e0400204021040d0b05c400040d9803000310201190a0582e02c1040d50380c046501d070090841e5103c050090741050400640c0141020400902610306500e01030011a2144c120f8481e11040c540044419846840701004c1024007422103a04980c1035681a5000500100071700400b4030a01900c0340083c4c49500b2903001500e614001881c205040b5840d030310a00008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 313814064 1250 313812814 313812827
    0x6050301150c1b0509010e040507030201110a02040c030e0d0c030914030123180706050f031504051501030e120304110112050a050411010305060f10180e01080c060703 73
    0x5030103001284449a0790100c06660304401580003801e0540152102100040704030f0070041115010f8414017990381c1d0701c42210a11030302c00c2d50024440d0700f251404101640c07045240c800203500d1042680e1507810356031b00043c21207030521a6103000c20b417910326003500d100c01800300d50a48031440c00d111403111295035000300100e8580c011041c40340700c41403000070942c400354050703d440398108107420104409200b0300d404800b0100c0d000c41c50101c4292142c03a8955001c41c5180441d50b05840b5241405030510084840381c03c0182035024505080c100303170b0f69540d00c501a0a000705081045800180b00c0380c0001070a84000d250000c010742d1000c5100301c0c10480e43d001326540540c100c9960180c035203e820040b51802c00070050984200d040c43d06100c24501980d001c1406148039140c90044080f4800046d800c0d140c00711504d0303622800b40300c0417500c0303402c00300c1010391018054a8680c404c04403200d20070ed104255500001034224400f0300510208008200039641100100d0b0b242d030401c091580c005028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 313815314 1250 313814064 313814069
    0x10201020310030605090705130204140a031109042a060212210402060c0304270c050904050a02251e051908041809121b060203090307080705030705011506050301 71
    0x143c940d900006603d01b20103205405c040d0400900001c4103003951403500010390403a0050070241804074040080f18a011828001220740c40710032540c0c0f40807504100034045c20003c105913400800d0b00100382401100c070b010800d0b030119a074008480a410600024903100c050b54208072108001c0000002401d00003441d10703401000030120310490307a1248041451401000000002031001290214175440c0d00e8030245d80070100c15010000710b03e05a04102c0987d0744c0c401a0902040c02046448424180b90b00829800403d100000d440c1007082d14014040c3c115004414082c0c191224805042044405000803800c015002c14a01d000b001d4075056160009500d0344407a51000403001410000000c041e00c000706400440c80e44121145024072000e8041d048007214107010780c00c88000c4103801450280703443d12a244140d0541c910719902e0000a5001038070140742448203100307440000f5091001440101e120304c0240d41c46810340d20740507007981c0342c152034640c94650784101406141e5000054904 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 313816564 1250 313815314 313815323
    0x307032904090611070308150612130c050303040906030b0a0605010f180f06050a030e1b010e010e0409111309020d06050a0902120726102712080601020102031003 71
    0x1c20054501d0000028140a03460340f010444c042201418140c100820600c248025aa251000d080403001c0005a00c6605074101082d95940c011500c0c822143c020421543c1c030844007021042d45035000246590402e074440d002264840c2014010000310001d402c0d0440002ca10505c003103420400041d03e60100c402614081080d030740d24170310008210055010003410051210030f10107848080080a07648030340b0041000c00d0078944800d248280004400c00c0d90b4a0520a0030044003413000119403941031114054100b02c00e400c5110255501da114280f402c0d8400c0d0b032081e0759803c000c000d2006125016151038842841c1080d280e001d030302c0d407941401106a00510019156440002c1c1c403005000040010f9003020b0340407001208402d00080c04020f0f1820710030810503405c1081030134114204141001c9a643d040504089107041558101e6000c101c1c80b01e4000c000001104511503e070600c0d01c00039103082d515401d1a14910340c0210780c40790007075402e200951541c60605803903411900144001131 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 313817814 1250 313816564 313816571
    0x30403110a0b0304031706060c060103080a0302040e0a02180102160317123417071106090706080a050717190c02150601020d2a170307032904 62
    0x51580d0311120800040c000d14000e031500c3c0e0a050400400392510b4148000c01c2c64210b1002c00d0052824000b5141a102c143c0c0082a59038207503955018a42c02201030740041c1a000d000210700f0340041000359202c0d41d2808401602d602c080c40101d6240075641b420340e07040d50020501c0f40c1c0f0001c1542145c0080c0c070b801c00c051645160b00b00c00c00072103d2061040110309946c0741000e21402d040b540c5522070f102c5460b030020b46000290700d80022800301800211101180405403413018030a43d1441707003a0301540c80c2c101000300c003015149080c10023000311045445500102400c2c17007403540000300d081d000706540c04208054988410090300c03418840d4210106401c0e048000f502000c0d20510014245050000c10300c01c02c2c0d00c10b40d020303507a104094140503910150500003810b5510008141c12110800c0c0e60305002c0d0907081d40040d000d41e04d00c0d1541c62240d1100f01400d008101c6506110300c03145403900d080b594900e00350320002d0403113036014001c07000c1c0e409444402901c0154542c0f07007104940101c4001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 313819064 1250 313817814 313817843
    0x40e07030209061207020d030e030307090e0915040813060f0504050105070501063803040f0305030a0b372d0504091101021014070c0807240e01020408030403 69
    0x15206004800b456134a10f81180700b0071128a13800701e0391a28030005510103110740c3c002809206c2d1240800c484220000e84041001c2101600101c070982c0c1040c00c4006460700f5843d448000440003070125400d0b6403803a40080c0184003603210340c0141000f000c451501c40041c2030000700061261046115240c10800045426014440c003940582c009001800c481c0e810100000d0340d04075100d16040e03c180b142e01103108a040804402e4044a2280d5403007404105000450343c1d040d10325800142061007980e5031a008104070703883c0e48050081c40c0104462800c2c058062a44c18801000d507902190420188444108000000010b03009280b8001400070140d4680503103803140e80418a074080e6500905140c90700051040229103104140c6081e8282c41041c00f0210400054030303048030205101240103000100e03118420700110403902d104001c19490301000d9100c5c011040c100d4500d002202caa4441c010100c80d880b48038500100700e10500035800c2a14001d5080c0c0c49000f04c0c800580303002e4032031490 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 313820314 1250 313819064 313819069
    0x1d091302130e060105011407170c1c022b0e010f03110d09060e070f03020409030c0503030a0f05060118090506010c0f06090b010609050904060e0c030d031e02040e07030209 75
    0x481c85000c010080401a01c00c400c40c68540d5040d00703204041c081000c81005100800c030b090210341d02c0d95001410200255008170b40042c00e9400b80c07150034030030b0290b001c0c031000c015502001956005e40c181c4c010000e0360f42650b0030268107121450012090030030b008443c0000c41c2c0022061a9508003424220f03000d5803050000e40150000c46110800141c0004040322520002d60000030341e18042c15081040810080c203856555006004405408044100c2000185130a4010040d510302c00d24046103040031540d43c4601e1340d04107136114a007440c0c032080c03015000070300e030b01c6030540c449002d1a0124a208a07051202141c00c1c45000301c0741d149880304000746290740030380c1c900c0d880c2e02d6001010036070b40b50321420940d00034000075000b00c6840401c6000001c5851044500206030742c401800d0201540300c80c1d4904004003807041440865018004603200d580c2d50610140501c480551004540c4003140c00c402120f140d001c000d05981c0710f105100030320141c0e10000b0002d80c46050381c140165290a000300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 313821564 1250 313820314 313820329
    0x4020d0c08070b0301150936060303030b13110f16080a09030519110d150509070509060d1a0403020709021305190608070c031218031d091302 62
    0x807942071151480000d44203100f0740c0254100d036210100d404034100304100072682c0e50058801d038402c075820031044901c0c4c1c2031038180000c03c945050b0080b2050109141c8040300f590130a51080e03000ca0744d10000d08016091800364805c94501540c420022040b09061943ca50300507900c429007000404141d502c0700190500104004d9074104c90003588844010000070800c00880c0000c40703403401500c200ca074a41d00c1540c491074000d039201078000422600345e01800701503001e1420a071442c815070001c240382c6602c148151070140204d90060440a4240810f220030342c407000e0b00c1c542c090014940e4110100303400103051040d076001e1805400c01c503101d40c10100d2400d602030300080d5189100095018944e56050050b0045442c242c40707103249446403440711541c00d0002c2c86890701082c000c20004000034440c0d000c45030200c0c0700f41010b442c1c00d0041244802151107030300401e0030380d0302c0d81c4d011a4140364010900050700400103100080214031600400d04c0401f0242c41d04084a800350000021580c6010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 313822814 1250 313821564 313821569
    0x601180e0f0a061b020115060f0e09070e040e16140604090f0501050a08210306040f0e030301051c0f0f030302070503121503161406040b0a0c02041401060804020d0c 72
    0x1003141d140000c0340c200b0800803c0e05401c00400d25034105880f2130b0090040c09800c00308030256002007200c61821800340e40c20514079261004101100700007560503034564540f00c0c09100b0710f65400e48080051014007048500255800d45a82c0c0a080400d1070341c8900140c0c40d068500074110303068001460000320b44103001c0d80d0041507105080142070741030112540d0156040300d800700d482030082e0ba500d050982c2c60b039850b80c00f0b16a00c404000c541300c02000b00d8034001e54200070050400181d4400030002e00c6d048550001700006150030000c0100080d10f0408004002004041d0001070f6508240e41c1e0b281c0d0002812a006102c601440200014103000f5030594440540045c00d80e03640da0040c51030081004803c846150300c02e00d41c0b03030703625542d414000345480313503950a2001c400c101c6050540440c05403441002c400e074060010800031414058160180040302115129080015240d1041000780d0303e000700355016603407252004000c0306500409007034015805649410740307031030203080001c120b007001d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 313824064 1250 313822814 313822843
    0x3090806010902070c060f05092103040303050d0c050c071502070512100606140a03090c0807230103020a0c061e051e180a03080c0d1805010e0601180e 66
    0x900005111820758009088135403064401c41c905644034181905d001d1140200400040d90600058482e0700340300c200c1041c21001c040f07510041000d4030700402e18640c01504100c002a5010910070100700650103803a0705003809050075400c2a4010208651b0703180980702c3e10082c000620011001240203128610203090007034011020307514041e42a80e526010b030700d84c010780c032031620400003615881400c034902d409903800c004514040c0808411005000ea501c415121881080f2000520035010414503006001d40800c1c0700504400200491011050360702c2c60341810f00401010020750741c4103411441c02540070100048024052400d04a4890750b900c0d613107a000d00d4502406110030f00300e14080c55034801c5a005421a179a061032211106580c2c600c008240c3d03000c03860102c0024000c03044030347c3c0020808c00560030907105540d04025600200071740c48284680150310401d02101f0302940500e20000001400036514080c600c0c2d21050503944240100d0350303100603492030503000303010004240100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 313825314 1250 313824064 313824073
    0x60f011d030106170c01090e0a0207110d0501050403170106080406020f0d1515030b0d0b09030c0307030e01110d080105090703091a0a0b1c080715090b070216080712030908 75
    0x1e074402034800c00707445105013035a88609552a01c03150300c5403060400303460682030400255115042800042c3d04101001c03101c101c3c10301100401610ba00300003610490023040003180c3c500305030602a000c012110b2280c0c60220b4440014450369801206050300544e10107001a52285003210b0242d80303000d608481c61100d401c1001d07023184441c441101c4003d94510105c00080c550011030181c1c219060380581981008a03901e038800410f5500c0b03c455404403261058038540b002894006003141d0145c0e00890104405444d00c03c1907583c03202001c4107500510000704001c0b0304100000d80300000c1440340e10710496410001405c42842500302c02c000d150300c00c040c00c843d4011500181c0c6102001c40b80e04111078580130300d2190f240b4050840840030b009540100040c001581c07030301c0d030103036020300c00564030f0300c031091205015489544140c0901c180110804440b500700b800d40203041800886e6000c4006a03080c2c018030510b18041914802c6400711181c4c00c0076a0a641380a1394800440d0748121802e024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 313826564 1250 313825314 313825319
    0x6050708090907260403080108010207020f040e010b12030a09060809100905070b04030b010e130804030312230a0c02011b05030a06150206041106070c060e19060302120609060f011d030106 82
    0x204d210900d0103980300b6200c81405130380345c01ea03c3d402c03801003160107544400442e8840303ca604056000d501d520340d12100104645c0e5822000c0361009011101300501035100180e450340403170344840100e02a08552601800a086c03140000e561081011884030210340d940c600d101c1080001c1110800600a080e1465159070b900d0074110b114020922408103c0c48032400080e111480c40d207035031210030f64003074640c50070700b030450321700312244000c1031203000196a80c1e181c007102201100b0f450310101d403200001e0704007502c0c1156461094820401c0003c0542e81030400c00030144020343c0c120008907005240c0180c490761180d25005c050320650b4030103151801d62020548060f40d01080e024420b900405004029035064804e00c106c5200c4e01c600507203100348507002407000600c00d0f0160402d0340002003903107400c803480c00540d506000940e40f001c800301c0d40c00210201034a01120503d03a00c041c003115899098501b45010602404040c0ca6050401c08110640e04001a2030303000d1a6013840c01a008004070794 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 313827814 1250 313826564 313826627
    0x403090e100305011506090e0108060c0d0f02040b0d18020a053604020a06020303070509121501060503060f0a05090f0402120f0706080a291201050c0d050106050708090907 75
    0xa124003c260001d030210383c0200c0d0348c1c4c00c0c1455484c1229030a02c0182141d580d0060351604903002403640441007030b12285400203122860001d400545000c81c0c4965481807503403c0d0104984010000189504090780001c004da540d900d520701c101c0d0800c1c0d03882c20940c042888040208141d11030003640d60040703c40010f0b203040c0e02c58ad0340c0784110710a4646507200c540703604080c2c4c0d0701d0004039402000244100050b50040c24000003000f22482d109040710180803100140501c241c40903004807000900105c10001e041c035002490700711040c1d0036581c2c400c0a9081030082400e181000702480b03610070308100032404544039924002420411ba4040e10700540d17051101c191601094440d6100240502c4003107003591107135104480305000c0c1d80b03940181c002d056261260510408203011980b0200590b80640e852600380117040c4101c003001140f642d15000003540e43c0c1100e8040e0000010010107000c1c1c1070018203258200c031039480b4111082c90042d40c1d0004111201c00d440c03030182c0e16010050140e5003014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 313829064 1250 313827814 313827851
    0x306140132030a0501082104090c050d0e0606090709060e31050f0606190c02150a09050a080f030a2307030e030708190312020f0c07030510050403090e10030501 70
    0x20380b210020707280a00d0b282002900c1f00c1c82e01e5907000d05201c400704810000950b203a8400300c400000b605149092a452207000400c0380e6400306070307005580100e410081d180c80e11131000c80e8410351070f003050b51240e030624400030040041c0d200c81e58080c2040e54050b44090080e500c032001d8503035040800b6102800d0a411900107441d0a03140d5620b2030601c80301098041c9410415140280300200c3c00007820743c46200e00703c6071200c01d0001a030300141104074a01010451000924041d0311544400c0d45040c82d007001c1c0f049a07a900e51000c03245030445201900748a2021084443c2c0e07007941d242c000060948510482c0e2407040760800c140240c8400610b9900b056040304041881034400c80c04c0e2401140e480482c00c0d00d940d0701a0040740d81180300071548000900406198146405240d00103081c100000b00460603a80003600c601035603400b40000f007080100401c1142d07441e8201000501960515517405084040b4a008559200110134002078032081c2034680003006581100c028083d000302e071003000311070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 313830314 1250 313829064 313829069
    0xf0427020c10050f0115120f0203071107050607051f020f03012d061e051333020a08091207170d0905030c10021c0503070306140132030a0501 62
    0xb00c50070400020b6a828503028054101c460101c04002c20400d0f444084850382901091301c0100ba5940d040d40d41c154100744065881444152121200512681d0b256032819400c0d5200300d104480c20040a8002580130a9954854200c4801c1c804112041c0c003070351780079000d03d1220300034030540880001100e05410010103900d0034000d903400d404200c882210321000c22140035850204d41d0104019031132648052490703194181038581181000298103035581041c00c1513100c0560702101800e001000600140d265401d00710003020340a06102000000e900c46e20b14001c040c01c05403010958034469121300340504c803009144415140c929490709948003000038650031148952182d050141051801804d0329020b50380010b00808502000104011112041d482500d0443c0a0b400b0340610740c80d00300741c04c05840c508075201e090f280c8c900644001d00b1200035130300a20780c2e1000a010b2040b1640c100145103c2c41038141304204902035004042a0f490007109030a0092040c000108402e5007420390102d8103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 313831564 1250 313830314 313830343
    0x120705120426070c0612090203060103050c030d050403200a030b091b04020403020321040e04050f011a0f090c1e0403060b09042d2001140f0427020c 65
    0x2c050309629502580183c580040400c0700700c80f01404018041c0d0b0b8000c5810b035800001048490540d40400d017010400c0c0e0045071070751300580100865240074004070b8105e5046103090342c185861030b110780c052102003218440144140c5080f4130b2040d00c4121030100619008912980c590078558800f96580344400a00c04d2402440b03032240c5c000d440c0074000c640840380c00030020050b00c040410700d1618091092048121880100000103100f1500512548200e0054014104d40e6110f0442d55094800d14040c900c9242103051401e007043d41e5440303130711055010694150040b81c0d5542d05606280c13050000144207904070254846044100100910940c0d119000c18800380e10b144061003000402a0b43c01403030400c0b01000d02c91000c411180c002a901480484040b60031031517110324801c90892010060940c0c00c1903454101c1d540c0200444020545411401349440a14040003689005601030704a005401f543c2442112914480d0300740c1034154203500719501e00c2d800c01d245a680d48254103114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 313832814 1250 313831564 313831613
    0x603012702030f072303030c01110310050603060901090b0102012406090815040f1e0303020c010e070305100e0705090a061503090302030d020a03020d060b030603070e040203031207051204 82
    0xa40d03889000c02c5034400c55040f4035440243c910a85c6152200d0702004200030340502c801c0c011a60002c10901600c02c254841c0d080d0165070382000c00c00c9412440075038100d03501801c1e007001441101d0f190400c4844c11190148400120f07600038100413400b4084106824034100c0d01e140b5455a0820401d01407021941c09440e034100341381e501e042454440d880c12142120004c00c0f00d00050126101e4204082e02900c1402540001490403003c41c990a07600741081c4c0009501050b60040e1601c01d10600700300009200c010202c0c189191394940d9650a200e40203151141c5030032400ea040c2c081040703c800a00001000d0b41d155140c00e42401780103054a21030389184449000c1e92200f05030083c82100b48141d090f5001d5458544d20007001d20180d40500130315000c043d401c11080706d90800510540c4003402050964540e00d003050700815250100c0c030340200c81d401504034144401070b540001290303008135601e00d101031255140542507415003c4d03032154020b41d1600340100420003031601c0d41543d8881c040358040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 313834064 1250 313832814 313832833
    0x5070609210c0f12020a0b1f05010c0c1403030403050114040501200405060322120e030d0503130501140702060402040614100806040f140f060402130e060301270203 72
    0xc82e02d20040e06005070500300e40e11a0b48012400d12a14200b96080500460300030701c8640c1d90f4a032104400300d500f20000c400002c0020070855520414070001c0c6001d02c2d0114041d07201d515442000c501521030022020003500d402c501644050044d10000d40c1c200c0e00801c0b020f01100600715581000b01c40454442d482c1c46800b000c640a01071402400352220032482c1d0030541448141322480e031014090341260304400c1510380707840c0c60710003011005900c22440100000300d0000042c094404090b1118402e41040d003101e1030096000c42540e078000c0c0402c10203408000c0c00d041c86401003046500c80170130001c4040c00c2042040c3c00045482c040c500c01d950410106603a500110194441c9498403540200050003107281e2922405aa941081c0028000110307104083d401e030003221407810741c0180080446003000307107150015075003d52020007650254a01a800e041c3d0820040d824021050081003040119000b51825840140e280311a01901e10002d1031010619146901cac49104a00c01d00c1110000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 313835314 1250 313834064 313834067
    0x70b0906070f05070f02090c09030d0f020c0411041203090e13020913021f0314090303070c1506050d0c03051e06060d03140f0405030607020d0509100507060921 70
    0x101031107034000365074681607500145000c80f0316034401070f01078581c2d100020402c40981d803078a0005010390b0b07204680380e0b0340d2078600040c907003041a20000303030b802c1c000c524100680c850340110b02c0504501c42218000f03078403a610001c3e88440e001340e0300b100302151b692001260030540c002c07540704291003100000ca220b5996000d135080d0719500030603000750011503010124034500c2c956102502c0c841e00c010096014411600314003e09124000c0c26503000030f854049070144500c4050307141da006a00340001c0c614518111002078030340e1a0140300103060000d50b4500b4821a4100d0b031028000c1c02005111403c20700e620300b0926980c003030030b000540e598000c0059210403a0f050035880741c1d0140d54440a010340da50f4035400c02291220070315081e4103016007900c40d04580d0780454000d005c2d10800401c800d450b0b900309004d151600100524841c1558001501c4411040d0003c0903140142d408a41403100f00d80c000030121124020f41c17000a0031142424421710070400600d6408101d01d9203034030a007010f030300c62010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 313836564 1250 313835314 313835323
    0x90606090b090109060804060209041410060810030b04051207030903021e010801090b03100f3606050c0d0e06070210140c070203030f070b01060e0a0303080a050723070b09 75
    0xc89404a501c4c8401041200d002d000b4282e0f101740203510050030702280402050660341290203c2101919030f04c208040a9211450400600a5868110744620b01410440808000b40c000540400c110500040030000c0070002a00504106070441d0344403101481c02801c0101c4c02d000c1248906008401180d14554108030000310038016510174616910380000d0700c004000015003e9011b0041505541080045014238070f00c4440000300003c00e80882c1d0030400c907014461032420941d50b02c26034059100b20300100046030194100f00002000d860b414449141c500c50610f00403540c0d42000d400d80020320020561a1043c1c0441d0240c4020087c640c01c0f50301150a086940e945000c03502c40030401d0381003c2c00140c407000d40b0150480340b50020034460402d194000c04003c90701d86d80c010005203c2e41e43c1c0002840300080007581d0403e4000d0030343c0d6010700075400c02403903250f040359a040001c45091044401d180340e0081c0390500391100f500482d5242c2503a226040694540e4928001308045500014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 313837814 1250 313836564 313836577
    0x50a06111018032007120209090c060d0b0f09090a1202030f07060b040b0411040812030f04030305091c02030405031e0304030816051b030f060f010b0c07030804090606090b 75
    0x1100b6107844002036800340c0d0b41850b85400c010b02a0f003000d06110b140603040006801400da01c101c440b0380112284104040301100401c0d00e5056000700030207080a464860640d10f4405510401180000c901c40c0803500481c04140071a0b40401046c003440b11400011540c0c1182d00d014006088000301c4294050b640c81c0f180d40c2440d5441141002410f022880d198070041c44c0d180000c00108440c500c800024041e2440044200b082c0c0000040030480e903142042091141c8840402c12030451801200034400018001d1002d0181501c40c0000b4581d00014000c92401450359006640402c4040c00d00964a80240c05101c0c000d10414580b0800f00e00303280c0c81c030251808418002e42c40c050a680e19507806d038020b6199034820b2145d0500720400104107200e40c49003509140d51035000c0811000405281100a12050442d80c00c560140020a08005c1400341510a1800c0303040c7d846940d10700003440c0001c181d2015014290100300442c880c051a04040100c80b8250756001415480382c07040341d043d21942c5c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 313839064 1250 313837814 313837841
    0x10806031b01141b0114100302090f07032004051507020607060213030503040618170c1c05070909110111060a050406020f0c071703040f0b070804050a061110 69
    0x90a10400d40c45240c0c89410060b6030242d543c240074150550b80001050006414013594440341601140200c40c0d5036290301004001328901558a19000b040107040050888055189a60000b40000780242c110011100e280c0c011801001406c407001d0003281c015004840c42003210303007840400c808400c02038648040d00100081d2500149903102c0300254000b41c111038000c01d000e80000040390341480504010031494440382c1c82d040002451540b4400c2503000303d101c000140c1c16080c0a4a000140070302c03e05070680c1d0720420441c2182024841c9110104000c000c0c1c41246008500304189400c05400039118403001280034801078019240b15107401c1c0048483d51008002440d0300c856500301030380140c05010010324014072003040041680c0000d41c0d100300c99110720b0080003a01d203900400820b560054020314101410f158031400c0001240c403613400b4071500421001d041c05981030032140208070003000710780e0351035590a01409421100344000c8903401020801101c1045a0154105443c41c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 313840314 1250 313839064 313839103
    0xb1804060902071721040308040b06060304050c040b0f21010605100c0f030507080f0307020601091505010e0f03011518060311120f010c030207140705010c29010306050601080603 78
    0x5048078401c0c5070b0000c140800045d40341d0540f24000003101c049450080f4000d907100205c915240c2080340d158400035003094080c034010070800c400715002060078101440c046401040182070b0b100021b400c0d00200001317903071056000441a42640340200c00b00c2400f80000c0003845000d58903810040364820200341c41004c10030116132072002900e11034891615a100b802d2603410000700303860b9019180c0048180c44110907000080c008000d07010400180100502d100c203108590403a001c0c1e10480c1411f10406040c0403007205094010340d100c5ea1081418078001e0002c00c1040c040107001040c140c1e10784146400c0504a04041c03050689a00480c42a650464030b81030148100e034051094560308c44a01900c20f02070b030080541c0c0131800303008064510b003c507034000d619000bc41c1040d0540b0382d0307801d191120f10341c414002000166000750b000c00400d80c02154a11401c280f50410100c0e035260044403803400c840400c004410441694009c5010345003c2c1d0741e4001954034081031507070322170048500c044400c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 313841564 1250 313840314 313840343
    0x1204030b06060c070b0313050f0c010518010e03030d05041515030320060a0614041a0f0102190804030b010803090a0902250804080138010302040b180406090207 70
    0x82c0540100b0f00c140750304040364580707690b5461815081d0410307159845000c40013681300e001e03c107042040322002c1444c4009011f2284103040041c04521a20745d4415032450140c0709004503030300440100205183c0a0142c0e9520304c0d00360320394402801300711001c0301c4401612242c1c0b400901341d440b4100c0c200c4c00901101060724116201528000311004144840b40c84201c03407040ca80c101800305500a0005200c007040c0c4c0d500f04400040401c2d43c108401e4000c034502080c2c1e084400191a00d800300c2035040e10202030003041c03240102c0c10b112802c440003002184180c0d9a0381041380c00001030007102e00070558a070240c2d807100f20468403071280701e089a42c051040d004c1880380000d15401000c2070720300e0580a02e0201500c0524030466612100140c840f220080380810600304203001e24001c2d2809050100c0c041094110381448100d08030f41c0105c0b0f03045c010000c0c001107074001d5040b940601490351040c2c4d00c405038075079041080c0c680c2d920803034017441c1005000941c3c80c451b4000c1e192043d82c04240a00f4042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 313842814 1250 313841564 313841569
    0x181205070914131e081204030f0f0206010e0919050d02070909080a140d0606050304020f100f0509030109060f05250e0603040204140103030216060c0f0605070e04020a0306081204030b06 81
    0xf10550400128100b50f10318510002c0d205100604108461980c6c03412a450a0308014103244d50702c514490a1010340011110941da002c0b50041c190303240c10310340400d20740b10700381010325160503080f0003101d2091040e074160901c40000751800c0b02c40400d0307007141e180c592504079950644503400c0340104100300c24000030440e00d006043d04003203072080010150600017016081000e940041d40414003140f000802d01044d81814180c80c07031a840241d0707910b8030f9141582c0c0010000c0c641c412050741006000f1402816680d42074010341d030006e811070024851107420a0300c0e100185003c0d10030040f14030307404814420b19441300348540500441c0c2d464001d00b11910a061090541c0010710481e4400d643d880a428480350f210318841c00313940640d0040c543c40384c110250f00842c01c03c4e034101c1c50034030501a20040024402c034183d441526800328010945d916180700c20386500d0392024440d6845400442c454100b140e0640c46001107480c82e03411210500c6403841003111520a900029041c010203500095150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 313844064 1250 313842814 313842833
    0xf050a0614091210060303031802060703050313061a01021501260c1c0308011e0902070201030209180603101808090604090228020d0f18120507091413 66
    0x4140c081c3c81c405030981900d4110741000c003a5410041802e617120814424181c0c148689a44400010212154442580c000550f98002e07020000c080040020016642198888032012a160305c01400c6c0050441c2000c0e05140e00000c0844500520503031070800d03141002a05648e040f50a00d90020295195401000200782c0000c440420700f8840e0164001c0e2584800406c0c0c0291218000036042c0301c00240b500810220040c0d1004140603c040b06400030007000110543c201c0360341c0000181c2d035100c20310041e40603001e2030500c00c2d40500c2140c0303140540140188213621641048080c4e031407034031110f0300b08000c5400a5001c0000080c50008280008204000500e01c1000040c1014200b6a840e11104281c3e81f004260115100889886c600080340c14441504d504020340060005980b00c0e0300010821000e0b01c090b201004907407070388140c01d10f02903c040da000e0300c2041c41c0c8040003005400d103190f0340c0a0300d00c03660038400d280400d0b0391242810124001d0040c61034284d8000540c54984405201c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 313845314 1250 313844064 313844077
    0x30c0f0806091f090506010f0f08060603180a05071802040e06090a14161d030a02040b121203150405040201020703030c051c030c020705011803060e030c01020c03040f050a0614 77
    0x30480c59006001c41c0c410100480004e00065001107158601080010b04884d0b061007402c06020070801d803010300036004070304164802410341c0d100b900c0e5503691040a00c1ca15036107081290500582c000201403200102e810700a940c600c6100122805c11207849008901c141c1c85a0140c210350040451243d03d0030f0106142c00c40c4040300701082448680c40c03528040b0710f01f5a1231611000340300c00e01000040c1c00c01c0f08181880482d40b100e0444003c804007082e120b40310710070000c4c4110765450341406a07640301080b4141c88943c0740200c8000300015840044294420745007080c80c0e6000404881861a040c01800c0c4110f5060340985410f0749190340a41e9011588482102c442c0130b041090940064108001e080305101c5aa01041c10a4002c3d4080e0070803040344c1105041004000c42c100e003600140801c5811030340e1040d030005403507030681c00b0075046019086408056500014008805e00740000203003089d20301d4640151805a50750080000401c400c1c41603102048089401e090000c045d080600407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 313846564 1250 313845314 313845331
    0x2070605040c0e311a0103030809060c09010e0d0602180405090148080106080a1a01050f070204050a0509101a060c0a210f05030903090603090a0f12030c0f080609 71
    0x20484519500c90418000045040d443c4805c003000401c14103610481039034120300c0d01c5001e400103040c45640c4160500c5420804d0b418020b64010100594460344000c41c10107811810464071075600c40100c00c8080c0f009030701248101d06003008070b01540818801c8030078410b4403440030b04070070124080303421514444103141007813480c54400c0d855243c080101e6020a110085c0c2d41d071552036040000103003481c10003924446a051410015102c10b10004543c10f81995003400c003651036810b0507580610030320650f00000d401c83d0078003081c0f2000b240c0326003210380110800d400f6110074420608103042116092240c241400c50744014030700c07860070301c4401001010160801ea8464803079548a4440b01500001c1d00111015003a214104859020700c0b80c000d091054a4498514200f2940d4280d8130701400f500709100e518008081a50948101f26146500d03074421505003a0710307558104282040202c41b50301002c01d06040713414000c02d20444801c44800704689a162460f00c0310f406100c85072000510303e50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 313847814 1250 313846564 313846651
    0x40e0403090b07081b06072307080c06010311011106070507020d02031f0e071a0c0c13090201080f0403080f151302130f12060b040f02070605040c0e 65
    0x22200b2000c001005443d0090041d0303580c0c2c1840100202d10501002c07111911500510240000c0310380c8481500c01e4200f1030f80c8180d460b041484404c0420384181030b401080c070b82000076038903850b10000c43c400d81282e01131301400380860302d80350055a08003348030304070340c05401820014420900940150045a00240607032500356039a90104c2c0c0340c034142880449140c091403e0380c2e81c0c048401e000d4007140f500f44c0c1e409894134900d403441e01800100b01486d1540000d10104070526100b2041081110f09180201611030703400800c24100010200e40c201a070001c0c0b07401002400f0140d1600d01a80030750360564666010b6902d66807503c8841c00d0181c20082c101c02070f030b1000401c5544040c0d405c20524503da000580d150444200d81c00b1030702c030a90040080481d01c1c00100300c0d41c040e0a0200e016260801804140c0500440014005080f400c00400c2090720100740d079070910806600140c4034a200350021103869866005019048804a5100f03510154070600f4118207280c91540c0400c26a031403c030903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 313848920 1106 313847814 313847819
    0x131406090d02121c030f0b15130510050909060406080c010c050114040b071205040816030e040f140a0e1905030904090305131a040e040309 61
    0x45201d0107032206440c1c15511844404001485124103403034900048044051490050180e181c0000c0d140c085640000070341c51080c1c1c000880010040d40324020f80c20b1a000c100da1001402507030116058a000843c7d45841041d4800c140d42d60f00c400f91a2403600f0280300c003c03c0b0017811240b0482c2080c03c10000c100c40030960300d801c1c1c282071900d88240c0d021405d249014181d0340c0e515541c806080c0c410003040c4401ca259860040c0125640c84074454801c411030815140103803005000c0c3c4108000141b0309421038113500c039406200b41008940d50070341c0400581101c4000014105403922060403038007880c1000942d5622050b200410001802120380155035601c070324141c01501041c4e4401d001c1440410006e40c1c1e00210020720901c55040c507440d00800781d4000b03803500340000240d103a020403100c1c1e1448000c49100f40160b186030401c1d00d080402e00311741c400a001a401c1c8800007501 = true := by decide +kernel

theorem cover : BRFrame.Cov 313669064 313848920 := by
  have h0 := BRFrame.cov_init 313669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 313669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 313669064 ≤ n) (h2 : n < 313848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
