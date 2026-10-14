-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0726
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:26:15.293228+00:00
-- url     : https://prove2.me/submissions/79fd99ff-c621-4eaa-b28d-e47ac1fcf633

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130395683 ≤ n < 130575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130396933 1250 130395683 130395691
    0x402040b030f04020a030605040501091a100302040e07090204080f0f3705030c0601080f031315020c03160e0703020405180c0f04030605090609010905030d090204020904020a081509 79
    0x40c80d10300755502d101c242100a4401003060b030f0300c1424604000003050083c4210b0b40600d0003200040f41d01125420071071103030740500c5c503482c3c040400d5004201d940c0318030000150070f49034104d0340030502c240c00201152900d40660014601d962001400040c070b044001111070b40c04905005545c089810400c41c6901c4000200310504210918004004607800201c55580d61900701e104210008402c2c0d04c425107035401031461010759034170100c01400b808004002d0400d003050503400071460600b0703401e034841c80b0010510500e070b080d601d41d9810284060081c400e01c0ca00050207421520318103102c0d0031003e1801220301c5410680c181140c0800d02d014464003c85083c1c407005041014220807a84089100141c0223180e6110304105007c2e0303100c14164180140002c43c0a010301080c24200441042c1c00d0220107044080c0316803610300c2d0a00011000720035503140d140000302c0026074424034000704011f44542d00c00320794080d2001584001581e0408a0305005d6200e014101801ea850780d01840402c03d03041d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130398183 1250 130396933 130396949
    0x5070905150a0c08030a0203060a150203090105070507031b09050f0709060c3201060b07030f080907090204060f080a0b0102071401030905070608090d02070510080901090b160905040204 81
    0x200d906108400d072004007400c070031900c0e003070040410503120080346400650fa2104155000820f002041c036282c50542c000d07008034046011030980c1010302a549100f00ca11030340c18000040755080c24040c061011100440d0403401715100070080ca610342180a202d801b804006515080100d1034140301000d20500c50515500e5151a15082c00310030b4070000704810084603d404089102a40001c03d00c4201c10102d91001c81401980540b0f0b05075402d54090307410030341d05900180200d1020a9020311004240e003001e00700700007192a9000c3c8207041c003a0603000440d14500002300011400c1d84034100700f01034202d942d01c0803002d4a0341242d1105a6900c500c1541c0140d01000052000c1e80d0010918030540105040c0003400b41056580e185c10003210754400382c08100540100b007040001800f40d207004440c1440034291081c10b01001442034980600142e04100340d15000401c2c183c0c0c25030108802ca03800205109040c0380044582460545010101c40003070550800002e140c1481d009440568030a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130399433 1250 130398183 130398199
    0x4080301050105030c09030a1101020c0d1a0601110d02161401080403050307030f0f060509010b1201060804020f041b110102040305061329040209250c060204170c0405070905 76
    0x10a00443e00c50300b015048a000000400203468156801c010000c8034900c500100c1d16440003400000e030a00000400f0f03170340220000010b840001c0d266510035580c3c040f5501070380841d501e40d200100c4a10303620100700c1c502445000d4501d45616000180c001d200e01e0040d41c0f240c80b468440d1500654446160981070102e58007030042070000740503002030340d800032043c23800050140a1060b00d509964040c01945803807613603081c041c8807070304001079500e0142c881011810715041880210141e00f8038144641c408105e950808a0300b155a0400c40401700f140c010004e10690105c260003079038103120401c44c003010406800d0b4101d5500018001e403011a90488003401c8607980c2c2d5004581c0c0c258441404698049207040400000c9188010414891442510201d020f14103071040c056001c8000d400413100c103120b0f044107264440c171201041015141ba141c110340f003000525002002e805160480800e02102c4034100744400b01c00625080a480219010302542e240d2030002d440c1c1001600481e60030820ba = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130400683 1250 130399433 130399439
    0x90602030d0f15030311070b04060507060504020409140d030506090907091d03040f060906140301060c0201090305010e0f0c0415060f02070b192304060c0602070f05010e0f0604080301 80
    0x699008580500b07003000003182030440d0007200c007003080f0039400440100340c000361784103010a403c20000d0301800740c03459810300c0c2a00700b20000d00940285a002860705d07031582c00180031074a45403c80303c0e01c01c0c1d0005d000b00442c2158110103484948010b001d4000038a0940001c2840c50b06902e028007030341c2680c0181044505102250300600301e6000c850100001310030803245480001c00c0104000e00c00100306440407401c00100504c1c425150740803004002200254011104248044a0440d403050400d00802011413006030381d0309050343c0c8040e025502e40600310602c0403012521004020364503055509103040442040111000005070402c1201040f03420b01200e4021881b503400c01c5c9060048411885d51804ca0801c250b000032020104490014028016a6006248000000d0641700820144040b4011428150040d40b098204102c020140344041c4080f50381140d9506820001b4070382000c46505120307010740000d440700245845080300c04500c40f080030400502865111141500c0c1d40d00e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130401933 1250 130400683 130400707
    0x506090a0e1c09033008070c1b0503160305070504021608180906240306040b0414100803040303020706120b1c1b061407140a030e04060609060203 64
    0x481d01c101a94240718900e2900e0142c81d01c400c0000d0800060303070300e0000710341c15458111034105a040c2c103680d024281c0100c03c650500c500040151440543c074020603107640780401101c4031205118054081500e06c03070310038420b03000e00c101036098650907422600300304180e040e800c142c203840348009415900007010a00052030190001c1c07100110200c40010000d5842d151400182c1c8404080c010250008000c100f113030400da2144c9500107012a5805200c10303000041840316500807180348400e000000001c0c00d10f940e554800003558601410401009400c00108001008140d808060b1400354000014800c88000f0488081d40d038075901600320246060b4040c1c1d03503190140b01c4d4408064941e25802296150a40c5d036500303106e40b5004110f24203600d0308104401810302240c1c50b43d008105001031044d0380c1c10103842241030f0320554009549000d1401e1000b81d01c8002d01c04001d00c1e00031149407800740b5038800e00754064a4400c440400c0034544e544401d036201e01c03040c860600540c02c00c0c000d8500c114 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130403183 1250 130401933 130401941
    0x70503030406171f080a0b0106260402011e0810050a05030a08092d09160c020d02060c0f060118060e06090414341a0703090801051302040f0506090a 65
    0x1184d014010b100050342c04101d40c03440c01c841d04030745216400304000109201c40a43d481e801400c15060002028451a0072040b5021000404400c0045141c011400316482820131031001c000b019982c100b481711985004064040903120344511906e484400b1030b152400c2e848a0003250710060081c100b09040359540705e6160170507640b0580c0611300c1e605501c40b01800e00e0070001c0040206280c1c5036409a4501081503103440503189003000c0059081c0c50800c1508074010149443e0103d0325128001b105100044080c46401d01c6030410380a80256002c00000001b40d480c140d5118003450303c03400301c03036124110889900c0c0c802d00c3c00c00d134030a9001c9416400c080501d039400c20301400860010301100313500b152901004081ca00b550800d520a01907175a8202a01c005032070405000102c0304902d0003912558220000340340700760300f9100041e00d404141c0251440c00c010514000280f00601e80401100c02050410034140d0040f0f0401100c1040c2403120f115551148800504040c89510350640c00c80040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130404433 1250 130403183 130403191
    0x10b0303120f07050c150a14010f0605070f060c0c030f0816030207020117040b06010e0405060a030201031d070b070606080f0d030c0309020418020a0b030f07050a03060e09010c0207050303040617 85
    0x1000c405c101c40280000180030940009260741410381c09801d0045550080340c3c01022001d584400300001440001441c0d00501c08458492030309a4072002c0c1805d2000c10140811001000103150102e005a030580045606100034000e864000c0c039406a42c6043d81c00d0941200d041c81d44640d41d041029100e406640684102e90061600c1c40c0c919030043c1129020050688054441e0440c85040240640e4040d0a12051100c00d58040c464cd06294000c6405ea54039808001d040c141c076030b1021189002d0402c0e40e600861141c41c00c8440596441044840c203034017407881a00c0309410300d03030042550701c0e0010301c1045100c0500d00801c0c0c65200442d04500502c041d8258404040d107540030310025a560340110340200442d224080c0c840640c42c81008071148165001d080ca400050007080724070f1804c800056400b46460074800d54602103514214000c00c440d800c06500c9103191000e00c2400c030415880b104420041d40c08403421700f5112410107076640298410301000070048100b65005000183c242504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130405683 1250 130404433 130404437
    0xb13050108160f080408160501060503060a09020d06020f07020607060618022d0c101505150a08100308030109050603010c110a06091a040305130f06090b0307020709050c0a02010b0303120f07 83
    0x7c00102c01541d150b00b6002c1d035020390340c5c1c0c0c3d1a82c5003440985014030003541c0186030380f0f8040144280c00e50209510012055000d000150b0200340d441e50a403400c8200c8481c540d0080c1010360f15403844c5001d800030f0255010b039120681010b0507001c62080c0c00c2c8203d076800c0d182010050382c4228005030a20389100703c807242c4a092007003400303900c042e00c03005c010034040340a072642c3c0428124402019a0355004e070550006110340c0200904450342c20440d070484007080f400b46460304d466500c0050b002501030a541c0010700c007000c000000100b10303400358000e5010f0b000440092100d840800740c112505020541c800006400c0742c4240e0002541c66801641038070b20481d10002c208020000540961900b114103070042803000420042500d0034410300b0021701841d00300150b4290a20318001c1000c51240a444244070000001c509800e0003003001400030602e00d10b06000c903241c0030040b03032030030b03081900000d006d9030820000c40311914010040e00d00d80c000c0101003103080d5898040d1840c012a0140002c41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130406933 1250 130405683 130405687
    0x30c0702130f05090d080c0a050a050c01060816030b06041407031d070308120a0e120c0c0d06020405040605030c0306060108181005040c050904031706010201060b13050108160f080408 80
    0x211282c01800348610031401c0b20080d149100000741c1c05095100e00030b15641083d103040040381440ca03080000c0c0d803a40420f40c604661244541c0c00c0140c0140301c2a048520540b04202c0300c5007040341d884600f1829284910200b44083d01c80c0710502040d11003140415112400030070001d03030050b100380d110000e28142081000c2e01034031043e42c503500342901d40c0c01c207035200e000005074044e540361082d20058110f00c09842c02c00640f04201741c0c10361603100c059509a90f00c040011140030320302c81000040b1203c000248514401c034100d240c124001c4d8402e00c0703018000c40c1003480000c1c1a14002c81e45034140f140160241c144c940c0d40c200111045407000b004421520f140b01e45402ca0102c04102030244001001800140c50400b42811851002503600c16441a02d014041000082e400041120415400301c0c20100030380325140181d014000d01e07007000c40c4801c008a80c91046146058510003195001c2c3c980c0c0140303450341600c8503100220301102c100403c84640001603c6031180c0d14050740075010329102c85c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130408183 1250 130406933 130406951
    0x109060e0d0c030614090604030912080c031605010605040b03030d1104150f0e040b03100519020d140708040f08070f02040e0a120203130e0c0d0e1c0302030c070213 72
    0x350300302c01d00c0e0819940c1a03514040f0400c1042c5103518a50450070050081681c0d1501e81d40041040740c46004401e06c0d840e00880242c1001207180940710180c0150301580c4e00e90811030501c9014034024801621158208034002605060034814140c0c4044c001d006140b400c1e40354945007001e482e0031398820100310420400000c1d0314200e564140f00a00c0d19955211000c04407440042c8001e040c00c0380c041c451444c1007040f503019900021103000d048541840450b85a07101a114200d003244152901c0d0b6140c0005010b400002075948400400d5015aa40e89800d8641000c00ca420000c11900141404ca220108801083c9281c001c0c01c3c645210302e10304401c52120741e01180980b010400c0c1201a940070113148820400841000f0300c1e01e0700c0c107100a50900850f85803002c0c41079242c0c41140411075026020135100c0c0600c1080390750002d10f0803010310000b101004426038601d10325008681901c9400710050300caa1080c002c99016040e555000c50401c42c3d43c1d001c1141081c40480d001020aa90724649 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130409433 1250 130408183 130408193
    0x6011e05011d04060635061c060c090602160608040201050d020415120c020f061801140702030415030e12030a0f060806010810050402031c120f02130605090109060e0d 73
    0xa0313014003856560700801c81c41c0e0010281101c0700d0511059883d4080d84040701224986508080e030004046980003064100071030301842c1c500107100302500c1941030030b00241d841c0c0e4000086a00321081a402c8400041c0007407240450300c44640a868005007132a000b040c05588218083c045200c1c03040c1c8010f2605a580c1940c640b001390501c0701201080102203100e262135406d200e18030f2550f04500141c1407a41003080c0720ba48a240c024a281100d0441c0d02d2004000c0209522414860640c403401c041d0303504000502a40e00e400c240701d0b030340303080d241d00c903110101c54804d000e0001d03803440c160000e01c01e60001c20109078490700000c20160350503a803081c0c0707041e0101c0340b8000c6000400403840544193350412903014180010030781404210b42c10a014000146c0340050070000441d2502d002481c040c01e40c10b0221b51080c031f00c03490270b0038450503e158880302d10016801042c031040e01d005c50154465031240b0a0303806009019200d070100d0311404e02044058000c0b550000c0c100d000505484800d03480e42e5407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130410683 1250 130409433 130409441
    0x17101403031c06171603020108090c0a180516020a080a11100606030c0320070215030a020405010905120a14010b040908030406140405070b09010507060f0b0306011e05011d04 76
    0x200c1e101d02e41d00d030b182c00c0021070f8142c901050380c0388118001d40701800030181058084120380c44004e0400c800d12000620b400001d00211030703450001818941810394500781603000c0410001e40207409854040420181018103800740303c10103d40d0050a90740700940c8640026800001e9040d0622020f040481f0080b14240810043d0181150b800a8150b0034400010101c411440456042c50306d000b00000440d42d13640c070140d0031155802101540c0d09041d1020444002d805d00c0e4114400202109000340e600d081d40203842070362001c0e6210405565036500300100580801c41ca0b15107a0044840c0c2408900860701041e42c464211001040c101981404034040382c10009040e82c1504020050001304501070180c04107004520303c190150703041039281d0584800c01072049002c00076001400a01c0c0b03901610913218440c1c1c0180c420403224050405800180c030121030a60b11074014038001254007460540342001c0100c21030705030400359080400541c0c50040000d03899400a03000820b4055a65560003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130411933 1250 130410683 130410727
    0x3030412050f060901020901021e10050f0a0c05030c030c0703030608030a11011d15090712080307030e0a0519030507060f150902040302010c0f020f041b1710140303 72
    0x2000b00160600c0351486400c00402410494042e401081100c0703c07aa800140000c07849101002e0b07840c1400c1300c1955924000754080107c510a00304010070180c80300c4150003510541d940d020a124a0002c124100e40070b00c01210f513000040f60520100d890301744a0310141046610078180012820748400c0510704d035801140070034000600607484200d40c83c500307008450b40065400788d03034260b440c5003040242d1102d1402200718150090800000d076400001c10694000381070179201e1403040c414504050031182e000f19103a1012904286402d48500000078811000c00d4110740940101241c610b0907070010420041c0903010000c082c085040820a1440388982c6151802c0c400101c007607903000d01100381403c690044242504c148030420140c0d130030220f0f540f4840d5000784070905042203403001503442c1c2002044643c0186c0760001c809042d42d140c20010840d0022500c51107605040050b800d1810041121075401c2403000d40803c00c5a400d03042c07601041c0384c00c001c066078240000a1a0b110604203080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130413183 1250 130411933 130411943
    0xc07080904050108010e0f150601030507021006030809010f0f08010302040b0f040509030c01050c0a02100519090f03140c07031e1a15010306030b13020a05130504020a140d0308040203030412 83
    0x6d4595812680401c0003504501c24203029007640c0c450208000d10081c0300a2030b69051640f07034000a55078038424407190a103500c50010030000f060f124100340711385821010310b4a010405120744507402e107001798883c401800030f80d580c209040c0c2c2945e003400041c14030300d903001b50489215001a01e00359101d000c2c080c4030f107010000a40e20b45007204010303403d6502c05455882c00b038804008034402d195000c11000395030f039215007000c0303025200c4488009082160034808501e0926040c1c03250200f0818480700c0e5003d038069600c4c60300d1000d082d9024400c510910055202e2540049010030010300001e40c0301120308c1895100c04e540040c90345034001d20b4040310003400c4c0d0800310681040402072000c1c40c0c130700000c4820b01e8100300050441ea030380c00505501400c1244044c8800c644a011035648100c00c04c00303003070050520082e0f05054240d0001628043d00c0882c41100540d1000c582c0784140c03092401908401000c00d4400400f0351801e540c481c401a00c2039030180410400440c115003600950340d6210300c28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130414433 1250 130413183 130413191
    0xc041202040c030e25090603020904032604050f06010816030b1b0c0f15130308270f06010b0c0304060f030b03030304030504030519110f12010c09031b0e0c0708090405010801 76
    0x3d02c070812001d45003908881c4081e4034007c401d0000d078031018201350b842079143c24005110007030500c4040900c26045001d00c81c1c0150802004100b0034045000c14180d54050102c90382a48c8911145480c0c001d1030060071100c9546010030004680c00c42a0307240c0001c881c03110714000904001d098040d41d031211810541507405400181075052040082d800e003176080050030b200b1400c0001a910744002022405002c008004d070118a2208000e0b1720031941000040c4181d590858461240c0d40b00e02c03840103512100d00408000084104180c0216402002410003440c5001c0c01c203001554a518003500b02420596140c02c40015901c08000950285000303884841c3c43d185945802c034506004004207081003c07085442c1d02c00a038003104401e540d07601c1100c0342c0c82d81c98610b00105441400e29a00c9003c150309019a0a000700d8111041c80d0541e13003c1d0201a21100b030345185403001d00c900780301d088012040e190019440103d2040a0001c491140201031b207040468400541910000e1b04903814596407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130415683 1250 130414433 130414483
    0x40b0304030507050d140306040f0b0306072f06010e090f01020f12070e220b0405040b040507080a080904050a0603020409050d0e1005090f0a0e011206050c041202040c030e 75
    0x204200c6000009032034601500c1a501222180301b05000142216014549400304203100c0d1078107401c210000d44001d011111076103082d507001070102800d40c080b140711410134581010110507000b5000c402c100b0840c000c040c00d174039100c0c4400e06018001c4ca03608070b0380111030800c025032400f0f00040c4940c4007102010354a1344c4440e0354070f014840c40506510207118034040c21080645039803551682000e03214034260504107484e080000580142e030b1090b54840c0c500030801c02048034000c5800d002c2e901035030448044548501c80c0384e603500807156014000c08414801280145480d4010b20b038800c41da904007041003903580d0b010800fa10b00e181030440e035640100c004040341c80c0e0700a800381c4c001001140c0c030349101040c002c0302070018801d11400c0b500036124643e061256848502c90a80141075540000100d9a501e03000458241e49140041b140c03203082c8404621402c1000090703609072520041440303082e06482c0c1c20080100161703c0c8640074183c40c1c00c20303403003a12428007000c08501d459011580800751 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130416933 1250 130415683 130415693
    0x303030c030403021606320d0203040510050c030f06060403060c050309010506060a050d0902061306020f060f0103020108060105210c070c0503030406090605031305010603031d03060103080904020f040b0304030507 93
    0x62500e103101170103004403c00c00d01d903001d84603e0310641c4140d2654902101c80c12030b400102078459411a0b043d0001078406003060841d8015442140910240e4200d84030042602c000da03201980c03020400d810a0000c120240b03181880f103a0030440090030039140030f07600e0780c030768058900075010031011480210030400840c6c1c003070013103c0d0f02540c02c42d16540703440f1100c10064070b1402860400ea00303c95170b90060400710b44500b0200c2d000c481c01e0300884da0380c49682c0e09000b591041041a003940d20b00551000c6020398807030400f283d0681c1d0b4161600700c00c1d42d45440045a4a07040701e01e0341030700c646844824030403504029100d60700400180344015a500594101503030b0448050384854080c0e0320410040064551094140041c0d03001490700d90b90b03039141c501540b1441c05044c03c0290055282c40000001c064101e14011014240d8201301d20321940c039542099285c500c03d10010b81902030070818a04141703041c0d4018101d550401030b1103400c164035234000403441d8204603401c40c04070382e0000307075003080c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130418183 1250 130416933 130416943
    0xc0307051c030b19060f0c02030106090e16032117100f0b040b040b13080708100b0405071e0215090c01021e03180d051516050906270303030c03040302 66
    0x30011340d4000030700c40d03240c1e130065105400340c42101c08000001c07100d101560300c00d8000d034a405030010000d00c5420340b0b807a502e000030b2170321a080c5000b9200f0581c1c030340d04240906c0380e084c0860f900032030078003104544c140341221904e41249a03072040003076130803880c1c80c0060a6034907940104d00243c004036420341060081001040c00b60090780380c418080c001005044051411142a02c50700d443c0540c40d02000d1a5520b4060310391b80040449010b418408280c1c4240042e404440b850200410700c000b42500e02440103d62040d54490000fa04010900c40c140501842a1619100c0351044410410080401c0c101201c000c5e6a40c0c210358000c4040142c2a6a04000400d400411200c1030350f56441c1030140c29541c0d1190811105501200d00200c808698941a0808800e5000780541d4140204170604021b03c0804842c1c03d002c0740d000703c10039808140b081040c2ca54011014081600c0c04807040c0d400860200000c00f0001481d00410303141c3d5403174400380082e6005154483c030083c0c5a00342481d0181c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130419433 1250 130418183 130418201
    0x4021e07060e101509151d0f010b07020f040903050c070b0d0c02070608040f03020115090b03160503100207021207080a031101230403021c0210051303050f0c0307051c03 74
    0x70904010200e044201c4d0980c419088410b032510010722145d41d030320344020031400b540c00010b0f0b40710354003410001030960391a1217104045041a48100c2e13a200d0100030b025004450300a0341141119103209260b0805900203c0300c81e000e4103042d0f04110080951601d40002a004196841008102c46e600d9002e5406402495011030020b44817403400d1000050603214000c00c050415181c00410a06050003903005202401502d07091544860b1a00408005052102032542c002d00c034040d041e904000420038450107644000b405845400352044000000e90031544003a83d000400014a14002404010000c02070402c1806060704071840d083c05060700c64060716003841c6905042c1040409030003808010000c0110400300082515071781012881d0030301d4400400204100070b000d440b08640c000880351403200e45440c041c80f856071070060000c0070125803a0018046034003407041400d02c203071020241c00c3c80301b45141224180211602d0b4185041c2d0170f1100c4142c06100708502444040e8180240402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130420683 1250 130419433 130419463
    0x70309090204030807030f030e031207020c030604110d0203030906121806100302010302030901020d090b0105040c210e10060b12090319030e010b0a080f07050d0503070204021e07060e 80
    0x145480d58135101858071034890020f00b007106080e8480b140b10b000740d1105c00c05035500c0084030303211182c0412000c0c1d05803055076488058404e960b540803d03031a0001d01a48501d9104076180b900400c3c941c10311074040d0f00c00908a9050106000902858640901030300c2035050510882840c1c0c28882603911810301100500060f540200040001e07414103600d94404a950a107801a56596408180360081c000c46000303005003400d240c00c850901141400e402c2c183c500803501001298103021040c5c035602603804000040018500c0d404804030300a5005034455818001560812000940c0000490704030390055601d04101007096080a0420304c8150f90080e074200007189860a0355003c107118140d078110420415465050a4401c030350b0a4110b110171040246c0254400c80e2102102500d9400403410282c4074820003000040603d0030079111081c254012001d145003007000d0b020300000e54041244d000b80c03001074002806038107060f003008080040c003441000035101e0a00d10f1190414014402d0010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130421933 1250 130420683 130420687
    0xe07030b06060906090402030405060a0c03020a020a02060a03020f0c010915020c0a0b060a05060a0210050a14040f080909040302030a08010501020c1509030a080310030507060203030f07031d030f0703090902 90
    0x40d4400e0300190808001c4031078039280c060850014041e842116542900700f4008403e000800c080090214010a4a40c10610003001c81d000101e04a0241c0410800164031080095025051620003403019242514000d480c0c4450004c481a207a40690302042c101e83d5240e003554180295800c0041c0386100722441980340900104030540e495070900c80c0900501c90b490003148a03076454401050041c10094207141d21018000c2d00651550030000c409400d0a00b89000100001d00380d120740f403844844035101c041e00d034949440d4508603150600040701c80680403c5013480b2541e40f01059881140700707500440d51000029002080d00d0f0701a44402c2c190352100d000880a560780c140203090755080c02e2101d6485000e031000191030315007c2100035103100400002d001c4405144058441030724015421030b06803d581c0c0c841207a80740f00442c0c821442880e40000311b00303200d00c00e4004080641104403106e034100c014611103400c5030b0005031b070822a1ba0001814004041e00105100024205848214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130423183 1250 130421933 130421939
    0x5070801060b12090f0d031e050c030112060609060f1d01050f040915111e070812060d120201290303090d03051c02070c080a0c05221a040e07 62
    0x80c154083d1540021000c807440000943c65134042111104a002c0c1204070740b0340c8800c024010b4018842016076040040d01444080c00c0c1e102507005040c0079015007007100d85541c2c03800c2c01007034a08090f00700c101e40880d220000002c800310a802401c1c05426003105400b103481c541150440d015842003070040c100d51484bc0104056600e00e80201003002e02034801154810940c5003451004d03442e011026252031500b42c10100f007806500180500b0b140007100c000ea904000035400109001e001c00060010400304290b401e074001c1582107580100000e41400c004400700c2da1214104040b1080303500050f951440d400d585500302d680702c0c00704400f400b0f40b41c034100c0e52500040783d1240b1514500130b0240c424201c032403040500c58000c0303034413002c80840d9a800c41c515404410700a54010b810135200007400160110f03100e10040345402400e64800091258180b900e0180840011107403034680340451520002ea03c2440e0f10300a8003e628000c0c0d960304800c0385c120f01040200c40880451240303e03448902d0034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130424433 1250 130423183 130423199
    0x4080a11010816090302120f011103160203070c03030509060d0504060c0306062607020c100203040603050c1c0905010b06070302070504061a0307051303120c02041a030c13021201120507080106 84
    0x304d000e80383c059a04a50303400102445910b003c402c05002030307046d032804220426401c03a00000d540207019100030500607113401c0200b00ea40340514240a00f41d071020500410000b070080008068507400501142c0c1890401c030750a40803100101c1d030984000c0d413035080701042c10342c4c50f00c00c0f480501058105101d120382c104c0034506048419001203003c0c41514404503480900802103082d60f4400240000e02e90002448003c0d01c9801c5131007a0804a130410000c9900e2100c0f003801d84001c9000040824401056112160b001d0141100300b03940c99541c40c0d02c00c0403d900c2c1c140091141c3e9009800600c0d2441c07074075040c4011142d0f00e0b4015081d0700440b00f101000e01303050380c080701e40103510352508507191810079003283d551000e254001417240c0941d841c0d8040d40341e040195804402d0084a042085211600c8203920000924101640c5034114410768851440c0c120720702d00e441c40002c0d07001410444646d00c50710180c0001e80202d01a0401900c0540c20000304007c1d95001d407501c0700090041a02c0e000314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130425683 1250 130424433 130424447
    0x2061801091e0b0f0c1e061b0d0b0103090813030b06030105060d03050a030b0901240f0e190302043b060601030c1b030f0905040b03070e0402010504080a11010816 71
    0xf000050079000410b0842200746400341ea100008105c1034403881c809141248041c1e0138401c10540d000c1c01200e0010310059114007140700d0140aa402c550716002c1110304d4040201384444d003150526955080b8000031400110252102155a00e8a85c4541e419420103002048008240368803981c105000c01501d0f48508002885081d41407d085840307001c110400d42c003909070041c01075002800700d000003550704d5181100304046c0078412980c1105591030360040790b20541090b4510701040d49000410384031700305a00c4814a070641510240b000365160350010f0142c070b4820312201c0440103e11643ca8200140302007000300014851554161410013032101070726240020f0034141850390350388604201c42e014070030300d0a200d0324002040680e010607207000b8040784600350401000881038034001c101c0342040c2c42001d000c440010003c00c502840c11542d207031f014134002c008a04201c018840082c280f101080002841446018401101c508101c001812100300801d030303010b0484821451803805810040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130426933 1250 130425683 130425689
    0x10e0c0405150d0f0b04050d1d0d0b18010e010c0f020703030914010e060c250b03010e07020115030302060910050105220e0d020a020f0301061a0304020a0302061801091e 74
    0x14014900c0d019400d03c44c96040c09030b0005846403640c1c0d002c11040000108d0680025450707504c801604445c460551039101d40c8041003103802c01030031208400444c0446020070f80c02404400703040010702d030101c0d58500307607070042020f415a03a44498a450032035400c8802030b0b0122410303200a0481528580b001071880f41503226428240c400300000c5e00391a4401e10030301d40142d0002d00a6543d800e4660513031940c42e050071035003010303030510a086868000f41100d00e950440c1c400c1ca14690440e400d05210464401000c0d007850b06665844602c02c900340a2640340b00001c0d40245c01030255460b112000d2410f100b440b440440305185002e00602c99565480410091907800100c6842502103065034000282503110795011207120b10004005043d80c00501600c3c114400d0302c805080301140f0f4241400c2ea4464090b04011a60001101070702580d04400b41d1761207400108082c4c42150741c0c0c0c010038002d40c401143c00300e4261455440103641d50708040348030000d00906818542000c5046000d003c0c980084c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130428183 1250 130426933 130426939
    0xf050601020703150209060a170106050903030f160c060908010509010c120f110d0b0f0f0d0b0c13030309081903050406030c050c0f1c03020a0206010608060d05010e010e0c040515 78
    0x4a031a043d460745e9040d900484005030103569102846540602034600821000c03141800708030010a940384a881590310102c0013400650410b10441c0320407035160401520542c4800515402101292240c2c1600c4024107150321118000390070060010b0075128001e010100683c102000b40c141507503c034240d03220048410900080d0f503585004460054030104010200e4008042111643c000036a03108031072551049a01c200301880c1c200c04d02c884030354a1024a035001c21141d182001140301c801055030700650804030585801b651981c000000c0c3c140790016000540550030a0151500c00c1100c80b40d0414960b5070f1408600302c1c0d030b400400b50310580c0034500c00c1507211810f407034095000d402a502080c40c81030a07a03140c16040b00c000c075030704c68450042d040f94160031008450058003c0c42152130f45034241d4007800f8641c0c00d001f03055900e40805080b55070814a00c9102901252081c45030046d203000303400c00414180309020384185007941d041e15051142c0e1401d400e0000042e0301c1700000d0076a107425 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130429433 1250 130428183 130428203
    0x70908210c01060306060501110106030803010510020703170301140108131104091703040c0f0806131109090114070306180906060b030c04050a09050c0d0b040617030d0f050601020703 80
    0x10108100c0680540d01100005608001003c01007064503007021056400c01e07070f10089207445442001d4280c038032a05c000f50090f24200010701c01c03070410342480151903040d40100e50203a541e03a5a440c06036580d4081010040c2400310060202000304140221607120900e4401c2d1142400d20000601c43d5240400801c004480c82107040903881c0c9411032899150400428090080c4022083c4095030088808030380001d40e00c0e1011450900c424080d1003540d02c5e9400070111690703980350100142140000944901412850f0116159540413540d8484c8180c4000031a81d4a41e1918104003440042c201e20107141c10440248101640111103503441e4009210100340a18113003080002030542e504035003000c80c0000200501c504094009108840c001d490b21900c4035920040c0d034044070f40588104a25074820800700111088a81040d0004070005100080990ba107074407544601301d1040c40ea40c0d180c3c101082914840740248982544001450400d11141c540800005e45404880c00001c00c08043c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130430683 1250 130429433 130429483
    0x509030d0509162303010213170309130213050102030f071704032f01180302060a120507020f060a061203110307060606050c190b130501090204020304030e0306070908 73
    0x8202e05580b1403c21074207104165220300310381c950721140342e100d0700c216484074044100e1400c5c14401c0300c05480c00b111414209034101100365404451258040c019403105001812090751042801da130480c0710700c880140d80710507018200c040c0c5c8409501c0a41950420b000b81c01e00b032521041121001c0d075100707100c5500400d0003000c1000900a03504041c0c4111100e01c40417040c0c0800811018026811340ca002e41ca1540890044466030350810b100003501095040420050510901030b18984c20282010304404a45080300c80445000f100c00400581c000d12052001d28020301046d40c1000311001c00340511400c0a42d201c0c0c18902c1c0301002001c00203050b030319400e00d50091040c1c0700410390180041c0304060741c0b508000d02d035810400e0242924002c9185004e20b8034425820040a9540301c00c885245070340721400640c5400710300c0d074141d0b00384d522034180310016034440c401148035504ca510b5440c42c2080100506140803001884403082c0320140301c1c01c0c41039800015150f400706145004421820308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130431933 1250 130430683 130430701
    0xe0a0206340609023f0118060501050406060c050a0308060118060309030f020604210e06032403031201090c0e0d12110c0a120201030605030709140a0509030d05 70
    0x200301e00560621a40d540950001c002558203c50700340340c000c03240041c26109618045910700e001c1c1100e01c21044250500840e80b15440a4100d000000b0f0800003e652502140050000c548008215140c070307503510040c001403a1602c51200a000e2a02d84414010031941d41d1640e12400076070042c0501070060700141080e840354498108040140c429070706100e607150005000740c0640c990460218494030a50104e01e80f0028040384541c0d0018401511008250841d0004034100900c000030009240882000d07610340b20b008501400301c240054074450780c06405541016a140c3d502c61203034008111608000b4034002d69a810744404031400107640f0542d50b0207840740e4004007806608041c00040c140241b1641d080711070010f5040c3d4880020701030008000c940c40354076044007958041d00781030060094040101034190100d10604000071015245c1e0002440c1ca00c00780c2c0010035144d1a030802410041980300e10f250000710442041c001420b1000d225a00c1c0d010b0b08014440081d03a94001688541b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130433183 1250 130431933 130431997
    0x20a02090603011d21070f0f020a1e051002070b0d0c0314131109011a07050703051204031e0b0408090a09110a0206060306010f05010c080c01110408010e0a0206 70
    0x2c1640c5050444021a035441c0d0305c1c0c840c15510029528024880c8114420340350040b00d410550001072121151015614070051804605040c0e0304101c3e00760000c18030702e0418055407201d210118441d48118038041c2000014500e607040d0b0421500001020045544090169036440501e0200860f200c04003031700c02c034010105482040d800402142c10703c81c42e403440c0c13501c0e11401806022051003541381042442030301c0100380f0400c11601800b030003009130b4070503200182154034415011ba5111650b80e440d80362500e03c0d525103940b0300d2400040c00b001081052040c0c4c200380c1080c5504c012660080307803200303c3c141c5070082001d0101c0500164140147d070f18032074070b80060071000b1030405c4480304010300305000340c01a2a02c2c0c8058801c11020480034600050041d0480e481e1400c0c50740540d003000c00465405101b510308840ba0001803140b5541d200084c040c078040c0d40078613442c4035280d51501a000e4250740038000380c0b491a0f00501001c80241c0c031060308071215211158007a24240780100c0101d0089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130434433 1250 130433183 130433201
    0x80903070f0606030201031404080f07110d140f0105101815080601170a0b071b060c02030310062f0304050306040f02190b0a03050601110a06270201020a0209060301 72
    0x54100c1c010308002c2002d954010010f0324001e0303808003d075112500f15014140c0c82a24003414161082c030107070700c0f080011001860720034840c540d01003c02c01c0d45004116071502d4540c045400d800211003020020500304003900705584040000d10107414031070200041d0344910f0044402010030b014068818000747d030020442030007002003010b0343c0d940d102400f0740c8130003080c0100d0795034a944c000d507814248030008140c0300b2039070440c0c01c88030207031680720068038880803400c0a072140b41c0d903010f0448003284d698403c02c11f00c05210b401071aa41d2400c400351800e41c6840b0380009041c0500d030600c0c03001051f40e0280c800071f41010011868444100c0300c0c10320380f03140100e902155251080718100400c114614504d918194070075120b804880350f005014207003070708880c060001c4950742800200c051902c26081143c000c43d06042c0030200120000304503040c082d0b8907106888442c0c13140e10a02015901d041c1c0e9001c007144811049044c0000c5a0000303440d2013a00e14040d10644914022403015602075100c2150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130435683 1250 130434433 130434443
    0x909102930090f0f0109170304020a0314030901080f0106020604030c05070816050f010c150209180103030e010206011a070215040902031006020c061602060315060c0a06061202010f08090307 83
    0x3986801c007400343e5030b109071541c1d900315070045280c029403080d01409404241c0c2e901100707504034629a000f41c0645900000e1044c0c0e40b00c05c1c0b5150002c08501e00d86e0304686030035280c901450741c4036107820014001150280901800c0c048070b0004000b480e602240158201d64145820104143e140c00c0c858030f0304207542c01c01e01090007008600180465843d0b624421640c0950303480c05180b01001c015a800304040c00702815040c0c0d5624816507159082e40141004e49000b044154400a261860790800600342c03c2200441c075245e00744a4503603010041e803030051007034843c41d5411001804240103540203070036009014105041024201c3c035420400d40d030207440f42000442d240d15085100d80c9104200780700d4800940586226444a8180441104d11803003c4050400d1040701503800e01c82154801000030b0b0754110300200b203041c1565480010140c01c40c640004090b1400e0b6800c0000071580c0652200115580c07550780000140d8200042c8005580c40341801c021942d2010240703800d40c0b15900c00284 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130436933 1250 130435683 130435777
    0xd060b040f29130501170705040e040311030a030203060f090103020f1005070506090304050a09050c0f0703030e0106030309080d0305060f240403060c080114032109091029 75
    0x122101c41403940c80841e0302c240e0741c041040c403502900c80706c41d4101b6101000051410003041c40303802e04241c10300d0707009486880c2007101660200403050454100c00700607800aa00001444520302e00380c20403e00060040b50300c4246035165034001004840c921011034024440e1480d90140e99000d002600c203103076040810340300d5034a08901c0d400d440f40e100340100e5100c2d02d41c202010429003010710802380706105402e00c0070314044e6107240d40d00454208190490815440d80c420400812003030242c0d000940c42501c40c07a8100307042000380e03401c00620714007200806141c501003005035501d542e01d603030900e581600d145a103956018090300b640d1225209000e40d51030001b0b400420403903280d001911581540c0d541d0705550340c80d04030000841840c4c080582e8103038070691400b09240d90314948103510320100c5091501d082144000300c1d1901000b103519142909000b8002c00008111480c841c9040d20020500510300c60000000345440c0110a021100705c1d2400c00c402e0b120701466541445180580303401c0b03003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130438183 1250 130436933 130436947
    0x121508010209040e071208030a1b08040618050c09040f0b0c0315010306080606090c090a060917030a1e120f0902010f0801150e040b0a0b0d060b040f29 66
    0x58041d610400b0901d02452901807860760440001c2039180594014039400003c024032501e030071a072a0009013044411aa84005280811b001c01c40580c51820103074440700510300d0b00e13050010485518010b2403292a80c10101a000030b000856000b00954080382c0c1010310b41c440341094010820003c400a200c3d0440704140011030220703a0203107100303142c1c4e408200402c2d40c41c00011000d840b200d10071803a0700e601550108a0030318010f510f0750f6100144602c640c1c21316010000058002c0d28650122002c81d00e1000d040c400c00d00382440c008010001c03c2d004501d000e03444d4600030031601c00000c8407244051081e41d958081c92041c449082c15409140d4284040320f030380c80f4060000e2480450803404182042d01c03000c04c0f03600900354281211600b07000d400c911b41c10708100782d45c9103100112031b81e4441d50724440c0030200d584070780d940c00142a813040a940ca800c1068001412a0b44603000300b825a2400d100800c042c2c0001030010b010303900c042c1040384140071400e2504400e0510f540c40c16050b000080781103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130439433 1250 130438183 130438199
    0x2030d0203070b0109090206030402090601030905061314070503030a05070804030606090e010509010b130b03070509010807061218060f09020904060c0f05031303110f03030f10080c030d1215 83
    0x1c1e05001c1e01900080f803241c0d80c2c030352444c41280d2140b58001c0d0030110a00014000d0300e0301800d0350341c0c001010706001c01c05004503602e103810a80d04840e075503003d451007094074083c000044410080360b00a0340041030b03041d0800d000a070740d901501012404002000500a04001401083d98001c46d4890700c00e01c070258491203000f018100101200305e6a42c07800d000116480c00500070700411030405040c231095000841380d400c002d407240c06895a014811040002405e440d0154000c0c0244041d00c05802d6090600b807000301840707081c900300082ca43c00c1c00740d2818640f40701d240c00d0307250384c4d07005030001a88050300001c140034060303d580196002c0142d500304020700c8459000004030b004280c0d1154910380c3d20f120f05691900040c1c41d401c1c004086000e0b000700082c000d5603070991010b110022a07000c100320442462840d44200c3d02c5034801210181032008008032440c928025050f00c00242c201d1112420100f542c501602c4a210100b210b0301914003441c0801d03070701c0004007a4401091550250f150f0043d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130440683 1250 130439433 130439437
    0x20a1a010302040b0f090103060f0e060c280203090904060b030d0e0102010609020a2c0d080d1b0f0f050d0204080714041415060d0504050a1527080702030d0203 70
    0x400d80c0180e013800d0007104507140000a400501c40014030b80302e840d03421611400020304221601800d0555143c90344070210f9810040f05104030403a01c466513546070482180d0905d0060000016048000c1132025040560007000341c0d1240007050318101c0e441d03a594103204020740807101040740c050040c01d0242e040a5803003402c1c0142201c007038000b8441d4650700d1300740350124400d841000300003130060222031031401c400021200d071144280c44d034080070150050000c0d081900b009011600c100e0300140b540c80c008250b0280300221084602941024511000050403004c12000d42004010b03c08240b1907d00c1c0c0120300b42c40220307490010440d102c907140c0001136a505581d005581c008001c0c202d400c0ea035480c03d801747e103000d00c150342c002c0126521000702d0048244070300c010295000200f130002c4041003000344109031107540580300810f00c4580e039040900040003107000180000703080116038000e20141070341018140c0702056181031070400505256540e4044c01030000d51500035040611609940040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130441933 1250 130440683 130440689
    0x705041b030c0e0d0204020f121326030c03060a211407030c030b0915040609030e010c020a14030a08030103050d0206070f0903060c170a4701020a1a01 66
    0x3401c00440c01c02c81e8040d5031500c2c44508036a400980c507a42d40300181031030b070050f0441c0203842c840c0c1410700034203606004080310203c407800b804600c0e030100501403040f44034401e031244102807824001000354203002000341c131005140030104280000810f5964407884004801804091151301c100c0100e084083c1c0a4648940195002d00d42204100d1202038041451400ca81d804030058000502c3c0d591030720030440d001840890a8001e0800c400744590170408028856840b030840011045154a00500102c00030046181085540c0b1401d500503222250b085080c2d03044c810003c040406c400340041d140c050040401424040d000c4000400c1082c0000c454140044a03000d480c5140c0e02c5541c1203543c041c20010000028090120800101e40381d079101310003030225840d005120a01e0f0300101040402c1c10b42d880e0600d10707501c4008116a216030f20306140505070b040440c4040e442804103084585048074001907a1420298038181243e000300080d11400340c1c48280004115000c52084100790000d00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130443183 1250 130441933 130441937
    0x518010e010f060f0506030a0c090f080a0b01140a17100f05100611030f030604060305030a09090b061c0b01110d09051f17040303180b100504020c03040e090705041b 72
    0x843c0418018032000c02041585c4c000b41440f07085980f07440752180a094030003045003d111106601141c80300d10b83d00801d000e091198001e0800680c00d103803d02e160001603002e5050802c0100ca040c07450fa84a204000c101c0d940c11402802516012110904224481310044151740c5000d14006038154603800041c8280c80703218011200f207aa0300c0003901d50010f4100c1070025034000304481d1241c03a5a200146030001d101070400076944d51607980d05481c41c3c0c407034a03880c804034800c1c010811008645004800d207040068943c00d08000c0d00501d4250300c42d8451030a0308006454601c0c00c041d5900c540b00d6056448200b0080b0b454000000c08042c0148200780223880c05007644d80138500b6041030002000d00c107026540c1d50319140e410100818580084094811020552079601000f03c103607001c2803081d2401c1c0905078904060420301700e0340e058080b46900240c01a8014096440c2d2180c0110688045461407100c40c141036840000c0365013400c036a504a43c0d0302603e403c0b6070100360130030b144000310503510503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130444433 1250 130443183 130443191
    0x6030601030c140a0801050a06020106050102060a090618060213060516061e0203010e07030608060705041e0504050106120e011404022205070f020c04140106050f1b0a150204050102030d0518010e010f 87
    0xd279412420780e01180203407805644400b0102d054100c160303000405c00703402004000742c821020a41030180742512001558510f80101d401501d901c00240004020314444c100140391010103070a8101868060001800b41d5584003444000d40ba500480300b008545038080c119525070316410a04024203081e10148002882c00e5404140c9600002d00301d401182e0b0354490780d0925107016004100303081030041c6c2c91404001400005840d0301c9038003455010f411503480f2007200041c82d5035007401301c801c0521060b90076070520742250b03074890243c65500d42054040c0d5019050b05946051121015284040107241604d4041002140c0e0b5000d4404000c0d20b15542c282c0d84d6110001007044182e070000a14488001b00071030042200901480051582d204629076680c1803028084803009520142509450680c01048040c000c10064441c910b0069240c042c003142003a0030500000e659000b5000a000b04980c2c40b0041040620bd84451200d100d1201000344248189021454040e11410320b0599100d820 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130445683 1250 130444433 130444439
    0x402071b0b0a0e0907021905031806040f0605220303030507300e0a0609050703121809050411032a04021204060506040b0d0f02090705040506030601030c140a0801050a 73
    0x101d2012680d080d161580c8001000c0064401c0081c4030314081c040c20250700c90b1072070341000c021480e4020541180030790f016503200c004c0308a4100103e006121414402d480400080c442130328684202c034103a4016143c255150400f089642e19201d80320341a10602c113800040000405074103800c03552140c051682c41026148120745552402848500907008404400000020340c4802d50700400c0b41180400c100e41010459449000495410740400d58150704a030b0003c0c82030000c1d00c1d80780200c1070012320301454944400c0b01c110154162501420707074515110030118040c41511456040d0340000101550350300e400780070a40e000000d1100b0314002ea000742e5080e0540529103442941c0c518503620b4065039060355076a9032080180703070041013568400da5410f40c05110b83c8884c1e8100e00014441e41940b40d01041034010000c50f01402407400003002400c100c04d00c56621000c056030b80100c000c5c200441d4400401d4020344017502c0d6061280c02004000c51350841c0035030322185050494105660650700503072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130446933 1250 130445683 130445699
    0x604050d1b02010e0f270f0402090420090702100b01020304080c01120207080a020d030e0703110112110a0e042003011a0c031c0506100e010f05090402071b 68
    0x40085540c5030041d0404806026502500d11a109190001e11204251540d04001000140710b804181d100704a01ca14001403000b14440145e04921004000c201c81e02c1e044e8009030b00c401008200130100c04101546262800200e01c01041404005080d00c02038070b0f013800001d64400d40b03000086041818180720f10b820b0350001c003c403002e0703030180c0020708014142c01d40150f641e0040468454031081e130800018001c01c0032200501100801079001e00410740502170001c0c1521001c5030000c540c3c0c0c010b950308200045c125041d42145510038204401100b01c109001e0b0007d0100d80e4002801020016038643d005134050b00301d841a800c22181004010340220320900781007240000074410080030801803003002c0103100394624403604002c5007403805d1040c0100a085412100c0100043c0c00001c0540802e048035019940d4000d9040d00e4003115880c1c140801841d11079070300000b03818044180d0355012810710a0003150a0344601500c259560708080ca428000c40d8a403108903c441d40c882d40010401507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130448183 1250 130446933 130446947
    0xc1d070810051005130815040506012106050402060d06090e070f0e1503070b0c03030a0501120c030b071112070201090e0c0405190306090b04060605010e011707200604050d 75
    0x4002805025101071a03883c20b6400f940103c2110b01464043c102c0000e250404010100c144401a02880d0981c00e2a00c1d00601e001410703046080d0a0a000e501d00c41d55001c0030888860031500000081204d4440f80042081886030104603946103040020100c2c50110a400c0108035100f5541200c43d459614007443c2420304907401031103c0b08540501150400001400001c1c10700381c001c0689490540e0388000e41c00c0380d404940c0940030382e0008001c0182d205524884c85004003961807074007401030700070380d569280c3e49401c0c04020718022440001c5044184500d07031071a0024540e0b0101c8a1013000a02841003540004a040f4000b926000d0b02160b107034034444186001c4c518810910341054200740030400070310008040640b00c0e121205001000c161207000320711481740604040181410a03003000c000340c40894200b94148070b2001c03000c46da01d91b80138980240e40300010300900c0241d11154030444103101258944096078250950340c911b00320020844500840c81001102c200080b441c500391060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130449433 1250 130448183 130448189
    0x51903020312060f0307090516050a0512041b030602030108060903130b0d1b20030306010f03051302060a050c0c0a0303090b1b0f0705150708070f0c1d070810 69
    0x58200340985141010b030045425040341004003e21284004100800c0c5440210303805410030940300d200b0b12503000d80710703a05501d06d0506480c0c05460011460005490351288011184940e4003c800060030b201c2e090340714454070303004a42071901280d0b980c1011000303500280600d81300b40c040c407000305142410000803164203090066000508030b191062056441c1c2103084511035407900c812018414400c83c1604007550000d0740c807030a100c480c4074010441202019041023005a10800074440e0303070fa8100700403140c07510076071034085180da48001c000709110485010094001c2c002040c1c8090301500300c03010b090050024002c83d50b0f070300303c04810018843c00b1440041d0100b851141e082c031000c210f0704003d00e002036001149041b2180102e03001c901d810420110080c80380c00c05002801203180c41c0b080f81601c10740418425040103240d4030354440d50b100d03924008005591040d400800c0148251958000300740601c071510300d04c01d01e15400c085903c2c0488540c00003401500000f800380700c644811000f9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130450683 1250 130449433 130449437
    0x608070810140f0a0e07062f1b040b03100c170402010c0f061401060f09061409010f140310030c1710020c0a0804080102040e07080c0a0503070c0206030a09051903 71
    0x30352503401c007100c02044041c20a01120b6250180c030303040340f4410001c000c004c200513611405840d5201999880608190010003070080c3c03c8d11412128050000e20000d60400001030500c00c80c0301307140000c008052090344e4030f8044c00795510b02440000294000c0408814588030801100101140c4070110002141e0080c0882d500b0310f0200049030907030300051149441440c001072520b80c4001e015040b0f020981c8200300048034804411405607010020400a00c5a42004503800240001e0305002d8043e01c0e0035181080b140d030400280252040c150344075111412001940c3d207080002c61b035074030b004181c00f05991440c070317800700051420040c100000f0304c0c045640c0600002501d01c440c41000c0d500840d0402250b105811a41c00071a0b040f0004000410642000603070301c600c0c2001031030301e05030b004010700140b00c3c08800300452021104200c840e900c580b40342041d83c82c0c1d00c0c40410340703c400c104032020350401008001c100000c2c0a9500000368680100222001e1000d0300b4600c00c0c07103007190540180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130451933 1250 130450683 130450721
    0x71d18070e072303040b0a1112010b0a090e090d020705010c050604020415050a080102070b0a09020112020a1403041202060a020a09260a0503180306040215090111010608070810 77
    0x31245103d030403c0c41c2055103424020030314128408114009400c26603003a40c0c180803d00c18400c0301c280a2186030400b925090f50141411170011900c80b1100b414422a030040000042c1803031b04510a045a901800b450108074000e4102201da8070740d680c0710b5040c0d040242c0b061b40000701c3c003580602c040044443c0d00100604580d501c0d0303803c1c00003a00380360800c80941c461883d004141035540300f41e068082c0028100068660245062004120300c028149030f154074901080d890141c1d80c4641c0c0d02c02c411803200e1025950351403440c000c0720801d00240c465224a880841480200066900301140e5215281c0c00ca0f0070f1621001140c03401c0748100f4905001203400342c2c00812856482100340304400c059000144406441c2c880c1c11800c1c0801054220703400e40000540400441c5580c14440c145601980281307480d180075404103d040d959801c0c3d454440300c021640d0b022130b07072190341080340e0348a04900034044580c1c1c441415940f040b00e401054901d002d480350b00384c125000c5200b828200036250607005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130453183 1250 130451933 130451941
    0xb06030102040e1302040b0306010801090308061009052205100503010e0105060120010e03030c031b0711090901090c0b04060306080a020f04150b072d0b0402040c02071d18070e 77
    0x444240c1604d1080341c0142d2a08034142c0140c0d004d0101d80c2c000e054600c00490103d201c0d04d402498030704001c08591040b86c0050754029010307401a600340680300f00b650003c41c120708803d2110520096021404550341c00c00080201d500f050005072000c844d002d400078001c5e442105040e40c2038503c100e032840c3c00580209540301e0740e410303080c036046841c0c90500c000141c083c40c165285d5045502c2107607452210500007041c03168080d44940e000c90300c0304544000e24100f071801c1c1c0d6050340c01c5411100403441030300140d02081c22080c080d8800d01798603500000c00301c0c1c20f5640c0d00143d901d641140c400d260109203003400c00591541c020451900095000b86804002c0024004000042c50303810803081855202d4007002ca1540000c0c170040136042e024104000000385d400041014040313010403075031040c0030700c899030900103040c00081a81080d41118003041910780f00c10100d142c003070540d202c0b041800c401e039040b10310f6110909841d070151100041c00c440c0e0b510780310300095892980f032050130a40c082c03000c002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130454433 1250 130453183 130453201
    0x3120509061b0f0d021e0c0322052205010503010e0a020603100e090a060c14090d0203030f16050607050406020a110a2d090b03030d051306020310030b06030102040e 72
    0x141e100d42e0900300980d800c108000907154002c0c3c00003040000c420b6800200c0300c410f00c41c0400c00103481c2d60303100809440c10284142c4e040d00c070b01aa81500d625106d1040b01e600c1c941c0039002c601d1020b060301802003524180101d6040031030700b04c10110b88190710b24003400426641410300030141d0451520b0000d042240541d03083c4040c66100615044490b41c58182c040340812012180500580c3c3e02030080c10100d11600b802d0044619820660091102c060490040d0305414000c0d258008407c81e101c0ca1010300600101c1d0540c45003c88075680010002800300d20045c100a680316224058421210b40c1c0c2d4400106a41030b105600610300564440a1260005407035011000e0072100302522508100d0790340c151229884660742158016042c8075000c5035100c505d011030b0307080100f500040600240d404003000c60340f20b00c21400c0035008a0b46840c0000c2c0c2c1c0c0c90030312102001171a4400780455580c030348038500d1000780080c1c1c00200d4030b014200c80894106c0c030f0140241e805a448940221115484003118 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130455683 1250 130454433 130454461
    0x40c050301051303050715060b0a081510050d09021009030b15150d060f09140603010b1c0c030218090d050901050301060c030c02120c01090b250c210312050906 70
    0x2c1307400d214221506043c3d1f800c240900f4008019204a007900c64424000180c1070a40042201c000b1140244880c41c0c0e5580c1c8465410610003e402c28540d01c1c030015a616000c1c082d10707100070303411981d00398165a1040e400070841c011a8000d0010545540b0340444104105118483c82c0f0340c09140750000c1414107180b00e0040c009090041d42c0001d02581da903070000b801e48500c1c0d0082c1811507a07040e0314144030348540d1100f644007008400800028843c44001f43c4000040c9464620140b24164403108000101042d04080c43d0010510f80c2c100000582170f044182d030880d03a0204038022020080d04543c010001e0390000d0005031100380c2180c3c24000200d5040314407810507001c0005036039051016813942010741c00b101048d1005404020341e0701002401c262580d5020f181901d00400440800140e03e0320140c002c6040a2070600c113034202820300903c0101c0039005a040c840038816403079601d040456406140d40d100391988030700b0491201c41c3c01c0440301c041ba004000b9030421400241601c1a443e1f03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130456933 1250 130455683 130455697
    0x102121206130f09020a140907051b031b07051005070f020406150801060e03030408030d0c0e120f01050c0313060e0f0102181306030c06030902030a080a08040c05030105130305 77
    0x1c40700c0d10724400101500141d0b4951080840100e135584642000d6041900c50140139201d6030442c41203403507002d000300b0711184005040004001c4049464100e02c0c421001c084103090b010411070b901c483c003102000c1051030707c120b003d4030300748201c1c030b000286e50401c0500d00e0f1300c40348107449035424a0a2500c1e1034030400e4112404a0748940d07151004154100c0c0c82c00300e007002d41c015680f050195810800c0c081d2003207040115a51007588180002c010080c800001c9030900b2000140c041a403159449054940c006000320307040e404004071113051001800001d0704950102ca010080c40b05840d15038207551235100680d800b030725580702801200702041054100781c045866035005c856031100c0d1501d5140c2240c021102050f909603840b01102800e00d002c03600a00491400c11041010500e0f542d620701503d2080c2c0304410602d9181c03e0b00d81c003595414010a680c0f1a00452002c2ea2501490001002c01004403400c580023071840b2004940b40c101485054070a400c070050102c004281500d081e182904000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130458183 1250 130456933 130456939
    0xc020c1018031419110f03010608100f15080d120c12092a030c0902161205041211040c020c0f01031a0a060903050d031b0807050c0114090c0102121206 66
    0x40e1002c80d607948015040440a030051a0204001c0117150402c0800304040034040d100b030f8101030040c8800038000c038405c4450501c01c10005040840140b038400980079140441048204480380010481008590410381107030755030fa204e410382140c0d40d038a070888092084400009054064001640040b03a0201d2107450040303d000140501d00c03810091920510403483c009458032207420010449056002d0014000c15001513080c50845100400c40403110302000d0101765100c4079641006015004490242c00290241d07400d0341c50713900340804990b41d41c3c6c0590f4020b41c034110b1031403ca00d10109408000c0034005061032000c1d201400110040c8c0000c500c0911040409220400d0503958064640c004004544134628600d285051540c203119504c6040c40070303d420046089440f4482c0000501e01c00158101641180c42c0c41d0401c45440c0102e1803100349540c603203042d40304049044c42c44984228071070012074010038080c40049072610f00100601038400014421031049a1045943d81e520003405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130459433 1250 130458183 130458193
    0x111b042408010b0114160803190504050312181002090a0518060f0a03080306090c070f05060411031b0405040609170904140411090601020309040c020c10180314 70
    0x40d10221001058036032000e4510381d9501c00c400303025608a0b030341203005284c20720301605266208600f14031252014a004008030800800125640700d0041d10107444415130604000c9032819150556881e0f002525800c0e01a040e030002860003004c2c900403402c80909030f00541101001d40d0b02e9000039401c90030025030b000c285080c0104480c0c80d0b4000d03444100311240c007400d5103800d0020a010000100d03a54050240240000a00c00f142860f82181d4100e03200f039072019411b5940012031260390041840007401210301a42030401e21100090340f500940c0502035004090b28004100b554803424460302500c841c0c0109400c890510780781c0d10035035200b0f0040502044040c100d035951034202c245010354010009003c42d00300480d0030300744121941c0c65220342c065101410306484c0c1d42d110901038842c1c1441080ca940014a90b644288180d40c580d55025005015015881801a49500e200031030207004883d10507483d142c20f4801c1c03501c10f0301c2000d42c1850701c0c01c02c3c0c21500e41c1c0b04001402c250130a002d10071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 130460683 1250 130459433 130459481
    0xd0f03060b070303090b01060e0d030e060f03090a02030c0405090a0b04050304120c14010512040209130b0c071b0303090b0f0c0303010e010302180106020c0d1401020403060903111b04 80
    0x1281d0028407905102c2d0754000348a010724a0402190345060308200104000c90080f021030791248041d00b960b0581500f040c0c0084182c1c1000a4020b20a51040080751070000c410301801100000e82d01c05118421001d450782c6500100a0000305c070401c803420301580c0e03c5828803c1c0864618440150014002d900381d80c9850384610900d00c0e10110b01d1002c0711942d0000c030041101c60104c003891203112100f4a8031074034010465050401c106006000a4840c5a650001c43e40220134006002280d95100001c0070040c07921800500a540102d0020744a10407848480343d682c6600007030b00c01c00c0d03d60540702d0120340c40c1044010354681e085000701d0781f0203041c1000241c0c890701081000d14002d159a84001c5401d40c110700c140440b091803030315020040418800140201600460f030b00c140c084064a007501104031500740307408158003a071074010865100250200921940d034100065441c001d44030f40d0bc0c4c08021041460f40d80c0e004010b4119040d884414010303051800e034100c20301e100400f1402c1c46522030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 130461933 1250 130460683 130460699
    0x3050f15040917040602070806040b0c030a0b15090a0506070818010c050114011d1005060a0309020603130b060901080307081c0e06070305091f0e0a1a0916080d0f0306 73
    0x1e071110f03020074003c01080400c01070394104a58005007101101078022070a29075160030035908081d008421085021000900c1c1c2006540100c3e140c540007005211940d00b1241c50f0b04195011001c45401034108420105490804208862003e64007030a103910309003250304040c2002502c004000d04100340c0b080300b280480d00c24020513980c0003022400703103001c1d4508500d146180d101001c3c04001541003504100c29801011585011030310b06683c3d090351400680f030200c0003006508070080d0b112801100b4810030358811112824041d07c40e03000040e0365101d984c104444c0300024030030151254020401d03100010103220241a201403c0c1750029040000c036011081550201215800305912510410403032039414003a00780c01c0f580f4040500342640b049513101101c1c50152241821a81d00c414a83c02d242504014001c4204e401100c0945000307014258038816541c203aa16a03142c0c4519009800010104003c213811100181c006000401c86007400b0b907029400880108181070366042d00240d580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 130463183 1250 130461933 130461953
    0x30c0f03020307080c030903060a090305030f102304051b0406050f0d09030f02060c0901090314121303050c010f080a1805030301060c0c1203020c121c05040504050703050f150409 78
    0x1c00a170002d0b58944d500d02050503d042d40c000c2004401c28206405280800d4021040381e40201030500a0a1907555510001040311403940c0046103400156410b1601500c10b151521125482100c003440192110076240c81180681030018040c280d0822080090a006600904042c1d80901400307051029401c9803030100c07410a0f20640103d40013010100d101c96050201e1a031100120b001107080c5a42040003c3c42c03030b0403600005280045010f50300c0501d4404020194800408094041d5240c0c03041d0420800c03840c40d8401100c41c1d11500016a5040d030040c8100341c5140c01903035501c2c500d5030f03035400110064901e024244501c40c140700c5003e40071800500003140648840c3d11110200f00c41890160792105c2d807030f40000795503070701d192400000a50100d007030100741c4000c54034889018003980400b8105640d008628a11001d00712100c00c0094128001c0d20444034101d4040046031303a0381c0001d80c01c0c2c400c01c0707400300038010f00003000603101c0b91600e00706110b14001070800140003426544424041e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 130464433 1250 130463183 130463197
    0x421020109120c030f030504110409030e03030705010c080703021e0706090605010f1e0506030106080c2206120e06011707080a0c08060c07030509010309020414040f0b01060903030c0f0302030708 85
    0x140c85658400c0a04d0340004038032010660b140b808102c40d1910b070329200c000f110360040c058403c03511002d07404241441541c01d100c40740070040c01d41c1d581d190700c0c0ca015802003181d005118003060711040000e80c0c40703000b482514040780708400702c0c0b41c9080e50b034644c1c207025a01c000c000b11200c903910580300c0c02040da588100d0b8082c04514207900000c0b418114000711008408012020798000c0c0e510510494442c4c8040d20f045609a041c5902c413511a0070810303c1c0b9001b0400c841c2201081200e62840310325101045200300d80041d20b483d44180b0001c59150203075540c0101d103a1841e804600108001d058a4480307202e082811800d4030105500c42c1c2007142403441100042e80c40d42000c120a0225800902c4883d41024410b44001c1c905022550040c01034050000c5150505a60b13260420541d1901d80200d1341c168042d1240b04200d20b003500e000a40d60a845109841145a44002080300c43c00345100d541030366010707100c40c40d0003003071a500c864503060075030b408800710302043c0424400545094054290 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 130465683 1250 130464433 130464437
    0x6040b010909020d0b1309050307170c06040c091a180901060b04090f0f0606020a0b040204110a081e0601140c0705030307030f0e030606010512090a020303031e0c03042102010912 78
    0x5100e400c0420100a51b80d4105207242031901503604001200042117903d80b0798042c4161884086405200741c180c0144407003400e45000740d0082004120084610005450101204001c0a5a460490710084800c60309003034101e40401c1c44025003561600080c1c0e8810828400070441980742c5003002c0c255005a40581c28a5442c3c00700346904000701d004810210030303043c0c01008078916040c0000c3d6103031120a005010703c440d4801240a44d103030381e0051240e410070014882e6840703040010090007801308039004c0f102c640400801682001507401c00c82d01440e4140e4403514500e115034021a0345600c02d618030b8415205241000440f528180040d084d03c5020fa11200d20103441400041d0001c00c40b050317083c1c80307904283c0422440780c0e0030200380c48654046040402c85559454041d501c1c00f50190000b0350b151001008109005070060080155180555a009059142c0601c1c00c001c0780810b45004103450710f50700c0b00c403100d44c11106044e40404003910000c40d00c8a0395441c0c0c40c09040924800b400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 130466933 1250 130465683 130465691
    0x10f0c030c020c0303072102010b0d240603030504061101021b07031505010e1b07020a0e0105040c09030b0a150b03130c1403070303080604090c080304050a061706040b010909020d 78
    0x107059018444269460f03001d030061440c0415a60301c00340c2c1100d1181c2d200f1070240500e080403c14610035401030700062006040080320b6115428100280c440e02d0381c401d222040500300c0c5074034062550040f042102d44c99212503081506150061382e00200071800500259401e01000c43c0038441104950701d460005400b90040c1801c50909a40004026842c000c80c20b003050010410794200a0344c1d0b5900c41060b000616102c0c0507c0c00500d007510030f450002c1d42c000005200452200d4a81940c0790403140c0880d4108005009003c05035192300f0030744805840c0d009008001914084540c1007031300c50285806189903820703220b80303090455400c00d60300030031031b0032800c01c01c28104802001400007034880c21300f00e0b40c4100d003140c0000f642c5461a000c0241003011090110f560f681303854100c40d4410360310400701906d0725203450b502c680e25045481041d108030400f0400040860064808d48070022a0b5243c0720419650340c4203100140110b0340215040002c0040000f4200c0482d1020740034017800300130085 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 130468183 1250 130466933 130466951
    0xc090613020d0617062401170f22030203030109180f030201090201080105150307030f0e0106170d0503220f0210080406050115090e060411040312030f02040b04090e010f0c03 76
    0x991004c10081c0d01589544007030184918040202da120902c0800040f00c010046211780c012954001d403600340d00460f401c8641400a401c0801d00c01a12802e84422102c24904055400f41381c6c034419001d014004d41c204200522a4892a410482c10412058042c00c501000e03076880b9003e69102400540050355100200c2e0219a808000030740140703c1110a24402110301d03001d0f441c0ca100c05018041032556500100d800600541c1144850f414242c0003000059a01c4070315404400030540364071b2003400b402010405144c000e0b020b4a02038496a40e264903617400e103040032211061160020380b5503103000981c0d000140d803030b00760703520310502141e036140045c1c02c0520300301041cac5006070030614411011803949002da540c0500010202e500107500e111058035000003080c0101130f4801100f148078000640401402041d00c080340c4c0b8400142c0c2c04200c02c03544200a0000c03409180540000381d00108420003070300711250800351440d8205000002d0082c10303800540102c0d070701401e60302d0100341c40703941d50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 130469433 1250 130468183 130468199
    0xb040b040f0e01030206190e031605090c03010f0618050604090e0d0903080a0f110f061603230402270115080c0a03051906030c09110901020c090613020d06 68
    0x2001000b03030b0050310081d9411680014801d0282907050600d03030040310500c0300560300c01c3d8001d40501e1806400d0b07402c6054001c0d070503180c0c42598012107000d82040c1000c0b68900d8480c0081b41e040b540c0310042c80b8405ca050020480e080c24546d010420180048440803d00781d40700802080141b005d40800102c0d002c0040b002401e1034000b594500611401400420121b007214085031045000f602d460380000502030800e40d01080e2202c0040f0312031248407480000301b04009500c5009409050a20807801c2c1d40c40c804400342c4480002d0146c3e022078908043d11010000140305030460703c001c14080390200340e004c9440801052000c8401c1c17007103070400100070111405201554032105842d064034149400c1d045903d040c45119201d40402d55200c00042011511100b018886005141c0c140016030740c074103081040080c079010b1b0600d03891030b2a9101d0b0b840b101c010125501614107070090005030640d803081102d2502c008054503000100305000002009440c0700a01c3d0811600c03d00283d03007030500d219 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 130470683 1250 130469433 130469459
    0xe0c040311010203190e0321070b090d022a04050a0f050c090a1809050a0b0604050f091b03100c0908060f010503030d0e01090f0609050c010f170a060b040b04 69
    0x619419900200b0020340c180c030900b0110844041e044c144800703890000c0d008a231a01319a044100814807510071001a2040106d00030144140180d07801d4078036448508060f40c44d03448900b8a400035904c2010a0b582540704d880c244d14110700d0401d10710028080400c0451700b070b00d02c201d41c0092100da07078002e000780481c1240300c1e20744c00925a15459040c11207620118100e0b074214020b0010205000841f031800c0c0d1519002504115071240c06d560a4403c0740c034248000200076103909105030704280c000340c60030749610f2004e440b51000c07078000c2502038101e410b00c03058a00307400840783c0c02d0b024214102c410118980500b00307802410b540d888000c10310384050780c0d0410101809200518900000420030355400209580090308509800251220b00340e035542d005043c2c000340189084055000d010a004055002c0d45d0068081c60507070b90881e100c2001124071042541b5140c1c00b00710004100030b01c2801c2091190781c4011a0301d00054110744a914244a42e04aa4401c0d41c109000007028031940841e052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 130471933 1250 130470683 130470713
    0xa060c020a060305011809050304030206070b01090e0a030503040f140f100b0910030213140408030601080a090507120f050105011e0f0605041a070b0702010f14060a0e060a0e0c0403 79
    0x140803c01541130460742c46c08100308581c0d031500380751520156014040300340201e03001903074014000c6a48150900c4d00c40ca14030001d04c180183c43e440c21404d411901004101400c1c4140d240e80e403030740b840c0e0721036541d0303486003654507010f941400b0300c00f41120440d007040102d02101464000140910035103070940700183c1c0d400200260107042000180305005100340110b0054950480b4010940c4598000740c000038102e40304c60b80c980200504c18070040c01581700056028080c00ea90b0207540780d490003425400d403051094010720551101008024100c0d40451442c0418841e24080e48603800948030107013940d100380c005281e42265410340c1c51602c03116201c03050080c150030840520040c40c004000c3c1160250380302c1c440105c1d0315102401c0ea68206541198901540950140c0403400c256400a00034980c000030401c00300e1070880410049241d00e05043d209182c01020200700e5400c0c000c200d0354401000e8601d642100b98110301040061602c610940b2a601107185540c896145083c2030080c2c200d441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 130473183 1250 130471933 130471937
    0x40e0105061903020a0512030c0105130c0815041707050f0714090739050c090106090302060f0a140a02060403170c190e0307060203090a080f25050a060c020a06 70
    0xb041040180c40300c0c503074242202c400700e84504400000314003041c214030443d49003100725441c000402140c100408045a9214000c40e00a05c0481d150071446030b640c0c06215440c0701b07042c035003000074000400e04444a00441c1c450350207981040b41035600c1e01e18102903080c4015041e001340109000c1400002d414004011044410b044542440700010302516070320f0700440b07e034254007454400b515911a1901904c40c5082450303428580da20b081c9541c58010b000e00162041820100000d10f8520440c00c0368207507178008200d240340c9120000107212550000b0354001c280079600360290303c004000005000d102031207401034038486c5854500203161005640c00e40c50720182103418030607010740c50010745203201c0080700f183d031170b0f0714841d0025562524500d1000d5803500c1450320101d03603280d020011302920082541c1200585456558060300c07920304030401003160340121648004002192400c050019000c2100c002a545903c041242c10b44103030070200100b0350410246086061000761000140218 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 130474433 1250 130473183 130473229
    0x10c02060f040f0303090f0609060e0304080d2f030c010605031b010806030f060114040b0a061b081c05060f0109060207120311070602012003061003050a0b040e010506 73
    0x2404404041e200603201406038000f02440ca82058001e0303000e802080d400c13101c1d003a480c40c2e6500e00440900b04012084407a5030030100c0d101c04140001060314159101d05025005139260514100c41940481d0a0707070468100398a0103820a410042c0c40300884802080510f5407203180c03124072030030350300558080d80c0a81c2c4049042e0305000e410120300e88601409280100a54488000091801d030b0841c0002c0403038004d082c00042c0c1035000e000d80703654801e815030b42444201546803c00941921920410f8040341c1c81d083c49600d00f40d000c00240c50790910a8034840e00307002d020207015280c10710203458a00920360b01d02c00d00c1450314184e0707004480c0354803d01c0c0c600320050520400079181c84641c0315604180c011740da07120342050301581c940c52440084108603041c09548110090203840361214400320f200c0340020780e0080041000c00c40384100070150501c02c1245024508138003d050062240504a555150b03000090395070b801001c202c1403c41d8004921418400208410450351009101240c190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 130475683 1250 130474433 130474441
    0xb031302180f0604022d03010f05031f15030501021204031205041110020c033f120411120d090f050a030f030302040510020304031a010501211803030b03010c0206 71
    0x655860b81d44084191409038641a0403410100440c0c1e120105d0040c01d40900748070f170020140c000186048421003104090305c55a11410706444400c105e01003903058411164408160810b41c00c0784005800c05400440c1d101c0c0d40e40c407000d0898024240c884005a0144240401c0c1948225604407510041e10700b00070303600b0256100000100d4a030b6004e4050310a0500c95040a0300034003003803c01601c0074003515484010208070140c0a94049a1001c9079148800d2500603121081041020802040003107481e0a84d100c41440b01110018001c071203100c0c2a102c4240d2603281c0e03840310780b4003e00f82001004005591200a09182966040240d14503401c541c204419a101c12900046a410000400400303543d0b04085000c1e100b0390300003542005043c0b2024003002c1d4000000e004890007454070200301d800030611489004820f2084600090401e0340840d05024501d4132817080700c04da00b0000514034202c120340d43c00126800001d8011a944180d00f10403818280601e00801c40c1d648091b103a02d02e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 130476933 1250 130475683 130475701
    0x1120b0c03010602150604060f080601030507090b0303030a0b03211306110304180906050c1e180f040e0f0309011d09070507050c0a2409031511040b03130218 69
    0x224a003117003d180b20b00700020544a0f19250300800140a443c103003018801c0d181c0b01c80542d14a020310040340c15118909002411050f20700c00c1c0400c10800902031032441d203c00716154058111203d006078180541e20b03a10030541c0201c000041d0424141b2185911000d900c0c150f1007035030702030398007100a224840250141d8400044215010b5030420314803c254054960710020050805510051246107071009102010b030002001d014521000d0320094140039410500407840c0c014030081c0c042c00600306070501c5152a00b0849084145000741000860100c4c10311440e15000d50704034101a00c5d00b0004801e8847d5034403004080c4038140071504080842c4020001c0380c2d00d0312006011804001d804200d500c00c000d0300703006400300080000d00c40001c198444250340003400081d0346400030200d100d1656003103540500000c40480750808000040c820350581d20b00b014241803800085200c404010115100d6103010246000c0d41100202e41c018510a105101008181c410a00901c030300c03030010408444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 130478183 1250 130476933 130476943
    0x4060f1b0e031c050c01020f0d050f070c050604030507020d1505010f0509090319021923060f0c0d1805030d240902090105070203010c1e030c08160e030601120b0c03010602 75
    0x1d401c0c40c4c0b181d035945180030700074024020201a5840d904c0300003403000c2901c034960440c90040e20706680c40c40c0c00c0d8035121030a59008808520081c07003a04a40c0020b00800d0040002c4d14000380060070700d2900a42d0380d991008889906145101025034500c0140500d60313010350454050b080513a50fa10007400c00410705a52802640305846401e25941c00b403103116842442034400c148608440c2c58124101460a5014591180c03034400303912201c015068040200080c00c3c0d4003544808050203101d8135003e42148603540300310001500c0350b80711401250402e1016010405550040c805076031a94200441401550404034440c04520030845040d807130100d070804d0881c2210401d40300140d58850b030b0310044e50180101c0740007035451751030305204041c601c0d0400e20148001202c8484120f0300b441a050543c101c410724a5004001803240f8000343d0360640c600c03803042e400d0b0140d08103120403a440c580020314084098010500e50b0448241c800d007000794864110340c02051218849003550b0402c54025962 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 130479433 1250 130478183 130478233
    0x10503030c06040f02011403010b090301110f03070c030e150c010c0905010f0c02041409160501050a091406070b09030705060108010b090609190c0f0905060301031a04060f1b0e03 78
    0x3807072852030480704583c051f581500225421a181586a607961001750405030003855205009500f00001c01e08540c0b520002c64a4900800c0d02803400e50f110310008035888601850114107210b462016410b6070354800d1124100f991003042c13090340d030f20854541107081d505905210000d100c1011030511050381c02070500d4041c54003525003c1030800c0e0b00c0c000180903254075403e08020b1001c031428403200307400c086081c072100c8041841c246011560307100119990b00c15811a1800035030179000600580c0403130042d20440d14401001c660800800362503d200e000d60a4400e804103078400601c8900b006014401cae03d0040070110001c011440712400840c0b1076113002042c03144a2056240020051041180702a44130161602e080040c4255913901418410560a5000200d284010700003550300e4950110b0341603983c0810310340b413a140540810790701500c000d002106e0064842800020a41e030912507080300159080941a0031625107001904c12049411901c5c029040701d10b5018001c52110410841 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 130480683 1250 130479433 130479443
    0x3070f03020c04090b01060e0d030207050103020c01090602030702030405091e0402090c0c1509070e061e1c0303020403020f040234140303070201050112030c0f0309180f05010503030c0604 82
    0x12058861404034100548012003a501c00e00d070802c4001480310007035440d81030707401c1a00c80900500c031050402c18104c4000f01c1c01001039118400520095101c0d070064a0045500340002c6800c1c102581c61400b42d806c1224114010703400071500700403d282007262540c201d10400042c2c000d03e552003070008807010000f44041d000784000b4000c500d00010403c115800c260303140055902c15071a07000065420303441070391900303405e201c1c4a40c0412461301c0e0400b0240181c400401180b003625640e4202ea224042c1303070107000d40c8040b0500030b070100c2c03400d08609078030710a04c66640182d4441c00c1d4410040012201c42d00540181d00c18026000d1a5501450030502581111403120100110041c4044440400380c00100702c660300c100446904a4004040c2d4005c000c1134009100d1603032900c1d0074400040e400c51019000401d041d14501c041400724840d0707070181d8000d2500c0c0d060b80d41c88200d803140c4030710b2034150306405641c0c40f083d1310552160380c40341902511044000d1854821081030003542c070314020300b024007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 130481933 1250 130480683 130480703
    0x602130f03080a0e0d08160201030f06050306041514092407020a0209090708030708090307080c060417010609052a03011202040515030105070f0e0a0b030411030c0312071a090307 78
    0x307100c0c0d0b600240f102429901000c00f5a43d52103541f03030a0402209807008902280c100410402526a01d000b80300c00e844028004003042e9940340c59824420b49004031100e0f0103540d8070180030170111100040d078400d03c0c48030001e0110f131245242c032281544628400103044111b510030302030340d180d0104105481c0d07501121441c6491326071458460038500a50701c264101d1200066400c1000000d0002e0300d581c134070880980340d00300d43d02c070500e80c0c80300c1d058a6055413181c0204028071609211010050100302190000600c450321000c401080305d00540708480a80c445842c0c100448503803450103940302102c61111030943d4508405036044a10b4040000d12850b12400054941410390510303819070f81c40140280001e0800c07a401400340c0d104524414002000042400c0442c180042194111454105034514640d19038651100d00512160003a40c14011041d0342513050340e04008801003070385403114140da00c40c2e091612080460030000460951608001003003c40000402610302e0310340c020800d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 130483183 1250 130481933 130481957
    0x703090b060f0109051e040608030405010e06030a1401060c060e070501050a030f09060c0509030d0203091302160219140904020a090b01050d0e0706170f0103060c020309030a0602130f03080a 83
    0xa240100d903170300035a8100c1215160000308401e8010384c00e504c100300356001c105d000c0d1210991070302c0703108034041c040c00700d4120500303030440b410040c00440c1d000710f09003000200200c02c101906407015080e40081c0020f80548199800d02030b00f4802d50140f000c068000707110091500c070003e8000d00a102c0c41c0010b2503030f90711031301c0e0300d40546400501d06558865410040c1184000c4041e1807500505142406889007001700303100c09000004990f00c201d00207061207000c2c0d6180744928042c0d4415000e4500602001020300b0040c0c944080c000c0d000d0762802d01d142605170070300d0411314060f44400e11040c40f80114000740030158840c55000010344500c00c0022a040d10440016502c610a614080010070b28043ea445403002001c40c01c0800c0d140e150740c0386c0c0d1002c0448401d009040744e00303481c40286410054010000122258000261810f2078016070341000d0307142d40001c0c140380c03100c28103640c119000034805000100038511100a00a03840ba803189aa00b10b031111141401060000002c1c030402c07030f0340340f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 130484433 1250 130483183 130483187
    0x18010f03020708040e0a0e1207020402070c050d0b060108161407050c100903020103050a063f1b15020d050f1e0d0507031109060306040e06070906080703090b060f01 72
    0x302e8880e900a0711051381c684e0380301002013140300300b19240d12800d4a4005040182600860450101000c1c00c8a40382468295002c200003540003103000c482c5600d030b4000029082c1c44400e5407004e080d01a080c8041245040d20002d03000020090400d0030071540d00f080090841d410091240950303041c540701c241c540f502c034541f4900d80480400302e5a071003c0310a4410b200240c1c42507011041d42d01c00c2c2e0303051202d5191260f02000f560150b001c2c400c035942200003600d1181c0307000da00c8046520029803201e000307040e283d000b0307070001c032048041655803c80d80000140c2010500a580b0f00400ba583e49218160800203002500c4105162114040000c0050300d05190110141901c43c0ca40880c148112450260507004a090303202d941c3d0f0100e045c0c00e00c000542c0c9180280b1821820103108000c00d4a0a8514001c200c1e490380000c04c42e0f94482d82e07410010b0500c09041007a03d01c9185c890701c2d000321050403c04040d1000c60010569030802d400c0c034890400140c1c000807003540260090ba80302d02c03001c40746401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 130485683 1250 130484433 130484437
    0x20a0b06060d1e0f050c0f070f0206040620030309251503050403020f06060321040906151b03091502031903060504060815010e19020c03040311040218010f0302 70
    0x1c42c0c001500301103d00c00c41103000f102d92000081030020400c564960190794405442088410000711441031089803101000c2d50010a030b04c030301c038450956104290f94000307003160300070790400300c00550b0840c0503610b00d444c25801d6014100055000303504615010b07810b541e42d4605000c140080020b00001004014140c1952070050160701c488001c00400d1a40700800603c001c8906a006205121490080d12030111710b9034024440078010301144032402d14240601210384880380301c504c808000001d41c950541c07042002402596811903225002c84200074480105680c00302502c42311342c07180000103500060301401f1a150000c43e00742191407081d0517802d44c01031410302c1d40f140c0d5004800c2c001d41c0d03038194031100a0700e60458040141035180c2038041d6131002d01392420034190405000601c2039010380309006901c407c4850101148411004681050383c108058101665001040510030000d20b20308501d035200301a6021420a40300d15031200c2280d41c0040b02d82e062009820070b02d251540700ba01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 130486933 1250 130485683 130485697
    0x50f04080f06070906030c270506040909020306010e0c040905100503030304111203210901020f0c0c01140f030a0507032909060a030510020d02040906060203120610020a0b0606 77
    0x5603800450006001d40d01c59204540c02e400049041e0360100c0e03940d009106104441c0300c25510742a2920303020031403021086016109041012100c180061940e540500071300162824540202d042c60346407052500d0080103812aa61902d101000c0081241c0e10030291130454a800001007000c1d129a2402c10000c1c059421482c2c05000000400c41404106040000402e40549000c07001c40c07220382d0300300d0f102c1c000c540c47c00395842019000142510340e070000041c0c02050b480e00052500d210340f200c00855a0040340c03100f50f5034120040700d6000e50780182102107031841a072402803030501c40142d405041c5c8801000408242c1d9a0030101e200316109a0103040c4201c0b46204035441001c403c02400101110b00122920a80f5220001503481c14442031b0b1108072a4098000c12960340840794110103500100c00100d841d81d82400700268852550140800034003547e0003840e603030007132011a0200000f00419042c000c0034810000c2c4406503000840e9045640c11040341e0001d515201c0001c0c4091240032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 130488183 1250 130486933 130486949
    0x1f02070c06030e07050f0f010302030619030c14030307030f03020a0210230a0e0304030201111005010e010806130c1401050c0609010501170d020c0d0204020d0609062d06050f04 77
    0xe01007003064241c0c2c048071031000480c044400b4541d0f6403040107212007150020680007401c0302086a800e5001c0c1d0099504414014a020000c10169800d40b9400074268010b41e4aa080900200070340003c00228000d01c0f4401c4e0f004c0d41c13402c00709850141003000000756000c101a8000b440740a0b2600c24000134050301201002804100030404010a6100c00d18040030300c000340c1500401c2405009200d86440010454065400c1c41d2454006642e0010300b00d0443d40c01e405031800303030500e40489120b0303a030182000700d014206650500802c9413a0640c0149114071005d10b158494003c00c44142c0031400702d40a5426248000c0c60b00c0c070040742e41d4080c038500100580328410030301680c26410741006050301c0200300f05811030380100c00703070715925120101c840025803c0001c0810300b50801c823841c441c0150014201502d0800c5e031071410340466429500030b503038590355071006000804501d200c0c500620b003648000524240300382c1007010368107007900c50314041c000300041d01c0300c4d560101001c4c0d400900d901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 130489433 1250 130488183 130488203
    0x3050c160603150608240a08030706090b07080f010905090a02060d02040617190506041407020c0a0618120201090506031005090a0e0a030309020102030d0905101506021f0207 76
    0x40c02010b03002c0c0900220880c00d26041690104a180c0702d6900c10344070710320b00c1d2800074510750700d580303115450002c0c0c2803c140c01203003032a4045400402080200381f110b22880c8002800b03400d42c1040204102e01410400400a500d000e01508119611280d810f60307014000025041d03c602500030b14000360110001c1d000340020884160f03039401a405403046601c0780d01c4203a15107140d8058010949011902d166090f08690000c4480e03081c0c0c3c5d4030565000801078000038424548554440340c0c018103c4507103005910840c50403c082c100000d21100030b2001d4140841c40007000035000175461381c00d00400c1c0745d01e003507540501c003076a10800444009080c081c0020b0760301d003070800703180070840c19034081c007070080c2103907804500241594440c1891294241d0007400940203141d070200c0183c0303209001a8114407090100da02035502c541301d4800c2603485a402070149000e508511026201031210313111080e00e0f208010806e2035004149820b120306040c140b500d07048000341c048002809419030141c104818 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 130490683 1250 130489433 130489439
    0x308072304030b10030203030708070215030103081306030c0906110a060e150105030a0c0b16080d02040311060702030c061e0f04031406061507081c1b080108030703050c16 75
    0x816001841903030b0240c25503d03425558140d42c45035040713151200a405500802000000c540350002070410244001d04181e61074003690155581d0b80c000b80c205440a4800042d1408200e03030300d00c0a0710042095060500c100400c03506c002d400814144120030510460a0016030040c20a1040c1d0074515406001003140c00104046039659481e10108030690506000011030903103000074405148691020326082051b0501c1c6120074560455061070b20341e00d14505038940003404c0c2c031010740703014a1045001030720385145090880d5007020444106002d0f203400c005840141e20080784400800e074082ea0b00c6582c41d1360224080041c010190081d00707140102040745000340b146940113004590040880a0222006002e5261074000503203001ea403040d800004400c0c0d44030020040e00c0a80c0c01031081e00c0c1040d048992401254019041d0058010759540f4400d01c0040701501d010215031407854003038829810107840913560310540c4d4000c0d05001e07000c0360880d26090100486440945461855440d05036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 130491933 1250 130490683 130490747
    0xa020405010206071806050a1e0206060102012f0703110d08070f020d09090c050c0f01050a0e06010608061329120c0303030606160b1e060a050607030807 67
    0x103802264018042c20020070a014403031034040d003da00b040d2014881d00340c501041568075070f000c0100c00b030500caa5400b8000c0849010401030f0084c0c94182c015001c280342c030704002070071500003440c201d004580543d8111403000d1070105016080c0032a041e400e54500440c10140e41441c4442c080d4404d80c4100601207030556407240425020301c01d5900c941440307401e40902030740c4805107404400c00180d0031400820858506401c155a110b00c2428442e1030840c9001c8180d007091940315500031640e44442c14048400494825007562000c0c42000d00311550418030b00401248000c2c041c40d21502c1c00c000c052115004960040c0180070b212400c4842c0c200a221800ca005100d02103c1441040500d2001404c164040342c1500710300c6000300514070399a1028200913041d0440106107107440d5a100030480068140801e546c0203075241c100981c51002c420f05a52003484008020f00d0040c40e0390030003003205840794003e13143c1c50b55250804404550f1914421541d0402801000f05160109109409003003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 130493183 1250 130491933 130491937
    0xe03073c060b040216030e010509030102130806010501020307030909091712040201110303060f0108040c03080f0408121201060c02121f0501050405040b010e0405010b03011b0206070201060315020c010b090a02 91
    0x41d1141c0424030001600100704070032402001102c80c41d00c3d2400c80008000f0b40b203051803c003d01014106079007000c0359100403034220b81207140604030141c0003050500c0342c0c030000c003c011b0042000b4402140703001001d55000305801e50b02d00c104051203442d54210010000040c10400618020b400b05c581c03540010000000b800c0c8050303400703a002c20403114195440300302c0401103a21a140141c203000380f04000a004444048000308140c842d00b00c108404000500c40c18010b09480581d268525100c030705000c0324a0070f0000142d145944c82c203003005606040c0301da00140604442d240d08019281c48001d0000c640403845428001c00140204066401c0b0000b14082c003060842001504020507071302c803000d00c41110010b950140842148000422448415411090b0300c0741c401d0002003a00504003000c42d094908e1a100f990401201c492103280150341000b01a0384070130544001d018107403454a4403152401c274800c3c003040854000504400040c82500210181c3c08040c1c407156040c903100303100c94029 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 130494433 1250 130493183 130493303
    0x706020a0b13120c02010e150316051303061e02131503090c031b09020403110d0c0312050703260a1a0901090603050c01050a080c160203060f040b07030e0307 69
    0x1184000c00c40d000b40d4108400038000e22319550807210306d552030f558211404c20030304100c80002c01c8800c2107241040020313003041030000d6100310313000306641900542d0600103840c1c400758500d005105100c940864000c00c00048d04848250a40e00f000d00c04580045026140c5110080c10080300003000004020350891704510780113a2074844550640c58290340350607031296200240c1041c00089000c8807a1400e0300783e4090503842940002034450f0f0b20345c0c48481074515450440701041000c91144107164022855000100980504c00281c081c114100b00f4507000c094940c8030b4035517485030320581042c100c002d5603610381001050546150380d5404103802800d410b00044906004214540005502a80a8807140121a103c1ea006a50345519015058004a420300c103007050b4641440c0141c0c0702805130501880e05003041e2150b5183c1418000300c1064040e200200301843e00c000010741400c0402699a01644009031300700c404e16880c0004800c0c02c400c41c030445429031852001d1015000c282d541f00e88 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 130495683 1250 130494433 130494437
    0xf0b0403080703150f03021e0a06020604020405060906010c11060f0d0b1306030804031106040306060e0f07020f030d1109040606051b03070809060d060b0c0f0705030706020a0b13120c0201 82
    0x2481c035044d00401168800d104e28491542c1d00101440146080070031045c032000e60640d81d0842000e40d030300084c02024154807960241e0400340620041d420280696a404102a10050320b0343c1000300000341410f00080c4064403552301c49419a0040d540c540444861000403a50b00740c6400802080b180202082100940f08400c000000f0740901514050542280d070094226400d02d0300e19110a6400c0b4440200c582d4804010440800091114403070030000e0500c801d181d08482c03070004020702c88074401925140540d17010144040424000200b1510307105064440860740300211b5005a446004101e81154018105040460301700c0e03010f40542803503c40101384100d00346c0d5294019441c0d1051072006869406c04000c0f484290078600001d00125002680001d1120766800301480181c116a60044c070b25044500b1050b090f150801c2030300c01901040700901201407400c00d02079554519445e00a007000d070400c0c0020340c03001100c07956400481c0c04c0001c4140c00d50004600501c2c510b50400100c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 130496933 1250 130495683 130495691
    0x304050a0b1e13050c010503040609050105040b061201060503120c010b0301240b0a0503011512110309010606030203011202040504020a152c0a21150609060602030c06070c0f0b0403080703 82
    0x10052048040f0080250400003901c04282145c4c011202e5a000a00a55034a42c46648110000d103017441110b204178002c0e0380012560a20008104000f4400d004491704e60381032000600c656a008140c1e01d00c140030b181d40465448824441c0c0b10b000d00000f000c660790551801c00c180d28007400288501502810351400c00603891303140d1a03030700038901a03420030307600280040c4018007641110008100c0c0b043c50038104002400c404104210948a030100070714030190000c03041c00030701c2000340504800ba1640781001e604542c10b00f80c11000c0d80c8600301001e44034640fa10301007010342d01e48100307880140c110011804c1c0d120300882e00c040c04000072a8041a074101e0003184441501c0d0309c0008201440740010044008685012802e0054030100c0e900d0300c4a0907440310702d14002035041040b0513001c0000031004a1110302d0020b02d14110f44580c0d0101c010354004111015090b080400c40a520010b242441006441c142c01c2080d45203e0361000104040014414031041c035030440b840500c100d1050303a040c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 130498183 1250 130496933 130496941
    0x20406080702030a0806100306031407050a121a0a150602010506180613050406021b0705030105090111030c03090a060504060209120c010207030602030a02071b09110f0f0304050a0b1e 80
    0xa90f00d21414180030b0025042001107a250b150030540f9241041d028030b80030502c641c072078540500706250b03154040d0941c4e00060302040b8504000084500501040c00010385154058542004c6842200946006504100b0001d40c0e041700551041003060b0000780c2201500da110800a4020315040e11454400c10700303005000b031815401c0007081c2c03280d000644104041c000c0318403140040c202c06130044078280d07001e11000540e29040001c2d03d0300c510701100149070781894403080c182119000390882c3e880340d0400c28a802c0b0100031500f101c1d00301c00030010003640c907500d2900c0c01e420700d0085000105103a060030280000d0100540251401034011160104152083c40c0c5895a03104182c0301c680c05a0891b910820105d0203036030140d40e000c010b0031009481d04a10b5556104030a11103040d00103014240b82e800d01848481340304039030481d29000034081ca8076111070b142c00307468000d1184d0423249010000c00141044402c1c8a00c9074120b034044183d4205040020030403101c01d800100e52034030004080e00003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 130499433 1250 130498183 130498187
    0x309100e0a0f06091115040306052410020106081002030402030c010e030d0c111f02070807050a1802090d0602180103020708070201200f030a08090309090a1a090a0204060807 76
    0x6803899a8002c802c40d0224400d503862102501d440ca0301031707542a04014509000d601c0391015510080382400b5a59170300d030704500c0c06500b00e4001400108260b00b9100e03086181ca0328100e03115407d60f408690100c003261100383c2c22409001a5000042180140440000190916009140650f04c04c83c20342e0941e1101070011142e030316241c000d490f8107502c0b450345a900940103a164005044c042c2000101e0107240d203020800250445851a94084140800a0405606101d080c014001c2000603107005841e140000c3c180c60703841d00403c40441e81c26071800b842e0402903411103001c00f0b000760042d600909241408002508190b00c6400c0c01428200b80c10003540c4070f4401ca4548541c411001400c000c660b03001110400d8407815810a812002401c8841c040070400c00d590701c045480c0c0c0215070303817002a400248018000b404a5140e9031050141d6440c0c0d03035034002840e40c8a410b0540015071001242c0e40c9500069484d4204c0e50000b8801c020b2090900103030300280306907070198540002607203540c141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 130500683 1250 130499433 130499443
    0x2011a06090108010b03090a0f150513030f120f05040c170102090d14010b120f01140708041113020a08040501060b04150c080d021602010e0405010612020702150309100e 74
    0x101c1030009900c0070040c0000c0f0081c801641d04100c4c03600489041c070030706658202c18086001e1003950420180201a00c082049001d142e90148400d1248000c0e0007081d0f401030324800c4803180310300601403041e1000d04d040c0016800182007149000c0d003405541040c1c01c01c00c00140941c054822510807502490700036070814021151b04001c050031111341000e45403244c07002d581c5400c4500205548800600c42141e840303480c000200c44401d8007802108524140c0b990850b10010314000c28000c11004001102d5001400c641c1c1c007a0b0040c4100d1b604045400009804a2a03000c2098000c1e1021401414680d48444610300caa4400c0000f005070a860f848201c00501841c860400790b001e804030380048951103001d10f01c40951013903205600340012100200c0503030700550452610a0101280d40d010b641e440031050035007900c242c0e0304000720350400500070021140104100415500002c034103007152075030200a2a01d0700744028150b100d050003034000b501c070540340d0300041d181420000d403035041110101d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 130501933 1250 130500683 130500697
    0x60702010e1b0307260d0c03050702040e21070507090e0d0c030203041d06041b0e0f03070b040e011a090a06080403031b030e0f0303060901122102011a06 67
    0x5240c0c440220303002e2400403034003580041e05409249400a412002280740300111106110000103880b44840203900e009994901b02c410400c0c3c00140c00c0220340c01c44200d5a4042e0103480204207490091001890690101c2c0341802d8407020001c0408a4221396005e0b080552081040d036030565030301c108050644140c1c000b0100315030028500c10b491240510740001c1180d1107401070341d040581d1800035004a014841d484450210008108641d2b07180078070980b2800000c82150241c0035803c05c00050030310f10007590a5005000040080207644e0b1b042200c18020000f41c0401e9584545854801d00840d00c284540581c12101d5004078a8070350483d0280d90342c00700d010f032000c031030186004004c460301361020f4410f40074569108410100701d441030210101520b100c1d06c01140c41c07406099544d1804603461400409a002441807185030b942e442e09031811142d04800821a80b5964180301241c3c0700b480d00c03010f04064894032000380d059019040710035800c6d92541400d210110035418440c051007145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 130503183 1250 130501933 130501961
    0x2070602071505071b080a030f03021317100906020c010501080307080d0507091d0403090f030f0605150a14031006060509100e1e13020c03040306020304050a0c1706070201 75
    0x3a070400b0203c0c4144090907540e4010480d040225030b64070072090002d0030320380210b0001c0c0c00900c0b02d0740034903030041c0001401e0304152030110700d04912800e20034488903041c080c500c050712201900800902d800c01070b040d4940d41011041201c0d030a90f00d0040b009620050004110b942458000145d9036800301c00d40302c0c0c03c2d03001080c080c070b03000402c801b0380005d000041c142030900100d06008110106040c80e41100050b030341054400300d040c1800d000c2c214103e198401d61600355000320600000c0d0111280c1c0002c81d5101e50003144944862040000780503000000c2c0b074003c0026070000884040121540c650040300b03406507402c3c050b0001c5130005031901030241c1d0022420800c0380c4103142c00d01c04c003401607000d030b1480e2052000071035900240d46042c8188000d588403d5030142083d00f4904007488a4902d1240c04046140c0354070403070181e03181e005902c0003500243c0d011002070180325050144c621281d60010060408640780e9030501c45c6001d0b0300020904034401c000001d51858014880d801e8000311003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 130504433 1250 130503183 130503209
    0xa0605090c0f07030c0803070c030e0a05030c04150518010e1e1501090308030a020406030b0415060f0504030501140106020105130507050d030207180518030313081b0604050d0207060207 81
    0x740d84500c06503c100411030800030040d110401080c0285c0145004d8000ca82c0e80110961480c10000c01c6100450200743c0300302280b84040007641c3c8c00007082402c03000300b84c03804190034203540d52008210380554012500b000c508403a040c1d09400c2603003418141d0ba84411101c10985446c10b8070100d0705c0203842e0b4000c14564000c0071070b521070304444602e0303408601490006c21250b1a50344251540e007065504020301d50300458140000c5400d8003032009034000a4501b00702040c4621090003071000d00d481011306100c41c40040d405070f544036204403006550170100910a6a282200540c040a001d02ca04ca005510f8036021840c0f9100e001e2100c15240e404c50000c10100342480104860401c07902e070304070f0651041410000719803002100003541000e4038103001a56107041c5040ea040078050f141104c0e01c3d0342082040040480310114086421382d0011242c584803c407008038001706405102e8200e050340b00f03d008000c01c101c1c0005418140e0358007642960307103090340e40da000e0703945207200c0c0224540a160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 130505683 1250 130504433 130504447
    0x5030604050c070f080c010e03070c0b1c020c0309040506040213030321140402010807020706020d03180b04200609090604050c071a09010c0504080c0f0f03030a05030a0605090c 77
    0x9070040c0c0e802890360719890340b50078010b94501454440040003112a603001040f003894080013032181d20042580b04014514240c2d881e43e80c0000ea2080d4044c0c90034410011681e9010001030b094203c610320501c4134110350319410351180940c1c0e0b801828869224900341400a03202c1d0400740240d542190865a0b810601815680c0075a40c0c0303699a01450f09100c03c090f44c034042d68841d070003803202031800c14400c4481070425000040035007070020041d101759442450704010082d400601c068264840303140c0010360840e5124a05000c03501010041d00308410b007018403041c055510071074500040c5a101c02e1280c4012038080c042c02d406070b400c925500030460301c00940715080a0b00070300e61050060b01418580340c4541e842c00000e09004510f4507410300c14001b0484e500b0424414500140058141203043c5450002c6295648400081e000c0c0900c5a0100c401d64580b01c020304000755008c0141a03d407641d590103070040c651b4104449081c000e0381020400500741c1003840440740581000840c0c00c1c41e0900c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 130506933 1250 130505683 130505689
    0x609010c0206090d0f1a060a03030c0201092c0105011407060908040b1c050c18010f200a03030612020102191719020c090c0423030106091d0706050306 66
    0x510380038281e810800401ca1400ca44d40c0c1c11984444140c03141e8580103214020381491100c003251440700040c0c003142c90301803007490796400300c1c0e0400722949454402c542c4c85007480129600d00c0a984946590200d5070020000e0742c811100b0b17a01c0074a2802a0150301e17070782e510011220002c106100f1468114100007600109060760802e9600c64000c00c581c5140c1580c491041060fa030127001108102c46050200c1146011580201c9401c2008801d020b410840803415442a6050007400345040c080e110700d184c011a402015072945120105007408401050301c00416112424540110002071800f8004140b04508090200440c0d406a0080140401100c08452820071f8103c00307440d1582102e406040450a0900504030000450701c5a40c1c04d4550300f0001c3d103886d40c0d524105116040d00020004181540030588044076040e030351440042d1000100880401c11958615406500f401004954203041c2d81003050f04c032802e40040f40258120f07905071074803400180502c2000810400204581d86 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 130508183 1250 130506933 130506947
    0x60105150903120406030b031005010812070f02030d0809100e031b03040305060907050a170d0e0a0509040803040209011509050409061e150611061311030609010203150f060901 77
    0x440c002d0101c5204041103074200809030001c5e030181000075151060a1510300741071144240001c4819014407040d4108049141c481c04210491241c00e9000304e003800c00d00815040402c000754003c0c0c281d454000601c0801840d140d800c9031030b4026882a0b0208001c0b09105106024911134000041c504040020140400725101c0750401d0200c0d10060102101060080c0081170084011030020007526103800c0900c4203540c01c40d4070010001c2041c0c0c6101801d00c001084410400c6000d00d8083d00c0f10b4100b1300010340003078442e003080c2d0300848000108010404086c00a50040b4021103444400c1da0740c0304c5600d80d040620996000c00a40703508404c11280c18650028840944240700204a8664002d94410021174460260340d10685480c2c054403901e110764240c0010705902e19000d103c03a402c408400c0e5403118058511051160201e02c0001806001888440640340c02416501c10f4142000581e01030740040d20304404099010340d015050386401f606090b00345002034145400d00d210365006403081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 130509433 1250 130508183 130508197
    0x7080306120c032a040204030f0b060118030311011401120b04210c06060b13050108060604080105250912030c15050903120a050106080c07030504150e100206010515 72
    0x140c070840d840ca0b00035503402e1141c100194001c10281d440409000700c0403807060707816125a0301440c410001070020440301d45400000e950840c040700401e864520048800d01c010000c0a885004402000300400d580180c1e02021080c400000740000004070000320030b01c84080c402c24aaa442c40480e50001501c801c5400b5409400f6101800300341101e800755001a0708211401000180302d103070040b04009a52080102070300d00e41420905010110220b07140e041c005005c0c450502c907605000607131580d9030f941113802808065000380708c1c0c1c0c213000d8030300c0c2141c0040220f039084101c500c41203200303501d1103041762400315605600e0400740394049441c10740e10b5030203040c004c0e41c0001c2c9580081221403428000c19000d80c20080c0119519110f11500084a80026101c0307401d00d4200001044001d6216500035080f48203145a0782d50307050146025526031113141e100c000c20412034041c410034030f508501007103024041620745940b48451140100e0b1034050900600340d004003841490401010072101030102c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 130510683 1250 130509433 130509469
    0x70b040501110d23010305060118021b0706090816230a0806010510030b0d120c05060a091106090d1b0e09070f05010c1203050a0207060e07030201031107080306 70
    0xc2e148600c18841c0598003c0c40b6421645840b24a90040305035440035990602003c92401402541169203c688416043c8900c440d01d48058482401d030244590448426131300750902c00c58010780e001e1207283c07220418403816006c5444c180b40019888404100e00a010350040c04104116040698101140111601c05030280030035411000c2d0b0307503d48100000141c11800020160303985001c0c10031003240c02841c000000c140c00c0000b100407036190320090307614040d030005405241c1c0303034001000c54070458000c2001d4038901c208014080c00f01c030154012131b034090084490b0414450200144026131040d212020340001d22803a4240103d100c103405028940c0780080740814848d920441c140d200071703081e01d02d81d059411005007003000c415a4a0014014482820900b085060640b00c44107101c12542d141c605054a43c0700003140d40c02070742c0c120f65481e9484502000b9043c00ca24042d03907a2030903030004901107450b1920075881c0310340b41c00589120f503a000c04280d1847d42d40d42e05000c804910322060040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 130511933 1250 130510683 130510691
    0xc0f060a02150c3a0c08040b0601140d050603150405032a0a050c0a080c0a0e070905060703050c010c0305010b0f1b060c120705040b040603020901090302040c1106010f0b070b040501 79
    0x1151031400c4103210002c0d404501c0d0040c80001204006803080c1c0d81184c201c0c40502c2c04030103605858014455a91080d00000540d0040d512100143d40c402e00b400c140e949512000100102010b01603804a405110180c04440242d940e19036000341405098a01418907070041c41000b40303480350807000855810180e045140c6491800c154a03180c91146501200c80390080401c4002c541807013000741e00200100c40c0148018510000490740c072101034068111600d00c1540040c600381d000e052844014103003c0c02582d42c558060900070016080100780c3c04042d4207040c001c64203940720340100f0381620750107411a498800d180001095607480301a40300000b2070303a80e4824100100a20410b84141407072b03400c196681c5130104544040f140003c0000003404010701041c00b80c0b42d494815181551544e00b0016620342e4944010789101041e40d10080d1301508042d00c158440340c1c404881d840c9426080304440e45a601d40f621801c03a4505d900910314491030522074980414040c0141e07036085070007140006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 130513183 1250 130511933 130511947
    0xa120f0e0102040807090509160b3004060c0f080c0c0f06040c03051e03030606030604090f080c010b0402070809090601170907050a05010201090f02040c05040b0403050c0f060a02150c 80
    0x160990f0802e610038011500902400c00054001d409a00c1e4410310801c040e140510411101ca20020058051043d80210118665080100c00038030b0104420200c00c000b00303144000482607070754800460f4112559400c00b03850081c402c2c0516105401da86007600c0b090850340d00c601240201e50071481c041c811a1103240d042c0c400e0310106009640c011801020300040c0c01d801c6080c514034109907000b8145402c0c00c003907140f001094002c42940c1d00b01c0c0040341d00360340d01d4071140000f0740507268030440a0400e030300703044000e810005540018000035180100074407903420583c040004a000f0510081c00c04901000040403a140c80129968803000504214604110300d81084040c80000c0758002640d6114420074405840c0c40071080c001031109100078004001ca55444500e0a095040b00a02551702c400542c1e40180c01380042d034018000c6060003d40f51556814a5070b5140444400207000701d030070601c8525981040b80841d07042000030740040c412040b68845040401e50020800c90020320306000c2c02c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 130514433 1250 130513183 130513211
    0x1810060e031f02070309080a030e0f0d050609010c180b040e09030c06040302010605150301230102120d0501050a0e04080a0806011803081804061a18040c020609060702030a120f 77
    0x61041420016104c0d03040303103000b0704a0f5240d600920b6a40d4012452032000941c030020804a880042c0c814011401206000c03e550b00c0554400409500408013081130b032400542c0860284110f0740c0d20140c4002c175182e8030b4040e1258500881c80d200b94100000d00002514801450b000720f404811240b620101400c0141080c60075102100181d445507001c2000f8039146c00410030864022103607518551403c65105496003001d808008079246c04a82c0b059035a000703100c06499640b030044400d41d40c10780c2e90034840c000d207801d0013500d20800c051840030030f00241c94000c003403040b54400107403850200070071000c0d1014007000305035604200390185800c1c41d1042c1007800100451003042065101c5a4180060410026090340d8501441ca05a0200f0941400b00b0200402e04404801e50366901c06c0581c0519100e0411420282c1007400d00a45400d040d82c002000d40c842c80c01601502c01c00d494030b8408a07204d110305014140010a0441100c000c00481c1d40b2a40390020443d0300020842c115000c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 130515683 1250 130514433 130514473
    0x3030c080c16080115050603060415050a060e09011703030408180a09020d0c11100c0903020402220801020901020715020f0d080a0e0109080f03060105040803040e01051810060e03 78
    0xd20503104006107040110850034017031404c0021004540350429030400000c20313020700005101e24070894031a42110900c6225914101c058840681800c100e00e45866018005501b650301080c0590241da00004440b002010071680c5000707904003071803031500d450300c1c1c51403603030095a441c1c18524641100b040003580d0301000d4070f009004444025842d501c14141000c21200c1d103550070300c14048007101c280740110000c41e40140c070782d040070800543d0072500e000842e0b20280b9a04000d40241c80091181d25007103100031a2000c03828031000c1e0391351061300c4018141c02d034081c4e07004050242e4420f03901842100007a844d0a00101d1807032040307405681000d400d0030720300f030481030656012800007001c0c011800c2030350056884200010009000e0354030305a0700c0c0300c0e03103102e0178230803511000011001c1074180e1f1085040b50028580001182d403203e0302c40c0000c180d94242031081c940f00b11170201e1501c651030078210080d4803451048000903101454a407003942c4401d9a9601280d01d03000b45441c0360b800a50b1415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 130516933 1250 130515683 130515703
    0x903100e10060608040308060402030c1e071721061c030306030b0709080703060203070203190503010e180a06092910080a0506010b0a02120a05180a0f03030c080c 71
    0x40107220755107103120341604842c6980c00040420600030704000c0801e4201d441c1a4104505a5005170f5030341e9810480785c010300a8034100354061a070319240d1110352101c0806000c0e6030b40109100700f981c0c0382c0c007052014a4070554048000c00c4441200e03007841941c1401250303a00240140950590414085000d0303d00886c40404a000c259210b9050003030100c024040c5134400b42c1c40c00d00361011030600710502d90700e0b400c61100411107a000130000d060607209000b40d44a880d081c1400206d030707401030b990240181e00240101c92004200000007220310080d20841000090701c1030141489491036121407000d040c00000540303548012024010301744030110a00486603c00c01280001d50a06032290070070407400303910480d110350000c07104a01081002c1245070444843d50f0840740d5030528044c0603130609a034017802400010000c502070b26555000801041c0802c580b4408071800201d820170060b280e015070041c1700c0e502d10004c000740700190040740307000724044c000ca030440e0400541c4607000e8a4105849 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 130518183 1250 130516933 130516961
    0x150f030406060602030f09040e01090b101707030206041809080f070521090d0516060339050904061707031401020306010f120e150714031902090310 65
    0x104000c180042403144401508851000d0740ca41110740300c0307540a174040d074080c07144119903030b09000000035801d44c8507040e103540c0203110130f8aa1406d203e03d2030114083d48a00118100031040d002e1007000c0210700341c401d4076070052460341010b0400c49114007000e401140c1c041003680d10410715011130400f10150a0300000da20100396a420703649485800e251034562003040c5807000c0c00b14100c0d05107541095580d40d0805450322085604207040c402d181540c409050030610113560404500d45901d60400c2500201d0391030800c10903015625080300868415241c1c0f240d00001d802c0f00c80359588608002c00c0c06000080000c14001e4a40186600104400b00b603401581e00c030090400030425400d0303209903038900c000021030640c0707440e00001e00640302205555081022000701d01904104591210180b126a001298480c0300e000d8000c1001240c25550000401d00c041c501030300c03409800f002c0764400c0003206000302c02616100d441c200a904107007011603260094910100c1400305a201e01f101c908103c3c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 130519433 1250 130518183 130518187
    0x21c09060c0e01031a060915030a0b040507050304020d23030f090306010617161214090c040c0e1009120f15020703021f0b030106180e0105061c02150f 66
    0x7040c0050210b010500b00030341403608060300c003840079000c00b0031080c1d00c040543e54141e484038450001296070082c08401d554030240070040c080c20f503202e0340c451a05a44240c03010461600c990000f59400c1c04120f40081d4440b0800e8009000215944203000231a402e501e0200a4034094042a60445e040400380a1000380e0104101e9028641001014010800c1d41401003a1950200c0200a441c0b0014081740010200100c499906da100751960000b526010b1420454852500903460000d617003660741f14158860300d445003119203400d1040c5000f080320b944a004c1180031000030f02401900041f841c1e4103011210030700003281d440f40384e031202c0c0325441009807082a102901d8200c01c0c0700d5500c011100d0140c418400000001e40001e0f100d407032075903040a07485155509542d0b1801900c0c030800c40e103030154202400001c0800584240c0c0030154103a0205120008203142038908076201115503d03406201070240900a028450403803044a00141c04800014000d00d990030b11031348692095840c034580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 130520683 1250 130519433 130519451
    0x20a0e1b16110102011e150906060c03050c07090504060b01090e090c090c210106020709021c020d09050106080318060a020c010c080403050d0807030c08240f0d060506011b0b0a021c0906 81
    0x10714580d01012302581c0c1c0d410054281440c00080210120800003010300c41c002900d0155140d0401008004017210f00302408a8a482c1c9018000781055020035408a122101c02050344024030118910480d4501d00401030b2114039001c0001c3e40d0000341c110280d01c881081428608a0111b1016252020143d00350300d41d540740002c02450510f0a502444c2854810301840c905c540001003280942e02803008003684404440c090a0010840990000c011303601e8581c0000b1041000f20241200c00d0a42205160000c2c0e080280b00c01841100f40c1600142c000541c10002e56004000704580c09014084040c203194990b5101460032507101034880100340307650200443d1651502840c009980711f072500c6c801d0360609000507420704404055142001554484101b4182c42e20000b41d05400300041203a110850f00d414000010b00d403d449250002d42c1c09000ca1f256102c04d1040c10340340a601c018038041940e9070000d03000007500008000560192400c406000c010240e0240140041c00786034001041e85c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 130521933 1250 130520683 130520711
    0x503061608010b0f0304060507050d0e100b0409050604141c02061815241c1403040b0a0f0c0f030f020f0106061218020a0e1b16110102011e 61
    0x20705030701080310800b040002440a0000c0d0f02643d0300140d0150001c24242ca580605450a0041d00310300304181d4034008494014890006203e268084507446c1040310840325000e01080e14070b13210000c1c2c02644450013040000b080c84c60248241200582a1041450000440365203810403d990500590007038080c004054040c1d0103a10100c1c040d1801410071100d00000700f02c4030b000007000c0b0584040d030294051400c850301a481588180f00800035140700311102002d40c0c1d200320080058402400c544c03061040d20f00000202c405541100c071071075003016032400e000c44120300d80503091000c00c222840031800003400311401e1460240310791210400003c55801c001d280001950300c442407681440d508022040d0040488100210b203d2408108144201c041ca40e814102450080d00b140d0405000240c017991000070711300602401801094a040200c050441809400300211120360510a40000241082680c800c0101c040c0000b03d40039651070741048490b0f801012618800d138580408043c950 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 130523183 1250 130521933 130521947
    0x3130206070b0106200c0108100815090708010e12070201030209040606031e180803060301110a05040612020717030406090507170601050d050601030f060e031c0b090118020f0405030616 81
    0x3500c005c0c407054a4100400c40d0540d1260780f5a0040d06204c81c1e000440c901c00c07440c2561300050010401200c8000d86400452082c2800c221104609400380043c0881c1c07441043c0a060740244100000f032014401c4072a0310903640d444680d04905043e07003046202415140ca00604004060720744001864600034048000d841072521301c0364010a15010400d005061901e01e00600150042c0740c1c1c644a45e6143c01090050840301131131360f040c00340480d11010b46a401401002076a1040d520182c1c20381d0301c1d8651700243d00231040020301c044003155a120b04d5a6020018540c02406410082510455500c4150500d000398100c07204411811498401c0d00100700545401400203442c5440906155244d40707444240c180401421032a41d4500082408505d811400e0315460f400c0c01d42e651202c0d08000c040c101445003421003e0f450030802c0c480850314125481c54100c4070f5018030324000e04191081100250702038034840d400c2240500000c0f516850400110341304c0c03400000442180c0580003400b0b0040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 130524433 1250 130523183 130523207
    0x70512070e091c21090203060c0a17041101021e070e0601020102090a030803150a0311370f08010209152508071407060c020d0201110a05011e0c020703020603130206070b0106 76
    0x118103141701d441c01602e0008500b42e0150120074096268010080102c9071644102b42d80f40310007407510203000510008071021141030700d098088a40321520594854000c00c901411040190800c8070b0401510b0301404c81345034000c50501c001880c10b4009030015079580800c0c1c0090b070358900d002c010000070b4088103a5020001604440480b43c45103145e5450052407440c14006001f00c9403044651f20f843d1303c070324404403c0300c100008604504182005054440c882d803088101c1e802c60b100002501c05818403c6401c1800b016000c075100a00c0071001d0040e131780c01710200020445c80f8030512040c42620000202c0407900c202c107a203940380503030f0038000c43c403803249003144185401c00f074410001950020320788894558140d071031b140c02d9411800140c2d0303146100d54484480c0c3c06041f84c0d0380c080050650062051540d0084004203100035540804116564076410401582c801c14003440585040c0019551020501c00c220b4130580d110750100d0015000780c0d0007111620740d034600500510b50030101c00d100d8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130525683 1250 130524433 130524497
    0x2060a0206060111280f1709090604053d0b040f05012f0a1401051f080709090c1e090506010509130e0c041805070512070e091c 56
    0x11030140f4141410032045684050080c030342110340000030400f03d01b03004018140c112800c03155040c1440c000600c9036020900b114400c4160710001055443c2501c0303080e0164904004400c00e03001000d09078030111110310030700c01e0383c07036000b00303072020302c3c0f180c0594000c00307088503107213003920380345010400c0002050300c1e00f246041c080d005d1043c0304611a0000c682c101a11000701d03030b240401d910b0500034182896070b60094200d0a0f0300b00c0c03244181005402c440c1c011a0030341440c000101135100440c1120740c850085400ca504401010400c40c207280d04906540c2d8005c100d811800d5654800f01080e848814910750403600c02c090080115001c3d610526500c48820b00702103182040382000141070440802c000750b185940c0d540701c039400840c1080b020103250350140c020400c03400b214011401d0f544e96910300301c0b02403040a40125050825017115107140d006000140310f12030500e00c8581c4c04410040885513a031068080c00705544000e0842800a039106440701c44003042d80c82140e2141e41446054019 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 130526933 1250 130525683 130525693
    0x1e0e1e0109031b0813030803190606050d0209190e0105132f1603050405030d090506030403030e0f0a06020d050f071709070b043c030b0705040302060a0206060111 71
    0x826008403119443c07403c0322040b100e9080840c90980c1244c040c0800b040078248620300044104a400c0000714000e20703040c0403a0f0340e441c10b0b401041040d61868000e09002400030310000715500b209030040d0aa01070010103202101c00e081c0c05480080b88964061444028850010071480c28404442444e9462220061002c0000180e00306160b0076800c2c44402e000b071030000000368440c102000d580684110084040849881d810f005044d41c0040c06102d02c0b0f0b00882a403043c400780126103002c1100e00240c6114199525a02c041e001001200b10284007401601508140300b90203018081c0002d202e280010b07103e58410b03000380100c504c020484100c07465018144600c10740c0050514140c22080b10b004952607881800040c20800f0a61200b03e0010001c00d01140c20078403a203031103000408c1100d89540203849211b4810a01282505080d800d1400304018000300341d0203160703258040d04905140307203025a00d070b0200d02d103588040780d4800180c000700700b400125a481000400f5100b244c82c0104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 130528183 1250 130526933 130526951
    0x2010e030f0a0b0604020f0a030605010905030f0601170304030206071506050103060308070609031107080a0219030308130503190f090e1b0d0e0a080c0d14040303031e0e1e01 76
    0x2540ca0010b0000078000e00038000c0007030900d5070b481d0102c0d40040b0824806a441e0000214050003070a054061140414001c500105582c1800922501d4102c8164018200759180c60b0081817504064040c2000c00e0004010101c003588820000704141442901c03890084000e42021301d0442e44103811040c109420254100b002c078402c0300995034266001000040e4441a034501950407c0085100c40c10354000d4a40006e5140c00109448480900036a60b500d29a401940341040d442e030f04c0d020080200d0500c00c00700e40b1200b41c81c0a000700c200c1c89402260b20f4400c2c4980020030403400326482c40c00040036401001151644001c1c0310004181c1c81400500ca0b040840d8940ca07111301a00030205400008149031001009a4101030510401035040e41c2548809007400602c540c020402200315108901003001c4d40c51040640c2c10081c0d642502850a103030840d541280942065664105d59030018880030704040c07074600c0390140740a5154000c1040541ca010f140e5802a0300c0c0d04a844540d150600340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 130529433 1250 130528183 130528213
    0x50a08040303080f0f150f0f090702070f0f06050f0a02010204030b0f15030604110105070314030a02071b05060a0e0103020d0f020a0908030c0309010c020d142109031b0a030b090a02010e03 82
    0x8078106d1758084400810114020340410000c2250300641c90b881040f50007840100c0c0d802207621810307100c0c2d034400c5080c0661262100e110b0003040344103140c000b0318104940e02d01d6041300c101811211046100252402c1d9407901c84400c85482601e0074491074041e0400d222800f80d24000031403260000303801504c042d2609480d811800384c80c89810078184400007503543c082620507950f050f05494141211522410507003424402904524421604444000c002c150030700036001215044484c020241031030080ba003903048601c2058900380b181415000e10502c410280c0f940101c03040042422001a00d071070b00e0f044020140482036000711000e800c100300c1c15507050b20110441702c1490003800d116401c200c2d90300c003094014500b4100504480513044042c4031400c00891150341415924400c2001e108003600340301103600c074007070026a040e40720540c40007500025045903000101c0003010313414015540c1c0c4464030b01c0e10703040302c44c074045801a00030101150380019195072200f00540040070354507424070384 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 130530683 1250 130529433 130529461
    0x9020d0e2a0d021203030f1810020d060b070f050106090603030509100c050307030302210f040b07030605150301050301060e0f0106050f1b010506030f061b07050a08040303080f0f 78
    0x5401c070199111402001e5030300c502d12603241c01940988119180d25200140c2034aa8006846058400322a00003182c8441c1080d03050441d4001200c0141c40c1118007500d6a100a5000740f144d55400f6448030303000140985543c000c1c0215030b00540d00c030341052810380340045c02c4400a800143c405440c200c800d0021a07032105c190b542c1e808055a01c0001c200405800b9540300c50200c900400c5803100084c00300c101a8950090101d5111244181500703040390b118002d1030b0740040f80c90309441c41e51180000c0219400364029074205030755040024516841c1d00c0820754018203889002c2c2c00c41d40000040007181424071401f00100340401400710141405c107150300100ea030612822040140100b160381e40369a900e8100ea0b0f40d03c0201c0720303000c4600d00201009000e8442107403e1742c400c2c01240741d000061803010804034403944080c01600e20741c00c40104000c03056002220f0941d1503102c0c40d0b01202c00140c003c1c00801c041c43c040d84540c1c05070b2500380044046802d0040203140c2111541c01804000500e03100c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 130531933 1250 130530683 130530733
    0xb040e0c0306180703080d0615090e0f060d0602090a080601121109160f090906030c030b060910060c1e0303050603160303120903030b0901030b060f0d0210140c0709020d0e 75
    0x1d01961007c0244016014006d180c1011b491b000360401c840c540d0076080401403040325031a104203003865507000c1141010041c110360250700601036180a0001034459402071000c0000200210391064461007118074044003604030300d032000c0207400110140940c02c2c0c198108400121015880da141601c0124900184500c5580034082800314422200b13006100ca2806001e0b410b00c200015036a070b0415102140c0e0521080d03a01c480c08102240040c10320040c0d451040c0c9102d0000002c113450400200e032041d41c070b580107030748109801025494103a00c0035040c480150017990040382d903040100816081500c0706901d400001c928a500f04006500258106041c60222400043c03490b0203060a030054070b1030001c116032014a200c00071041250550807680900f5080d21105005552001400580049488040d50003402100c0240e800d42c45001c2040e02522003081c090700f0800c00000213880c124a03900305003170154000c6000c4110b07000034403a0341c2d00e41d800c0d20000d146000b40c0320b44400580055036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 130533183 1250 130531933 130531943
    0x3020309034b0a050a200901051c05010e0304030309060c0c0605030705040816080705121504060921080601090e1801060b0f0d0e0a02031f0b040e0c0306180703 70
    0xc68141c48202252021070807810b160648040b8985440d06907143c1004d08012260403240501612841409007141001c2c1c01014154041c83e07400d00b030070030114440701d40d0411a14078106110704002242030003800e4082c000c81e0000c40e1164114074001d02100381580000c03082001642c004804122100f1120b03080754001c1c10202c1c3d0f01d4548500c1159184181c0d0080f2580b4414007403150502a4003544510807140c40005840c807150b154810422444207001040613550302034001c010041c984c000340d9030b400c244a5000092407140701d45d6018032022404401d480da10a164541e041101c0d000303e821507100710300346000035a03503091036125806940043c1074401c0e0a1090b00f01c41640c51002d40c8100080c0c549a410300351213117600b0412204a9210340401c1c400310f424412600134405000600e1a007040c4e00401516803d640440c400c0c138241c2080c0d40d081d1b030a546400310410151a03901c070b09011040c6c000c000d0b24041541030103240c42c11002400320114643d0544c21000312650102c2c0c3c507001e41c1c0d400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 130534433 1250 130533183 130533283
    0x40201120902040902060f070303051f09050c1201030b071b0b0a05151306051203041d07053006121902010216060c020315090604020105031e040302030903 68
    0x1d030000c20300410440f14000c0d0050b0700014205030b10706a1402030b04202c2e02c2070b0707814019130f580c0007680303412801c0c8500341860501042c03038203201440d0f0a07000240c2c01074494004070300b0201c40d542648030351103007a80242d44042d4000180512568004c00d481007111000d210302440145980c1c2d000824680100117040c0e555461011600c6814080505543d0f080010078424181c0c81501d601da00078615441413a00c42c641c1001114030300750b0f0100580d0102c81c0441c04c2d44083c421801091072380850b00400d1101040300c10407015610000203c03082c00700c0724035074034148000d0507603860140c2020b4019003440e11611290f0b41e0a21504400030340000c2d1000c012001410183c1d8034401030745020000710202c00080c188800220762580c0c4400038410b5140200d0407110b82100c0b9602010035514150340203c1941c00c41070004000d54002ca001799000340142c40d90300710304140381e046400c040b90141c0e4124016080081da40b1031078642006510301ea5104081d0100040c0112101e024211030f030300c2040700d41d0010f2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 130535683 1250 130534433 130534451
    0x80f0c0d110310090302010506010e0d02060a230d020a0e12100f021c05090601060c03080c03040f02091302010914030705090c160503070501060b0412060b12190b0603010504020112 79
    0x400e03c12190098286002030051884601d00a40030340030072680c0500040a410341c050641c0b500c0b08042103011b401415031840c0604030002251010951880c0020f2060261041003c9418410080c01001c03a038290058403200c0940d001000384000c595003511070503800a0407280361401060103000000400d0000843c28050104070019015041d11100c3e0007001050702e5088221076041144a4044081a14550f0380c9600040c0e0302c0d1500e078000a4006544000040d11030601800219081800b52145542e1a5450b5000403051030048402c8010044408108403c40d60072401c500301610b40e805519a04210940100713a82d54850305c101c1d44604141e40103d00214422001c0382c4001c1c07c41c03441501d0380d49142c00c050340c1c0d80e4482e580c100ca09601e8039000041050500342a0341c10350741030349540341c590300d616155000a03002c40400c25074000404221400200000c010950b0405c64006c8403007202c81141c00c01204000d00104032034080d074105010040181ea01c0100950f10642c840d00000359070300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 130536933 1250 130535683 130535689
    0xa17041104090b011d0702280c090c122904090204020c0601140d0c0e1e090a02011701031e050c0d1a0702010b030d031e02040f080f0c0d11 61
    0x8000c0351503900903241c40750210920464100c01e134181c51a0840e1001400210104144140b00032901c090041c0c014817150030203001d61000607201c01100e042d0360540c00300640c0b07900e80c4501260380070a414503601c0304510045a08598591240700144000300040d84aa000d1910b042c108200120340350083d42200c0c003460380d00c07540b0080446402a1003107403104401403210741c0d2841c1c20f000c0c0c808446240c540000c02c0d49488a0702e0703100c007580030005102203498480014012140038089007404e022105685102141d0301c004a40b195000c800203000c600180d000140c0240c0034100480c910400c1040184045008000000301040100498000712003030350810b241003900c10301c10164020304030030040062100b9103810340181c03940c42c54a01ca1340d07154060240d08a80b101061940c00d83c020122510710203004c2c1e07004e414030400b020030724900c194414680c2c0089070301c150000c1124440000007805055410415803c504050070010040c00d203051001a82030401c0c41401030000e0004604610303c0e031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 130538183 1250 130536933 130536953
    0x70f0611100c0c0218040804030201032c070f060201020408071a07170304030809010902030c040b040207020a03230d08160c050307030306080d0207051e120a030207090c050a1704 78
    0x60101c01040140c901003480040040f26070010580c42203440c50191050701900d95001d9006540c030000c05442d00c0d10356401500038182c4809a602a00500314454062401f401454a00c01c031000c009850901e09009010740208200d40180d02103a1051105101c150030001d245002c1d101d10f050350a01d012852009568a8811040d0040c0350400e0011640d070346076000e901840c0610300c40d86401c11907544004215080b1100307041c0107949644020720001c094103186c2e005d5041c803000604054a032820b6074000c2030030f20140d54411140c5105a84926201108603035581001c034800c280589141030441c0313002013003400c020380040841c0314219203606c00d49005035200510f0f03a900405403a154145800e01600810252080130300c10b00441c03440c0f4541c14130204a40c1e0503541e000f0f2140e4030038031403c906408441da200800c140c02c50180c00380da4450581c1000269005440396008007410380c104818041595407100746502441740070301c1059101ea4104003d54084004504407c5c141c0da41c50501592132 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 130539433 1250 130538183 130538203
    0xb0414030f0a0302120109090201020c010c0206091002060402040c020a0c030b0a06030c08030d0615020714030307021c030306060e010503040209041703070509090f101a121005040b0102070f0611 85
    0x1c030000040e224005509600500018070300f42e84485041c0c1c1c2da039a2480140e403580d40b0000d006800500b46200701c1c3d8014500001603600292000e801c02e80c0c16000724261030030281241025902c184100000c6103403034050103262280d5807002d41303140f50141d030f44c00c918008035010041100380b503440010308140156200100440d00b02054008450b594040c0d9900c913840340151000007810401c0c0414292014141e4840c1d9080d558024204203207400070503100000f440d52000d505010800c00d00380540c2d40c60941503c440030820081d0000c1c045031402a0860705d599003c5000d005043c10302c00300340d82c1c210f02a640d205405540202150341d6518082c10500b80700b1a081002d420080180052980c0c0321000c1c15205005680b04003c80d11442e8507640d0700341045482440e51528020181301941f100807450b003a00c2403080e00b19060007200340c0c5204001604413000c1d00e144c0c0145208020394a081c1c0217070121a0740a001400c0c40e5820140600d41c0541380c0c1c0119000c1c041002c805620040c0100026260 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130540683 1250 130539433 130539457
    0x1509010b0319052401080c04060c020d1202030322171c05071115010e060f0121050a0b040c0f0302340b0c0301080a24050f100902070b041403 62
    0x3c52401d07200c810460459101d01110040048105900e2940510119401003104022040c2007502c2e2941c100c03850b0702c2c807840407038000050000850014403629181b003010340e1160065601da00e02201c45100140315110711002280345d05842c1c8000ca074184d09a0f045500c03a2440c05aa074008449c141200741c9101d101075070301d00d403500d010071140700d62002d152722000d049001030742c1e445181c00c01410340e4030f03400b03004c0c00ca0b102c3c04180c0820184c2c81d01000c4031500f460b06050544507440d9070a807000805100207107203201551103d0070040454118840d04031a001d080301c00300029511468018a480c403103008032020f050340010403a640d610346040b0b10900000c01d80304c0c034412604002800f08452540f40c0d085408100c0100403130548250042620b0684102c4c000030130981d4020b4a620624125048280c00d14012404040140b40c80500410b4803e9402042c045854140403c2e0b40a150700c1d03550200c0c00651051058400050403c1001600940c2080f06400c192010000140c1140700d401c0321054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130541933 1250 130540683 130540691
    0x20903030a020d080903091c05010e030f0d06050d03050304020f0a05040f020705010e071a0a05120106020312070203040b0f090f040c0c0b0601020d0c03050d0e1002121509010b0319 79
    0xc00c10394006070b60800c0f011180d8400095490fa900f40c0c80d03890041c10040b9622005e4030400303040d00c4100018180303007980241c002150300300440c5001401c0d44d12040f40218418000140e03100400c0f01c41c01044000c0c8030035036042e4010f41e090745008180340001b50000344258070300004c20105907540403640b005010300030410000803401d8200300c0e0080d400880c00302e980e07509004808140c0340c0003184503800c0700c149a41c031a0380620004054091340d0306c282d1b441c00501c0014090302a0024400c1400390180005800869030303000d1801092011160050a910443d80100020b0010000403c155428124028031050301c030191900011003002c08040354941152501011150b56a8410440d24150340215196045070b203807080126110115600c00e130006c0b40310340003072070f0000384204001c00c105d58400b030000440c90002e404840c104814801c007480d0664000c100c5402c0001c100b41b040c1e0308a810700e2151001c0300b4070800450007140c4d0522034400748040c00f0000640f10f01c2400d10001e890100758100700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130543183 1250 130541933 130541947
    0xc0a090503120403020118050a050d0503121006081006050a030c0302040503010908090a0f031703070201090203060103031d0319030c020a0e10140102030909150607050709050a150b09010309030302090303 89
    0x141d043e8100344410707400602c07130b103018400c107281d00b0f90a0400da503000b42611800b1403c2100b401681c5403410720440320f611041010054042101700070a0145d0350300d40341104040d2070008010b00b40340c4007500461200c0700c0a0006c001060b0081e04031600258681000300e6200c01e0310409500034082c607031015801d5401c00000b407007003002840080c000b0f404115510f152450f1114010012070700385000082c002e04607000e0202c181d00980c0e001e580c0c40600d520001c224070f10030f98082810b00100303030300c12000b140f0001201120088000800828880f00350000d0941d0003600c450398010030404440079084c081c2d08503805082d510b9200400300541202c0049545a00782070110244e03c0b14039204500c40c00394503942d0500701d584048122540307003400521094080d2261004ea6081d904850b0120784e10100402c0400c0020300705004260042205e80310000321454881896015610350905031135055044100a04c1104010010303100280403c1c40c0025694880c0d25040c0c00034441c1200c0d02c0e9242c44041000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130544433 1250 130543183 130543213
    0x11d0d0206070e131b171005010804020a170f010b043e0c030a090f031a0907210b0702031201090b0a0f0e0415110405240a08070905090f0c0a090503 65
    0x65171810103581d07101079484d0090004101e000c0c1d01580c181c80c2c840500501049950310440b4103540140c002801010002d5483d03000c0b15580007000304a1141d904482208051010288220100960240c40602800f03208011490f01c20925a8081451019200031a0100304541c2d860000e5545000759a503983d501600d041c940d690440440480011189200030498400c121004002c072503000100c0d01c04143c00d603454002150006180e01078911642c0e0000816940d00c189801910803c145162046452424019501c0000502035400d41d80100506481c3c509460042030454503100c000040c88511b0380b0004945205650002e0030036080e2000c04200303108110940c0e4092481003249110f0b4076440030400341528100c410b04603045030309000420250901110040054001446510705501304044254443d0060440180060220b004001003903400c941c01c6805040b084400240b01e160684080308261401032800b81241000f00e150710310705020780b078008054440141030701c0b4001d185101c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130545683 1250 130544433 130544471
    0xc0c050a0f0e010819020607050c090703020909010b36030604080d29040c0228050607140403020121091419050601030b0c070602040305011d0d0206070e13 68
    0x90000b4000c44580000780c0c038440002c007058200c540196054421046400304030250304040025106030290012004103076075000c109070712560003a240140c40da4030440c18800c0d9500160401c0e0744d2200c081040026044d0150380c228590600210181c0030b0746400c480c00c0c042e0072040003a4980604c01d16050104000070440900034280c2481c00800100180c0e0b0300103240014034030145e0100c4400d6030440080d50600742c000c00142d541c2c500403121040f404000302c02601400554aa4801c400b4030001c10030407605001c7d2540113082450580352410420600c0c01e107078411488006e05010040c002642c50120164a620b10345000340380c1000002046e090150441d188040c000d08540201001c103612000760a0350000c660340c0000040480c0d030308680c3e45070501c010150403030015890a11100c030004010380020301c06184900d001040000c0700c1100344101e40e01004082100e84c11100b80c3d14616a80010015070050b013a140814100c00c020020a03007041a110b5684041404d01098203500c03660190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130546933 1250 130545683 130545689
    0x51203040503090f10080f0a02131503060605040e060d061407020a030e03030705030d0e0304050d060209030709090b060d14030a0306031505090d05131d061e0f010c0c050a0f 76
    0x94001c076010304c41020410024000305074100450303a10400b0a41d801110744565074070201d0b18074010b18148401c5205500e100c156807100c0f0b541140100c1040341c103a45801340b64010700403400c000e401d082c106880c41078514001040c1c10b00690102503801d043c8001074001c14840031074403a07818010704102d01c00035128628002d0680210710710711b0100003e0300740041195070f81c0380c01402441c200043e906149006e0110b5950824980c4818403012a2079985e041485901c0380c80f85100507907074000e40c400d060401d591540028500d610700031f0400041396240040c00d602000c1258118000e0466160800c5c0482c80b01206443d83e1201050394014180c040d0b1108d002da9002d1240c8031250a2500c010000341d50f012540d0758a150031041d120415640140040d00703401803256940c1c0a01ca48400c0010100561100715012150400c1c0901c11381d4101600008400c03418040c1081c1e11240002c0400c1d9561002000c0f1810091450000300601c07550f00244070242c0340080000c081150b4584c042071117412540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130548183 1250 130546933 130546939
    0xe0106051606094d03160b030f090703020a0302010c0f06061202091333050a02091c020604060518181605070b01030b0429090f06040b0c0705120304050309 68
    0x2001070707403481d540b034161005034224038262542e00c0103810340408200103590124a0b0907204086408841120142d6a2000b80c5032107001c044c1c49142c0a09c1d1692917600240c1010455002118140096100d07803003104266602800c0c440140203152412140c414061200075108525101d40421414403054030502a01d0089a03004601e48800d105030056805450300140515038000303c1d41040c40c003081036070300c0348844070903400141c529542004044d144100c2d00440c98550000d1359400c1b619012048a203104940d60110701c0d450110780c04614140f0650007400c081c401c0201d007600e20803103144102d82541341c000d00700b08903c0c580600456258030b400d03901c481240807090a01a00c5610441c2668211070304100a200c3c2a4655120340308841800342058070705400721020546804808416100c1e103546882d001065450f1a5401608010081c041f480c21600314400744401300b880383c000580c01c40c0030404116075501d9a1b2824920313050350491100d030b1400001c000c000502101101910400c8415 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130549433 1250 130548183 130548233
    0xc0102361c08090904060c030b01021b09070909050f0f1302010207030303020d060f0824040f02040221130302060610050906030601031b0201021c050f0a0b01110114011a040e010605160609 82
    0xc09c0059031210900e200c2200109140c1180c4e4400c0c3c038080360043d40000303481c1080521b160311a01c0500030b813042111070254810b410307400e0003850070b81d00003080d80c05002d801009522500320760000f52101c0ca03034440a420550086812458a8003641c0030b103000b40307110007905ea26141d403003401c20f803124844480c50f12050a54580444100100540144a103a01400c4c07103a00e01e500743c0c200070080d001460300390400c10700c0700e1907040c01d10b40d0803054501800740d0b250100c404d60320b503140091070200c001704481d025112071442041019000010344140c0f1304100e803c5900c96941e480124018118070001700e000d1308100540a26064041d401080c0c000a1141403540c2c44410351100801e480b41680e240c840e0406403000100b484415600904100c4030500d4040c0440051000043c01d65516544160b06148024010030075800010209400175601c00d00b030500341031805101007011001481035200b8040c0000e034030760a01c48180c00000401354015400c0101040c40e08101c0507110010038400b02103680 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130550683 1250 130549433 130549451
    0xf0801090c060509130f020906030108030903060924060f062803090f02040b0d080a020106061803020a0e09030f0a090314070f0513020c0102361c08090904060c03 71
    0x400ca0444c1c00038200502100c00d07603068800c0b00401000d00140c0c8103002c030350030700403048640e0b1444000c41c002e04411f0b0041d0340791710040007094200740015000d51040d40c40940f813050b03031600340e007803c03480561003d084071041e50304d400100e03400c0610300c0f1100d94000700006841c84014002200b455500000503442c240b0b501200c0d02c26011114074140280008c80d070030082c0c000524103031704180105103010701403000c8412541c1c0c40d0708030350700112022009070351124010303c0f507a80d000052420307806000300500c1c505440c58000c03403450704141c0104002000007100140b1102030030000c64822003c0322f0340c1c49541d0f01c8038000042218805000031612208604000d40a60300b0018048081c1e40b800a0007810719440c02c81081b084880300300700241050b130240151443c40900b880a001e03005100001c180c4103000504010803900346c118040c4955050580004a0b240c9801c43d4600c2000c1c0c80c0e031201c3c0c070414001d00b000a0280a00c0070300540c840d0b185001c0008129403a04154410001c6403014806200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130551933 1250 130550683 130550687
    0x5010617040201090e0604021603030c020d0c02100809121909080d02060606090406050306090a0c0506070b0412050d0c0915020c0618010c02061204050c040204050105030a150f0801090c06 82
    0x101501e02030300050907410244401002d80c140740e5088040207000501e020040620080c8205400000b60042a1740e00001b40141d90180070343c0b6100030b01803800e0703440014154005070002000060000403c4081d50008070140c1040100b086560401e108003519a2515004a180900e02003259000901d0680c800510404002001c0328810b0098000e0195030f0f80300400e100040d04844040d9030700640710702c40010300d924144005805111188042e000c6481141080f1508100c0c6500140c01400c04114034400300e0b800300061904180c0c0100c0086255480101c00c80e264041c655005804501d401c00540a1941140c002d400310745103a00107600c0d02084030404d03030310707a481118130390f41201d8104045a40a00840316101d4030706014102411030046640210b20307143c03c50381c4030740c44040d110700c01c0c03006204040090504800003210298a0541404002000c0f80400341a0041058a03000c4601400e8600c001d480050309185900c180303481d030348070030060103461032003002d58424000340c6021440c1d034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130553183 1250 130551933 130551977
    0x305010c030c1220070c0503010b0d0309090903170c0a02060709080727020c0d0e0604050d0809030f030d24060503040b04061b0c0311011a06090a0315050106 69
    0xc10a0b2a1120208800c82461000d00390b0284081828408030340090015040d10002d000c1d21402292a06d200c54140002c1c5400c40c3c3c2030010042c4075951601400c0d0000394080841016200c0c64203020561404c4c600d0143e40780d840c0044585c4070080c0e4001000b2400710014050842e21201d40e0841d2800e480700202662044801d000b94545a088010b0030b101b110030075a0945090001e808111510364443e21000d4102c2c0c000503e55120f54000d60500700149501c01404003040c1e00494595140507d40400a2110705c40c844c0c0083c041c103004180d40300d541c0d074144885884124140c054a03a101071440d43d11008205c0500318031030104800507200072802015200b00265049600c9291440d122507d880c26840c50040046404513203c051160080b00101c071010780001e00c6843d0544c40c03100074507015122038030300816194640c6c540811440e030b080da0942d080c00c1502003940c1642e908c40032000495044400394101818009082140040034a101c0c1d1042e030403503c080d55020950248102001c41d02c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130554433 1250 130553183 130553201
    0x5030708130c090216050a050109211709030c0601060504090e030f030a0e07080a08040609140d080901090b040b040806060307121506030b09100c230307020102071b0305010c03 77
    0x150302d985074248000c0482d80d0050003c2e4880f20362541c0480d00e59a2003501e031846030801120965102ca40d00742c04c10031200c065103001c00304242d103002110080000282172140641c003082c1e03404101d50104443c0d80051007100c0114500c00d0988000390384a0102a001e9802032181d89803c41ca040245075044501100f900d16503030311140f03036030700e5601c0307200e08400a0b0032690590041402125000035210004101803c0600d01c50718190303440d20324020303015081544550100d5541c00113141281c503d40e403214030b1a60b21030340c054105512010303808012100b03d0510b4102d1944160f00080c0414544d0014025000310350150049078015501d01040c180c440400b4464004000b000c240424000340d2807a210080e80b0b01407480016105a40f03864000001006651311341e200d412034014946240128014440303e00300c1804c200405401c5d0040450f00c1482c5800a40c4000b0004804120258803e404a456554000007028190303082110040e290301a1440f04031010340ca01540c511440740a80101582 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130555683 1250 130554433 130554443
    0x108070605070b01033008060102060c070b071202040f0618050d02030a03080604020f16050d020105060f01030e0c031e010c03090b06040218150a02061b0a11010902030703030503070813 81
    0xa910319078030003403200c080212000c540d0030b0b00c030b00025081d103030000240d1000e151b6641d040c0003418540e0029041c0000a40720012010081103214041880780c001c05400c0100d40c500080ca00d0803401804d00280217a403c07859030001e145200080540e801027083c5c3c00c0c4c856160210160329074500800c4191020b0100c005d4068110300104000b107402400b01541c4084081c1001d0f1074000ca548041c90350fa880700002405010b900440c46003481000c21400c192110a400200b0150034105c5c0010f4011400c008140d0406441d070803020380c81c0d41c00380441034101c00c0280403114100104001e01520202c8140103004a44c649880808007521030300a07080d40c5078110440b500542ca440080c04040d41c800c201c00030807426504800170035600d0b11b5820b03c0d09507130313220741c1682c80c3c80140200a05184000d440311440e1200d8005110401000d001150502056410010442c01e180102c00b07000d0640e12801a6041c0a24040001850342000040d4410241e5a481c500d4991b0344004115003110407040180c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130556933 1250 130555683 130555703
    0x2030405070b0c03070b04030c0b090c060f0f070b0103050c280303030218030d030e0d031b08040512040b070b09030703020c0913020409081e071a070903060f05010807060507 76
    0xb1001150007030181d04015010b6a15181c01600e034500c0c141c10a0300c040b40000c820551182c1805250307500c1c241c00000c200d011341801b4007140000740180c080c00316000c1104000084000c2103140350421a101198480c54001d5190307540e007051502c62130a98511406a12480c8985420084910a202c085000c1400c040c15141c11914100c000b9080051051850400d0010311810340d60200941509036056035004107014a128003981c2c00d110490904500745130400b2456448250b030b922078a840004280340802030307950baa040462034100800307503450b6044d40004002c40c2d1f681880004002003400340d6608806038032910381c1c1991700e10840d240a401a000b5805d49840361030503041c06900f1450034030b90300182e02016000a130868201031412a05d40f24006458040d00450003840c41d10305512240c0742c0d0401d02180c507202821200e90084a0841c4102c0c80060714603070141c0c8081001e10f81003a01086001d1800d00c80ca0300601080c0507c841910600d000058060301c1082114000390b070045802c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130558183 1250 130556933 130556939
    0x90e070806010e2716060c050a020910030f0303020307091d060d14030c030408010507030612060b0402040e0c0306043804020d020c06040c0504020306100e030a080a0f0e03010203040507 81
    0xc80d40e04400360400407100d200140c858802c13401d0b40c0d10b07040e0003003045000e4024034080000900418a242d40400288a03c0a0f5000d02041c4042039055a583d01a00c02c6105662103010f8030a68031402c0d00004d00302000c01d035426042c1035050340039510884550b20b41c030203115144c5009801e18000b04000c440741521b60b0300003401340e0030b1650f00c2c552030620505010703c088800704000b5065400c0300008082940c4040780030131550300709001d010b4201009040c00c10800e400e003100b400403e0602c07030000c0e01840d00c480b107880359034440c0d90448008188621090115040203088085154801d50703080b8425401c2c141c1c41a09130f4090341c401c250415031524211307040c1c2c04800e50520321552007182e17603502035424010700c200d44107280014017000b240070000d00500d1400d0716000211350304d91740055010354810b10400280b80c031485050140000c0d40d0901100740c0d210000061316241e40c51500400c13070030340030802200c210340001045c000d40c4c200f034545081c040c400100745404c0b80411100035215034040c3c0010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130559433 1250 130558183 130558199
    0x905010e060d0302011b021f0c020d0507030e0915180105030c010c02040915090b0c0c0c062b0b0102150c04030b0405030706090c0e0c0c25090510090e07080601 70
    0x7910042d4424000400c6030360f007481c0e84260301500c0340121130258001240211940c40385d80b2a000311404141010468001c2d4441c009540e01040ca040c2000d1180010b28031003814003450300c21a007000010140e180320324280700b00310070302880016480d0154000050b072030440c1c7d144a4501d0305855001d00140b1801403414011200080d04c81001d0782c001d0740d034085002c0452034a201012903508100404118645c252515450100c0d000f4a4800c0d03100c1c003801028848100031561305550071040320b403107480d0002c141c01d48c0c01c4803081d180040e00104038000708035001c44c07441e0040307019030b1030907001daa09007625480d0358441032008984030568090104401e100190b00c002d03c1c1c5400c9400761080b64141a140e0340d5041c1180c0401506031940d0882c000201301c1410840400c95000317031100c07612030a10a601041a64402514a00300201003503854082c21104072020404010810014240701900340f000079039101c4107960160f42651402d00b800180842e100003102c0c41127990003c0200320982c80d0210b2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130560683 1250 130559433 130559449
    0xd0c0201030510051201020703020c0916080a060512010e16050604150504150801030c060e03210d090c05040c260603010f020403031805031609050402030c040e10060905010e06 77
    0x860143c00014101007038540790201c9000341540c1803000169558040d0802a103404650701d40644202c811208001c01c027220b00d401c1c125081d0181c10100880d4030f59000b082e0140201c0d40249030080b001100503200c0da581500040341d030300008800d80740f408596806050350b580042c018241c2005040004100241e140c00310f80c3c02007030b45490498205034032030644e680c10703910900300c100014420800600c03e0282c1d410194008042a0829008108007031001c251039104034a00950031503021303aa03a6145c040c03e03604071004d03486008404c10480c40e01e40b4010351360030f140d8043e10713001d2741c0340902205625000e40603008042c030543c6130b1000454100d0045240541000301002d4065484200316000560386001800144d4480d444089400560000318074440000c0d90062f4400d90244c0251051004a03005103c141e40c2c2e80f040104555585001291a0012111701c0541003498030540c91342c0500041074207010415010000c0c400035554510700c000b07540c428010345c00072108071004a011840c001d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130561933 1250 130560683 130560691
    0xf1701020403080304030818010212040206090d02030609010905070503010902180703060509010308070302010f1505100c020a0608090706090b0906090d0b190e03030f06101404090c09080d0c02010305 87
    0x26241c10784950795040e1640041d03804a010684002c18000c0595080e0150011420414000c50a25540c6461028050406800640603180c0001c2280054030f42c81400e58881c0c0d0080c040b21441c2c106a10707414000c1007078600030750b824010030402091514040c0a040130958000301001825401c401421028a9010307044005055075850300186035110181784a000354010342c666511050107050107800c1d1554000e0039070341783e4500b15201c1013140040300d442040c0d0b00240e03081c4001c0e99119000742c800c203801000195010005c0f50340001c80c141c1c040350052107004102c05440500d0b40d680ea05032006191800394035003880c01030061505904000c006040c0090780141044000007050b100c407440c4080640d1000d000340d01155a6aa810341580110f0101c515014001d5265140c101c4010442c4580a0300b0303103100300c8444c2c400305035151040c80d100d07506c0403411103595901c03a56960305400410a40b58240e0118199203c009840c03000800e0201c00000d481d2180302e100101d550045005000c024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130563183 1250 130561933 130561979
    0x31e0c1504051507120f14150904060b1201021b010b010212191209050105070206130c0b0c030f0301080114060103060e0609090111070c050f0a030f1e020d11090106090f 74
    0x101c1460000030b41070080344141031011b040022800030041c404502c020b00108815491400d1803080700050320382d00900c80e8000e4004400040d004540c0c000074217050316030644402c056001081440011841113a81018406604000c0148920341d07001a45c82d40301d20b43d03810140c01820b10002007030a440c461034a68045c0241760100904404980f200120f441900d005d0f50b041c1c0d540e000304486250104002500022480d0a8109036a015a030307924550101e4058802d0400b00131401c035800c40c0c420800e581507030281100b80d5440c4c1d0384500015000349614844c60540c13414510200b10325501a1082c6010345900c9a100491944c86000f071140c09240940342030b07129940d41d82010025500307000540105da01c6109116400e500d04401c00501a40f10824940310f23000d125002c000007007041020b200305581c0710000d11400e0300407d68030b019200325040069081030341e03031a540080144008002c181464100c0e0107100e83d9807038000489a2030003500500312000080c1707406100750300840403e0b21480c0015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130564433 1250 130563183 130563197
    0x41e1b081f030b090a030315120f02041107140d05070c0e041719030f02040e040b04060b0a06030606020d08040c170a0503040e071b021e03031e0c1504051507 69
    0x195480d408000f404031001c41141c0c0120403003504040d414043c2000c1280078504c04402c071404c010620094048001c001400311050b10080011500e5603048007031250034040769240c451150741032602e4040d038200445595801051244085580240159104181c10031114181641044d07004075404401800a0700c00028034800e80341c0c1891107038002d2400c11810901036840940c000070203400d43c0d0b09542c0c10031b06140144801c2c810003040c09280c030b0f8440c1e007110709800c0940340c41c24030000030440e4a0b21715405c0118284040b440b150182c000408881d00b59089910030501690b0031188110161402890030081400800c6040b84181c82e10704007812a2081d1071459140d80d135000d1556005500600c101c80740c038401c05c6000c9801c6810700d992a2180080325640c804d255001407080f812900c0d800804c0d40c085000381d089520200241c4490a41034442001040c00341d00c14034440d500f1444a0081c14803c200c0013004201d4049003481c01944d01000500e04c1043c030b141c5018a8200c020842c000b08014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130565683 1250 130564433 130564439
    0xd0b011e02100c090e0c1c02130608070507120806010e03060a0905060106020307050330070806040b0d03020c090a02070b0117060f060d030f0e041e1b081f 68
    0x4004120303100000140c00a2040c0850b07035022000340c070100c8284034184071001100f044a50135990145600c50003910903e0f565031040d61031080380c14000c0d902100c1a40c4086106e21180b03018044801c1030369541d440310390560303031000000c680d01d10816600802b40c0a0200b00c0ea031010740184442c5401c07410505105030603124030b001081c81c1500c101d41c0703010300390b803222060024000c8c18400d9601520061001e10314018694546603a00d00c2220168510000d81d140c1039005001441000081700e182c0e2207210b5582d08100700700500c2180e003521414400c1c0c1c50044118603510b448029003400641c9034001e070984c0a14041048151038bc010518005d9507020040900003880f07d80340f4501a00c136041841c00e1218a40e0011468220000e003a0b40b00c1d0358141c070a1248551b0303610051141a941844c0980e0301000a81d0200c6110741c103c4007040c0c1003402c0030890300001b5400c0364009c1c0c20f400b01800030010024510b203920700c02c0d50540ba030301010426840c0410b50140b648044441c21100300800000b50581d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130566933 1250 130565683 130565717
    0x3020412050304050411090a060e010c021003050f0129030c160c0611060106081512010e0f0111030c0714010209100305040b0a060503060612011803020109020108010f0b0d0b01 77
    0x280c40c40c4125800e40000800303204a01d802d10071403940314000c055450a0891100100e241054507010f5001440341c5c40c1c000040b140e11500c0c80e2401c3c181d000d020141c0319060744001401400050b1410407044007480c001007284144031204141019265407040020300002898600c070b0341c005408000010010031414042900221640700481d01c19180078540d540b0780080100010440194024103800c69801002811340c0701440a030010444a41c9044420601c00060000c44951068940950130030405000311440400d0340cd001c034420b40001d1086542110904c03c05210448510b100030300c1c2030040c00c000c1800e10600c01c0d458203a000005141000701c00c00191600000404080040d40790802c010400009030b0f40e554011007401403c1c80307490b082c035001036102c0c40001c1840d40200d11a400c0702c1b4070741c2000d42043c0351941e10181c04031180801ca040081c081c0504800507404911006d000050f082c070213660ba13100710f5503000d09642c14440f603816100043e20144c200c8174100807000e8610ba80c819 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130568183 1250 130566933 130566959
    0x5030711160f0e010b0903100e031306020d0909020304230304120609020f0f03100506030304030f050309010215010812070206040b0a03050a0506120309060306010309120801031709180403030204 85
    0x2040303400440843c03a11045503881e000581298081d09401e200951541e140000c04264005040d00086952001d101c0141e19601a8290000c0c01c89420300e00000d0154020540e9042d1012a40c1c640869945421807170003030388025100100342c070700314503440d03040351482124070a4011074203c02e807032030300b5554648d500010b66004010384040d0340d106101007c510b000d01c2158011042514502d01c00707419400060344a00d07000c015010900c0d11030000800940e014011a0003a41e4840d0303614040540a0030100c1e600d1b001052a82d0243c030488001a00d0084500400c504039202000106a210000c1c41c1210b010b400c1100d00b01d802ca0b80c1404041b813844a02e1001d408010034a6074001210f142849100003030f58030141105024200154800c00081404021241c0d0114240d443c1543c0f500c62200403801040141009000740750314802c0d0000699000c0c0c901d9048034050b018200503001d04140132001c41c8104043c40e58001003624105c100071842e01d860b03540c002d00138240141403595810300c80c1c00c0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130569433 1250 130568183 130568189
    0x31303030e190806070c0804150c05010506040504020a1401090b0d050601020d03110702010c140105090303070305090c060d0c030608060c0d060915050607060b1c021e010503071116 79
    0x803400d24410680c01e814101c1d810381145140b000046034841c9080c416544904000d8003d000708099580c10a06001c1e5007805c440007007a0395600e48a500fa4820801040c101c4021000c1355554288800304040b03107064000c0500460300109140b94091a020020703c03441c100c1488603052013903a03800054803000700b02c05010040c96070007000c2201d1038400c000a0904682038210814940b4290034510b240780c201081d60300007582801d001002d00410308002e956074130003021100c125800c01c0c04111002d5000701c040c50040159841c14070031616a8907072507031545d140f014245c1d0032000a2200180b2244140c00a8a0400c8241070024410b40c030ba146217801c00b0000c42d4060003110340020441301c950001d1092000030001c81c0c0c0c1c03c00403c0200218080004000d10845d4400d50f00883c0003424054154014084203c1c01806140b06460280243c02c040404103812f0384190681b011040c03a049841081460408050752940d1443d918420169a00d0405441902052180785034880200e00341c03250143c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130570683 1250 130569433 130569437
    0x40501090501052809080d0213080109030e0117010503060a0911040603050d02070816030f0534060305190222120b0c040b09040b2b0b07020d05090f0303130303 70
    0x70740c2c0d60130340b00895000c8503100541940d26001c092004918040155000d05040c01405030741e4000c1800311003030103d01074024880f0b9518111412080503040f2503914141002a203462001d00420907200045260074072940380c25410200028107108000e50210071380d103129101c000b40c50718644010400700d44bd1a0011202030303005034150580f05404108200040ca4400014501d48075000f802459103500d6102c02450400155468402c000341030000e014050120001800f408080c2c0814400440703035103c1b481e04c4411441004215588a03000c0c3d507208861008111005050080c1c1600080d8040c0d40c0582d1000007010020807a010943c540000030002003100c1840c0e4a02c6041c0312a1880c805000c51101c0041000100220300a05043d50b107482000c0301d00042d401c42c40c1c000301d100103100d4030000807110541c01e003542100840440d21411940240950501d5503103070342c4140e91300d8000d04070000c089a420b11aa0002d03144c9520226001c0c0382c054292400c0c42d0001e503580c01c00541716001180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130571933 1250 130570683 130570711
    0xf06090e060105121908030402040e100207060f050c2208011805060a0507080430050703030c0503060604030b1e0c0a0f08160e01030603050f070302040506060909010e04050109050105 80
    0x100740e252504107009840d082030043c2c07040b4400107680f15a2885c104000500041c0088000780666851b5400781c02018103074025070b8030850310711294030002c1d400b0840484d5050301d00701c0a070866801d01d00c0750381d00c6500e040c60b0309433402004030b2210301c2228503032401d40003402c00c0340c03004034407900b003801070039070700c1d441030229080502e80d511b0b2036402e1103c0100303217a9859280c80c04001900e5805011213070043d40010103c29070b4000742c14071142c09004075081241c0705502c156006000d6174030400904020707000741d908226a0302c40c10310440d02d512059440d5035003c48240300a002240c03142e255107400201a5801c07050150b081020f400c9801c1084030310b03111a10000c21000450f54020003141c4107209217103400f41e02440c150442100442d03114200504210000208032400c2c0d011b0780c4154040e507089400ca4004180f24011540c0d00c4445000c200d002d14182804500241000001d8a039040002440c00200342c4c2400c4684400240040c0165140d40d00c8412040200740207219060040e02d80d2603c0c08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130573183 1250 130571933 130571939
    0x604060504140d030509090a060f06091503050106020d1206031703040b070e060a03090501150801051e01120209070210020c0307021804030e091b0408060601030608070305030306040f06090e0601 85
    0x1942d48000c4107009030142c0c803811502c100003a0300000f104c80f8110304640c12840c6444800020b4014100c540044180c050051008030703d40b5040b003580d104950302d101c0142000b0804000403401d80d030702845a00056848180040c14150050742c039400a90130b00d48000415603070369182c0040360719440e40740c00c9a00b00000184001d0154142c00d05030f01c03610714106800b84403040d001041091040c0c660480406640c2c1400301c04014080d00701000300140c0300c3c1d5107500941c23199512030090009841a5240c1c1a41d080540d0080105440300c5048580d9a2404400500c1c29000d102000f40000c00780011800740483c4807000d903a183c805030111145900003161039072203e01c1400420a1034030001e000c6510340034100800203900150550540000ba601544180c80d01e0300f60782050780001620300d0170a000410040b4002400207211031145001340c0c1c0c14040259100d50781500c41c8001c0c00098110703041000012003e041c180c10000140e100c070b450015416030b80da05270104482011a100d020741c0c01c044010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130574433 1250 130573183 130573199
    0x509150c092206030c06080c03040b040204060801020a0e0f0f010e13020c060103030302090907080411130b100302090f0f10030515060c1b011407030309081b060f0901020a0806120c0604060504 84
    0x11402a010347d04000340c0a040ca80c400348a01d000060000301000c640c000014115213541d0802e9008181450095480300311940001d00044c04050b00c8a00415a0a4101416151140094185c1201a100d0f0b01602c0500e805000959241d00d555904d030316020402080b00c0001000781038001e6000769001626015001e040119805028210340700b008880000e0101064402100e0250700a040b54042411281c50410001919104500903440064120b150b00c85c180c05400820448a0448440c110240d004040164000146050541000039007003544a518081c1e80015000394661065072140008940011255031090081c0340c141e81000004940c0e01c0f2020304240031241d001d00344119803840000e072151160007513a101400f01620780101c6003d010b0180d040b5000540b0380113070b9018241044002682e07955090300d17034180071030411f17002403841e10040c030985a507041107a272581510f4695100b0002c0042c1491021141380c054107240c000c11b9521315002740028040c0761609610b8610300307029 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130575539 1106 130574433 130574453
    0x314040f1a040b070201050a021207060906050a0903050d0209150c010c081608040b0408091e0102010e07080c04020f12010b0d0509150c09220603 64
    0x101181036040015a9000e48031821864841c0c84000300030055544200e229405441200340400c400642c400d02c01802c0302c00f018130450700c19240701c0d020951203138410441207500787ea50b551090f0410081d8003525520440425082180b4070054a01070010b00c601c27120201b03603541c000703020011a907401d00c080e0216024500c04d44d840c0d044055040d80200380c554062004110303010001a640304009030038514400c2c142d96810700319100d135038402c03400700c3c805081140c40020a0141e20101c0e2103040c0002d551400504215044210060002e4215a06030f14a17021030b81102209000c078441c00200d410f004c034001d85006a0b15204006e00168071301070200320f083e840100030000a030050a02d00075001000e1101010411a1580c098450b51240c0e4241c0c440707060920200041ca040241c440601400000230b404914054070400c040f01c0b007070300c40f00503c0503074030703640d03d014000e00c0444c000d = true := by decide +kernel

theorem cover : BRFrame.Cov 130395683 130575539 := by
  have h0 := BRFrame.cov_init 130395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130395683 ≤ n) (h2 : n < 130575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
