-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:30.655832+00:00
-- url     : https://prove2.me/submissions/59c6f668-502f-473d-a3d8-db6d2ab6e1b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557374100 ≤ n < 557553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557375350 1250 557374100 557374123
    0x80d0c0918020c1c0f02160807182a030c0e060901031116030918020901020705040b12012306090106020703020603071713050f03090901030b09121209012714 69
    0x4e5400800f20032580c0e10061100c1e4a0010b40c089504441c4020003107000c0702c0f000e1183c1d42d40d9a010714028440040400448188040300040c0860124030510b4200da08042440341e01b80103101e150301c1d22204a034507010b6501141000c0c203000e0300120181c00030884605c00e6880310390501d600d030b940b00c9042402d010211410540c0c45450b00c0440b0070340f450000c0020840e0301c14003502800454000845c00c40c1c034401c60303082ea00160010280d1a02d4401030101030042d0034038a0358400040c2a04290440c0c0c203000c0c501c0e0201e80001082200803480c0c1020500c000c02600c40760003020908014460301d40c00060003400d81c2c0d0100c48050b01eaa540c50b42c1110884002c014607000844174105200d0500305150315030020912840c01e44040411829010350b59010344e5413950b6002c000c140040010507036940f500707500042c00390140c4096400280506040707501a140c0000301400a10400c20b118a0a109608011070024007040d60524040003280640103032010142003410b500003640b8548608221040418 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557376600 1250 557375350 557375383
    0x42a03240b220e160207050f2d0301020f090a0b030f0c0304060216030e010206060909030d0504050109060e06100f0b030601110a1e1b0605160816080d0c0918020c 71
    0x3d141200f03813400d440794032202000c094843c1c40c030042010f1030420020b0000b45009488400c0e82d450700b1000301071222a20545283c01780300c42c60342c608140c40a0009010b0700c64440d10706503540c0c8801013400885040c170307448442d0003003061081c0701d2200450b0f60174a40060b50034030f8003034603522181005802442031012424100c82120204020160405a55040a03200340c09581840e40c82ea028048030300e01c03c55150500d80c0040103c1300c81c20803250301881d08a8020301c0002442c811942d101c1040301c24802c09003045c4c2d8441020090a002e45400d01340140103014600301580d8903048100c0c40030300014016a06000d2001141c82e0500e4080200310840ea41001300c00182e80003201c449030403d0034054090b692900000b02c4075130076841103e0000202c5280b83d40c1e03e45000402644003082c40301d00d000468640340c080150580c910038260f80800c03000d00441c0d603242d5861481c4810012242003240c0b0405000b0042010400000440000e404000440c0c00250341c03000240360f00303030601c920302c40050404c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557377850 1250 557376600 557376629
    0x180902070c050112050432070303020f19030905010503130204050a060510260c040305030f131d0604110702090108030d0501050a030c0302042a03240b22 67
    0x1440301407459081198020703210500d010060f14080d100b074890480780604500e013490000d04880c41c100710030400310180071840000501203402c1460820704140c0c0180c005a1140348110f1502d9400d1010450540d80354031045100c0c1a1030340c028040982a05c102414400e010000805103510741e80e40084140e40101b0801c0340b482d060404030001c01150180c01d001c1c4074192003442850380100312110520700504090060078054240380c120440006000d1660510180b00010002d80c040020303051054542885a8540942e406903510781222540500704800401011043d41001070680e00d030070100949000c20603900c0d400a40e6035610441c0c00c029003042e03a003000025071000c048090580c07000301050034401c40e6030325402c1115803c0310f80001341c4a1008110f041006240c03942c0020500044111420404036035054000b0449080401010210f510b078481000c181c09041504024001105091803a481c201362002c4003a01030540101c075501e001d040300032000c0d00e03e00703d14401000c0f0210041e54 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557379100 1250 557377850 557377853
    0x618090c110d11031b010b060c070303020d2d0e030312061f0f05030a20030406060806130609060b0a2309040308040816020603010f0f09090c0618090207 67
    0x40000c4058080c11280075860000d540350f071180c100001c140052400031810001010701d103802070070000d0003802c3c8a44d607031110403c041c0c0761304020744088001070000c0c003e002d2441c20041e003002c100c082c1a0302041038500c80c036a504840c0c03c41c051180d02c001000000101c0072031006076040c0440340a607942c507200200d0700100307000b2a00d10161240006440080765821021000c82111000c1901140411400202da840d007911520140d5440b900d1640042080f034001070040c16403540117801c0342440b000010400040c40181e0240000030003084000b8140b614207140b04540403843c18800906154a40c141c1605000c0ea076003024240400050020071003940d075000080180c5001c42849000900f100c80b90041464225400ca1145030992111116070343d650351401821740c400c86280d0100aa004c41610141e12464050350117001410541c0c40294107010343d041c51098241d103c507010034107110024002502d285051000c5820038181030202c0e160b09020a101660240c100240c0c0c9407004c00e2140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557380350 1250 557379100 557379107
    0xf02030f010f0605280b2b05060103141b0a11060f0601120605090708090a0f030e03070504050405031b070803031306050105030a0c1511010f05040501050609040c0618090c 75
    0x302268012103207022074118216a00c980302c1402c60300005c1030003800008100d03c010310002080300b135002050f02d100100d0041001401c0341502c0c0758a07100c06039100f04005841d6014401e003180d610042140400d6854901d4101c0c025807101d0f44150700c2004041954080c0501034200084203403189001d560030752402007400c11445408030b540741e00003415540c4030018172105128210a0f25000f0300060659030351400199102c003800b41441949204298a40d804500704641a4189074800c0c0d42c0e0f4860070300140c04261910596400c03032489140352006000010f0000030440b84030103800083d09944103031008001e800c0280320741c010011404000704101c00382410281240255101e0740b02000507903201d40905a460380d00c614010320303103001414284542000b002c0c00701c10707840c1c851074282ca4171a0b00c88040f609441e44002201000c5890300305102c10081300b070148950010051b90049114682511079819060483c840c2030140491203141d80e580c00404844d0302d02516000209100c01814450000e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557381600 1250 557380350 557380361
    0x50103060b240d090c091401060324120c05030a1202011b0f0309050102041805090708010c0f1116030b0403090602060108120f071407030b010603180f02030f010f 71
    0x1038810080e00031484071981282c0c184018056580c0b070070905080d48061503400400c2c0e210420785007140b10075000a850051070280213084401d2188011095240c060050b068031107442503a1464440c404820481040c400d1288044030403010b0640c2003a04182081c04000c0c9060b0419501030044005030424451444004504201d030781d402000703041c200178507103505070100c40d1402c00041c111106c0c02a64611071b800c440007580c040e0000500d070941d140b1082d041c81c022807403400d01c4541c41e1010095200c0d070a00420000308504030080c021940080f00c0100002201413440060126100103101c8400302000050281d42482032601d001d16142d00700b100c140d0404a800b1000200540e002048440c0701040c00c9040740d40c100001c120706d8001040400183e04114103940303030100c1c02c0c03003d40081200c0d00744001c500c20350507000d802440d0544c2009000035005801c0401854103201d040103441c042e1080e0344080036000010022040001e00c00a800c00401c03941c1d0560769820500046a0701800780e005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557382850 1250 557381600 557381621
    0x5030a05071109010e0105010c02031507021f090f080f0c0109080702130c120c05090a090c0f08130f1e03030b0102011503120509061b0705211e010f05010306 69
    0x81800500c90b040c100200e16000b40a041c034010a82801017000c1d50003074403507a00051009065601000300960300e0003203004210baa12005a2040e01078402d118618240015252003100090040040d5500d0b003291603800ca00740200341d95000154403040300d44540070389243c403d011009000b103400504001c1600c0d00300040c164401d1100c0107021503d90450302c01c0b569100c0c445e49480760444184055030000b006014a030f6001c1c81002c205c1844a03540c0d00004074040c148207072002601c003000c070f500104000d052401074420301019005002135000c000c015090001c0c0e10003103c90008070140703030100c40090490007844010400301041000c043d01354010540d0400282d008102c070071a80440c100721002c941c0302c0501840a030440645034203110b0380c01041402c1020307101d94a070010428a401340c2d08054000340f451500403070b4041c0710614000e071035901040300341081308050598000000d900ea031505002d090803106540310035003c240d020b4020344501c4405000c20411581e50782080000b80080054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557384100 1250 557382850 557382863
    0x9160305030405040f090209180f0f150f0106051c1b0c2108040b0a060e01061d0a03032c0402070507090c030c0f0305061801090c080606041a0d0905030a0507 69
    0x14000140750301ca1103402c41c6c0e190020000030003900c03010003841603807074005690501800703070a9102c6804041017040b000a441010002c1c40559425482070741d0f10030016180812001d140e00041040c90360020668160100440301c00c2c40c910b80a204039002010190341201c20740070301401011030141c00c0b42d00d4030400fa00034518012000c011440c507040aa03214003102001c00c50410219001c1950188481c0d400b10340304100089160301c460300c5030700c0c0790400d90050b8006039401c144404800000085500380c290242c680840b0383d801c40d41c01410400a64042c40805100b28410a88846580120880302840030340308540e07800e01d50130f1864072580c1c00c6c005c140009080400700b190041c401c1c80b07001d100040541d10748480011548007240a42000303131456500c019445240019800002034150080c195858001440d20410802400d04d0000401d038910070207080c8802c005449440c1a508181031118080980d0b4600007080380009103042800900070348004104000c145400000400040b4010302 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557385350 1250 557384100 557384111
    0xf03210f02030a1b12020309010207020d150b27100510030f060b07030e0907050c010c03020702090f040b0c0d24030b0109060f0905331311090105030916030503040504 73
    0x100300c001d20269640318800030b00c03081c41d0401000c515602664002e00b4a00000d42f414040d500000c281440b10101a940700300d00c030710f201c6c844000601c40e10b06001c000391505e0a05150501d00301c409100d407400010108504c06001aa06844031500315015004c01081c60368421011040100144480010316038450301c0c1003404210041d40c4400c5c0c0c1d548030740c19518400c603020080103001001002508440500c94144800040040203014041c0300300050b80d40180c1340c40260040064228010b094072071046803031414440415000c54800da84496000c5c0c815650b201ca1010107030040ca01c0684900707440318414000d0030450303102e003421411a4000c0c080c049069888981140444600384a4410443d0f1b62900c100075030002a0000c592150144440d840d003035091840c4c1c0900d81e8288080383c010401b040c000c614480c07402c0150b40d40355a00760032003008a00c8031500068428482c50a09606000700400001e0101c02c0400040401040e0740d10032071101a81c910b4072950740e42103402418842c60901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557386600 1250 557385350 557385371
    0x1410051008090a030e01300c050901170601020a02120d030b010219060b040902092a09030304030b09030712031e11090f0a1511010c08040f03210f02030a 67
    0x540c1070a00402d19100905621100c659003540e03001850f0001ca8180000094039000b1034015035080003800b10303483c0750014406640d0340c44070308403100d1001000a103c0b040c4001b8120b42d0340302c0e00003074640c4005400e1031426125500185d1819200f080000c0d403110a507404d0005c105000b240c1d201c054112500e042c026505135600590300c075030903c105c04030800c420030401c8001c9400d5802c21010501c1c0030380001482030517a00481e90700002194440d458805548101c143c010400d40410740700802c01c40c1d40390502c0407000c0000e48070b01c158480640b103d14005c010401070710040c41211a5075904c2540c082c84518000d4019020b441e501e8a080915207640d5051200011140291803242196541c1ca62910800008100c2c4800c100d001c2503070403400d100408a011018030617466200110788e1284080b0021110030142503a0061900004200300c1d90140800141d029030364264090349400c041c3c55914012400070191254603c0c2d0700d000500f84004c85400082d07a500031401901c003039405110030241c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557387850 1250 557386600 557386607
    0xd02010e03030408070602040e01080c331c2408030f04260706031e0207080301030222090c03030e0901080d0f0203040b03010335070b0402030114100510 67
    0x680e21061030300100700060000e00500700511165200e000014185500c1e018003100390203090300900050381c40403404007494540030300c000e0049804c040501e400110090f18400540036860505001240c000c99230600b007440c440701d104e81a81306490100041031402c202d894401290041b04803540094544c04503040d0404812101e0145103103840f2032806141145601d1840c202d0391010070f607000c0b41d803450a0010310510481d4020482c0d99000310315103242140d03103134825111035034031700b03050b0710400c111400603100c0e2060b241100d4040380c403c400c1c0c20700303802c592a0142c3c1c02c0388441803583c0380162420411481044030401e59010b41d50390740145940c5402d01102000a003e0515940d2104142c0c4100b5440341a81c050740c41514415030b41000da4540600100e80c0081e0001ca8100c520380b483d400e01c91001c580c0585080d40d12038100440c4a40640040c01e0901c101d400213000e18180740c00103002e43d142500000c3c1301035804d030b80b100160320b80360761201c03008540e900805204500c80c6402c502894030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557389100 1250 557387850 557387861
    0x20c040f271b0b0a05090102010b1522050f06030720010903110c01171503010f0e0120040918050a0b0105091503060c1303080a09030203070515030604050c0408011d0d0201 75
    0x3d080225500d8119031130001c4ea5142c01a0007114115904c2c0c0300c6064580c0c884035613004100c4c21010500c2d850b00146c01c80408651245140840550403c0310100100c0d5601845802d0f181401d88906c0d03581d0300c460404491000400549a58103210004140d50040c0154806a010381c025540c3c0242404903151468969205444182c002045840c9a04074001c0c5100030b180c000c2d41d0001900031002212002c01c0c02c1d2541c007001152050764134000005001030a005007494040c0500441a0f07550010418001a0096000d4030041d10b40c0d0714a10b6a605050324100c1e90703007a80040803203400303071400d01c1c0075948800e0902845014400150104010101c1c008880d000302e54028080c0115a50700c0b40307051a150003200c0480b122114107040000452a00c00c0140b801954543e14034075100e085005040c586441035000600403400500a007000604142c00c1d01e8100604850105003901e41c042440c0c01070243e034000032015480c00f144400810715461500b180f65000b0070950740700600d118801d80c200ea2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557390350 1250 557389100 557389109
    0x4050f0615030d0c020904060b010e030a060f05100609090e120d0903020c040615030519021b06010e240102100608011d0303221b0e090105090d020c040f271b 69
    0x10341d0800407d00103070540d000382c90307840c6061416402d601501f40001c0d240441503d030561309181d40388000301518803030f8000c980e03000903005228408507161410080c06102e070b500c107841c400c69a95101d02411181442544440c108003038030152110640c40c0c9130310040c00c9545080700036210300300c201c40745420140035540840d00c0754480740100411484e02070380a81401004121050307507059541300811550700c00b41011070010341080d00c0e5151511440c61800e4410381090403031541c20801c111401803032001d109555001d070107650305c40e041c840d00181e02c0d020385010800c0c03800d0f061250200e202101540199050303504030304540001040c049071aa100e100564004004112202c11000c403802c503013509900e0144a80840c4c80c520356646a810700d5042140c000c0b0018030395050600842c04000d0040b0340d04049214040c10211035000c202030342d2010410840c5000e0340d00c81003003000d100400d074803903c8110281c05003002d84045100d215034003801e00040484800075501240b005030b141658900c41543d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557391600 1250 557390350 557390359
    0x1e030703052502120a03060905011d071b1716210518040507050c030706050106081621060b0408010e0d02070e06060d060510020c01020705040b0307050904050f0615030d0c02 76
    0x60300c0f1340a0f050401e90141c0006414185c40e4040000c07000307083d1203514000c4c0081030300140128101d1070b019444150142541c000c003da105550039588650741c011001641c1c0c420100300404442003a41d04042c02000120041c150611700004103101d000000314039200d0b546079240c4081d0201480079203540c002e140e0302100201c0003200b0090242071a0384060f400000f1400c1031410031203800401071665022080031202c0c1510307000104026900840290b400c0300354001c400c02c5e01841d4200042c00c8503101c04801c05140084031084004100300d6000c88050030b01c1640c440c2d66640c569408070301901807a507042c01c0903c0b403207842d0f040d8584049440c1c030a031062001d2400b03a54540d102007042c0d0703401550144141d82d0359080d002400b503444405400500d2041d4010f0141302480700d002a0910010781e00542c082c60030300c0300084040e43c000c00da4105450702110410341c503895a051052408184042100441c8110750a100303410000c2d0301c40c03007900503044046940807100c400b0100c9552440c140000d402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557392850 1250 557391600 557391613
    0x420509251814040e030406090e01060509180a020f0c0a02030c03030712030b01140a0c06060e1b030a0612030203030a05071409040b0f090a2304080901051e030703052502 74
    0x111095040e0007801000001d0000c0307075903280070502c4e50a41d030090b40f040300441e1040713408124226041c010140180980c0c1807003400d11140d00007041e00d00198114074002182c0310300c0000c0089980d64192074a10854641031500c0e000c0c0110903540d0f450400106922031322a1016400c0d40e032a00204a03030682e6401400d209100c03805000c2900603008966855062003445102c1028a181e00005003c46070095a1520440794440c14080700311000c58124182e019640c004203c0b0344015030b5040311940d04100d206654968800007010003d0445411001e0081e0300050414141940080914017852680720100440c0c0c03074028040e50f45800c0c0d039005034400c060501070381c1440c0c074040d40800008540230340084454440c4070001000c071038003152074034825580c030a03050840c11100041d000e640340d01d0141610740c9040584032642c0c140146528581001800101c4071016401b4035100050b6407010b0130165101c0c10111809400b8000031075070f81c80256803801054074000a40301c04906000884d4000d0f216 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557394100 1250 557392850 557392859
    0x1c060504090c05100210090c060e011e0f1b080306090a020309060c0d0e010507020313080f19020a091b0f0201180303050901020c160303034205092518 66
    0x40d003104c00d581807825401500c44071485004980102505107110305803035101142818409015510707000301080c108190101608a00c02d131000313460883c284141085400c880d01900200c03071010300e200403030b00c012641900074010019040042d5010b40d50407a14002d85075030b150410402c0340000c43e0410030651140001c81e4081813484006e0220704100385010544030751040115081d60410340e03c46d00164800104c00c0c400c10300200218018000f100040d00e8802518591603580c0d03036070400c0383c04165055828080441d6519510b8000a00f40c1c00018403482508a1000c580070184400c0600420b2080c00c079691040e2061249000e06100b031b1380a25220754440d10101c2c024038004010b0b800c150360070403149055140030842c4940140c01550400320043c2903150040c01c1d244c4900150400b03d106103401410155000034174180d1104065104505103d4a1081000590b80d03522068003d00b20348184a0100030001c0c2c2011010170340d004441c01c4240e0f03007400b02c50300b15124410400c680c41c042d00500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557395350 1250 557394100 557394109
    0x80912030604020d0509061f0602100203060d050703030302130f050904060b01180e01030507091118040b040c0e1801051c14150f06010504230d081c060504090c05 71
    0x1a04048003600060501180004c080c1c11680181c0d100d00d45648090104500b00004140801c600880c60360388204152818030302965454000c40705190481c1c0200029280d40c8038a410705400310340000c102d17141d03286ea07410043c0081d80030145100c0c0000d4501004030b1446441c6001c2c00880c1c03000340405400b656030f526030314001c0c4072007191181040140c4094024104501c8112005412003a0082c0d650f03514500e01140307050215889145500c5c05c064030b5030b40c0b00340e0084c19076850b8035030050100c80030740181c400680200940e1004c240d209280c09446042d2680c000c040381d680010503603112480f10100c010b00100e1000900c81c00d54480c807941c2c1c60035070702010442c10500d528401d5807034205003130440091a040c2a40780c001c81e46d000110204000b03065054140c0740d90032030b1083c00c10924040c14014411108000d0f45982001c584201d00a55090340b503c00c4040d9032a40c00c220000c1d00c0700003071084c41741651140141c800070a410200041039034500341c45805452a404814442114688000d20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557396600 1250 557395350 557395357
    0xf0603050406060803270f1c060f050f06121209011d09012c0402030d030207031809020a11060f1620010504030908460b04020f01080912 60
    0x842e855a00c1d5840000c00000070800b401c44912202d600e1a0250f201e52801561080002155440345241038150070843c0c440740c0d140740040c540450703820700450242c2030041c09840f945003178500c102d15000c100000700f400d50301924001c000840304c038230982580d81c416650700d08c6501c1c0f01c512619000c1040458640c001d84290201d8244001d80040c9000d03a1000a054034209911903285182070001d401c603a86581c602080844e1802804030070a070805070042036a03044880040d0f401e2540c001403050600d4020f031940c1c1075a2401400100703900351038040b00c4000c0e42015000c2d80201d0190320410122000c0403e0203442035045c160640c0b0711fa078132100c401d5900b030258480c01060001c04e60001d0314801c1c035002e03890342a05541d030010600741020714000300340300002d42c0001e010350407026680e000d84803451410170100d100c20680f420442803010748071070301d031100e07403030203c0545680c1c0e00072010040304888440c40342d8000c413035569a0004940065403604011248140c041e04200700800d000c14250018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557397850 1250 557396600 557396603
    0x80c0a09091d0105040c09110f0a03020a090801051602120c0619020f070b06090c03060d02040c1808010615020102090a1a040306110913021821060103120206010501090f06030504 78
    0x6035407000702c2d10000903085a9042e0340c20340c1d000640710780c1407109403d503000308200d600d55410542d25090800b090140a030081d21195010182c0000d08904543d1265200801130a00d0200810150800d11618000520010310300001b6025681102e000100c1c480b05071100c00389240c014003140c1d0b580c401c082d6446c1412195428140742d00344440190300e030218004d4118130b80700f0000542039040c1141009100580201548900c01c0c0800400507a43c80d5201c5031905e05506407001316484080e040d050310502c01030540c0340490201050300040001054119a00312801c21038640b41c00390a01404900341e108449115410445164042000150141c002c200114a01d200b81e4181500c0c2d0395a541a50341c0002040e40d0f01c9004121111540741014403440000c4030a00d08501e01882c1120700d2807400304000c003007031150440465504280300022118000a10100b007a01c00640c1c49107042c0348400b00a116020040c4610000403d841d40584903070015611182c0486440c140703000c00880150100400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557399100 1250 557397850 557397881
    0xd0806030708010c0807030b0303040609030609021f0c20090613140c040302010f0306031104110c03120f15180a09050f0d17010e06010e0d0507090903080c0a0909 71
    0x2e9040d00a11403101c5840799540c03180b40382e0800314030040c203032011407a006200790400c100030022685c0118110044907889400400e104e038140c000a14610380b00089011031348111742c0b41e41c0c21694040c5140070040d2082160060f0407074402904041d120f1440c68150300840a000400c040d468001c070800d015640132800825000c241c0291119000c42c10b4410782e001a03008a418030856800180d1000009040e14081003980e245448620b601c1c118095160700031907460705101000700c3c00d80120b82951009030201c9540d400d032000c1d00b03c417044040f54048010100e00c00824203035000e040003040c00000081a500d0b040f0540000060f200c3c074082c0100f0741c500e6540344030200140060040c001c00ae04410044c011281d20904040c0c40c1507a140310940014443c0070040c48180e245c9030041d50031407800c1ca4403204d81404c0340042145044040d1020304035104141c0005040030b680c1d04480c01c03070362090703070344a0b001d4a032030400d51000d004140310300002ca6001d0302c041c040d0788480d034800c2c18489202c0c030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557400350 1250 557399100 557399113
    0x8090a0f0507031208090a150204271107110907030b101205010f2108130e16080906040f11220b0d021e01030902040e010c03050601110d080603 63
    0x19a00c154411051904407480d80190303104109011905034445030220301c13402c0070600352405501494940035028801490005142c1d121095a01140c0c165009803030446014514441115030780e140d181c007445401011141003d21031114035003c0d105480845a000030200754001c030440402131240300051010f404c0554650f23034140c50b0303600d1015040808110f0b8803080c0c08450b0b038202c50b03020b60310160014400120040d00821103514181603c440740c8006908050308000c207460801000e1084240c1e2068200c24072101244078004403640b24020030807180501c0c040d0034002015212194102c4101d00f20350803040014000c65034a8081c442050710901400b00b80a000d0b200040d4075401000c42e8281c0301a503100c426490003400e102d165150b0780f0480d01e69240b900c4682c009401881c0203c0420304613050300200c0c94099000f0f4101e101069802070050049009240405000782441a141701c0041e003440c010620650140030030a0b294112040601503180e2140d0b420b1750410805406244c040c032a08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557401600 1250 557400350 557400353
    0x80a2415060507020306070f0e06030c0409020c1c08060117090a0b100306150b03190e0a0b04020f01032009010c0209010801050f0903030f0a0905011e0b011d0901030308090a 76
    0x403040d06000d44415220580c070b0704014018189000390083c01441804900c405180e000707508002101050081156050b640303603100c0a24091078003983e0f000c9a500e90000c60b01360b01c00d88011440c0d40d03100e0780c01c001c28001c4608900007110143c000b030364160301007030020300344480e92a5064402c80d448100c843c00c03145042c6207541d03001d500f640c00301c81c03542580e46451000d208000a17405860814421000c20610850400b04610890f21000e842040c01801c4840a00024011500719894040303480081d038291020904001380c001c20110b401f24440c01050200701c22039800381c07007000c00004038030104004c0c805080001c1071480c2e12062626050040107284580107903903c0c051540600304400000c189820000a01c28030103002078030040c00ac0c3c10600400c000c22401c8100c00b9406a0749900105500c1001e09183c0d005117000d01c10380b8404a800c006031a40c03100b044c0c00100c100b04007a42c880d805882480280c3d118120b1458107107034003c19407401000805e2044102503040350807202698800001c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557402850 1250 557401600 557401631
    0x30309030a0c050f06031510110a03020d0e0603150906030307080403210c2120070e0703090b01050904020a0b160614010323240907080a24 61
    0x10818115a401d4010009000c0740c2420303c0c013100c111400752103c50035418010040100100d01e40101402040c40306411070215108180700c80c0c1905555098452000722030400035143c003103005855010a0050103411000d00309402180d1141529110080e041c801c51010064104400340440707506110902180300451364040080c030081d03100d820119801e0400180c3c01516850710003600051281c00469000454850011041490880d0b00900e2403500c0740e01040d100c260340081041e050300780464503205c80308000104c2c1380c02c3d40c41000c1030855940c1c07100d608506403890340c00700522110490380100082e042020707075150418801084804500d0701c4d4007803d5080e4100d142c0c4000c0d00c0c040c0211010611046100c1c501041c100d80f54000078540c1142c0b02e6000003590b40c8044a154101c110320101010780c00d006507044140403044802e907032205040e14a002074410f40d212205405507040c009036094000403003407280c50b44130300a0801c9460094030259060f1444ca00c08800c9030f2a82d1500442d483c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557404100 1250 557402850 557402863
    0x103090602040b210106090b030a0504020607082106121f0b100f030c08040b040f030216121a0106020d12020f0d0c110c010806150c010903020f16050f04020903030903 73
    0x2084d01c0d0000759158060081401d5040c0d11801c107004400000b0310001c00c80c482120f41c40422008040740e9a107c1d403001c41c82c0c5104001010305000b00201303140160303044061441c00d42d500c0d8118a01d0050300e50101304188142c110071844540d5001889940c01144000c910800d4000001c800180000304080032515452001c4440c00019643c030b42000300194041c8100290030b1601e14040d0458541591120b801c1140500302400032170001801c0410540700308508cc051000800070613002568816400e590791242c7c0104031140e0b40c040240c1507006456820207412101c1640c010400c100700c030103042e5041d000050030003020640030000e0814502450000786012140103070000703114241c1c182c0040c6084845201452103800843c54005c0c641ea0080340950004011199001c1d600d2140440e020b080c4281440c00e48694282000c92081c560003150401603010a1f038107071400c2d101070101200c0614018000c5070303400710a02d00d034030b0724a05007503000c1c0030788420203400c880c503000752003000900e0f149 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557405350 1250 557404100 557404117
    0x181f110a03020408150112021c0f080a0207050f030c09100e090607140910030c180806010302010206060319111305090a020a09060501081812040e100f06020a020103090602040b 77
    0x2500000e04100c2410b08216417100002000d030b801000d1350402c6d9203002d0034014950003910883d0b9420007030032101c0f800c0c1c100c41c90a9030301c4841da880e819100d203003e61090f08045805405402031010020305801d00c40c441d0081d5a10003000f604440304041e042000e81d03030014002000c620390348180461030001050107140071b1b0041400821007483c1010008203041d061600d4900140720901c421425521070b00c0e02070118101c00c1c1804280155040b800319a080004011110040c0c5800c100042e5401d01088582c181d80c002e07400d44440e80d5030032040c1a52450130407449000303084a050400040303014900382c591140340c000c2844400003c0701c1c01800c140c07402a10098a2500038207458800c61408e03800080040a80310f81c10f000540c58140040c12429005240c0c1a15080c42588192a000107103d80c10b640300805e51015151903c42a100c115418111800c03940302e00185404a8200c40d030541600403114031350300800040d90a54011409420001411240c0f542c00b0700c40420742c40a91005414400d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557406600 1250 557405350 557405357
    0x203030703051806071221020a121d030304060e1f140a0c02071710090309030303180f080c07080106080c0a09110f0726030609181f110a 60
    0x4114461240005081d440c9160b4484e810800840e00081d280390700d80f030801882030410b1212200e10048640050010710b4102c0421840010310f0740e60150008a03180080900b14070402a070013403c01e070031782501c0b50001d10f805941d00500020b80018425007106680c2c108900a44903170310402d018034412450303a00c04106c01d050301c441072060455000c004450340b01d0a03104003805240341811002c0d4548219000d2110b04007a03000c907140f400c05c42000b0b6085414202d9208206500440c14001c2c010707001c80c042100000d041030143c0960207030b44484806519007081d103500d1580300603690400c07580d12204180e0010300030120001040d600c00e00c6000700910303041c1c01521f00700c81008208900d545c1c06411801c0640c1c03801c901034410300003031801d480180905c8001c8942e29441070900340c204d515a9122406400704ea10b002c00d903944514800f560107440292010075803519469a035107a00a0901c662191aa0003501c2c203000303601000d0909192500a000c002603480e00c0d2280c04800f507800a080031011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557407850 1250 557406600 557406607
    0x30a0207030f0f05180a0e0c1b03040b09060a110105070e0f04150e0915070c11090f040305030a060302210f0a05150a060503030d0903030b0a060921020303070305 71
    0x1070503001010201e61412910300a40c081d140b002000d00180115004161904907006000055481d03001900010340f174500b41032101481c21480761000c41d408210210b4501032141042200c1c040004140e84c01e4828000189081044031f0007803103a9500912030420030001140c010083c400030a205150107440b01d950351800c0c0c4091401448000d8030006000ca0140345001540d036191000e110380103058621100395040503445120f9180e18107005039407007810944440040c407100a4001d0503102ca018828101e13481c1c803807800400c002d88640100e0310307070150403900000035000030310400007154819860340001800c0c40e260740200e42440542640c0100d40e2000703210303034a080d42c1c04120040d10f00c2418001072010340c0e84c036540c2945505020b8441003072041c006001c141c014190380c00860142c81c01604070381d1201c0c03030307100f4071740140c40b07000c105030082454000500c10078246280f2804c1682d002d42c441c40405890184a4202c00801102000740008000c1250005a505200500c5240d010707950f62503c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557409100 1250 557407850 557407853
    0x403060f140106090b030610050c0d030e0712030e010e1903050622020a0b090604030605130615060e0112110f07120825030e030f07060b030331030206030a0207 70
    0x718200d041c2c11040601560784000c01c0160321050450303034010825070b101e042001140700e0541d52409003800d100118040e108084403202c0d070603485000080c50b440221071040e6503600c4040300c81e4803182d2000c1d001401410340101d265004100c070700c650b02d6004e0000d1955000d80c008200031003450390811502d03a00f0407001d014082c07003680e403000d140c40c441c2d2000c540081032650006540c05950b104500d960318001c03135101d0341c031741e9414256001107801032030600a5180154842e90041c06104003110403d2405220a4140b5080250941030b0760080d21207071031a9001d10015a1b8800703441c840c0c01072407511000002c80b981a80380103420052000d00480c0d072128000d15280603254440c400000410110302d08004550b8402c6107c441170144110020184403a10301045010b411003074401d4107a440b0000c0d1503001e4640e0903004118a80c06250104081c12440082580ba40f080301e8030382902c0340d030f06445a9401d0301e005580c8000380c4100540320711680d41e2903004c9605904100d810080c100d5021442c0c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557410350 1250 557409100 557409131
    0x14070b090405160c1e08040306050a0e0a0201090611070924120f031b1208070e090103020a3507150f170705040b0f0a1806080c030703020403060f 64
    0xd030400b00c00f042031101e05070980c1c402062840c01150141c090181d102010701c280c40e0384c480d10070505802100059480b0748900f801809090162b070a4182e480c41d002d8080301c6c540c004242c121f101513050f9599210145009c41c1211107441c42c00c4c2c102c1c0680118080020341c00414030032000c21101c002c4020003150700b00d41c2d1a07100c0307950f5a80404020b11520401d000050b014090021109a02d820245d4100300b10000305c01e483e00704218014100714801d40c1c280031407a0043c211600c07442e401d94455895503410700c2405100e207420311009402c403408003014889c41040500c9250b50644032040100e540081510280d101a40d013840c614041c3c00a02003440020300402019440c62440d081410a540540c0d00081c100e14502c160b1209010740100810030080c40350f0f04482c02403080307860550b1144081c07110090b960740030014003004103401920b601c10140600342c594080712803546a40c9529669911640e02e00d078802040b0100300741e4200401300c00505944120020280c68403000516806400c4005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557411600 1250 557410350 557410361
    0xd0305330a0f081f0209060a1d04020c0304050f0105120412141810030e030a1701080f03030a0e0a0f030807110f1207051207150b0103090206041214070b0904 69
    0x10030007004512000c0c882c1800004005040c108550500d1341c074081e4090281c00280505001d656100100007550001d0b2036201001900520b00307800c40c42d858001a400308030882c401d0320a02d030242d800c02d20040019190035502385100020605020345001c081f035005018080048404460b0340010079000c6000c9d0360702203942e0214a1000c00d4603840c003c0100380c610781e215448010184240b5070700130320854803480780d000b0360000030340c00c2c0459480b940040c9002e401c01c0824400034a0511108000160400002802d2140f0011213000307585180c481b816000c1c050861041c03045842e200d107020400000f16252a0140c0c0d281c0a65200f80b0203040010004200e400d100c901c00c4010740c81441c82001c13007031001c02c40403070072001900503d80c2c1e003a0700c2c036200c0d003000e1280000103d1141c0116400050240a42c180c2504242d0b0400403c03060100c84c005600f2580c4c01800603401c41000d200c03e10244011007100e0908a0080800b00640700341c0d4039030035244c1401500031043c101ca0124a0005d907081c10b0240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557412850 1250 557411600 557411609
    0x60b03071101091a040501060e01090e1c0f0516020d1514070206071214072006071b03030b1f020c0f2b0606121a0402030d0305330a 58
    0x203000c04443e948600d60995503851844014503200ca002c513007003190941c0610020703ca1100c95031143d681d1906540000d180045441086000b800042c0c00349081b200040c002c03004164607205021845d40f9000c85080c0c0006584442c044040c80503c07016a440c5200103042c50710449001d290b41c1c00704076001c801e41e54040b51070100d6030341c068184115945c0104007627034042d06524040b00380d841c507040703201c020740b062025507440c210001007807068650f80001d18035406030601d01c0403451128000041c6030303502d00807505400002c20f2003084105612700e0703804180046010740707408101d4080c40e10001e40c1020008280c03100416200001d212400c0e0140720a00e012034040b070303980c5108201e45d1b02150301c4c401c2504134203120481144260300e19080c1c55074285482d94019004100403a150504c0c0035907100300ca0300542c4c581421200c480412440200080e11490b40a0080d055680c0030103000e502915010b0b0a1003001d1407403826100c800040f172200d550386483d14140d15040350702e050083c000f0300c2c0540d800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557414100 1250 557412850 557412853
    0xb0a060e042103061d0402040c05030106080a1a030105070c050609011a0609032404030801051527040e100c2a022e0e06090f01031e060b030711 63
    0x10403000c60030001c900007020030302c4034201d940c540900c07404400a100c55003000781c0d4002c1000100700c019540c1c5500c94426442502d0404c1881000d41090b81c8030f002c240b041c3c0b4001a5810b0000340c446000760062140c18584500032a0840c208130b00190a5030012a00d0f42c00041d03070307030308038600348102000b0a54010510000030410035480c03050741180c0500c484051401040000b5a91803181c408100d42e0180f201c03903c038400e00034100902d0712100440b05a40560019a544001051519040f01464001c1d0032210800f4602a204030300b10404564012400b00e00c00c20700c4003c409141c4960184122110f0120b004d80816601c0c403148400320742402c00100c08001041c96000130b501122103580c407104148518081810145200040141c2d0b020003030422584884032112011401032031b2280c4180301c09403560a0300d04400700900081c0c0c081e00d41c045a00c130842868082c0c51b540694001500380c082c901400f25a88410f4007801c081d00c000b07600c9001c4c060800801c121034141c4c06000074041c0d518500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557415350 1250 557414100 557414129
    0x6140108030f090f04050f0403030507030b09041212050106050c1b010801050d06021c0203061017010b0c010e0f030909100f14012601080c012a03020313030b0a06 71
    0x10196924020b5192803038031040e0000d105089582d0300220a41c105000810074001490100813001c9003080c08d690880102c1e0801d00802c004902030700034507030340700303405059521141e58503290b00d540021841d80f0310040c00108181c0001c41c3c00f442c023425028081c10740b42c096581c800905018580342101c049005d00c211140002d00942e82c1c404601030441e14103c8000a81c4075440c1030040c002c1c45031a07151141c03510460300c4094a40b00ca9006103102e21401c660460205d01540c45c1a0b420030b15802c1003a184082040040c8508011b0174003404400800500008003030b0903841ca558a81201803404c0d024070f60003ca5032007410300d890511f0550041e01c031818003107503d203003019003480e820403409405c2e9112200c07042403030b699110b008990302d2071600c1001c5400c250050034000031050003c0c0108186070041d4084074806500407510100000c10070034210401c94100c83e9000003440030352608030114081082140318038a003a0f003040002c4c50003a009499103090015940080320ba02d90700c009201140b41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557416600 1250 557415350 557415359
    0x60b0301170114040201050c03130320010c110112140f01030c051e0904080f07060b01090603090b04120212030702010e011a1c03050d0c020615010504151206030c12061401 75
    0x1030000c81c4d08254207003041c0351180f00c40450310b8254002e901044486120414000040c8084038880510202011131041d404801e41401102e4500c1810400f27812807401c03403c20403880d44528129a050020f80d0800501045081c00c104000740d015180403019549050060040c440c804113290000c142c203c0c0d13030020445004807a01d211100140d110762041608200043c2880134402c21a84000c071480400ca80e01c08c19494450000e000d804801400526201e0307002c140e95010b482401c80c0c07103411a9014070302c3d6031142d88102c4103403400d048100450042d1914192660b644801a500801c05500089083d010b0742ea40242102c88a10140030307140c1c4200c581c005240ca480c102c2c42c20b208111040d65540b98100c0c142a1802c0c41080300141c3e0f81840c3c43e80100b1034503070103d0428000c583e2a003d9504070500303103004644a0042e8010221520115000100814003e55201a03150350040010a04a0341c0e5152245102100d0b4800031481c4500b4482904210b00c900c41c0841d03c452071200d000c1e007541007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557417850 1250 557416600 557416631
    0xe07020715050d02030c12090c01090302040b0a1703040801050c070f0b1f060c0309091526010f05040201020f15010603020f040305010f24060c060209060706060b03011701 75
    0x40c0e10540641e5121220984031280c424421140d81441048056540c1c0c00c016681512580c000716440048010260100d070b41d008005c1400d4074080016590f0101060458080000030b000418520381d106d441c0710f03400910110003100e4005c4c0c400302c00d4091600c0c0c43c500442c107401d460300201903011140f0300700048000210141c1503101c0385034100610080030380d0b03810b52440c00c00c1101c8140d40c1c41405003100c0021103d43c80203031024020710a50302d0300781c21903545481c801954032804c0c820200c0561404103104003c1052200011840c1340759400240c1c54005002a085400d20030b20038450b40d8030780f02080107558040218a12203032130b84008060400030205503480e01c0b08107000d00400c0640005d5103c201c4134000c030035030340916000300007048400c1084541000420000c02d20056015a44903414216495420484100c41c2d0390703158038240001a9942c40002d40c4807030720142e8071680a00420011650620178000903201e050109640c0c0e50502a200310201d140940702d14580e03040000000c1c9c0302d6031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557419100 1250 557417850 557417863
    0xc021f0209190524033c071403090a060207050a080d0c0f18051e090a020309071505090108060d05010c08040203101515140f0406030f0209100c06290301060e0702 71
    0x5203204205038080e091503050b45e000d07007456200400c8036244104505541020311b14240144946d444590700d462044904e064203000886100076542c00c4281c2e1000411441d4005080c101e200d0425592002d4917643c0f1000c1c0d54004c48524044542d039030806800a80d0003181204c0c03a8a0603041030f556402401c0c0802c44494401d000700341c083c1c2d1100c0841104c25a00d2003460314900c2008000707034070600c0c200311020000d4008841c40d08042c0b180441c00201c40c4044240762502901036a905490000031600640d11080060007450300030711401d0360703040800e0b400c0c4100c1d82511031640d2020001e0030640101480d1525880c204118503151414035441d213000f1041e04012076840410304402c44c001d0782c8059a510350218901e82c00601c2c00120003050403005002041503801c551410802900903150543c100d00624440b5600300c4082c0ca0034074502402080c01250443c80341c540031505e5a07a6000c0500d51032010203001d240101e090394290301d14030b02030040202a01d1102200d0005251840000f940c0300f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557420350 1250 557419100 557419111
    0x6041a151c050f1b190c060b060c03120709030f030e0a050a150c140102121015080c0c01060306020d060e0903070305030106080a1415090a0c021f020919052403 70
    0x404002c00d291322400a082519248114a0b45040080c90744000c058007500c039103502211203070b14101003165030340ba000042d201c8a01001000b113042100404031500d0100d800383c044d100344480c1c08000000280c218035802001ea02ca0364410344031612140510680002c140c01c041d02c10f41d0f0750201405440112010301e5010841890b0440340c0e07000c0c508040d14480340090050095500010340100d110030148000b6010b40500d48a0319071207603a43c1750003002628810301ca030700021406004200d0b1003c0d40c2c4013030168038000c00000240705540380d80781d10880e44180c002e00c1107281c03140c030700700800001c20319200d07130190032807020314a1f29103255401003240c44140106000d200d0058042845101d540c2d11102403e1004e041c0d000403814000ba0707645035681c08a40b054440c084080000300d50745803074002c0503000b14140e002000e030840380380c03250001d512540c003101100940c24440706c0e200303640b8902c8403044141001406101c2c2820312042c409003c0c00b0f94002c08401d0707500f000b01c2d20608144412a036021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557421600 1250 557420350 557420371
    0x3031d1002070c0e04051501080d0c02011d031e120c0d140c120316170f07211a03070b0a12020d0f05071206060806041a151c050f 57
    0xc6105240c41115030301c5a0300041100440d0404005c10800c00280060b070640030162070400b0380c0c0c1d1b1010f00658480b404a40c1c0c1000400f842050310055029206200c1c4032100248501241082c84012038603001100008000b00e1115100310026948107000c0a031703507100f1985555181102004c11582d032600c0701a00c2104110f40c10407000d00300c1c00c1e02d00a032f554501041c0d054401c10525881c003500039400603502644801c00b4049249001401807940032903412000104c4203090ba42ca15180310b0040e0005c1448080c081e070b5090307240a94620324032001d801090304000007122394200c015645006c0c286100b490180d0f00c00401444100c071001d044d5107900040b442c000c4511b420380d44191000e4000c44401c3c0819609100042030003040e1604000d208264507692150000016800c42080c0c400a10075800810005000b14825050a40045c0b400b188a07028940d5490b50010108503501780716562100200400720348411004080880343c0301e1003602010500550030070041c19290094090603007100d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557422850 1250 557421600 557421607
    0x2d0a0c0b070302040f0b0d060e0105030c010c1e03020610050114030c03040804090509030304170f040915150801171b040e0c041a031203160503041406070c03031d1002 73
    0x10184a03404490290144005e484212551001421401d40002011041c80c0341001800704010326000e01131412118028014046070341480e00548450f10040380594040200c0050300d03070302c0380030414520142071181c4d008041c58942160321804403101c90700080d04100380c01c0010f0f004100c02909594001066614417076a0b40c07994602032001e88140d80c8001c140c1d0b0300781000c01c551446d010000d1031113640104000d110075140e06d0008041c900c41c0c99181c2545c18018403041c0243d488581c000404070712806aa0422251a546886041c3d464500da0b0400140b419006128041030003c030b946141e98414010004002c140310401c80c0c081c80602d01a0140750384041c03100304401304001255030700c84041d00c1003200320624000300c0007450300401400d01902ca004d4070040c4074001407040300c1c4540107240040d07800f5014524115030031b40c0b015109071a050252030000c0c944030b5003070040c60f00600345900c072790074414003a160160540342e803000380d0349454013044a05141044042200080205030160050340d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557424100 1250 557422850 557422861
    0x11704080a20060109020306010206100302240403020402161e0b04080a17090115060903050304120c0b160b070305060d02040e030d021306110d05040506030a09020301022d0a0c0b 78
    0x7032041484000c2181c2d8460040009114102680107600842003a0309a801d540c0d1560a0800c0500040c48000d4000c1400300c3c02000d1154143c41c40380d8595103884a05182c02d50b250002403c2c0d801549444d410a03800c1c10603c170800c010396a2907001101d848000c1800c1003001d488280510000074401f03807542400240c0560620b00c54941610001d01e1400c10b010113040001d01c090090040320000444210300040c00b0aa1a005620000450358002e009519060801a4900356070b6260042240c0036a039500000c01d4110300003002c0d20316001c2a1506013128811f908028075000c2002d0202000c0c075150000307001c5a80c60b036261501010b80c0541d00400c110461024061451141205a070101480420204c0007801e03050b4100f0101e440590714400001c4a8041403502c4e8010000340c0c801003041040100803a087c4180a0751744544103800006007545550013003801c6ea071102d003041c81c403002e1094400c3d004c244a8a04000d200c81c200d4200c0c0d04081700700d0340240c012a4070040142008640100056 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557425350 1250 557424100 557424137
    0x10f030212090703022719060e1306050a1b0f050c070b03100806010b04090f0209060a05031f06172203170f150d050a0212030405011704080a 62
    0x1c40d0741645041400041c0b802035407094884056000882c03042c010640c11402241802c034001e1290100c0c260101079503216a000160a81804508048425140d44000901648941150341310703c6d84104507520010f100c0c90040100c80d03008060b60411031800d402e001100401d80303041205924682840c00250407034620035507007400b4060030302205108954022802001030809036004500c100610f04216480b0710400d80c480300c00340a21414039405220410628005402144003003d5402c8010b00c0c26109030089096544140c3c11000030400001c20301c414014801c81088098660102c1045034030306100380100010480c0341d00d0b00e076003643c0d0000301e030220394102c0c150100a5030078420440810500e14028100700124404c003080c000c15140010f449425400f00d6070311072055803072158000d608490400c5006000a841541c4501c06e9182520050b143c3c5c0c541e0001d26100e52001b191940d280c0300005040125513040003451400c0007040c8000120343e001071707822800260919507402e013000789441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557426600 1250 557425350 557425357
    0x40314010608010c0f050306180703090b130302120d090602040f080c0f0a170708030a021614130207051009110f0418080c0f240114010801031101020f010207150c1706010f0302 77
    0x3080e680004a00384440ca034bc059201b2a000f5104101e03000c06a5105510305100d40f411500150160b00300300d182448050650004151060b401000001c40304042e80340c0c0000ca81280d084032201e10348040c4284401d00e803c02c441503000c081151101680b117007a10102e40392002c50300c6013070201100000c100b240038009006200150040703008607a01d42d64070460080d034485590b17801143c17070201c00741d01050710841c44a031b000c0c0a101c050310990032801399408103402980020b4094a450003002140c507940c00d02c03400340c0100f40340108010010031408d81c00300146104c82100301ca2240385000c14900d000d501d01146d442c4901d4102050645801d56048203a05019a01e0501c6d0060f002c0c02c09884000b0345e2044c03441005c0c3c9070b10100410b007681c1300c54921100d400e4003241270340801c819000400008043c410540c501440c1071050780c81c2c400010300c5040c2642c00c0141304403541c2e81c020780081c41c844820301c1401d404031580e25003404400318104050008140c003814240c100102a003880c0100740c0241c046 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557427850 1250 557426600 557426629
    0xd1112070b0f07110a080d0c02060702120709050a02040f0b090d0206030403110106060c030e092707151b11010201180503030411011412100b040314010608010c0f050306 74
    0x6542e8030458450b120850794003a1000f01d03000c0c1c00081003d41641040c450030b0701074898000040c0010354260400307070707a03080100004076401001002100010b8a81d041000e001c04144401070201c1030812a02c00b054500062840e0582841800200440d28090786400300f1144107128090b42e88030008007080103490b0307006029401039000010310040560003c07003441c0500100c80200102900c4040031220143c01841c05000034142e03001c40c02c000d08d480f0388101d800032012400301080b444400c14210810002d48100010f5402c412410000c20040c4004185111034034506010350320120420034540020341300001d04000c03080c4200f80c2440c0d0017503205e003072010038244401d1950980341c0b40041c1e0b2544121000c0f55980c14030300701c0340c0b4554014142d10791080710700054507042c41c2804500c5d0240782e4008110148402130304100080803d8014000d0014500444001c4d0200c0c581012550075280f4541c0400c860742e2420b009410300030351100e1511100c0e002840c2c016901d0319a1000a58192104004e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557429100 1250 557427850 557427869
    0xe010e011826010b060f04090e1606030b010908150708070207050306010f17162309130317060303040e0903090a08010507031109301005060f0d111207 66
    0x14800b09220015200c0010881d00074841000c06005012103801200404035522009000034454030100340c120b2030041c1c1d41602280e00c1ca0b04090600c443c807201035072040c0c0100380e642c00c444501d1350384428070310050150728000304062506081c5145542a00401c5c941c2000302c15004252810310034010500203100007003c0302e40d1943c40e1944120918402d01c00d0035070007a8458034006487e40045600c00b80c50250b80030303200180c1d141c50301001540503803048001c04100c0003a070048072030359610281400b480d80404015200c10580c60060000d1000f40306800e06c118260302004069a000400c983c02e84822101801107500c031311400e549180503801e1170550001c80a03001050301d08055000900c2443c041d0b609000c2c0c076114030b261904501c5041a030640120824002c5000140e1a16481050b80308400783d01d07100d00103014041c0d041c100e002030b004010540700c1c020711210b45004403803140074200c200d544d403141200c0740d6180302c103e00d4a8800e050255001142103001208240700600060041c0d20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557430350 1250 557429100 557429129
    0xe01030507050406061b23010207060e0d0908190618060c1202091c1703151f051e04121112030715090609170c0105070e010e0118 57
    0x40e005807a5100c6000742400349240c20b2000498074490480c40e5540c11917046060304040c86900e42088424098030112440b0110082e03d1008410074030007010a1401414002481c200c002030032070800a20344d00312000c0108480c003d0090b680c0118500c0004500703190313409000b20081c9020006001d01c4600c03041c0c601c62141c1802c080c051107400c101a0442265502102c010041007154124040e4200d6280c0100c4801219000c041680030000011030290210022402070700c24070250715401200e01c2c00750034400000405144c00c003d08a01d401c8900c0c40382661090b9a82c1400400c0d9014100c2d0303941d040021520309101c8140d51604440142036800d00300c0b110640c1ca800c00c040392214041c440d60046002516035091000c002c020384180d140d200405a0001c00502c0c2200042c2c140d840e0103a0301e032070380c94000c01c000820520401c410402d00b04031280d280e42081c030204d0b0850700014400428809550f04064150b03030702a048420240c402d0030403a2248011a052031054050b94125036684540c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557431600 1250 557430350 557430353
    0x4150807080f06300f120a05070501021e04090606210b010905030d0c1106030105010c140c0406090c08070c050309041e020307181703090f0102010e060a0b0a0b07050c1203040e0103 79
    0x1600c0c40c1d00c4d401000001c41c0d41c1c1e0751000012a90712442030105600d1002c00340013040e069841007008041c101c0c010700015003041109036005100c03103000340d000260f005c40010702700203111203070203800000c1059040c500103c50071040140d04032048401803160455448800d0038040e0f02410071003028220103012074417580c080100c090040c0c007140000b80d07811180442c44c20810b2030014102d0f410f80f041a56004400e100c191b0340d8480b406e0550300b1411050181c0c981803070b965161440f80307100401c0000b07804504a015490082c001079070103491041000075990661010400002c00c807a90341c842601c0000342903461304074515400c41c02c01c00b482aa0380c000000e2051596000c80001d4030104100e0003001e91550b83d40503e0102501e414031280c2940084c00301079080e252580400e5a4100107000200350300c810030310000e061038011500780c02140d551b1040308110707040207540c0c1c4000d011030034150791030003c042c0c0b20302d6550601103215512130040d003c000781d4644001e105031001004101d40552903941c49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557432850 1250 557431600 557431669
    0xd121116050f062701092a080a050a0c0806060f060d02090402041202040c1b030c0f0f0c09051f12031704060209090a0612021003020c0d0504150807080f06 68
    0x4e01c5074641d80c640300c2c40031307080b05600188540700146074060030754610403511480004403101d00204841c82940c441400041d10102402040c100d2071040c0c000d00b02c9600b96140a41c1800d400b40c000c1405035010000300241600c420b00354002c10082181c2e0326071604000105c0c58064031a030865603400c280007050001d03009400f07510401281d44225024021400340700c0080b82c46118494032206030991040e0784101003401440c201414a00442001d10a1405916008040d40d42c0c1030003103c0c406540041000070348503a1007401e4124200096030140c45007503400c407980042c56402400c01c540550740c0391300c080502400152070407c12100d0503241a00d064142640290017020080c2e008050040004809090070310aa006503103a0041e01c85c440a8140c09001c02c50650156150501d6801c100042014030204507200034600540d8401e44c0d51414503d040c004001e43c0c001e40740601c4070000501940d0f0350800500ba503c00d80c00c074401c45c825a20600018040005c00c8030448100421481c6031004510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557434100 1250 557432850 557432881
    0x90302070504050c120406020a1b12090608010b070b090f0706050c07050604350601080703290708070e0d0b0105041802010f0c0218090d121116050f06 66
    0x310b40c02c000654a12061103c0d901c12080303214905228400001c001607603a41c0030388035108607850b200200f200c41d04400d41000036810010790b0848580007032a84078907448100031001c0c20151615a49652600018030181d024a62000340341d441200c1c00154002c008202552a803c0b140c4215104c3d10742e1510013407c95030203c0c20304001801000004245030400508a0781104d000c1c03114a90703100b80f1601c80304440a910901c0500100050350708080d447c4042000034042c003021000b03000b0962540ca4181c008040c02d1801416200120918116591254100550081c241d007000d611035911088201c40c0b04455800466100604004080620048103400b078140c41c03041d10100300084140842800b00c1d410b01c28002e0004405003206021f46204001006219202800444500c4020310058000d01022101c3c001103504c143d40040380590320405021080e600541e04220006d5011407013685841028074074683d86c458241290108501001882c2420f500c01e02564000d043c90300101c0d0480c01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557435350 1250 557434100 557434109
    0x6050907080714010509030c0406090507120b0a2106060b03010f1d0615130b03070f08090601050607020a1502010c1e080a0b1203120708160221090409030207 69
    0x415003202044001001075000195554514209001d14411004482641c007020445800d4080d5503c01c00c0661900d000c0e08003d0b003d2400f0101d1280b800c0d81004101000e07107800600bc8a0400ad20884d2644603644031320140c2d00300207010480c03c1600c0c984034001032841080100803e03d4014001600c00010018605036207000c0002e9060f03595a09005402080401024a80d1000710703010610500c1d08031034200021002120030350622a10082c603503000300e8944d10407104d00000104100c82d00c0c0c2c0c4a910200c005655041265a606105040c151b6421050103030a020300030004040c02555184210003006041e041c0c0001070000c00c02e040240686004105540030410258012141e40035401e0041c3c880ca199581e00152a0b4816030154058180c9501d090342003600383e1489884420140010020100b680c84541400d0410102c0107015610003000350001c2c803011103158100075400300d0390640c0003642d517000002038103002e1103801c0180324590086030f1062902d50180b0415402107201c60486 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557436600 1250 557435350 557435353
    0xc0c05190201090b0903030a0e0406091515031503060e03070803070e0109080123040f02090103050a0b1e01030803100f06021501091a010c030c0b0403030203040605070212180102150103060509 84
    0x1d41e607132440d080643c0101c001d0b00e030b803540041c0000d640c000e105007003070004d402004001040716661031489000703c0e4095848084181c911440520820000c12030107049800e0902c4e041100442e041d508044000d61400b00411040c0c5440361049030807030400649030703400d8105011690341e0806150107400d500307004001e503021803410034000609010600c1003600880150068003601b56004001d600301100003171080f68a040c803d60701c140503895104059010b584180001d2100c60980d04003c00b62120040c00ca0b410f659045080c40800e4480700c1d01b032411680c1c271540c0680c0305e0704d514440c40801d00a07504442c655a880b04000a0665070008040440a0715aa1003800d42d0b62507065801c26602d010229000d8680480500c4446512946048007a54000c0c64010b455001554500703a0b035200c1070b50141c00103500801880280900da110b01c54100c8031500042440100903021085603004403244140300e40c0d1601c00a540d107074004e001e0716100d0344040d082503006684030715168000713000a54402415 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557437850 1250 557436600 557436617
    0xa05010806331f022803020703030c030512040804060f030e0a03230a020303071202031e1b0f0c010e07030327170d0e031504060c0c05190201 62
    0x2501c1c000c0d80d2901180b9403a00701c80c040b51200040e64410300a00303459840d0030241e0500d400508039012080c04486032003650281a502001550004000e41c802c04484946007091080c000040d400241d4101180e5041c1001a1000002d080607260750043c640e048845001c108100410803110034010410b585c1291900c003400c0b034218004070121825002090300c181d0103d01c010300840d0049540804002c1b00100058034001d00c24256040b0390042c902510243e030012041c03002c2982c01204801300280710355021811807074418080c11042d800b5888607050014900049501d00c02c0d9001002d08065a031029079640f15441c140040f0075500c010040e0206500e41260540c85c03901c04a55401220703010356070001c010000740144421000242e8602d100259041e030000307542000000b54076441c9802a019228090b01144058801c078807a0320614400e0304406098010b2900c00800e40c1c4d04aa004000041c0850041c1c0040d9203030503481402800038840c100c0000820007441c48510081c43c400c1c2c0e5101d8a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557439100 1250 557437850 557437861
    0x210c1202070f0204020309010209060408160b030720120c0703020a0902040e010e15042f030714071e0c0311010807050706091704080f0f0706020a031b06050a05010806 73
    0x228010311000034030840c46a4000c02c00340c0307400d4001c0d40d000903404000500d880a1003000587d9a800fa5000c0c03641604007075407154036540e02007030f032000500c6400c0780d0518600d4a400d0051620454402d00107466086180001204108101c0011080d610b9200700303990f0100003280a9a032000c9120482c0300d074101400204030002d07503009680803514004680e0030349034201030911242020003482d100303e040b5080000c0c000d5a40c0d60141d80001d40311400030380d0403999603110108040c000f445001c0c4036007508205118826501981c48443e0b4036100e00c4050700d441c0305190440342150041b55440242c0f500102000c10310500e410504112441018050170031401d500c0150b50032001207c1440100740244404408240d05410008600e882111298038074552041a000c031030700b06400c044910b5010582c3c00840360010420024001c44080041c00d62906d072080082d034424031040300400300b240343d0070362907001424501d1a40d00198005001d000524140440300c004000c00d01c07504440744214000f00e003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557440350 1250 557439100 557439137
    0x105130803060d0f02030304180b0102070e0c0f0705030f0c16140f030a12030507030605031b0105130e0c090f060307080c0c070519080f0d120c210c 65
    0x40a855120315218210350324035080040d0700d21142029038515803050042001a90180004c1016010704c000b450b0040d003400011800b00c2c0c8030042a10b0641d4481c86c1c1c10b2100b4071101c4485a80140040761850780c03905d8020540300c050180810060051001080440054600c03d0207003090107800c904580703841d00c407501c0ea00d030411040e108030f50300c0414506101c016800d14650894920702d001e0b085464210b5240c1d0350003210038088030540c00003a910303011f0001140d8140540c000030a0110300074031003480d19140700140807a4002d0214180400094103403240804092100e00900c01e80960038224a46091511120f9001c004420b2154282691440c05880c05405903801a941907650352071039074810007103655035070011070b03241c0c4581301d1500000340955800580306106100001e1f0040d0507450700f048149032402468811525030808840000c0e0964890007943c0c0039110454007094a00700d400b420b48052801060046804881d03440b40d080c0782d00c10fa013020700d82c4202c036980c0100711310170b41c002d80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557441600 1250 557440350 557440381
    0x10140609040f09031107030c090c050f070308101418070c120804021305090d0f090b1803060a06051c0320030a0f020c0d0b0408040f030f031101110307211a030105 71
    0x4040c6230f2050001e0044507820b9000b00c03070740c00403801c01601c1d200c3c1d02140d2002c2038011142c21800109500c08200441c40903000b003070001d0072014009409084058001907020b540c80541c4100c04025100051186102d10b100840103a00540b0000c3c083e200d04000500b0030208075400d0707018100d5480c0c0e00d81001803601c42c0510a56400e0050800a480c100085550682e40d190440c04c1009d18200031940c803142078010160190000e081c0c113020f10201c401e060602c6c0d00100400d0103585401c0040006849840d032542030700302c00b5500250102006e03d03058078000030b904648503910341000c1c0034245501c8000020112020243c0300d180c03501550b00401c070381d44e00009004540002292180e08000351140951681252284c0d070315074106a01e078010344801082a0303100f680c800240600c3d0200385500039a9000400802c1d500034000048500440880e030300c8003618910810070b40f0390004004202912810403042c140da9410304c0a85142c411000341403001484a0380700b5440c0c81d0100d0040c2070145144c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557442850 1250 557441600 557441603
    0x7140d0c0c0e040501060305070906052d010c0c090203361207140d020703020909011802060c010b03010905030d0b011701060e030f15070e01050310140609040f0903110703 75
    0x1c00304505116031035440300d40241084402d507403182004400580c0c00d11030400901008040040d0305032401d0708000180060140f004c500002c00040c0941c940c80094040003011002e0074581e9201840b40b0304210074165582c09001c5440c4040184400008564800c450b54078621600c03204c85481551a503020a061203404070050340005090a5105038a902800c0214045c540500300c0701a01507043d82040c3c0011a0100180c000c0c2c1c10a10451a000c03604681200c1004000c0184880ca401100309203417000030081c0c03041c0e074040390804109009400051003c5005002803102035514545036589400040d50010040d0401e14403a400f94810318030100b43c4609441e41130501d0346041016200c02c2417100d40781e07805000d60304004c20495420032640c1840c50300d2260300c646038600264018140840c407032446040001c00c0041c09100c40b0b258201109aa0450612030105041d01000074803a110781d100300754016051494500003c00035601150f4558080d0700c1d810601402c4822194850415000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557444100 1250 557442850 557442863
    0x11806050d1b360f030201080f010b071e080d0b210c1e180f0f0103050a0209101e0e0603010b06070b09030d09111513060311040b07140d0c 61
    0x1080c080ca40000b0441800c025220000841c080071801603845544604e4110004221600808008550748200050340c08080800145c2055040648402040c030880700040c060640c9240f03a0380000e00101c19501c0d88560140c405a500d0401705d0382c2e4000b402e040e00740ca910402c421041581000e40ca0f101068060078100060051640540c04114850b1214600100300d0a121a0301d04220344601c020001c0942540000c1111440c00c018500d91641c3c00500301000d03480f121004000140c0001a584032680d81261200d203582d1f1035624543d41000c1c2030340400032640c00c1102c0d190281080d1762250080d00da440d203041e0b580d90399042c10315099607070320031856402240400140e03011038004da40c80f64014220000b40e07407619a041100e001031b5000c1d00b109032400304014000046514108140701c11600304400410304004101e0f80701c040c90122031140e03405045e02c40042074040307480d100403100a0885408110f4480300745040400c041d40041103800e4a0384106034246540318040c5008801c42940b240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557445350 1250 557444100 557444117
    0x90a02030d3b0d050303040c0609031a07031e0b2403010e0c0d05191a0109090f0603051002041a0c0601050d0f0c090e190b010e0402011806050d1b 64
    0x360280440822480e0448003040503000c000310b07560b24040481541800782d4015a22030500d8103001d0f9900c600380d840503090207009102040060500000640c544e003000315003e4060356500010b5026001d01c948010b41c80490603080030503500a40d01c002075600060711441c0505441c0e80c0441004100380352a43c49602d030607c01042500354541505030f102c0c03295640b9500703080043c00741c1001c0c1c1d001607843c00503036541c010410124a14511440006a00401201241c030036402e0000c0e0507401e05010b2408165100e8409003c841c809400400c002d603404800c40d5802c080c01a0382800a42190040889001046018003d003060050941d00001e80d03010240ca603a900e001e00301314100040e03c1d021101c20112483c041c009c545000b80d05801001c808001050b0303000502d10081c100075a140503201100304100880300807410107502d481c1550a41035050025448600050320b207008444195014000403101c08220f540c2d2000c060b0003a500301c92010f02c07619110300c00340740c042075604589034001400c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557446600 1250 557445350 557445407
    0x50a03240903050c0d3621060b0103020306090a0f110301031208010b0c0c1e060c060106080105060a090509150a060908060a02040e0a110c01020a02071a0301081c090905090a02030d 79
    0x41000049903400c411983c0b141b07940d20001c0102c0e681c91600c00c024030341c0a2660001c00d10056006c2e005011030246011072442c0341c40000a00340320000b4140310000c40c0c0d40c0c0701d01c1f400700841c4d9018541b036451400c0101d44a40e902d1814000517001004098005007270340000045041c85407094820880a00b8043c00c0c0f484007100600101910448106030040b218021580d216200c0354020840d00081e44050171043d030500c1c4015210f410183c0c00140610400c1041c081300b580d10080000c107681e030454400101c2d444104a88680300c011101c8140d020180010008415800640340f2044660030350030380340070303590350f091440032401644158004600f03208009081c4500c142e00c1410319110014410741000e4041c4512801c98100907501009a84004810720504102c910801400c4411600d401d00d158100755506072140c0c5400ea2841c860749590a502c200c45004a01340d002420480ba4204550301e00003405c603544202182c4181d01070301405104a5036184100070f80c03c0e2045070b40349001c1041c44903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557447850 1250 557446600 557446667
    0x16080606030406020f0d0501090c030606020c010e06070503040e071d180403080703090818190b071202151e0604090c060c0807050f0a1a01050a03240903050c0d 70
    0x41805c1007107000c400c0080900607005c5110391406070a1405000481d04004107000c2c1c1222501d81201065610991200c061aa800742c10819081015201103807104168646545580540d801010a40c0c4040e410010200d0b400140d40008042e41c510f06902c4417541002d00c8058090103041d00c1940600c81c001601190040175407a4008802d4540000c10310543d4440400f182c0000801c2c0c0801c001403800c528061403d07000c284402080141840066440c1503200300c2c280c450200014243c4025a44c2f601c4881c0c02403140c40c007266200001c1550601d00608070001c01c1040c028510220000c00300412881e052a03c103a40c9003a07401270f0041e008900300f03502510086024201200c0d107020400c010400110300780814100c0e014042c004024003070303041c0b4140c040301e28038819000014114800410203039503007480702c00032a038002204052800704150444100700d40c8004000c141810308408900701079001000342411101c2d0700030340f510034100000484181c0c440c0d407c10403a030b082000d03505103030503007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557449100 1250 557447850 557447857
    0xb190c0c0803040f02031501080d02030408070608060303070b09010902040606020307031d030a0602040f080d02150a1512030207090b0105090a05131401090f0f0b09070c110a0308031608060603040602 87
    0x5000c404e50f18605a40002d103441c01c20403003c2c407150450001040100c07410060642c45c0d0200c1e0000c1c5003064104001d4030740d43c100038441c940c104207505010070101e46081c07003180c0032a9008641050356241c040e04241c0a0012807904901903031409100240f514404000d40342c2450741503440200000c02d028210b209102e41c00e020950500400d0310b4880058200c1c40100021310300d540307910301941d1034118540d0400c44685401400d44d007101c40e5000c541d80503043d01e1544a6126000040c1c603140b07480d0f40d1030740380d0ba082d0011103044404907103200503d07400081e2802140c3c0d5551050042044c400011551401240f90503074100214883c1071106242420b1038445489007100002614909821500102602a4021415540d82e50001d581980c420700404204100200701404500c8142000c11814040144214100154030251004021042c400e41520380e60050440503ca07451f801c0403411a4003d440f6891340350b0041c800028002e0141d000240306601c004c14490449d500c0c0c0d01c0b0b81d0080d50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557450350 1250 557449100 557449103
    0x315040e01180c090605030f03030a2408010b090a020903190f06091a060406150503070908010c090618050102070330080a0e0c0603070e0609030106030b190c0c080304 73
    0x152580c601c0b600d4207290030140000c0d18040c50f00c0301080340c9010119030440e142c540106000350007215982c801244008100c07500003022401c0000c00080303440759800840b203008101c250b0035403a07800001301a01d05400154914a0484650b080c54031501d59040c01c03445804a501d800d80c102a01002251000b1a181364500d40101010650450140c0d1910110b41845008036030103843d800380d081e03218100e0603005270700c120f00341c40420019041c4042e8a08072050300f000760081110000000d620684140c03190001012404000e000907000c207000a8101d45041c045c5034001241c0c40d43c61070141448048140859006802070402181940c4800f881034120031980b6090004000040b01c10690740842c42c021183c2959071041141801c00c1c0d5202650318141c2020300c3c613070200c900c8803401c1d51100222a04600c10b400c0503000094010040340c01400b80c0111613a15510b0481c0c00000d21403071586641c4141c03204070107402182030080f11241221984060100000c500304011000a07881c44002e6803c00e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557451600 1250 557450350 557450353
    0xc041d061509010c0c0909120c0528020a08010605120102180126010f050907020a051c09080328050a02030403080d060b1603121109040903140a0905010906050315040e 73
    0x224555110380c201134500d613201010f80e5a942e00250705004003c0f0004548230407a18081032600380c10341f51281c0c0d811011599441d1150340c40d11801c990b4440c81100355649501420451074507a9032410640206003500c2098080d0b022551264030800040c800c603020400b044000401e071013101e50046500d500b4003585680d03002c1507669140b00c03c590303d20b50b0b00e00804a41c68904007440c189070611100d120040c22203400d540c4042070308000075001240070102c8170b041c108800c03013075403919008441070080741c1d102c13150724000061143e8000f07004807000000300c0c0784604020705910401604440500c244141080180c100384018400550248002c1000300b0508902003501915889a440c6991040741000a0282c807400c001c400c05801c5184049000500c080070005002c050007401c075244a401c0d655072186641d000001c04060103188220100050071304096103507052090080c103403501ca401101d0101e015114001041403240c0200c910983d10085564180d804240900001d17001149006c0401e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557452850 1250 557451600 557451617
    0x30c0a17070513050702101a010807120911030d020d050d0f06170c0a09020c0a060f090b040516090606090314070513150e010b070b09070803030c041d06150901 70
    0x480d41c5007143c1014002d10307040005040e041400010307280521803414010a941002c100b180103050000c00e61103090f200f0f0070700411658610400312200e000d030b010f141d80e45902e00040a420b02c440900340f400145016000c50b03141e02e448503401d81c0c0d5a1102c0000d6000034038100010b42603113045411009d4210001d2002243d1f003515009408030101c840400071034140d0011540418034600041e000f0b00504039140d007185000300980034280c031107048410180250341c41d103aa2008009082d440341c00019000300f071140a5040a01d01b940c6c071031540c080400b0b0280072118000ca5890210710a400c2151010303140c0c040304610b599105601c1244101c510603860041a00c009200d03210384903000b80350110031b1030009a0302104d01940742080d440f41c1049030404104001807000c41c0040c0c0c00c4032945508034505486954458003424a86140f5804c140401e000c08401c0c45100c2c038008010388241c80940e039071700048060b110251150b4203401c44051303a12604001038100d03c2089031000b401204410301d4410794 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557454100 1250 557452850 557452859
    0x2a01020703030209040c0c0b07180504060b0c06100e150303190305010f0b18010302070c08070b070b07030c12150806010b04030219030b04020402030720070501080105030c0a1707 78
    0x2260006241980400c0d00000c20380400e14081c42200605101d42c10001c0741d44135140c84640c0010740c010708550a001809a4405400c0402003001c0001c0400400500506494065080840e0070400505040e0310820020500d000c140c01c2d4000b099400e1f8400c000c400c1e40e02c6d81400b0022600e0f5801c0c0303d4142c0810440341814600c080200f400201182d2008100741d450300100954040007580305048031101031100608240c0e0544441d00c00794400d00e8050385820705810000c4c0710038000d034415181c903c074031031b40050503d048102800600c1d004d040c05416907910f910095090b28030b012010030000703450a143d481000881c0e0b002e810180898030717018000c180c981d9005c034a000820b1700300c0c180704075000c1420021440c040c66030083c0c9410004944110501d147d5540e409040d02400080c812600400028130a5105000144065040c42951603414a82c0c0f00c000f81c03034908500805000440c0180082841e080020b802581800003802d80c80030b0030320745040a0500c0e131071090f1090140c060f1420018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557455350 1250 557454100 557454103
    0x1006051503150d300c051b031f05370c0e100c0c0611030f070302010b0907120606090b07020103020d0e060408220b0403080c01141f050301020f2a 64
    0x1207464561040c0707400c401c2403042a1000c0441c4900c2e4602c20031a24040c5c04d000500049030104880412103004403484030038100007401d1455818003003115500211080100c00c0680d0049401910b0342c0d0144810300304004240c1a000e00c1c070001c013a080c0c000b030080c5500d0402c040c3e4403201410700640b505450300c0040000152842d8a039170306240019010140780740501c030080d00444010a158105003c81c020425041e544070302502e002c510a059020030450300b814000e41102d030b0741d11002000c038000d40c41e2212002d00f81201130350145080f42d18011010800364010034041054a030b0300381c94941001e080b40e0045001e54010310040b8882034076080c08182401041102a00451003984019181d1181030300e84030504814414038124490394a00c10000c80303c1c10f1044a082c0c2e9001a5210741c1d038038150b13000a014004441400c01100401d904002c030388010829809010803e252104404650398030802d420703406140741e84140803104000030b181001ca202c41c602400c102101d181c07441c0181004500707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557456600 1250 557455350 557455373
    0x302090c1c020d060806090c0109050d0609081612030606120b060c0114061804030c02060706290f03010213211b170637020c1006051503150d 62
    0x100301c02e41358401400851000d00c190342d0701c0004480200b002100e6640020300f40059442410b02640115000105100054200c81c404070f4102c4000da6803040b0200700c60f01c440c05005000e0b109030340b6080528014034400d0181c03208840b010358425650b034021310030741c60081141c04500c540c031040c01c201e4aa0414403c0c02214412042c20b00075049515001c02480881d0035440c00d12148000c001c000c200c0000d81009442c10040d40688405440e82c8007860070600516110689a2401c0300d9505100701854080c41c0790150594240c90f050088540d0741c06060a0740100c07080c1241081c01c0c04414001c0714151102c0202107900e5032040c0d00000420f4076111a481c1004240d01c3d1103010952003484400c589190f00da150b2044078004080d18500441c4500d50143e45051220105071503486100490b510b0800743e0141506000d821503865a172020300070b0352005e01290131810b180c00c0c481c00241c14a004400c1300c580d045440803c40c95a986c07086010f0782000180007aa81c03000d031240249000c1400c40604 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557457850 1250 557456600 557456617
    0x20c0616080f040f110f28080c090612070b030109090b06010509060304030f180e100e041a0c0d060306200c0c010c1e03020303150303040302090c1c02 66
    0x2800442226100146005401445420b10701da00100b4000041c010809601c2e802c2d420010310110b4114403000030380081e46040301245d00c5443c014420071007a94407400c0307098211101b51004d90107036442440e00d448003600010b16600c601c040000031084d04003030410b8880b4807902c60540b1a00c948454201c1c2c02030308203030000c41c0c00c2a56130341880200b100548504d0b030414000d0802c071b410320050000164051000901c000c04010001401925060141320305141012141842e4030204c6d40710750140c2e500c044100e9180410780181140083c100c00d0b0300c81614000c5801c0f1508120441040c0e40d01404404003802050300e0301e100704003a1600311194800c03100a103105081c003140f40c1050401d0804040c450441c0904079030b104001901c00c4420000d03000340396280c00e017044910f15445041c00c01c0c03120308100030300216441c00c02100381010380c08001180b00311401d40c01c4901c103000f81001c0c142d030381c0034502009420010390300c085050110448064074910303482c601d03061a442c03900c914503002ea0300710307425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557459100 1250 557457850 557457871
    0x60f04030804082109060304081e0307050d050f06010519090e04110102010b010201051014010306170303011e0303020709020d091202070918050c060319062403090b01150201020c06 79
    0x1e9050a1101581000404d1192802e100d05040d0703002c00281640c440a0001040700a001590400700f02003401e0f00c0440020300e90903952a0720301603034003a0180d40910f042510a514150024003007048121070795000b900182d5519041a0f04503005c02950130790761940e50b00b4410b132860001050890000098411480b480c40050b40c600e142e4006401d403201c1b00341c81810359040000300403020415003038100071030b52540c0e01070504496203001600141441d4121a615080400503050071840000045040710b0702ca03001301041040c1e515220880070aa8040180140c0020030200705189568000e00401100e0f9400020601c00d19550f1a1b03c00c040d80381c900015801a8604100a00045c800d21042c0181e0f00d80c1000502d0540c1c0c2d80c0e946400c25603a845200700c0c004804980b00b0942c508003c15120b142c940304001c0603441e01500310041280d480b00050103013843c04411003071842400342380306040c0c0c4000c180d05030b80d00300600000f80c480395203195000c6650901a00818040c10888180210110746 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557460350 1250 557459100 557459113
    0x402121207020a06210b01050706050109021315082703070f03020609011e02071b14040b120a0f051603031d03030c03120601091203020609060f070e060f0403080408 72
    0x4144488039683e84e10800c10322401d03401d4100b500c100421044001c0103052000644c2c80007100c0103031a030303000740c1502034903c52270440040f078040040da000b400b1080583c14003a20f0a0b50301d0940e45030350922840890f0014100001052008d0316001c000c0c0c64001c5400480c03910360003000c19451454021903001e80b4071000912803203007856014490b0540100c0c1a0000344810005d6050140403480700c00c4041e00e0706a40058644184680c0710410700015108030710180c20982e0b510221400c0c0400c0520b09441186007180f1044245030480600300051400c901030583c02420f5143c3c55411064a101075856001c0d92041c003d904c140562610003951181d00c0d00020743c1869030084a585500d6004213010345c0c13080211503045100003055842c4842e1103441120903665502c01220006055070021241d0b442e16983c5508268021490a120350300c00421208690346549160015900a0b105080802c103941d1003480c2070b041040007010405c6540e280245025034a03070b601e995a9105600c548410381204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 557461600 1250 557460350 557460353
    0x4020d0b06060d0e0c04201c020408030406090603230613060305030a0c14160e0901020708160b0619140f0d0501090515160309030c0507030303052a0904050402121207 73
    0x905c55001c80118140c0014424136824584a0b407078442c40d0005ca0300700502c0465281c031500708c4c0c0c0468000e44500800d81e23031101c0d41d4001c09003450006010300400709042c00b50110560070190118030504410401c07500d540d1300e0b24003d00049400310403200741c0c050f880e224040085541003004101400c11035550410011a40c2084200030355412409510b035006071b400401b0440042138402d05541c4040c0080405869003c00709009104000c80103003070110101d8080603c50300070803409000c47c0030303c4e1008540e507261010410b840421114041c1044a918400c0c8554134a16043c083c030328002800c002d030098200310004000040411044842e61344942268007003000038071070b6210003614070220b00800e080902c50203610084c400807c4042554031041941418402c240c1900d1554004054820341622420010042d100031607400d00e260002e440c0d2000c01c508207403155051100c3e200300711810300c102c000400000e07250142090b40d01000540d14400c0842c420305c0240f030180812403000d5920100e0303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 557462850 1250 557461600 557461609
    0x2a070608100515030f060a0f060309060c0e0102121e07211d0d030c060e10050105060739090b030d090302030d08070207081b150304020d0b06060d0e0c 66
    0x2d03004180038010003030019460b2910f05095a07004502c184036401d15641c0d08000c160451655804450810342c030000000d1095014bd00c00302000380105410300c0041d248050640304c02021404090061340564101d0014198180c041d02c80b084c0352403452a0502200c440f100c00350303000030400744c90354480c80100500c05000044c1c480d0b0411240e08040c00030a4000030122102020603140381c1c0621170840c480781c101407080d00030500d00c0d039022004000060315040019619013940259500b21480d10001040c3c3c0d01d045c42c184c07410650701030301c118500d402d5290500c80341251400f51440d0824000c031400c80b4950281c04500c054403102500040c40d100d04070405240c25086031803a010311582c1729050000d40c50110b003c100030210b40c180320b2079546491070101d00d0600a41c0c0b22030403d001d13000c00000344403040c08500303900140c1103808182111141c100544207100555000354091602031500e40020441c1c0c03003640e4001c0004109504002c0781e055450103460341495945507981001030b0321101e0380790 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 557464100 1250 557462850 557462881
    0x10c030f051501050d0c031404051b060903100f02091c050c0a120201230a0903050c03070b0909071101110301090f1505040e0106050406060c0302212a070608 69
    0xc040b5111280c0080c00512a4441c030080003600c441075480940e000383c102007403501004410140c4c43c50f080c1005c3d40c481a11010b08603402000036102c504a113071500035100d40380302c01000b13004604082602c3c0c40c02801000000c0c00503917024016205150742d2100032003603540394500e9944505440d843c00608000e003082c20188610030000c0148008100480c415510a40c203080c000c00c3d103803141c1c1d07182c0b4650418407802c83c0c108000146010035143d01403d003504a074450705c01c480400c4010003c26032200482c0c010720700c403010240080d59040c83c3c11700fa03140e00302e0300754140010860744450070399083d2000070035543c400c000e000004002008103842425070010000c202080300071500c042902c100b125a100f954030440c1c5800820808010039800304009000c02002040b10310b43e1140007a0010804003020b0300580280720304540b510300b044407141c01064981325080d143c4144868624030350086845082420005130340c0e42d24008104100c0900609002c1c0c442d60360714a0103440141442c0c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 557465350 1250 557464100 557464111
    0xa120206010806041101030b061b0705040e010209030307030e1306150f03020a0e01080c120a090611070f03120f021602190501091205191103070e0c0d0e0f010c030f05 73
    0x3441001084003084480c5c03140d8003c04030074038020401000c1c03103000907418010081800c40700801d4400740c50203800700007041801c4175030641e028004801e8079440725080340941e083c0560540c0040181c0c4000910815129054500c010b0480c10050340c007030554803c0700d445400580032190a92100348000d5003043e941d64000315145403c0d4540243c1090003400d9409034018103050203142d1012070000301c1c60034240d96455171400c2c1e48c03070304c0307482c0c81c3c07003403001604103040140c0d0030302e00d007100c1e203100006028201c411154011003150303a00b500726542140c806403441035800d00140d603160700e0300c1200c0b111b000074203040d5001c0110120600c0240100b0018070300c0e0211281c00707030405170030801080c0d030404103103400c43e03244250006002c81c039410580e08100e00300900d240496205580304c0308221104840000c1000c098044400c2c954903004220503002058540e40c441c070200313004400d403211654001400e1203101200ba0346090061035900c900f580c4d440030b000b401207522542251040e00f2503100e4294000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 557466600 1250 557465350 557465353
    0x30708090c0619030e0708030a17010603110a0f050d0e0c130e1005040f0204060f091104060c0807020a0e0112150605010c1205190309051501060f200a1202060108 71
    0x1000c4201d6449030f98001010701496110005100803003018000030000b0812441942d964201c1c0c030100419180c00b0b0001d50402c11408400422000d02c28811030101748903542e075035840c12070382d080c096507528401d60500040204c00c00854085070700b00d014074403145044070001d201c110042000c104a0240b0b40306805030b0b032072420724544d8a03c04c0016000349074012000b000605a00c2c1c508103444140361240c00a50020b0804c03d001401701400c0260b042100d0b2021010403558400001500c414402d5101c3c0e040003810341101c10003c5003080c80100211440203110001c0305e503803a8441030b0121006d80c044108846c0b1010b800b03051000d030f401108900290f0100400001d410030001070440c2c02d54107030160109000c400b00d07141480c0900e04848131800c4131003900175221803007c401405000e040000300e502c1d0080d0349900c501c8044403400581640c8050302c443c1410656500110f404800c1c2480403103046080448001c5460414000708203200d000d01260707003016140c000c1c0a0324000060340070309940e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 557467850 1250 557466600 557466607
    0x3020306060904020901050d1a390d02090f150316080f13020d05100203011406030709060809010204050604030f050f070e0106180510120e0705151e030708090c06 71
    0x685d5160703856410344c0c004549031b1806036201d0425405118400c86001d55154010b0140031b50040f00c4240da4083c084401001c0c02c0b80c10555000300c0307094018245503484180306100f8401e0341c411640181204100103860f68540381100700c001029690750b010301e81e0b1224000020301000b91820345120610019600340b1703407041c1c10400d0b1740520b4818010992030007064a101220115514806841461508007088070b0300100e4182d0001c000358428811b202c12015030800d1307503109003000c4054070311030340503a01c40004161030f0000544606100802100f2103544c20000824140d4030100030307001550007032103030003c1d038001e9103051490601e402450740e000754440c65040205002d00c04805040d6001864100001d040c4102480500c410f20380151f58407100301d204501c05240e01503980503c4040c014000d22603400041c607031a88844042c082c43d03402c1505c9070310300410381c5403410051034841819041e00d07110740700020001da8950019201200020030601c140242048100310701c001c8400100c41e030350328 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 557469100 1250 557467850 557467853
    0x12115170c090406110c0d0806041a0409020a0503010609150e1b071b080f12040b16020d08031e0a02033313020403140d20190b0103020306060904 64
    0x95500c0020701080c425125080003400700400d5421100e105101480071548640452440986882d85604503100042461001030547e01d000d0142c000300718000e10717280516040c840240b1025000e00305003a40c009038200000140c6440074850080288080d1030001210102c140030200d20884d51b9004a40904104003405907241401101c194111000b004042d84d41540b0f00e40481001000002e40305682d0b4070100c0040c11520102d1150f081801d2401030341c0000001143d1031049000c1e0340191902c42c0302c00e02102082080b41c1452001c940c0c0000c000804408450790342181c940c0c821038032252034402410844804180c1d614041e500425175070300940c1107207419603524108105182c1c000c0006030803000c540707441110095840760104405440c900c100c03829800490081d500c80d21040300c40c8604451029030343c507404a40440403149a64405400390441d02c2c400a00c11400055500f80b070181c0074100111070800003000d51800c1c8070f64205142d03580755004041c140600104404d0041880500302300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 557470350 1250 557469100 557469103
    0xa0c050f070609170705101419020721020d0f230c0601030b2706011e0902030a150e0f04080a020c0301020c01150b0c0304030b0601211517 61
    0x10440d00640380e0240d1030740010305100d0b0250081030f40c00f5100a6900501e811540400700c01040703942d00610460b00b0b0301102c145a0411940e015901c07424415a680116030346400049907402a041d000343d015050441c50348850580d546546031860448500307461420701c454040c8000c6200c18264200445a200340d103001800d14016185100740d205010040740c0400c2e813089042c0e541f03c3e26401e089440544c0c4a1800480041e403d48201510400540d660144848540c907889000c184000c00b4040236482c0286075002d41c2007410060300c400c94001804900500c2c141b014504c6010740e8800801d10854481d005d0022010b00c0c0c001c8940149503004105043c0e0781c4020440c0c100e43d002600c00d540e03524103c003c81c188442e90241d15490b500018801f0700002d030540010004000803501d261a059496022900c103104a201c3c0030216041171000300045021090403580c4068181030802801d00c2c00c5065008845020b504510000d035100c0d800e01d00b592040800d00040c0910030010580c070350100704801d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 557471600 1250 557470350 557470357
    0xc0a061409152106040e030412022404180b030c130e01090b0901050915070507050c0a0801090c0522110702210f030313030309030207031b0503060a0c05 67
    0x1149052400288140030762103000c0071820320071000402c40d48540c1000c1c114802c40300002c641d000404003001c04201980740512034034405129810003145050706c1c00d0002d40c070644461005a9001e6a1b02a6400060b00c202c90032420162130944400d5649050402c010084d488004012401d20701d00030300d80031180c500181d0070801c00030448070300100c52003c1070020054007150a038101d055081c0140c3d0010054042030381405440302400902c07541d40c806944542c4e88116050815840350078202107603240c0e004000401d4000d0107001501c2c0007e0204d80820074450305580080f2041c0e6503203000c0803d104846032048081d0038200c481c152030320281c02100b1208224821102c1d0710607a50381c40c200d8201d0844c01182d411903805040390710000681003000c088484a070310010703014001c01c002c607541403802008803032040c03075441d941156803146510220024042c0c804101c06502c00c1000100120b000300f003480080441909211103210300701428507080c203102070603200c4a82e00f8000400c0c50540c0190a5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 557472850 1250 557471600 557471627
    0x100e240715061d45010203060907120e070b0a110f1e0c040e01090b01090203070c060e10050c040f0b160b070207031a15061e0a030b12070501020c0a06 66
    0x10452a40b00d4400306590302880303a041d104050b281310b0507412540d4011200b400000112450002c0c10420800102c0c03c1c3d01c02243c12580c0125007c00280d01c1d607000c3c2601585582a01a001521403d03810300c0700d00d000f8060700518106100441c2c2c5103859035120030800e50080294026006000c9071400c90f070f645100d0f03018203280028444004a40b80b080401001d401d02c00c0091060010a901411850091905840030344075628800d0011a01c00355900071640038003400d0381c40f1030482000f0b86031600103103080e00e1251400d005852802c2100c2580d801070501800920302495511403603e18011039920070380e803101ca8860024440211058060b069403907165811130704082a40d946c04004a01303280c45500007c000ca174206295001080c0c5200800e0710600c801509084200400000c10215008181e400105190724011b020111154040170700749446042c1001301c1c014005400003007400c655492880001e40c0007240030440c1d0740e07040003200020001903d100045509141c001800001811f00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 557474100 1250 557472850 557472899
    0x6090c260703060230162109060204030f11040b040c02060f06010912060e0c0409080d0b060d11030406140601090603090f080304141605100e24071506 66
    0x21541c040c52501c0204010300032031445c0b25020903541d4103528400d070206076103021000b01d0000d03ca0300018001c8510101c03451052882031049507207000b00001400d500c90b02110015024840003001481b07003001441c0740d0f446080c42842c80c81c40081417200b103503900c111503031160f42000504240150045a01500b080080c0b001030119a14100145c6001c03ea80c0c5c09000c0d00b90410041c4d009000031fa03480311320cd50b200e080a444507c0d2071002000140d941c81c04000d840e0040401c4904092140342c0e0102901090180c8400d06080d24100d20b5000c82c0c01142d65040b40398000410482040b68901c1845004900303800401103c1c20072800003484c00e0010302518081c1036807581500c00388001c2403400b105c090341c0318200c00c0d07403440c06184c0014211184d13810b0740344900c19409182c3c4422114086041031b40c1015040c0d51000403151011a0440501480242c2006000340c0f240072031110401049800034168030416540e0002d8034010f098034542401a0001600d499020700c0401d402d885983d0703003107480c0c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 557475350 1250 557474100 557474107
    0xc040308031803030106050d050a051905070212040f03050c0907050304020d05120a0302070b060109051e0423060a0b130902030411090702071e030b0609070c06090c2607030602 77
    0x3002c18440322000300c0d840b5a220200000a1560b4032100800211010344010300a980b0fa003011401a5041994814100d0369140d0805450706250b03840140c1c89601032040320328010142c0e003038481650050f0405a0411070200301402408001c01030701d5003044d42512040c01c1440c002d23000401e54000944000d200c0d280b100c40c49010311000b0040b4260002c9001c00301c5644000340640a402580000e40840d04c206401c40000c4030b031343c0140c00c224100d0700e0251504008810310110039100b10340f88080a035002da075842c0d610389030391a2312461502556181da80da04e0305041c82000c00114040c00d500c00c0081c0344040109128991890b44200300300c0e40d5a02d00982c0304d4555180001c0c94004a0304850382000d00d07407040000301d40d40003c0560407207014200c0c0019003a00d00c0700410041e8240d00001d003000c0040004030b408c6060044000b80d12408504c1c0c492411440e03980c9034021b403034150758142c80502c0c0002091290490400d080004140c1403200003514070700b4001d0040d202e0744144000b4000d1607012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 557476600 1250 557475350 557475361
    0xf121209151707030b01141e030115031409070e071422080c09060d0f02030f010606030f0902030a0f060b060d1a030109030c1202010207140307050d0302030c04030803 73
    0x220000e002415001c80c400080410822008210104a40105205141d482c0100b07442c2030080c41621081841170f922032808050381401c5104503409111509000240d03c020030084401c1d440c0654043e040100350f00800780d000ba4001015901d004003100005018241801030b40c000000d03281e011660303015400c1d4000e9661002c15580e0b003403c03641071802c4807000a82ea0024400c880081003005410142200c0c1d0300d40c450894071381d11203050700915004444400455014680124400c01d010311600c880042c6012079804681404801e0b62529071503916080248003c51b003600451900c01d01c407078404c00c580a00742c1c001a0780c4042c41c0c080034080045550512082c00000e410004201c90007500700ae9076482c504031044c0003410010b103202e04d0078109400c0001d840c50b043c020004201d400d0341c0c035100a03094580b9030a00d841801c000c0a01599806c010f0f200004940c031a80d81c0a002000c805140c803903501c0c0c10464209030031680d40004052040081108400003002520f007542e80010140b600c0c0daa07013 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 557477850 1250 557476600 557476607
    0xc071d011215020d090b070302031b090a050d15180305030a0218060f121e010b25060605030d0f020303070c020102010f0603060203061c0206030106260103080a090f1212 74
    0x41c0c0c9100c4001500001340c480c140000394100c40406441201202a0b9903a8520202e0480c082038510308250f14940d8440440c00c140310020b80b020450042042c06000e40c1c50b00050003040608404035811482000c0a213150215032103100c00c0741d10070001e4091070508c0b40c1c0e0001c241c1c2c070004184a500781d601107a00e090b505c1038400060408600904883d940b0403200300300f80c1850b000340a464101e001800c00042e00d8040c4102c4001c03c2c0e40e03031078880c0c0003164240155031106800c0500e210200e81c50ba040440c0c01141040024606c00f401030f080001c0b0541444181340c10400404468024842d0382800e81c0b00103940042201d5100e00301d442e0100c0d54424610040303000d0440280c00c40012030514001105000941e401540984001c803880202c00f0030070078180541001041e0013952016092004001d1507000b00290800501540079070385044061010580b2030900a800075038440c030300414004013050300100b8003805801d071f2001180c0341503c1c2840c7c0c94990004a40c000700340d41340e000c1500b082c2e04d02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 557479100 1250 557477850 557477873
    0x10150b040302010e1225260a06020708120c0a0801210308100509090138040b0a0302211b03120708120c09030106050105070b040f051002070303020c071d0112 69
    0x65241d4150441940c114840032141050301981f48120000c440403801408030030488802030b0070150140000b0340d4183c6548000b5004020183d416010400c964a074000710015007a1045e45d900c14004c0e150003070b20b200207010b448140c21002916101290018074255107400301c4041c44ea062a140c8029942c2d0744403030200d98107507804140c108002c01d00307110300703000190004003480080ca10702e520b40359094140445511507400400220315241c42e0144114103054110000384600030f01130904060b5243c6c0030a505103000322005110101042110301c0c2d00d4410310603811340042c003041c08002a1004000640c45404c00d15201c008074070002010f0042006030741c26104008001c1500344a01e24004d15840308170713031101c200e0920139440c00c2d6001c141917000360280d03508160000f4180c01030755119a1600400c14111205451500c641c0c00446c003408030600080501c0307482941c02588461041509910b0540d9039003003440000360006031221401d4002032600d04650714913a200c800ea14841c05c01c3d00c41c01c013 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 557480350 1250 557479100 557479123
    0x30b060f0f130b030f0c15041d07030b0d0f03030b0105040b040b183102071a040501090b090c090603010501050108063601180e0c01120e10150b040302010e12 69
    0x100707100f00c44885400702c6c0d4131107100b001f038440302c0382440782c845011018410b50141250b0241100304002e5802e8400c604160310210500700040d4001d0f480d40010401d9070405c000b101d07010035010400c001c05a260103038019444081c205a403c0c5401e11006c07620300d000f0b034001c20310005000f10740702070110682c01010420f09409000ca4220710300c05290351100d80690352490080298890802e8105a414401c03285903503001404c41c0d1141c2410305a00e812914040c0054480f5900c401c2c442000c03584084000d0300074070401c0c0c0100301780d0038000d0601043da0802014070740b099140500401150341c20005441d030142080ba41243c1c001c80c0580d2500c1285603034080190301e100c10404000100f002d200c0024140c0d114040c4a016411005146200762072006450b640a50040c040e0341c1099400384014a100070f40340d0f0404606600c0088070303079181c05020810f004041c0d44890910b2070201000300b48101a0001d640c2003454642181c0001c1c01884880080c2c9015071846108007200303280034008420308a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 557481600 1250 557480350 557480353
    0xf140d060803130e04030f03090819050a030f15050607020109120803040b161710090e0309040c020f0c09180a051c0c0c0b03100e0a0204030b060f0f130b03 68
    0x1074603405440d603250020003103502554a1103034040f80102803403400c1441254180d039000c01a0201d0785d0202c000e045548404c460043d014029001d0921015900e49168105580c41746e440d008040301c010155501e145e11800d0780d41c0b078a403041001d40110b04d152419900140c40c6140c4d96081361004a0750542140e00c9202c21900c40c13407a08007000040c00082d0b0040c1c1c005c8810110588420ba00d041040e80c0b036010340e0000c01d1300c90440c400071204500700c41c1e80c4008141a0b40b03032455038038061070058904043c51111248c000241003982441c013440b07400d52000f9144010404800d0501003680c0e03840795540707035038492043d100003c4d184a030303444c0840c0b0003000b00500799641c0d0115440c1c02503aa80c0c00d82c071100f9502e846000c11600b19841616882c0602c0d803c1001c0c0c00a451074480500e80603400030b001c87c10715440140c008103040d100b81103941d000e8064202300680c2c448c07440c14041385160020707181038030500e025640030840c0d0b51140c075903030072405044400b81c070501ca004c0700d1380000f08400003c0d507415 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 557482850 1250 557481600 557481611
    0x30403061109151e121801020d09030207031211030d09020406090e0d030f0b01140906040305060906040c080303070e0f030c040c030b12070521070e04060c021c0f140d 73
    0x100f5842d0409003100340e014040f1091070003034032450f102c6640105141e011711038500c00d0000d40560b00d20094040300d218810001440c24183d21005c0056074000d840550260384181001c0040005180000f041000245091f01d0040402c150b0386849200b1068003160b11754a4034620401d540e65540000c00418141204000c5608843c0c0c800b52a04c8000951002280c506600d248440080e800342440b9601c0581d0703201600159440314418039040f02d415140c001e00309010100000d0405c10001c1d0007840c0703000041c000d529040ca8007010700d0026810041c81504144280840980c00c09140302c0540c504452030070010941781c000c01d180070b45207204582d1160421072003d40303d94165025202e40d10085e15039035144510090403590b45c140610a842e00030800c400e0810a4003800340c0303624403c1d080c107400d0b03942c0140d8544840c070a60b0000e403829901c26a40341d08400c1003540411200d50b4090070344003a013200104500001c1e24212000c030043c0144080c01200704102c10000f01100c81e039909030b2404100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 557484100 1250 557482850 557482879
    0x4150903080a1508030301050409030c050303040302011b0302071e0f05061602011401080339011a030f061902130b040515280309050a06200a02030403061109 69
    0x710301d1081d41e03104286460b101c584614408280b41150641d1070a4000b5031540e464103040c40020610344800b60100501e8a402c40d0005a0a00c02507001e1400395002103207510300c96500182c1690800c8044040c503204000e81e03400507141051a5940310100c40c90300c0b950020509000404c0000c00030010180c1c000c4204100c3c044000388619607040131643d0003003103485900c034111324003003a003030254400b41e80c001e02500d05102400c08003080010020b400b1180e2101042c1c07a409400c12919401100594442c0a94911603810071848880c1040c203c00600080c041c04103403a48035080074121311403c601e0724901000c8444c080e0101c404a20f45900300107452079a50040702041c1d040b178041c851040d1000c0345000318a40c00c076010341c4c0264501852010308403500940310303800041154511400c0c0341d2510f1f6440080703981840340340d6400d80206000703d10013000210845d019500380342d0385102d1410920182c0e03c01c543c00401d40f815a40c0c44080000d4821084804100c14003a074699030368440c0d50a0149074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 557485350 1250 557484100 557484107
    0x501050411121209061c050402011701260c1206011a0a090605090d0609030c1104291f09080601080703080f0310030b012709020a0e04150903 62
    0x5116a020710000703214200088100304a446500c105100c80fa8460040503500040101c000c201c03451000b4001d0345800c20b1160500c0840401c4c14603402119034038420003041d9600081d4001c6024403000c4000e03c070b581080c0c0d001c1120014070584841d0712481814141a1450420a035950f224000704007070341c50fa803040c0300f6582e030b503409001d44801e5055514a07000c0103e141d030187d80052031151190f40c0824204601101c0030f0304110301075a804cc501d0003025000c11614070521801d68003e81e6450285022400d04400654907610168000c4d8908100522100031698020081e55480784041c208006032000141d070101b1540c3c0618030030060f52010104c401e40120314001201c541e24103455040ea40d410341c664480030540b00c0070302401c0081184c0c5124074406401598880e07404800c0740760440c6ca03030b282c04013600c2d8260400d17a108084400801c4201440301d440780800c030900c08060011b000d00341c0c040ba465188034420003441c0310500002c101004014191309072224109401080010407504008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 557486600 1250 557485350 557485361
    0x121002070303150e06010516060c0903110d020319140d050901090e04170a050c011b030605030606280b07110a060203071709030f12030709170c01051c090501 69
    0x48000c00e107410041d0142c0075400141c3c50480300f088800496950300c070700041d1801e5020440d074000300380f00c0b0740350340300061510b100d8541c007461103548112100c0d05501d03102d101e803107420008030b01c10304000071a030005a0740059030b094111550a20080401c40a107032850111141f10760040d07040c0105c1002e201400d030300c00c0180401c0ea03000d0744c070224505d50f100409182400d0668015100241ca07850100041c540000100407660b940d1802c1881d01e280c0342c0c0e40d94215032080d142d065903444a13510403055280d05000304c1000c0c203011406454135050080010303980c118041600c5480e00c1c034204070410b41e4041010044010100e10080d60b65a9015103081c1545070790605c4201d100380701c15000420702901c00025a03c0e81940000c003241044204410b0303c1e039035008036140b07543c14442c0304d0184940d204180316840c504000d044c413450716401c5c061009054400d460f000a4540c40c40302078005c1d00f01c0e10005100b69100002e00b0300c555500b203a14034081c050b0058a410344042801c003c500000c04c601540f18 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 557487850 1250 557486600 557486603
    0x3040801093513030506090a0c0f0e150a05090c0310060c1a100b070506040b06010c021f090306141e1911130e160219060b12100207 58
    0x4050b030905005165405440c150101d140402ea45802c0540030041c0020040c0701e003445843d4180c4056913aa075980e0b00d00724003224190000d8118481c600304204042c40d06201030402c0070881d4031468149035000390403840040c0110840d08406050350f502c0e4450f030b40f080c0050300c0701070400095890001c00110b02d5920a0311110105c4150202c0080d80601c1600c019001c541d00990300d06012003100c4030303460400400f92140444d98402007000441038446c400802089100d500940850310742403c00e02107880000b810320341030012400721440140d035014a1b00c04800521a41c21341030990f0b1000c200d410791129080103090500e807005c900d5000c0f006252403441880c0c4480840715050320303005420070305d01003039a956202000001240c8041180d035002100720400b25040c150402008001c0c1040080d910b070300600e10802e500040c8141400c08240d0f41c07260452074002070242e940c012404500840010300c0180c0610380e40e01e5010020307501e0482d02600180b1071030032500e42d60240002d1034020b42c00140d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 557489100 1250 557487850 557487863
    0xd0806042a02070b030402010905041d01051e011203140a0e030601030f060506040903120b0409020402070b180a0c0e13020409150c0306031a0c1b01140106020a0c1701020c0304080109 80
    0x56113800002140d1146506075070b20f07000c030741c505002d200c042d050f0407000b42c3c141c0140b4840c124160314240b0800e0301c1003941d15004508a81c3c001034403046840d041e00b0100951085c0781e08803001c42c1e00610142180e901b0b00c1520307641e40e4200c1e0822034007035441440c00c69040c003600e0000000d203c2d12500011a46000d0b0000b04a580c49090410040341c402030320003404500503050f43d0650880c00d5110030445030303003d440480c10711207540c0020b040343c0c850300d8112003410150041c00a0310007603980320150540404021301d41c440c416202d42a11800030300c112038542d5007520002d21100c03031322681c4100540d8050010f00020015107071440707108045040c4291440d2814650300301c00c0e07110f4043e060450f0b4008500141500004400303070203400000f8200050440d0400400354082c115003802c1c282001c89030000920b842042c0c8101e181030038103a00503021984007031000004183c50003845012a00215000c82c0952958900301d806809000722964590202180009140c2410340209203407522452 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 557490350 1250 557489100 557489113
    0x2031e010e310c030b0705180f010212160b010e07080c070314121501050a1205040305070b040c03050615061603021c0302040905060604080d03020d0b0907021c030e0d0806042a02 78
    0x6c0c8100c1c2c0c980141c903210740d240d034800b140e440840c0c28040c1000400620600c150350b20340f844011020500e600005944130701c0b80d80001800306004a03d103030380303000d040d45081b850107600b48450000e0058801403d866022407000904400b010f010b81d0441c25401d104c140000c2d01d500d1400320412800004441030100900312106590070b0350310501c2214440b0b0401e448030840c240460b0180b400030a00100110140981000100046886018490700c9a03114042d02071a9508519000d41880070207841811a03113a505190741140da108400d5646808108048480e04541c5e07050480c0b500c81c003a07013a01c0f541340d80448400c1a2950540040c0290780c80f84005103c1e545410b81809891301c101c0c803d42c9450b401001038808a40c4c805d4000b0b080103074500d04c02140b50180903000603015007050b01e580025901030384030456040c0e8840e142d81500701090900b001500048140143c9400300b0484010802a00d100081c826507599070260b03280d208402011420504000344040d487d5a508802802510031b06 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 557491600 1250 557490350 557490361
    0x70c050d09050310020c010f02070c08070f2111060c15060f10050c0c0a0e060102100504080307121104060f1e020309060307031b0302031e010e310c030b 67
    0x340e801100b1100042c00801900c034080868500940080009488079501c500340e00030b0441c038500140200c507001d40881e151081c80d1512040c6000030641c890a030b0301082c3c50081005840220018568846843c540c0142c0c91403403400004000c02000700ba07a00600c0419142d103802c000003810030724041d1601c900342c11500c685040180700da460301240fa611207030440c12011600d20400c040c040c02c202c81000c0f2150480d08000184540c00305401101100500c00c00f001115a4100034440c0300030800a410401ca0070b00303449280c1e0313a100c020400c0051001101400000b0b070302d190301580001c12a48003c43c2c403680c0b0f50000804110381c0410f40c200081c04900b40c026181c542c145c1031407074101c45400452a00f60508180605500f0040c0003005040d900c0c11a1082c00041560310780014445a6005960345030184801c41803540303da00c1030b01c8100c03541c00140f04032100034104540180e01880461002c064405607902c0000144d18442d640c000d448040c441040036060200d0705070303407259115070816a0388 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 557492850 1250 557491600 557491607
    0x60a0605040b060c060c070203070e070807080c072102031b010903200c150909041101090803180913050d0f0e0603070f0f09080708031803010912180509070c050d 71
    0x213903611314405410002c0811500c04e4044001c1c10150320280644801c01c0d550301c413903c4030035011122035000c10325140400a1307055001311007642c08001c4025a07810041d294680000c0004424085140c407882008c550b05031074000c0060340c1c200c0100e0401491011100c64005001c0c1000b00c404901003a42c0501e0710542201801c29000c0403c1745000401d4185003910800c021402c00520044410f00200100c580c4c82d1640486a8406d41c0945030070300c02c0c0a9044001480c080096114040940041c010342403050481051241915130032901e200c80e58030b0303200150502d44191070009200384108128810340503042500d00801d84550b4981096014070b46003840900c0c40f04075601000201640304003200c89000701184a40c050081c03500300412516005007914000c441e8202e0909a40086030020605039440310004c02404150000d00048000782da951110418000000c2c2c14000041c0008001031201288030000304030003400d000460610410203458030048520558240c0030760740300064001d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 557494100 1250 557492850 557492857
    0x51504030206030a050a0609020703050a111c051806120a14060a091a1018052b0503160305030106030b0d020a0501030902010e100e030d090b040b0705010e060a0605040b06 75
    0x40280c0102c2c07540d0750710b903980703030092000400c40c004159450341e01080e12881440501200c2f031007600d034035960300c0303540324050440742c92034044a500b6800703041140041c8054804010390213880e814510784814410804800580c03002d041d05420284c080703401c40ca5605030214540c09030301f8002d01040324001001c901d15202e841202c500d84c22601d0310f1000c00411405902c10f580403004004c1890001200304001414005080c2c40e600001b00790001803050710219a61103c01098200c401f090020ba800400121650741d12580400400050b41d07a001070010030301c00c8445104900615900b1b4185501e00907000b500280200d0380003d1401c0d101002c0381c1020108240e44540007007075582102d24207401140500b042880c100c0c10021241049061621035034950860341039180c50300ca11003203a6406061400c1e01000e01704080100d4410104412041c4000b150306649070703d01c4031527807003800303042643c00740056515640c40ea12170041040000d00255201005562040760248030480c00e000400c6407a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 557495350 1250 557494100 557494103
    0x70e0705070b0a0e1b040902130605100e030a0204110403060207032a020d120c020402040315050f040c0605031315050a0e0102090f0f031f0504020109230d061503080405150403 77
    0x6001821700000b0408428254118a400910100340e580440d404160804d00041007040c03242d85890040c8128501105580407030041840d01354000c0103550b0000f1341d0b482c0944000303030195545283c58a8008000c0c403c0305d010356000a01595a0901c52600030102c0700c00c10201051136403004030701003d50600c1e680328821141c0007805c15411800c0c64440c0051004161522018020f005482200607280e40c0094001180261000e190483c14040c0003401e6660003481028103485d10000c1100007181003ca180651318540703000c40d280d81d50031030194007407405a540039040f2031106011b02800d00c526000180b048814410600c5a0100c03040342c1e60a03401081c19840c1e0202c40600e0b0f100b0365043c01d10182010000042c00c464940380c1c100e581540d410302c0b2030600307107125480e002000150b5821281540040ca01c58bc820341c0403103052034a031406d074105240d141344181c415079090018031131240c010b03038000f0054403440c0781003e0b602d250030700c1030b41c2c0705224660082407000d1030343c0c2c1541c2e440400e031400ca0303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 557496600 1250 557495350 557495353
    0xc09012a121e03272f0a18090b04111002010509070524070b0406111e0a0e030708030d0e061038030402180108120705070e0705070b0a0e 60
    0x841422803d070040d060881940392110700011143c1ca484c0c040c0f90042c0b42d00ea000b128402107251040c14102c40c61345076840110b400403803003800e5880b0368445c00030100450b90140f0356020481d9034080910050241514040d11a08024003404244200da014401500c8802c454103200c8400000f0164280c820844044003950042102004103040200f0400459141c142d585400c40a500080c4078092304841c1040c6d50100500e0100070401c00300b84a50f6402c0b4110804240c20045055000c047c0311654008c10b40e60342c0f4010529441407405403240311495840201a141003a448100007552604841004d40c1c005007820700319035002c08081520b50086407080c44a41c503150030203618042400c40ea4007641c43d0b290450041c1c100d2000420740780c88211601601243e500d08290040116505051100303000c10907080004120340e44000800f01c0580c2c0b068102940c46d1050350409604250079039100e0351140f009a010400070b2075104000300340346481045a01011384481c000c4104982588840d0f4030103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 557497850 1250 557496600 557496647
    0x1418030114090712140604030e030f0f03190e0909060604230601050705070e010801060501090b09030601030201120902030319030e06040809090a0e0307110f060f030c09012a12 77
    0x48886400c21401c030300d0048400e161780d1314031210340324900481201c2c141c00003810702e118400c0500e0148401c2c549030103440020a802c410761240e4903140e1040800669400300120881050b150041280c0ca0a0381c0307004000c00c21503c0d090517425141c0ca03088501d03510071440c1240405181c99001d81c00842c80c07640c6150480303e46d032502e0054507140c4c80008151030300c0c89460400a503d80344a40c84502030b0a0104c000b0807203e162000140c00301e001078115409031030084c0003402594400141050441e0f809107040b4403c00020610701004014008020b5010f002c0011814904a0b03d0000980442007940e010020311520251032500e840e0182e6009042c0003081120111500d8040c61643e0040384a400001740141900801c502d180d02942007112504d0820390112481d1521a078101e242d80c4050342c8030307464060b20309114401840000c080304240c010100c1c40d526143d1040c0000c17880710650509075007100e0200340d1400320301d01c00d60720304543e82c4a0011400c0d00d000e2040003401d0305900b019031400c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 557499100 1250 557497850 557497859
    0x240605040b0403121106041410050903090904081c020414031507050901021606020d021006050109060c060b100c0b0a020703050d09020103090c0b0c060a020a051914180301140907 78
    0x1100518400d940c00700314548850343d034101002d2081e64081c602c075240234890403c8507200d00d41000d00035030365181e18518002c208024414040112119803d0883c0e61403e2541c5078038000d60f141c018840c20040c1c0380d032654185841c1440c254010400d4134038094034541c15080600415a071105c1000711402c034400b03031802203610a40124003800400c80140103031051111100c0115403800706035844200141e00254000d42031980512000c1855200000280506d509010020304110182d104410030040c0d003281007001d20940d507000b2028244000d0003d10b004902000081c01031024a0080d00c0340e0800b040803803403c0403144200c3d0810399158a446082421228190004080d100343c240d06240e169907a910000c1c84a28004014107580121036480d4000c0003005031504d00001c0460403601e02c10000448619040030907110160261001c001c00040840811a0070303130030105e224032110001241540e100c211030328041c1c025010603130003040740c014100c5010300366500c1030312031030151b40142e4820f10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 557500350 1250 557499100 557499113
    0x3040e060f150d060902160b07030605100c05010e03031003030f2f030c33091c1403150f2409150d060504050609010b1219240605040b0403 61
    0x4152201c0f01000074416540c05980303040c3e07031003510030607060004c200740038082042d440c01080c5c000000d40344c108034103802c00000c0740b10810000049420b0292802c1d43c041080800d4000c14122500f21040d2501c900300700380c408001c0c0442c3d02048010420090010849520400d00428071a8502100512800b2a0f2403214168124400909051301042201c8000d0307140412001410211740707a80d54420b82410642007441180300c61400249510150502142c00700000e603580e10380d210690448001074507001c0550320b0900d00038020343c0c0c1481c0031042100304d841c0000c248031050350a5484100e00c81c80b5004110003404143d0390b640c2100c003480041d590045a00e80500035074400501001c0501540d224035400340d40103610403c0c40c40b071b161802800142054001c10380c00400942d040f4007654100302c050036080c0541c4210a410700c0000380050020340d1030303413804110006030707403020007840c12003403d0091411101c00d1030030b021203c0ca440c0018054030039030803a0f0403918400079441c10241180e4452 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 557501600 1250 557500350 557500357
    0xf090525081c0e120a12031109060306040f020405030a030f02120c101e110d06060306030213020705010b0a0b1305012a06021e1305011b02010813050d0203040e060f15 73
    0x39821581e0088420310300c4001700210380d1194081c40d1000080200842c006060b82c3c6c1d000349082c59104140a040031540318001940c0e0800400c4070302042102070546200c009000350392281d50b0501c00d460700c220900d078003c1010300c1203003d240e0980c0d50164401c1d008401e18861890100e4141e030043d02c1c2a109070304140d1104035040c4800358581050800d02003302c05540e04003030402c4a02e18001000141507801d031007035600802c03003420300b4801d40b46141c0016941c40803207a0f8a026194001801c8003c0090a6000c2d403e100d02c020008580140c41d042e503918650043d08450a80002ea00f40200302980200a4000503e2900044542c062020a407002442d480a28100c41840d001e02c60b080928590142e1701a01403400080180c5034003000325078002da41002d40c00241030081c41aa00311015030389590550b00a9020300f08403c4503112030b00c000560340c002c20005001ca0160403040103e00e54040000c00445030151070f15156034942008110144184c0c15003a648100301c00e070700da040f4142007000b9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 557502850 1250 557501600 557501627
    0x903070b04022224050d0507030308150a0b030a0b040b030304050d05100905010209090a060b0306040e0f1c180b0d0c09080d0302090907110a060f090525081c 69
    0x3080010840c00d011102500d0354001d440c0c007030b41d1348550200008a41040110001c04003140c0c0c5a0f8041440d440e00b94584030700780809030801c031507040010000c02d0900718010a0000c060720804070b8950302e6815014582041d20484581414100c59418528040c016800c1c6404001d010710703d886c2c0342004000620781040000c49045c0100803401d10841a0f03440303070340a090300036400503030b8441c4030008006034a0001444440941e24208060010109803015640d00c10b405440010301c0c03c1c00a038650b4a005510f102e0b250f0a403003801d1303e050401840d01d81c90b14101190751580000f001c04e0144104c075000d021701800fa02c40c0030034802440740300d641d81c100e010401c40b24149070742055154942c5500b85a034800c421300101e2b8000480302480d00b0400076584c1d00070f603540380c0105520310300240a82c42d02506000a030805446503140848510302c1d5000304000c0b03034040c0c11642c0000346240b0f8611061800d86440c001034080180000d61004080745a985003a0f1320100e81c8101505e03c1d900b9074926944460 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 557504100 1250 557502850 557502889
    0x90708090c1e0901061106060402130e100302130632060c07060206060f010f0c03090906030f060b01030203090a17090d0b09060105030c0d1115031e0903070b0402 71
    0xd80c1c44440d00d0302c14901c0a100c1c40c103010b14002c484a02c040c00028001a4809020001c0749514003a94400c04180e064100004440159403444450017a444844258029090320784014090003600848140c0380c03003c59200f91070070303540e08200d540404c040701e03054030550b078070a0240752001035850380d1011100350800030b070022403910303c03844808681340b900301c42071030382030f82c2c0c070100307050199a40400c001540640101c4104042a0107140000c0ca00040b2008020520020480150806000c0c0301940b0241c45101ca0800c01d46a40b42094448104035080940e4609d1503c15000c071194824000c4920685600008121180f4140d45041c0300c420384a2169610754410b1100480300d0b82c0300100c4032140c50040d10441414100000319604000341a402680700b5417225464103800e40300d00280c3d800c2b494002c40004400c0d0400c801142000c10401c81003a5200340000030000440701e10a071000b000700c105001c558a40d9503441980d55240705003036015000921041c0050018901201304032a05917007941e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 557505350 1250 557504100 557504113
    0x10c0501060801060305060702011b1413051c0204050f070503010e1e0c040303031802101d150a02070905040f0209060103140103060c17010b090d020607140a150b09070809 75
    0x82e0182c02c41d0038980084803d50000c0c418404540d509004e090002e0030070140d100d100f91110b050180205500c17880319041031750049810340c010002da9100000401c400b8001401580e21154169040402c07154100e114610784400310701c4406c1d510401c14498045504c807680f850f400d104000700c403018010816130203140d20940c605122700617140c403103028410304000c040c1c03a68154034004d0140c8004060211042000610300005655005c1007107121015609200d00405001114940040e01c28510f42d60090103501c03280c40b07410207500080c00d0032240303036007038441242e2505043d01c181c4900b039502074402000380c8001000740c40c110503002c1d04130f141410006050602c10310020b840d031809a2040c1c40450f500e0f52110460343d0050101c4041c0c00000c00e08040942c106602600140100c41c000c0380503000000c030580854440e00120b03298507810451008034105083d00c0d89940365884c0380c00311000341d14003001080c15202401600030080009140843c260313a500c03004c54000300003d110340414844c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 557506600 1250 557505350 557505359
    0x604180f0c0515030609041101030e0f03030a15030c0501030b0105042103020607030207030909090f140c0114160b06130204060c021804020a0326040605030a061a09010c050106 77
    0x540c401032006100d0401207241610744010881ea4541281d4840b0701e2880c04c2041040ca5650b071480f07140d206500c41440c0c41060b10240040780100101c3e81000e140340318821643c000c000e0008003070340c421036400d0030034400c0c849105503441c103800c2680f200800700c20842205000c55800780c0c201c101100e2061510300c0c14070b562205c0003081c44004010003521500d1100d202d0041c1070341409800d03440015418107510304175041d075001702007443c54400c80349817030780e40c1d0015403c1041c0d101403120302030741200c0440518111420001d40710f0381032240441c003050305801da040c3d804440701e040d0b034002040f424288185103c603869041003004000c080640c0944220244840c050061000d40058819540d80005001031803040c000e40182a6003c0c02203c040c540402005a803007640804c00d8035409003102c1385040c3c508030701c3c0b102440008949506010045804922250b10002441c85030119400c1070000641c0d0380321101c45c0e0288031603562120181000605082d500915482e00c000707105800002c1d4880e6203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 557507850 1250 557506600 557506613
    0x70507050313091b051602090c040b0f0c010506220b0f061605070b1e0c15070e1f020d03021b06040f0b0a05010605090f01051b06070f02030c06060418 66
    0x1c3c0c000e601d901c3c2d559101c914107000b000c0308a41111070355041181c0351030380000282c0c000c98140036000788980031243c001120b900d902001e640013040c0e10074055440c0d00144014000d240c01080d42c007a80d80d03107000b002515507c1c2c820385d94120008111811050350007501c40ca000642140002650000c00c20702881c800e42d1100c40085c204484c034605510307141d51282c54882e0900e001c2e940b2036058100280b14900e982e4046d20740da07580001d20384040954803240050500c0c180f110604d03080741803807240010466042d802180c1541c14a004444081d94a81e051441e000c560402085200060f480351100a03203c80c020750051044d0840f4041e401000d07511000034074503006080710100d0710400707006030f6901004201c0c0303081c98004a41c07050602166060070001860f6000381c0d1003552041216240f1902a42d0040048680c5e280e40d007116191607103004c0b104540d4031001610300c1c10001c0c04202c030704c50b0f8003031000c010f444207151031380080d0000c1d84032401040007812040c3d042e0341c0703c911109501e1000400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 557509100 1250 557507850 557507887
    0x308060904030e2e030603020616030c06020d060f0b0c060f06030a020d06021b030f030a0c0306090f0606140901080606030a02040f060e100309150f0e010204030515060d0203060705070503 82
    0x3000c41c030070040c40084a00005004c02040c01e14050504000084c00140c0d9042c2c00e6508040c0030114808074a6a84d003411282c681c0c0c80c2c0c4010f80b11902c0000e201c920454150084801d40d501408800310b1030303a5413610417420740b04562003040b0940141003c2403c0c41c00c007007079142e00201d008084403503040c1c0075000101450201c4004561741c070b9000504600304c61100d10400d00300b800746406503040c000c107100701d90283c2c13100500300d00308580c3c0d844541d18114084e900880203052401c000f08010340c488581103000303190718007a510104500a1107001c3d200030b400111110124180d445011945800f802c0c8101d80e0400f8210f600325039001d1201042c06418030b01f001700189000d51765010b04581c6401072014081c6c10461810405042440e0040480e003480044d8920b4100b0000000d080015040c001008014a006800440d400050004240240000d040b0340d6042540c1c00b448580c0c64210400c04800b201c000002d405411210029140502510140602c0f502034002d482c90300c0d01c84480c440e900035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 557510350 1250 557509100 557509129
    0x4030203070e01120f14032101050d0f0312150303080901050a0204120f06021902072c010e0405070906060e090c030601090e0903130b0403061a06030a2f03090f0a0308060904030e 78
    0x10448d0042020f001a0705a038014101035919101403034250700c808030412701c004000780502c8805c14940312100705a83c0621888201c90002e015000d41b00e2500410881095880100b10740c2810040703048200148215022150240c1c2130b200810b4041d81c40c4002d0111f81d00042d0740195084c4554007a412550216000e42041640508411030404000c100d09201c004e800141c41e0604400001c0040c0b4900307081d41c1507524001c0c1585660341c1342d103071a03440c0c000c041c0c1068050a0428000092498200c0460700240d003017243c50311059039864400039650300007100e40c3c038000b51100b0010842c0b0760224140315000f20720300702a64645040074404134000341280e030040403000c400003000c1041c014117100355244056000001f500e03c800300000107025000103000404065540c400300e03203010001041445c0c180d5110302c2101c1d62032041513806403507508100c1d00300c4024050080b6414102a0104030700e200e00364103131900e542c1510341c9814000030308401003048040c8122565040416942c10004040783c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 557511600 1250 557510350 557510377
    0x80304030210030c0503071b1b09060b0f09010f05070f03020a150917090307031b14030d02030403061107080d0c27090f0209090c04030203070e01120f1403 68
    0x461031031061051841d081e542031020946000f481080145e4000c0860340c200184e4a4031000340760041d00822546003810400601054020003000d46140c0c01d0320201c0c04551541c2e404020b2145d0741c00450707003940305030080d0503002801003101b0381f502c0d8050744000740540043d190545c00c00b0825030364404d113142c50003415009680000407100810500c041c070310301001c8541d1014404489141d0365550980140302c0b0f444101940494020745030b4404108000040d900b2813540038904150041e035100b000d200b40a0080d10010b014003200e00d030f041c0050f403d103444020740d008603d0710749542c0750b0500a14030f5190000034038000b08901d0b03003c1007019000e040300b0103058800240050b080d003400380801c105040c00c0340400f0404001400c480c074200410004a60810700c020a11307800d1040050700074800c40d911103078083d104009000010007818058010b0700c5c42a011190000c0c0c41e003c02e0f0180400c24415030540307440a00c0820f0000301c14800d140d80710782c402c2d03030340012043c1c1d102105802c40e0015140201a03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 557512850 1250 557511600 557511607
    0x30a1d10060806070905130c180608060906090118020304051606031d01060506070f15240b180d020f060d09020a09090201020312070905090c03040318150e01090b040803 74
    0x1082c2c018820b03d9040000350801030f10003454080840c06c201402e01032101650350310300c0260182802103640000942441c03140c0c0400c503440d51400703003205c07400355180d50050000348000b071807e00781007080e581a514107668059042c9104c01112001e58802041243c0c54041c500e001000070403100908400342c50340351000310740c14840c0e1800722480c40141400e07404070380c14014200141d854007812540315507001103041008007020f080240f461400500504085403400384400b0400c128100e01001c0c1c1c0418032303030540c05555030f01d150702668010850301241d50720010784075480c94a41802c40c45181c1e44060701003100035001c0b400042c2e86400c14141c4a0b10385803200100f0046140c038000400c041e209000080146140d00c5d00003d60b64001c403030000c000080103601107001a80628000001081d008103d401d040c5001e041a101035042030303404030080341c2104400400a007040800c001541c000d000554044820701d00308844801044041a05001032403e0103d18080300794000c0c8060200d01004594 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 557514100 1250 557512850 557512859
    0x30b100503010b0a0f12020f0607111005030f060d050a0611030106030b06130e06030331120b0a110d090c060206072102130518040506100803030a1d1006 67
    0x20340d03d00003505445110554810f0001c010510480c009440d05602401854803452010862455580303280360340c000b801081400403c0b503d00100b41c0044402c1e21210103c00ae00c3ca003c2c0c2d01c03408140c1d0004035000b49000002c0b8207040c00051881d07800e010303400711081000d40384c417000300301e400e00c0e1501c41d0003490000040c803003550140a0032004000640c1c11501e0042c0003184c45900404d0303800340904280d00940812020350307041055882114031400b0807102400120050760358500400c6000c02109104000024000c6580520f61043d0790031440c0e078103a50340c4000c051030040c07118074040c43e1403c80610075183d03586150b11600140610030301540c6c556900344000079180000c0100340004002c1b46542c0f980e40e0100d00012005c0c4404031480146e2900d20003c004152010a600303c0d0b9003000110f05e01313102110b90030707810501450080064031b0054039254003090941c0c05c01e00031044154410000701b103900f4055032081403440c0129030030030403030741e02c5612844c100381c003003040503054070703141e0300c0602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 557515350 1250 557514100 557514103
    0x51809070915020f06161107270e1c021626010209030d03180b0f040c05011103160f080c0f0f01150308030a060e0a0e061303021510030b100503 63
    0x5035401542e000800e01c500c078608490745c0e80e0710014108170311a642d0124008034640038851030b0008044c4c4009a902468660000d000c2d1800c000c041410b0b001d089001405415030a8880d02c070744c01c21000080c144141d003c000c014049208003800a0451161070014890140c051004002620741f10410310b0000c1c42007a00c02000c0d518451200d52207910412019006079000601c01503ca4068100071800c510001540c0801c4002a5400f0301302c54014010800791821001e6002e11940c4117005440320741ea110401105c802e00d40c00680c44c0d0941c41000f50701032071042500d000c15240d04c9410402e00b000b02d25903c3c81c805810011050450398020501c000c0d81c00428022440303402c240c43c008000c030040620403120f400850744405400348000101043c140c00190708000040c0c50b054030a41418140244d204004001400d80c400050103900e0114427441040c0c16076000c0030b505a8001d1800c407500b0810b0119002c0e0160101400610320a4000700040400300141e00c10580d912500710306914020905 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 557516600 1250 557515350 557515379
    0x201090506060f1f050c0102030c0702120a0213020d0b0a240f05090d060e0109050c0a0e0f010e130b0f07030507020a05070324020d05010503010612080a0518090709 72
    0x18865804101511080d0301d45202004c003420b205141d40000481c94a030940d501d104090b180c2c0125400002005000c40c4050000c105441c4240c80e06600e0b0b511442590ba101d28540c0f030003e5100715400469500602e994014081500d40362000040c00b181503800500144499840f000c030304036034440941d003140c2d00158030030082e000702d040c00b5160401c5004002c21501c80c4441c0030748206503140d066000e0107980c0d4843c59950780440001c02c604105401e240f40c0d43c1d15483c4000d403180307075040004a008501c29a01b0b0b8087d01c00090380c05101d03403c2842619043d01c1c010800fa810383c90a00c2c074040410400716400b800f811101401c5440e9041c015001420740c2c9004111805550000c00e41d040020070004025084941104415410b039008032078840c050301d44881e804803414004a00205807000c03640c4454100d420480007044069501e960461207070003070802c00307040c01c0c03000d100d4000b541d80200010450359a5800c0d0060200c11000e00184c460700059079200c0008203000310900803101d090320007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 557517850 1250 557516600 557516611
    0x709050612070501080a09120915051c090219060509040b090103021c05010b03121b0a12030207080d020f0c06010e1006030b0607020a03080c060709140904110a060201090506 76
    0x86408241c440c0c40354564401c014410b03a81048003e200140d00c1200662211440075401031103000f024081c02d03402840c2000c5406141801032421451110742409001200c401c201c0c9041d6001c5102c00390035176100100380111081c2d82000c07000b28080c006506500c00c10307000c2c22154031001d481d0103091040c401190480c0d00a14000c0750103200601c007580d180101d00c2510a8a544440c07110340841c50700a0142c040328084a0b014850002081c0301c00e40c04402400104030b0b40b401514050200588040d95142c2d00d40d030103840d03070040802d46034101c0d200c2d4000b0400d850040489910b080504495001280d00404492041e40d41c0401c912413696414080d40d401081c0d1140300d81d03a1801c0c40301c25000680001d04c140c405150391207a60340026151002a141c40c65001801480041d943e41003000703859020b140c215000340600310000765802c0c0100e5107001030321400b0400140414204091000318003001d8000c0c1ca03850b60b2028100029910440c040024111503800880c0d01084c13460720b5841c0c0b0030040c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 557519100 1250 557517850 557517859
    0xa090501020c0a2a05120c060a120e0a080a050a0302040f0306091e0809040e0c04050c03090d26060301090f05030414040b3001061203120e1203151207090506 69
    0x46000c0c220312031901241505e404a90014003820301000c01c42ca007481c82807406030407490105070008001d8010752140301d103211000c014401000030388046a12240c1004000b4901d040912100d00d40e148118060f000c0d1003281d04006143c5501c03076190700a4010f00d940100d0300d403529840c3d01d00805c120002581d080400c00e09110411108903030720880c150081000590146603190540104070b1010060000d02c410040c10410141c00c1c4080c502d8010740c0110380b06081d901c41e0000c0e0344c035518481d0541808401c041301c88420b4050051803045074400000c1c18481e4550340b20740c054004100c1d148402a02148250700440c1d45a24240e4404800d01000300b40a2050b481d018005001e5111081c048480c02080c0102c0c8a014006604e00c0c0406034980130144415031030a03002003401e01c1c0d0308850303000044c000c1d1140031958041a00c04000d0b50284420b400d41f0360005401e602c41021800045c5400c070001000b80c00164a0120100768080071850000720b0541c0034039020480003840b4840e0681111040e20b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 557520350 1250 557519100 557519153
    0x203070f03020c0102090604030f050c01110616110319080702010902060d1814060415050411210d030212070e1e0a090606051e04120b0a090501020c0a 66
    0x201800c540031909000e401d140c2c0000c1c0080c00e91400794125402018002e220640b515160304201c07592041ea0503003160a4800c030f003640b607a258061541400300e905204010442581d544110b100218002e400c0d460611007161410501c5c0d10701840a80041310306030040c00321082100100415002c2d0241028065916101c00e010141c0c41b558205d8518081e401d401146004071840405203a0158100180601c0e00c500d83c080a01200468060b000b07500824415043c203e041d03e0007002c0b05c13030980d4001d203803001090b040c540c181070611050602000c0b075183e0803010790200400030308100c446074000300001d900094503003004000e0b4440f0380c1c0049641c50321a00003031b51000801d01e0003224010f65a1700ba090321403c000035903540355411010b0074040c0c0040c819603a0380c00c2c01402c076420100080070100124550140754081210959044407404134803003840361a1500c0c0c0c0c688013040509140c1c05d07642c8070a041e00100e24240000c0039040042e400030f00401000b030904400300807048044100006420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 557521600 1250 557520350 557520361
    0x140102160b070b100f080d0e040203060f040c0207051f02011116080d0209030a0308010e0f060a090207030c0203060412080108010606080a113a0203011d070912050319030203 76
    0x3070055944866004480780425251001807011031010b5900204001200d0803000c940114041403004102d03200c0d841c0c110030759000404020590004480c01034100034038504485040c41c0a40000300e50134094019160059214408903459820f000e207803801d03643c540313900703d0a000e50901c9148224440c0f090b5441c01c02c1c2da144006d010102d10500041c02400002c02d4801c50940c2580c1150010040101150720f80d0007036203405484107909210b07031094024000d0000d03440b161003010144c4141070052084207100d0400c48030340020f401800c0e082d0200300840c881e204c0141c40800c400381c0158050640818107800070003004185040c1608240d1650b41810020010030350080401500082090800308491100c0310b0021b180d80500c10804000d840302003c550618480c141800c0c000902010b01c42410384041d2001c1010f070711080c40340c030048215240100d4085903544264607000043c900e4040e070401d039030300720085880c4070710340083e60705800000c1d010f040c980d00d12902e24800c4905080650941c6040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 557522850 1250 557521600 557521619
    0x80c01120b131a0919270f03030b0f0f01050d0f1103010503010605030f032706120601080109020c03070609140d02060a0c0813110310020a02101103010e19090c14010216 74
    0x20464140f085c2c6031500e10b44010140b0f84440c0107000d95078001138100428144c101207010f40701d00c7c00c05801107032030a503141100e800c10060070340c86160040c0ca14031540c0300103001121264880c1e0100800582e54087c40d0380d0b030003070034001c0018210202c2031a41c0c595051504141c215202580542d110307032b009420703124005a002c42510703d807048a5806680481c2055581d0340c002c440389c1811540500d0018040c0070b901581450fa6000300402c0c2e8401ca843da880b0101d1204920440c1001443c5610900c414000510030390000060144510100d02c110b80303003c107200345400085290000582c000340100044030010340b0030310007282a40e00d89440c4a040010001018407440880a4200a0140242411a00c04101580200910520440d0f85001400e002516841300c00d2190425a080052001021006405072410307145501ca000764180c607130740c03a00790182030800b0350900059199408034000c51006075103a801840d00a01801950414030002420300000b407942d0b0300c180100e8403040c005400f4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 557524100 1250 557522850 557522881
    0x70b040303120b030c12010c0e01050903070b0f070f080d0b0f1005090102011506020a05190503120a06030f0b0a0516140702010201060306050c0919080c01120b131a09 73
    0xb501c150000e080c0381d000e00070a00f404607619146801c201d401c0350321401c0c1c07201503000050a00d8182d4941d0b0703244852000440d014469500c5180d85540b11100601203419031400500d40140307100702c4586007909035501da07032039010f4045080c2d0750080c0c04103240b01e00b1041e5006200d0428411200580c8880400001401168008500c001040004248481e180c1d0007544140b2001c8007008480c0b054a5440b04000d58803001c1210031209230090002204c2610b440e070340e80303244680d40300001d1404c008031454038181d0700c400148482d014546950001000c1074441c4030086c041c0c0e0003800c101d9460701c0c240c0002815500042e044000e800c12445403815600d9000030000040c1090f121b0712aa580c0761400102e0140c001604080c090a14020611105070042c0004208188051306c8682d901d20084100b80592801e61007150300385e82086105559030b42c403c500083c4070740e64202c400522043d1160200e02c4013049440b0000c881640d90b07480d1100f6122803c4550062842180c410040e4034051030000c28007030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 557525350 1250 557524100 557524127
    0x9050f071a09030124090b150403030804030522150c0f0b07050f0d0506031c0f0c02060408010e011d19062309031c0501060c02150d090602070203070b040303 69
    0x1076000c00d0b5018559400c0d084420044100d100705042d1410f10081c41503045c071303580305010307013107140c20081c901c10f04125100003400e100c10005203082914649095514900044c1304604000c0100034002111101d0207040d20304a00e610b48940440381000c0c5d014501c02c000e00354030030502080b00807800c002030a212403c1d00c42ca61000d4102d0180e00d510700141c0d40303401001c0c0708444034000420803080042c296440284107010031400c5940699003000e80380fa085085200300360004510405000e030590081310721905481c4007030304d460700d801e907070b4140c25084600700168007417241d460341c40005491703101070200c84900b01920090305d5101e047c3c103031130f0140301c50703031100100f682d81c6a80c10034121007041150b9441c414540d015018041c500256940d03107e602c0072843e02400c0005806070729050204d449403a042c0c0d42c042d159003040198a8080015440000d00002c40401c001c00c14882182e4039806810f5586105100250b25a0624030405003060400e820101450905000c100082a030141500c3c01c0700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 557526600 1250 557525350 557525399
    0x80d02030a06062d0216083409090f2102070603110406030e030f030106050d05011505033912010e0f0118020f030c0304120305090303070e0d0b0a09050f07 68
    0x1ca1240c1c100741e0802c0940c011003101810180c03400580204003051101405940c0e008e0703e030781c2c1b010700c002e080c00301206a0503d5031203041888062014030341c25888031203c2d03070140e001513100c405296984400d955000702c54100c12803500c22454040f503010041d0ba0042e12003030a06201d090000d6501c1c2e8080d00036807051008254a440704051400350500858040714081004682d60b9a1220809465079018090364101c246c40c0900005042d807801d94504070100a5594180c90b5484007500d0000103403d80340c1d4885166a03078580786100048450807407038481c0d00783e121305444201d85006800c0c00703130059003c080072480304001c00c01104200300e4000d05403510004001c462280d8052200001d008800044100e21400000d000d4480801c0d400345224500c95804204070f000e03c1c100440545405980c0d4410a0b4414408584403e01030480e005614001900340702d02c0c102c1f1929103521203c0c040c2c800c50060f40d03807042c0c02d1041c00b1041c461700418511810003041c81900d04848249140d01002c81d1850344c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 557527850 1250 557526600 557526677
    0x120604030503063015100b09220606020705010e030a12051323041113052404030f0c05241e0a030608010c090609030605060607080d02030a0606 63
    0x7600d40c8041040001d0100c008188140380c40d0300d04c0306541c1d02003600c42c03090b95a0414006110b80c0910030301a0309541310420005e040202c86011302040310700c280c031103011510907410400c09040c0e01d441000000d211503802450854545000503140032204080c003401b0380c01c285e003038074080740c440c103d44606c4040c980740c800d64442900c0c0c80d0451083c101d40001070201c907607550f07101140103144580400d084045800700032022560507403141900c00c00d074104000c0490008100001c0c5040100752419808040c118460b9000241040d0550b0344940c104a03100c48071800d05200784844400b1000103050140c0c2e850001092550f90714525902600701d03112280e81c0014006003520a10b00345008881703450a81d40c1c2c44854103640907014050b5806941d1596180040f8105510b00c140855400c4510b5911400811070440e02d8520140c1001800c09410030810070000d000290460010080d441c00e0000c01030722410a082c2d15000d4684961200c0200882e2003102035040c138000c3c0100407840404c5640102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 557529100 1250 557527850 557527879
    0x1b08062e0c05030a170c0c060a0504060612230c010503160315031104050901050613090f020303030c03010f060c11060c0106080d0504030c0803160b0403050708030a0b12060403050306 80
    0x41814000340000c0080c04082a80c40c121900502d0320917040c482442460042c0d943c030000035800b400f665203245210780c002c0020943c0c1c00c607194005600302e8015040400d2064881c0f981011644400104451810481c045a0641c5c0102407421542000c010080d003034442c803405c0000c04a010280c4881e1004140d213203071480b03140c002d61002c94405448003001c804995030381401600f0000c40d910007030003542808009070400390188245da00c80e5100400795026001c0300580303440240000402140d0b0600822200c0c400759504201a40c416000d548110703941e50704080d80001c1604503036005901b4818880b8002000842009044110b00c4c1c0580340d141e140d0300743c0040d01c0d01500c140c1e40801818041c80c0e03c1c00101c40d80c05401002680d01448880b80683d40d500300a0303959200e0510750405020703460381d4882c00a8500400260024041e1a10500f44400c83d02c4030050f0340e01c1a00c045003020380e1b400d04400141820800715080542c00d001803c07441c6801c1e1005803040c4402042d0031f00c140c08081d500a07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 557530350 1250 557529100 557529107
    0xb09060405211b010810031e0201091d04030f0201061208030406090204060e090c0109030507051207150e011103090d06020c1002030a2703050406030218041b08062e 72
    0x200242e00800c90f109038420900740e00450052404040c000740350800080c01586450120000b00d03988103146445100703602015061645802c0e404904202c082980010300071a49240c1341c241c03094a22224495003030500c3c0140c89a8952605513095904041c4d0800110303144d00c04901c042d0790018041980c4c2d0350f4074079044c0010603440000035801850700c2c9001c80d1207075070808214402c40074042103a55071580301005445001c668840280f456211507814000c500300391f800b0031038481c0201d044940c040d40b503800034201480c621108400003460160030304419a80500309585941f80407000d9071070030b0621000b01d0f2040c103039105e000c7c21103600010214040c1c1c4040010a44036a4101021526800c1120804c0098031406012204080000d114100c010340620f402603212a8151203071840c1510f0600154007135000109090041015202e13180c410707440754095202081001d22105001c60001c08020342100c002408040c0201d49400d00c10200c1d0b945205d80c0f4054581441d81b0740d030326055660048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 557531600 1250 557530350 557530399
    0x6011e0b07020609041404030e18060d110a06110709020406081b0418060305010e011112060f1305040303110406020d080901061703040303020f1f0c02070503030c030c070b09060405 79
    0x55800911b416000100407001d0b0014070f000700d1180e51440851102d09040042d08510707d80f0010340340a0071030200e00c1078942010321181485c1f0440c482e602c2c102d000c500080100711a17a10250104900444000c0c0c5440300b84858000350141c444110b04090900d44010181e000041454042c0342d40c540041c0081030b806019140100800e003244000c0b881040c0b1440094901d0340320440e1035600303020210b101e07880180503800d0850f0700c0c1806e45061080006600e510800068a4135030407041030b0216240e1502ca1004081000039001000f2400c3e04261400604a810701c5010f00e40d001002c0c0004c0c405154003044440b00f1102501e007109841d10340c1f04240e801031419a01900c00740c0c0780c2c12101c0200030310205c05403084038082e4003514a0040458485900c50000d4611200051200b0f5103050349100c0d140d20120820580344103c1d0181034588000c2071456004240d10310156101245201a4007800c12400001d406240c2441d1b081000071008920b6600880c01110301c16102e481c1d49058070341c01d92525 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 557532850 1250 557531600 557531617
    0x60d14010518070f0503060609130512090108060114041802040e0709080d03060e0118090b190e03070b0f09120a05090906010503042f120601060206011e0b070206 71
    0x200300d6810500107004203454185011240d5000f518000034200403518036403004c4070b40180240505a40e03001c10441e820f580108550a0107040d001e103880412402c10800304204c0007001c055580340c500e2400900140da00400c5141082114100304c000705441c50151001ca9440d449501d8486062241d40c84c007a000300d40000400e44114410081c202d42c0c0204104211080c03401600d50f1000c160034114103440301130041480013a00040100b0034590b907445101c1015180b00c0d0005244103003a0756440440e641543d02517007140031050b04621101444c4507102d10701020300000c6140400030707522507062500081120280c042d00c4400602c1001080c420641d0324000381c000c042c5d4032021940050070f90b8200301c00040c09921b003080001e0310380d40035031300701e900591700f10700c090240402d20020704044c14800d21030b2000304c0c007406c40007404645a034840c0e801da1000e042d015104c0780d03041050007840c06038164403150380c41c0c000000e40200d0740c0300c0440242c103075101c0c8030150341c0d01e10081c0007003119442460b28 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 557534100 1250 557532850 557532853
    0xe0f040f142505091c0602071112070302030606090a060f09050405070b030121031b051f0207120f050f030103050f1b03250509040b0a050708010608060d14 68
    0x390105141880e07885144190703200520004003008041c1c101e858441d02c5041c0c040820b00400100519191035003840d1140b4035001580c3e051904103503504006c0c0c3c0c10162089441d521656180c0d2118500b048080042c911000c1c0200b4280340745070000780e83da05001d05064080c110f840c0c00320f40c00003c10b03080040500700d06a07075426230035903484642c00140303c211004d948a000b14000411a085040d00b1681202d0380c0b030f00fa00030701107006011440f2009010a0407828403c0d418140e56442030800e10081c0399a01460140455002c21421040480e0040352000400342c0b040241d40006841d540207101c00840914041201c06183d400035103203031060f0b031034547d603990b0044000800c000c00014891182c94648003520b4130010883d0740014060911011558180c102010102e411402030040e401250b03d151001c030441580e400104140e114241e0302a40c0b005503010800c40003480c05d0050030340000562800866540c50408020210400503003d00d100303c0541d01c4c0340d010302c885c2400c0540441038190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 557535350 1250 557534100 557534111
    0x51e10050406060f020f070e061e0406090906060b0a14310312090b041406130602210c0304090504060f1a0a06050c10020a0909050a1a0f010e0f040f 65
    0x24409022043d613081d906005221354010544003160204102e803c4940e008a0702000741c0f241030400440318010500003068000c1c6200c1c0f50f640380c7e41c900401c00207100c0a04001080c041a040041c140c860a410101184404000d01c0f01150380c0400c3c00496042c00c0078480344c6074841e02d90082510307900c100701103408000c1e181c9810172801400901d14101d0f4450650080ca104041c6010f54201c0090b200311030034000140010406030860341ca654020071002004507140402c034620f885101c1038503400810050340141984081081c90300b01e454a050210702c1d80b1070400800f007403243d95a20490003500001616040440d0400000ea080b0b03001442c082c80050000801484030301e4007540414092a2040045a00004085000e1030859144c4420351001d01450700d50025003001a40c4044107032030401a503200c00040b6001584a007902a1000e19404210081700c2019000d0040c4581900c7c3c3c46139001c842d07070030140c0e03811408400c0c00480540300614034502e240300040c01003440f510850646410700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 557536600 1250 557535350 557535359
    0x115080318061e090f0301050f190e16080d110a261b060606160b060303300a0e0604060c141b0f160b07150c120609051e10050406 57
    0x70f001d0007140c10162181d4400345240003c15081c1d46081e0f0302c0c1c062900c00c5802241003144c1e0f08075810500c803001000400c0741d060f000305d55403034039100141810a086410b00e081c000c8800074400410207900518102605070b04800866032240390740d00d001880502d03a40c6403035446642c100070400030281700300401d60721049100d00c01b07049602a190252858085d4400060742071a143c400c2e82c2d61007910b0b020510121000c1c1c3d8811030003800c050004c0754588420701050311403030f0b108400a800315031040c032580f180b03905e48404042c0c407103030107055030381010b0034100002541140012007036406034000d9004100080c0101c02525043d01010250004900004881d00002d146250f03580c4056100400c4036461416211030325120440b40800b10605200010200318030f81030305d406042000c1c05025400c6e0034440500d01740f02111041640c910105003150080301c803c0b000c3e44141d02c02400b0008061019243c84100842003d00000340c011a0003606004140d6052000c8000e0b0050701003d00100025501e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 557537850 1250 557536600 557536657
    0x3060f0b0c0d03052701020702060307171510030b0a0b0f0a02071a040302060c011407080915040b0a02160b09010204051f08181011040503011508031806 67
    0x201c490588580310300b0004004203486485071500c2410b035904100580c6102001c01c28440c0050b05101803150b400b07000420169640400840c01282e0686034600101d448203045102e0980041480507540c0681002d00785588942410052011040c9000540f4828a01c0011080e28040d081245a803101040e103c14507000714000300502440e50b001c03142c44907581c80c01c1d0184110032400c8041e0900b0203020400060030f240000e0b0242201900001c246101505001c41d41d44900319900c03000250113505101c03501c2c8060048003010350b2295002c4002d40380507202c00b04400b034085e1900c03c10540c0082d04c0c02e185080c54050042266003d91030703504d142001108235000c0d42041c01401e2040240900ca88012a070f00320292901000b20344030315281c0c0d83c45440c10f24081091421529081c0103508080c650704031070b849040c0710f03103540b03510858035281054141421a8410741d440244070b2042003080c000002c0c00020b07202e17092225041c0000001c18140402c24078007500040007500305400503c0c6075001c0a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 557539100 1250 557537850 557537857
    0x7110a0f0c14030c0f300616110604031409091608090d090b0f04090e0d030b10090e090715090617060108060108040206041d04060501120203060c0a03060f0b 69
    0x24600862121810100b041544405034000d00c5580108000d60300704103801e0082d0348144440c03c003081980050728117080440005941d5851100079048001004441120316003101c15415162800c0141c032105507074a20780d511000f50024042c8403144001e00d40c01002402114000342025104142e2410540141d103d042c45800641011501d91000034a1004000900c4d5810703442550358030698600d4410b031410b16902011801c0e00c4d241041001240d40015400781130716803400740c0c008000e281000f01c00141241d03d83c4001500c9042203109810916600c07811407410f40e908072003c80000d0f290211441d00e840c08a13800320311544808000b107290a904007280d02c04a03020768580207240080a242c411000c0030898600380402c0528021400c3d5510490b40117510501c00780511b45469111480382500104000c040701e100046641080700f001071a000782030040070590003040e0294619400640c4a110080071800881000325005400c43e00ca030b08400003c1c40c1d03494407101c80d592031f6407615403a9032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557540350 1250 557539100 557539109
    0xe150f0a080114060c151003080c0a020901050909030702120a0c240201091e060b061912060503061306020405040c120c020f1c05070b0a060317070b07110a0f0c 70
    0xd140c042d41d05940c4c10400220344401550001504000141c508070405070000903000010003000440c1c00b200188602005102e80c001d01030040c104028503104202040d141600040e003d180c8a10034028003020000a48801c1e44c0e04854040c000f10005215902d00002c07400060301000d403140c0c0c00a0041d148144840807030704520501814419180707000d9081e01c100c001c1c002c0050700c0c8070303580d582c10000401017010500e224010214400a0510024080703410500c0003011844011440c6144150010458070003106161401c0c00403d103402c00094031200c000701090785440c4400c0381c400810040fa130441d005000002d0007040250b5007084010281e4001031040c02107649070100c2d2050f4980006028104030b405000200007511a01c1a0703120300d41950208002480000e005007000031300c500d441144200e01c0f481d40001d400e03245040c12420000100f50114a0348000c10180c408100749125081d40103c50b8208103c00c04603022020785000803048000d042e4045044840082060750884101288c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557541600 1250 557540350 557540369
    0x4032a02030d111c091215090f020a060302130303030b011701080606013b1207030305090405073e010519150602030304021c02030604051b0f03030409110912030918070e150f0a0801 79
    0xd60728cc02c0e080d1300f00d1050389001c000050a00200708000b03446900a074420031410300d040d6540110709006014020400e8000c032080c1e4100d00100309680d40c2c00062140280e21990240d40c0280440c2d0f10484414501c02100480f00403441194140361500c800031a405c010b08003c99444a6682c10000e05c02c2e0000084140b00300e040c940846e0304030340b00d40a01500030103881440d0800801d06200c800c1550b140b10180c0c0740300d00d0342220402000ca0203100d41ca10a46006032007203141060504607108442a4489510001200d0360082c00340b95400025a640680d050741e045000443c20070220700c480e401403000950fd403088000f04020454045404030180b0b0500c2442444121410304110135551a290b80580583c014001005142d5058100900d100503015080e803a0000d100c0c0415080b50910040c403100f644002580821401c080102d98202c00320b00c01c004403c0c0c100404014010002c001304203200d55606941800d00740606030031141030301c000440e1345540b400071a0300035100510900c580d5502e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557542850 1250 557541600 557541619
    0x501090b0117070c02010e040906060e07020303040c0b0d0f2c03031303051c0c0203030405070902160f14010222050904032a02030d111c091215090f02 66
    0x165001e9182e195807904140b801c0a00780d80d518204560002859500380d04009205440e0310141d02e6901ca0303008414003540e0086141401c040940c2da22650151201045600810800001c03800f2001c46000384c60130040201e50f904178284840d00904100030081240924140c1c440071011045656a890b001c1c1c540400541c1030f00701910300e91240021202c081340c501e00d0080020000744039030002d050b0741944000030165443c1d1018110b0032540340040b0000580d00c00002e101c1030000401800009000d2200c0941c649007aa05018000342d41883e00140343d000131010b18400c00110500e159241211003008546441d8a82d042c00501c5e4081c899941c14002d04101c04a420300f041040184290740540315040005100b01d0a170409140751a115101140140710b10001030394280041d20340d408907650380c01141494286541d003001c0c0009454417510a540d40090402034000740c0080465001c0c804641d51841e09051000030254011400302c001361419441008000240304d4800d485030090301d41d03841 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557544100 1250 557542850 557542871
    0x106030f0b01140301050d060905121e0a020d050c03120f1005031506190e0f04060b040b030c1e06130f1d06150c0105253b0a0306050109 60
    0x10b00c4000c014900503c11410001480181040b0000b200c100780701c0c0c00000345855a540b607803410401c03107a01c3d0040100d800258843d031070b2070007140d94120f181c045407030529228407140301179500c07400070316800d00340480450059828030090040e2100360110151880c0e051a08484a07084403038101c039441600030f4440f402082a080019116860b40d02e040303291100e0ba16811708104200f22a09401d60002151002c0400c0d48806400030a018034501c4128103920b06086c40e00f04261240780401c00d005903d001002c4d5003540c0d000070251000300c025922042554102c8092201038000071076415000140040c0502c008140b003081c0808480c140400300050544a0050010100b441d500d440d8410014001042d4540b030320606880c0d00c2d8080854084c5004280c0c450075095500889260344112807900701d0410b106c100d1104022400b01c41d18203024011140d203411231003040d64980c2410300520888000e023900d1205505400d0b06c9000a0a4051090392890b00741c01078042400740e44100c0b03081c01103520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557545350 1250 557544100 557544107
    0xf0501050310020c12130b1809010506090906090c04080f0610080708060103061503170c012d050907051f020106140d0b040303060e011412030a170c0708030106030f0b01 74
    0xc4030342505501800c0c0d00201c0000f004083c0c0c00c8070201000c15a850000047c408820034018030181c408101d501c5481c4c400041040b56588059201038040d903000c20103000c09d6540e240e011540004100c540c198991629041003009001d1500081581d100b17192035084130b0310300081d00520907540600100c080c5a12401d103d9219038543c4142c200b00d0307105600510000d01390750011595450500d04540d10603030360707442d40d0071403d00c0703500301001401000650b40b400100a0103a40541c2074483c526003806080c042d0360903024040081000e84860b038a50101310002403e010a8004103802420360340829007200c2605005002c03400c1400156103043c200284612a4122100e0404d0008006151004c0d8940f905048000c00a01c11010560307289000304003031a020f030080d8040c100210b1580014a4404144903590b0205143c02c0700540c4240106000207601045480070503500d480e0070449529440b0081c10a8001c2c1200280b0300c0c0380c040000304495600d5800014558116174091041081010040d17 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557546600 1250 557545350 557545357
    0x14100f0e0f060103030f0201090b161d0f01030e010e060703050906250f0216062604020a0512120c01020307170609040318091b030506190e0c09040f050105031002 71
    0x407550000401000821b01840440c05040860b000104c1c40c5602551012040001100c2c0b110154030300240040e019035102d07005600301894040310f07810403184080010003040214011034105901e031306243c01d140c4030a40003100c0004011040380e4080c10214006000340c641103c000e561845404009075075812803076080320386403a001044a035180c0c1144001c81e605da800c90200001c0d40b1642d0010007481c040d800e0f21100402481c0c2c0e40070314490003580c400003108032031440200102500e10a0001680ea1111a181202c20840c0d00351110983d560180e07003000805134400f4003601c0003051407600c40c84190021480380140b5540c02e602c0326001d07040c56002c1c44041c3c3d0701e10703084086000002c00082c000c0c01608290710301904003c0d5802d0740c840703c40c02a15200a240c82452a03c8400b0488517605030103401d4114004491403580040f1580039095100321520850f44450308450101e600102001c0c111201880041c100780201c43c10450410040c00303080c881d00d40280302d02480d0458855a40c403e9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557547850 1250 557546600 557546623
    0x181b0d020a121a15040f0204030b040f0606060201110306040c020a0203030f0414120c0906011404080709060602010203010821040315090b0606030603030d1d0d0f11010b06070f14100f0e 81
    0x40094004004c103000080548510950500e5405c200110102d21000002446036210b1200400449401c1c6401419200340358440d600703580c1420b4464007a24030100980303074460410b03140000c0c2d0b09841c68049203000c100038006034060000140c00c40b60031078944020415130300003030150321001040c601402444095030315511410340091196000514200e03034441d401510501d03044c1140030f61071076055451f81c001d602c596400d42c0f000720708001c144020701400d401040c89000841c207561501c00c44640703401000400003403003054103401207070101020040d10040d50304200035140a41244d560240182441c4209032505403045001482c04c0c50207c08a0344074203005030103113040002149540010313103c0d100a802c1507080d206851810b070401009840601310050b80c0300b10703424042038805045540324078804513941c1d060004000841d2900e1080380c2c00c90b0740c492a03074000c00c415400c21600110110750f490030540200c5401c0018200c80380c10115001c581c00340304100300d98801c14220340d10f841d2182c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557549100 1250 557547850 557547871
    0xc0d03080406021b06090a0506150306010e1009060906051c02060d020d14090102091008040804060e011e08090c010507020306040f0206071514181b0d020a121a 70
    0x2000280c50f03402a10a0041c40c64002c1038902c0d407008000e0606a0840701e513840d5501038003d0310180b0400300704658001007194080d00c04e00d19190007003521201c0502403082c40b420743c80003268030103604000c043c00a2828036402c000c000d84400031240034080c81d1040324814061201907107002d0480040c0c6400566004185d1441d01d450303284180041e4005a01007120560b071046400d091181b191602445044100300050741c5210760000c00504410341c40f00b02007005020020040020782100488040c3c42440c103201d4003001200c0d00481d4603070582c0a114110035007042a603041d107a005444e1900031040c0000741d4500f000c00000440b880e025209000e0341c142d11000c0400e020641c8a002251102d001a12442c902000c40d21808214840d0b0003144c61110b82d11989007041802c010441d640010034000f00144070f0070661003041d5901d8038101651425103101d0303003601c40359450701c040c02001c0b5806000d810389140c1c6c402c0180c0035a654800c0549000c0d001c0c03103450b0401e40c0b410f034131144208000700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557550350 1250 557549100 557549117
    0x6040c0b13060e030a0204091406010608010605120a0e030c06010e0a020703140a02070515192f03090406060e04180506040b1918030e100c170421050c0d03 68
    0x2100301c4410f44480001c0303405004903070754100561250f021b0549820300801d904600782c114010170380c1c42c240050707020404004007640140038003503018003119a2140c508000560780d444080f100801031100c14901240c501c800140d1803c1c00c40c0c04183c0c0c078101c5444102c0b200050b6034074520f500691094402c0100003404195400c09010b0120010300554105441200c9081e5216000310717400700d120f04005c4004460200d00c50042c181014504188a006e51510b413a5245900310540700841070100c01c03102d42e03010040465458207080041e6036404200410600480e661120041c02c0301c2040300c031141c0a5410f02c00300315001c071610596440a0380d4820000d00e00e542d0307a030311541124407018015420100c001d0f1140d210005c01030050707061008041d0313040d8081c41c80c070b440c001d0f00340741c40072404900654000c810b901c0c1d07081e040350020720410b8000843c1c40801d0101120854180301c2d98008082c00070352042c20301030388408030b0a2420f15500c42c404075800c0300649000c0189541028200a00044864 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557551600 1250 557550350 557550359
    0xb03010524010503100506030c0d0509010612060b010e1e01020705030604031e091e1503051b0a1b06050115031109150c100c090e0c0403060b010504080d0206040c0b13 73
    0x3d00055900ca54400d8001410986640c0000d101d5401038901002c4100d000c61100124035152050a4004681500030080540b8040441d080354203400302c054a503c0c5d542c00220720326401404600f481c10300051518542584c0081c181c05582d241148a50040c030402d0b07000310f543e080008040340a590103442e411350502d04040d84006912109a4803810049142c500055501900fa4041540300d590001e224a480c10622403a0110004007841c901709802c02003400405000c00c0351400f1005a00442240d03a44003803c429600c04038030f002c0481e00c820403100c00c001400381645c8010306a504564001e9061008104114285c80c1e2600a144041d48100300c105c0f41440c1c0b03140c544e6500300c5802900b50030711803a5040c95040140c41c140125500307894003400d109651740014004080c2a03003a0b450784c4a800c0c0020010914061404001c00f51303075650900007040c0c1c1c001e80a46000b07000d880300700d81c54102c1c12000251150020f81d01260f61414146000c43e049030004140c3c0e400c83c0c00f40f01d60f040b1003441d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557552850 1250 557551600 557551607
    0xf0b0424020712060614011d0405060616060912020d05030105090415020703020607020c030f030f34021c050a0f230109150509030a080405120403060b0301052401 71
    0x248484190312604000180128a40d40119495402400000345c3d243c90b202c26440344038000d10790715041012981490090951403c0f0001a080064400003110350f502c00102c1c0c55403080105160b0401c640d10041c40030040190442d990884c4110708001090700c03045800da9444035090b01500104406000500c440d04007030b0303d481e034405d0052021614448103600900d0032a80012300903001a00840d0400c6641c6404000b05080c0c1c85050b8001c0240b2000d1a88ac0c6071a4002e510300b0b00c01d01e200008020650070041c099030300c0c0f202c019a010007402001c50341102840f0120b1081280039800945101c010004c120207201c2419070440040c040f001e4203039940d07081803440b0050842d80c1c0400c1621150791040c01d005001c4c403107844c440001541410605200c09200c500c0980741049900344010030660fa080070060b00c50744903503801c201c5082d8582e40b40a82c101455507010721b40044002c0360000c14806207400c207541c41c0000340c000700322984440100729004144010b84000c000d29a00e1b000203154803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557553956 1106 557552850 557552909
    0x906010f03080903030c0729031308030403020109080a0c020906031c110a022205060f150d0609050f0720072d0905010f0b04 55
    0x98205640c1035900580001045810003252920702c5407000c2058550b80c00940f4251803610762126000350340041010408400b80400340800d648040040080703d00842d420740c40390107190b0031622040c0c240d5102820441c1103650340c40c040300100354850050041c02c81d0656410400740c401c0c0c01040726a440140c0a1440384d08107503a81400c860001c4019105540e6600300a0640f4107600485810800d0074080079401c50466404024840414428560259085101005980c44520078090713a141b008045940041441d10b00c3c0101c0c0b500c40c0d0203000c00b804600e001290140d02ca0a803c0d094a2040d552419004410001c4c80441500000c120404030520368042c010741d0070000b401da40e19985840f076501200110482c02d00e5003620148580042c00c0807104e038400313040d40c505003000284002d12580d45048060080070910340d0400080341d0858696034203146941d00c040150703641d0f507203 = true := by decide +kernel

theorem cover : BRFrame.Cov 557374100 557553956 := by
  have h0 := BRFrame.cov_init 557374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557374100 ≤ n) (h2 : n < 557553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
