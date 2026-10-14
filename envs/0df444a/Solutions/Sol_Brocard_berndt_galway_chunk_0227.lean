-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:35:09.816584+00:00
-- url     : https://prove2.me/submissions/954f8669-c307-4995-9830-c185a10375be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 40647486 ≤ n < 40827342 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 40648736 1250 40647486 40647491
    0x2011103042127090b06090d17070204050c0406020d0f0206060f04060314010b0f033c0d0206060406060c0308240409050c03190c0311030703060219020d0f170a 70
    0x944001c1c0d00040160b03d10403010f4180500c81c1c90103009200341c654415581e4492070003841055560307100e485018504503048144082c1079150105140103d101e8600040e401501b05010402e4038503009008100300c4120380c0c04c4588280400508035100c0350740c50302e0080141c0140011582a103008488001125002400003079402ea8075500d01480e40e6141c020f8402c44d035120301d81000607207010094074024040940192403140d408040400c402e0280b6030050b0703040c80340041d15a40340d802446030041e00368031050445000e13480c40d081c082e6507580c084668510a42c2410070101d11107115100d0082495450f44a410395516604081100040401086203800b07840388006807150b070b035034010504845d0040e0060318400102070241810325070340e40b85040c00080d0002c0c88034001aa241c462204a07900225803149010042002a04100190340060101400805c0b000080c001c0990170019058007902140c60328031019100741e032482c000c0c2d6005008912084003101002c050f005001e58801d5070110300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 40649986 1250 40648736 40648757
    0x30609030e0d0f050c0324040501060b0a020a0c1401080402010503060414070903020a090501050105070212010e100509060601020a02090601030207050c03060408040617040f1403070f060507020111030421 89
    0x80394490303440910540f04000905548010301405005824542c0d1040e00903008000ea000c040d00440c590110034888185040d10003c1e0034407c00b940180c0141c0343c58200c0998804c52208002e5440c0315a6106540c801700360400010940c015042465140806031200005544c0d40d80041d6800d0700300400c6a604103842d02c0e08090701c0e01c03c601d00303d441441d25440d0310441030304500600c1074929103030f00318220151404005000c0307603800c201036071003842c1d0407100f40e40408600d44029014080762101c8810600c40c80f40201c107445866002584100c40310012602c42e60740384001240e890b9542c0c80c01030f400c11201c2020500075442900123150448c0640125070f482c20b50200840c1c5040c2d421601918500710105042c00702c075078440c20b59080e640015003440e180c1c0c20940c55191000c6584a07000340350301c0705d400b03454252007814802e640555800514040c07445000382080310160804440c4200194604410b92a240340654140da0045801403600f41e40b4451252840c1043c041241f02407041c032004450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 40651236 1250 40649986 40649989
    0x3030e0d0f0b01170f0120030408070501020a0302041d04031202030a0227010305070903080f0711030105040f1104060b25020616050114010b0d05100b0a05030f07050301050307030609030e 82
    0x542c24000c0a503000001541c0c1d5040c1181c500f0b1045034469814943d041c2002038600b0b881e180b4402c507110040011843ea00d49440c540180750784650301e0010440c1d400402d40e001010f030591b000d04220b800711055202640e03c0a408202a183d00300e07002008030300910759080001c0c5440c5d0265602866540c001490b0181149200300b88540c400b1110525564001c3c03d10004d5a150041640041e9142006c0041c01c2c2541c1c1c826001e4040da0003040500c002c007080c00002c0c0300f905154a4103e03d800340c020407560929042081c001089041c00703803519070500c1180445401c2500c07802d000c42d4101c08900e400c1c4010700c0c03000154200c111011411045407102c5550150351084001c00880e00b41160805440181d803800c0ea080d10031052052501c82c8007640100038040410307088a010310860ba40008855841e0440e01802d4038040e000200f13110b4021408000481d04403000314014010300501040c1681c2e0307154200d4480c842401440d4160b08454010000a64180c001c6a0041e00c282020340081d8134000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 40652486 1250 40651236 40651253
    0x140a11130305010207150203100e0702150421020c0f060702060403061409070504020406120203100e0903040620071205030405040906020712080c190219050718020403030e0d0f 77
    0x400a8035281d41c0011a1410032180e0f4199560000c4100019408e41c40c01c101e41191344806441003680740b030440c10025101610030703c019544444112074088442c145802c140301c3c0040c0303281c07072035941000012040c1c120500020302c0d4269401c0045c00d41c120303200d141083c080c094000320003c0760000c2092001000141280c06070345503a00c03595502050b249800d07010140342c5455584600d01917803040006200040e40140110352403004440c000d40d0b281c441840040707402c113190f44042d220000010501c000100c01100800450b003e990b5901c10080071040720075100e0441c4111552154420207041003190500b000c031104a0340507106a90810b69903c1c0171505175402c0081c06c8a000758001403c0341000801e0086041d1103090b45084100362130300c800394480c24441c459000841400014000c43e00b20720070010f860151200200c40900b600180c503045503101d031680a4039003c0c0d00100e07240c0f041e40780c162090b00d080700d42680d1508603406001060140c0d09074035140955601800078034150101d9400d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 40653736 1250 40652486 40652489
    0xf0909020c0303060118030b0112050f07060e01120e0a0605040c0b04031101030c021b060d0605040f050402090615040e060a0902070507080601120f1202150f01030209010504140a1113 80
    0x406190f591401100041c40040d00001d0b1b201240d64008041c40803540e003251a03415a030341c4a010b41d181000ca4107000d468002c1b0344040c1e003250b101d00800810300c00d81c40f100006101d042a22203d00906001d07812070203980c003640070050145d0028103080041900394102a4005000381d03000d004c4aa15254103501e2940709420a4482d503024a001d200c03a940c0c1846074010390a0b0a1014205480106420703680060207a9809413195002103041c0d0424102e652014000300f000400411482120f0b28850025110889050388241c10003400240d107030600703001850441c60511700ca10f10f03250404c0d8201c008581c0251000b0b410207860784003c9040d0b40944002d0080c2800b070001003403518a4950400e1404505030000d54059200241110000c0c040e04440703e1819400880d803246013803000c2c400c034a0005c0da50001c107112010003061000b1240b0206006050300d00a41e44816680e13219828001917807031400e148481d880e016400030751208a20760102c903c2c50a4152514504040e420910551030b949 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 40654986 1250 40653736 40653757
    0xb1c08161a0c0903151302010e040b18060301180f0f03180905150402040506040905130b040f05060c03040206030402040e0705040203010816080705010f0f0c06020409060311011706010f090902 84
    0x41528951404110018416014820b020841e25040c011031b08401c0b5402d00090620a061440d1101540e0751307001360341d544a02900c0b0340c103254440102d00407035001c00c1e25914040d51070003001d40750602070812070b42405a001284100c41c80c06682d2240c072000c010010a50070490411041640c0b07103076842c540b0004150910012a0500b868100c20b49195000c090440c8901e20410081110342ca900c41610b00710b0385070100c000355a039548062000809200803004005090740c004000400000b0300c80344444034003c01c101c0c0c1c1c00742d8581110018612065602a5001c0000c2c00010014a001c0d080070003000800f2090715500c5a840e40840e084c0d82003a0009405500201e107510512810b4885e010001d25484006000d4103290000180074180200106010005180001030f0440d000d45440300a4590103803045544640e01d005000041c0f0040c001260211314200b4220b116600c6a007003424403070368442c0f14903030301c2d02c0711401510b410b101c0b00b4505080c07000514000843d082c1034030240140e0840e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 40656236 1250 40654986 40655011
    0x1b260109060203180f010b090115030605040603050a051c0909180203010c080105030d020601031a1f06050d29091801020c0d091505120a06030b09010b1c08161a 70
    0x40c04d40c0d0031410040b1884a0b050140c0c500304900c0740316a00c0544881c119030380800e0398410100c400000702c0c0500850342040d07030010304086001041080005014981c203001d081503400c0c1c1c0c030900d034000c54200802e80c07005002071584602401904129405101101440d11848001c0d5845901190a41d40891101d501280021004101c40d0909000a0401414500c060030a641c15030f518084030446080c1041c01c2440740400290340748a40c83e0b109125452a99195034041e95074445c000c0c4175030300208c2c4203003515040440c03001d0f5034406052401c049444400a00c10003c40c0c0030240310700210001c0c03410614417409d46140744410710a100034281030189802401c006820b00c11302411a002a0b4003c17000306405210210301c0780c1e4800280c80e0000c05030b00c064641070b1500d0080701d029101c40c3c1c01c00362a400300c3c00c043c0038079203805500c01c02c0802c0e42941d8641440c520701100fa43c805881e090301410781c120400a902612100140c0340038601c1c0310b9405a021140c485540c018030741c8007160382d44420300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 40657486 1250 40656236 40656271
    0x405060601050406050322170c12090d020409080405040f0905060601020c030604030305150a1502010b0303090609040906020c01060b07050c030102130e19181b260109060203 76
    0x1406000aa500c50400e0900ba4038040c0b03440001085071000800340c81d12104000d040d0084079803c840715072401a080203c2c071010480740c62005070581e00090301000c06218850035031419081c000c0a0340c80041005140301e041009940a000107000c808400f00c0301e0100810010410b6a66031150610464400100060b05040e614203d464080c010741203c0c1503612610604046035800214281d01c65414030f004103241e12070102e500d00c0400454041a40300001d15004282c3c03c0e048186c4111040c90350307000b4004d4504501c1410780f6481851003080d000f0380100512350031400c2c80d410910050703210303c034010314210a00c5586c0342101c44503004078220000000d1200c0600ca0304025090310314008030021481c29041136002001f4440520074042e030f10682c000080e41024640209400e0014003480034444e204c00212403003036080741800100e80000e83c80002480c018011506482901c0d0f409516031003e081c52041d0481c2c49401040400300c40d03403540309050000d135060014600030b003100c810320041035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 40658736 1250 40657486 40657493
    0xc060b19140418021201110a030b03011401030201200703120201051f0f14040b031006080f0601030b070c0f140303060f041404030e0a0504050f061906090303030c03020d050f04 77
    0x10164000714512803800d001c60312010081910b0350148040d4100d900c140300180580761980540f294000034488039801040c102d044542582120410200450003084040360346881314004210a00019000820100c007030248106004a159400910714088036040c50341c0c1d595040c0144186500040181d44a03000c0c0070004d41c1914111007074080c103000c590101418580500b841c2105481010041b09805500d11126102d0394444c00c03042601070250341c0f0710300c040c000310340180800c1e1144407401d00c5072454600b40340d10081078027416240d0217080241903417a0f1043c22580702c60064001c0d100881123417840c1e0005610450300c6031011540902840e21ba2410f0402c0014942040700d40380e00035420040c841303441808010710300390700c02e506040c0000060340240100c1d021a60701d0b0007482d0405d25010900c100a2031490321103104040c100c9840d06081d81d06455844400041d20910b004035200c0700050000030300a400061895819190044c10f1000d80c04481c01681c0307099800e0014081d010080c071060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 40659986 1250 40658736 40658759
    0x305010c0e03060103030c0206030a0b1c0507080102070803012d0314010c030606050a03090809030d02010515010215071b08030a0902030106170309010806031c05130e01030b04030c060b19 82
    0x7950100c025004a41c59500d024160001d500d80c000e2244c0700c004005040706406601015580c0c00140c810000c082e041c440f00c0050401c0e80d00d040d00c007482100b100141130181402180c0030581e1004042d4256464500340076098000f021940c1c0c101c141e619415600f00c130140110130021070045054840c00d803507510000d801c49100f080040c00b01400d100041c4084c0c1d401200f180c0d04107041c0e10740054003213141e06148a041c001c1d04880b6030705006516003100b00540c150011800303548401d42c900c00d515503110045e40d131200541010910350011100007000c0718000d00703500c400440840300c680d841107001d07030b0380c1200c07580201c030810602581d81c203008080d82000d209090182c0415003610002c1d1002200655503030041d0414a41044000710005078a52014400c50144506030320303048000315922100a0300c9504500143d1007140110640015240040300105048179005600d109070340c1c5039911b0031200c180c01c002082e6070584d01c81d0380c0100305443e04003510f10080365070800b00d14a50b0411002208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 40661236 1250 40659986 40660007
    0x1020c061b07170a02011506120506190e070c06020a0801061205012102010201020d0606050a1e09060302030a0e060103050706030e2a03210405040608011a04050703060f0305010c 78
    0x75a40c01c1c07152034001080420020b00c000010200c1e25155101408100c3c054500c0c00600d43c10100380940000318a90000703544044881c0040d801c3c00955142014054008241001078030103000d21501005010205001e0b80d4001a20b850680e014203415203c140903a40441842e0000850b0b090041100d9031b40704102e40c0d5200e40c042e070f0900107035140003004140d0780740ca401c41e00c0400101350b00c00c41c01c6a000350304454085111400c203001103035a03128082d00c0c40d00201503a10104442c460056a11141c0d035680007201106515007100041c03c001e0102c0c02034100070041491181e6a16100c1c0d201c00c000c008960003544604018030745117082100080a6030304001d140c49040d8048c80800c054103203580c5854185180c906441a0304214500c0040c1c9003c1803400780c0d450300306118000001c0848101c00510035501e040e14180480c0c0c2d03460306e20900320787d40118100f40e1002c00100242c800d181a801103608032080d4071f40892000e8a910140410784803030707401210035079511140c6c941d0326a0000c14400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 40662486 1250 40661236 40661281
    0x90905011e08010e0715090e04050f01050711070603020304081c05070216140d02030a0803010e0402040c08060603270f0c0a0f030510091a0403020d0207051509090405010b0301020c06 80
    0x22010880601c805e5981d070003070049420420301404401102480340817043e0050280740b01704015070030300742013682e11143e62410542c003030b5091000041c2c040c1e004140c103400300541080208200c901d880d03c102d00940000e00216001c1c0010404046051402c0407481c1c0005826000081c113401c4c450300203850710200724128403056400e20340802040340d0800c0c000100309829161502225a03038400079041a208410041001d0030100002c2000445c0b8484070b032140e40b0940c3c2c10031041c583c03400190741a4004031141030340101c0400010f21081100c0e5100603030001d44807034403800d507500c10a40c0d07410071412041d02c0c00e080d4030145c0d0034030319860035545010003031000f6110a155181142c84142d1910000d034407000c0f80c0e60b180e5040004008410750984500310140c42140d80c103041c1460000d4880620301c0c64040103206440002c034951034910b090300803a4001581d824030300030072403082c4040800e0062041c0ca280d542d810706816107407404c0c00142031100401c40604003500d0515180b01c1620910b203610f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 40663736 1250 40662486 40662491
    0xd020a122007020303090301020403050706090501020a0c05010e0102150a0b18040807170712050903010509070b0306010c0f0203010513020910080303040b091906051b070507030305030601090905011e0801 89
    0x9030103103250006080031421049003165561010b900229183d4481e01c03203919003661000800200340b00e070200d103503019100340d0340d0784104441e43c460049a40e9209604050400c2d04031100030000d66000b0365903440c5100060042c0d030144242004080030740c1c10300311030f030031500c50702c1e10140441440e0003812445981000c01140519003019199629903004001008225903c1008405001d02404098840240c0d00141a070841103035060000c02c50741000c0f00d258080d41c00c2c0300100e60b00c1c0c000840e0341d01c1541d1000303803517034103581d42e42d0011142d220074010151041402c500f40640583c8003070140c1d600ca1402804083c070803203c90302c140105202c00400d250303001c2d4402e110a010480740401283d400c56009035550805840c0d10002c50b0410004210081c3c0306c584055111040040b19080288039000d0b07100796480710841040c460301544035200e001001c981000030207000103030260024540200d810315250040039211415a41112420781040403800d007440220b048000d07072203104070b000e4200c04009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 40664986 1250 40663736 40663751
    0x105100c0812040f0c0f060e0409050c150d0204090e0705030a0305030118060504091a090c060d1104080f010207020f270402040e0d1205010b0a090b0309010b060d020a12 74
    0x1000345a020b01690710002c0011400418140001c900130074107982e401c003c1c00e1150555403040192040c41e00e2203600c010034040d018070480c91915100b2a500190070070050220382950108003c08100e10481c0e45a0041040c48000d090710201e20241c40a84805031780000c40424401007686440e5113613200758829880742035464002a48501620304482610040010300100fa207005ca002e03001d983c2141d44c2142c42e041e546428405d00700d01c03410151004110142c0242c80c0d51448030b03201c41143c410380c1e820041c204198140d01c80c1c258010208042c1c040c1c09542000e4881c40c9040c04e1100c09440100d19039008100042580b800002c0944e1340f480c11185145d500085e507052000e00480354024510041c2e0396400107042d03441d035420084180e0105010380b561500403910146c810921481d800c0d034042e207042c0022811502d88030464070072140540755407034880e1800002c941154030050021380355548503400e4415a88402e07000d4801815450b03000760b110800c00f9001080003486003503030444142440300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 40666236 1250 40664986 40664993
    0x901060f060807051608070b090616080c04050a08030c070e01060e010c06060e0c0408100203010b070b0a0e030a0c1101031505040b04290a060c050c01260408030105100c 74
    0xd080448880d810100031035598200251200e00032021110364000c502034a0b5020480c0d00c80003001c00b6440ba00c024851a2a50400c595481e00200c4000c0c801d0303500d1007858030344240102040c550245081803200e14058541c00440c401c0ca040751b204a2442c0c3c03002c200d51010349018803004018259969a6010325850488003c0c0030300c0d500d00d11203042c0301c101d001c2c500074031941c0e4011f80098030703e090060020342082807242d2144c1e4454030699609000d0712980c208041070a0003104d0480c0e100c9d01605041c00c1090311096000c41021703081c2507070346a0740c920661401a09101400314544281c0315094940c1803824401c2c0c0ca90801680a410545445032411403418016030315020340e4401e480005401c1818004a001040460313032496803a92851072000704900b80300c00e83c0e60030714019038410340c8081e40c8540643e43d02542d590003c1c03032a003100368075081952007400c403030800704010780c0e140c1c0212115155120904009507030a60b00303480000018011414000d540905040700c61502c000413200c1c0d0b07107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 40667486 1250 40666236 40666259
    0xf0307050c0d0813150f050304020f120712060f050105010c02031e1203150316060804020f060409150303030c140f0a020c0307090f0506010e030d080a0f0e0106050306090106 76
    0x110741442490103080020500c0030000c1030b20040008503444e202d503551242400100e54080345d403070b1000a00d00303545500a1600c00d00569000c1c0351301900e0140442c0f0342100300422401c01c6101511188900100055880622030110301418040c04000480352800c629000c15554142c10142c1880001e135590740050720005444400c07805101d01c14401055007498040c01c042c01c2c005409003601d40801400312900101880381d584841c22400c4400200d1003030420750841d0340500c176090214011800080141c2880d6a811884c0c2c10001d00701b5240c9615440c2e100c044031403100026038040500d00080c400c05400d8840c01380071304200c1c24445c0b91401d03000c0c043d81d050300ca44d00c8070b600740c031501003810941c090003000b40c0300040e03a00906032040252908022402405c540002110490801002c031710954094044410780090190140c010006140c10641d0490000b800c52444180e6035400100701140300c0c41812100b002040011810a01d80010103161000240941000740d00d0881e0400a44c0f2005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 40668736 1250 40667486 40667503
    0x3030318030d0908040f0e090613020607080708030604050c0412020609210d030c1d040b01092103082202010c05070f0b0910020106060f050d06030807060b030f030705 73
    0x34984200100025203100307055018101c9180c082c40e00703101040041010000144c0113890031000c540c0b010954940e0758890701032090707a44244542007000401c44584502e2403203000d060010f401107140114541d941da0155002c804240c9460501001784a5186442d0203502d410240085280f801c0c242041e110300843c84d49846c001f071040e200000c0c07004103a2642c503900c00d19000001e23407208540d034003044040d0301d42d81c031890300f070703001920700750030760785418000d0480d41d01c00e000460584407040c0308181031100400c10741e150581403118000e070000701078402550380100342c115a920020100c510345006000e14801505520b4400c4520046541c801c08054210541e2502464a0700080c08141007003400e040054100170050071944102149602d1100c0003484d0410007a2100050304010000407400c0750340c070340a0a40040c2ea440c03100078082e41b086000d45248060b8010020f02d4541c2c91b0b40b0032405900c201e4003244c1072078407050400d50915085c04000d1540c50200b018604d8003006507503440d192801e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 40669986 1250 40668736 40668751
    0x90705060903011b02010203040210110307080a20070513060b0f07080f0a08061c050604060e011508060108070f03050a030c1514041502120a0207030509100f031406030303 75
    0x801e410405550940010014000c602c09000c42d4003203102c0700a010350b1040310203030300403440d0560201c01c01d88601071146102c41d50307002550811500381d4800c940e65010480362402c0281c8600c0103060066001c0d041403091020030020141c0a1410003404042e60010004007100da00c1c0c034a04000e10320b0031104031182c002c80001d0f21a901c00e00d91401c210b0900980e402e0b00858400030135240e811903001840603001e00400c072074a803a031140c0039210000010032248010000e40052000c01c0c0002c106800522030041c40000214414003843ca4040c4c4480c0030741d00880b0320b50300c100300400c00310030103004040144c1500d0f0084011941503072909a134a058407500181002040c20300740003804180554081140b03007a0000b800b055507410002041c24100355002d4035507256904075004030303d280d031003110b20f0000e05000c00409542c03400022402900240401d07030900008011001c000e41c5c07040c0801004901540310070a0350300e400c1d1001401c0f40c0c0d580d0010010b11002105000f4140c0c0c0010507079600484 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 40671236 1250 40669986 40669999
    0x1703071704030c060306082a01030506040b13022203050d051c020301030807020f09071d06090a06020303090c0301020405010c150b040c02010605010e0301050f01060c03020307050d080a14090705 85
    0x103000d030030001e1080da4005400d20141c1d0f48041525603064000350201d0f94200c04650041c08030401003545850101075102e103e030101c50f40a04a540079411069120b20000c10014090340d02e0008a4107111251340080045940004c0201d14098940009500c20a025801c00b80540c155694540e440c42c00a1003102407080101d407040382914160f0030301c4c4115400d00415074407540e580c5050070080c7c20800e8102c1c421820001d0b103000781d082c0301d421203100c1d1229944190078240150185205204440ca146801003010055070242d526000b03001d200415050b402144d4034604078840608054488008900c02e0740108010041607038080304011030140c001d0380541c9451514003021004001680d4441d40280c10050314140c03458042d40000d040358401c3e215071809038074110405007240e508403910024004140014440c461054141140052081c0110303443c7c14296100d842c640044968100c0010780700c50108188551240903103213401141d00407940c4c403800d11400c0281c0350702c85402154007460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 40672486 1250 40671236 40671263
    0xf070c08030a060b070309051f081b0f0304081207140a050306010507021e100305010e01060e0111010e0a0c0501020f0d030e030f0d0b010e0a08060f07031410090501170307 75
    0x1415075015000400d50f588446076217a996160143c0401d0041c800c103881406217540710310300d41d40040055191304000355204211a65034240121680c00450226001d04d4014042c410003004410f00550041d4003c3c000d13a522000d42034060140010300416400801405c04c6961108002c94000c0e01c0e004400390915580301d580307080040700d0500801d000030394011003c0c103d440b81e000c440d0504040340c04003550b0703810443d0a10041030b402d0321001c0c071407075221001103001005030b203100d010074125003001450300280080100b0165070a581c5002c401d980f46400078007001c17040040007601440202000e001402e0328409203003089272501d00c2401041c0a068a820b101c120400c0d0600460328040e07103440c110303515203a0743c0607090001d002a100c0ea50101e0000d54141c01980f400b0343c40c00003140c009000905c95541ca0042e078501d40c00c4081d2000d010300d600d500e5404180e0380350600180c4110004091510f500d4074006041c2c058401c1a4890307a01484400d18110f200c482c0402100c84407030308082c03000c0814 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 40673736 1250 40672486 40672501
    0xa060804020405180d080415020c070e060301110309030a02011802030a0215040801020c0606030709092109030609030804060b011e050c0f070e0109060b04060e120c040f090b0f070c0803 81
    0x10f6500000313450601070410101c100e42c2d081070b007a500560045000000c05044d61440e18100d1049015031517250340240d000300000c2d01031041e040d0344a02c01070004142401666107403941900305030b48628444e000403c408541c03682c240b0843d0316031121000c0c9a100c140e482d8010176118000144068000c0000c0511020840300200403200101f10203402150b480c030010007a0743d1110030940f40d01d4400e00510070001440e5070b640c00740510346034100031840c600c940c50844a1000d031324a040b0000501010107c004003245c124402c5000d40340c029240e5031560301e014130740722048031003118155060110f84003100c40000303d1540d040c64100c04606003643d035180d080c040795140200088040c802e5104451000c500705d070742c20407e107040ba4060700051001c1604c1ea001400780d4041d070302404001410410440c1076038508000d800c80060b4004003941d00d0110024046000c1c6c403030307540c050142d250b00d440d00c000c2003000c002d0b901c0381d10414066043c205414007003801480802100702c041c0141c0004001304404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 40674986 1250 40673736 40673761
    0xc05060d0e060a020a090e09030a0813020d11040b010c0503030c160f030c02090c0307121d0703050105061203040f090518060910050f16050a0504050303070807020f0a060804020405 79
    0x301181070200d4500b880d000c15410084c1d0b118400301c200103a00384c840000e40071079841c241805403070720402950070309603801401c84a250009000038503102d82203c4007009611440342500360345004410780b00d003040d020300920082c1c0344094181810000640c80d244003044000c026a40c1000600039480e0782e51003030392002ca00ea804004800751840a050f418101059040b00054a00c41e2003540d100d11240c0c0d800322007480d640001c41e1f0700404074443c0c085510703281d88541e00081c282d4100301d014078a545100340309981b4098880d042224107170340d140140403292401c4c0420110604044000798905414444407480405543c40b50801041d100d601148210100d20090010244944100c1e100d9107010b4907983d965140702d1004400d00c918200104401c0882c800800e4480e101000c0070021454003103038200c400b0b40c021025030003081001e00c4040f60568085c17000b011541d000700080c0d5110708a9004101000012801c12803050020036420083c0c540c101000c030b80d105404440000d150765502a90340d03407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 40676236 1250 40674986 40675001
    0x102010b0a1401090501020d090e0403050d0903031e0606050405040203040303090b0403020601030b151c1b080109060c020303040203101a04020f07030905120304030f05030f1902060901090c05060d 86
    0x380810040c0d07001c108806020420407800d03800342d0358001400d0b80d41006a80341e040204c2e005000400000003400030480501103160014800c0c500706251801c5503022a0444524200890000744c0700d100e0400070617962600101100c150140c200b001c0c2e0b282900c050406d110707030b02c1840c0c0a16000700000382814001c0d803101254541006107000d492030903240094582600b4003040329528561b01c0440da160728468030304510034070041d00c0350110000b43c3d89070000c0300da8129000c0b5100c000740f44000401100c4048a04000e200000011400c88281d140c100140c0d4010450300c41158028010040940d40008410001c6015680001900c4c81801303008404120400f4400f5049400011780e00e40c0c501c07001e4028070f5028080d44e0b81a10b02c5458004020b110000504603102e02d90044c04248017160b5019a21000e0500c02d0302101e203045c0361030481d01c20507080f42d03a0f0b080350300c400c0c0c107c055100d68050181a07800401800200b12108440c1d0342c403126141c80e03024440c002c0780b003c01e503403482d0a1142e203d2103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 40677486 1250 40676236 40676239
    0x6030b040e0a05060103050d090b070b13050f0c030c0405091203100902040b0414040629190908070807050105030c070203031c050108010c14070201030c091802031e04200102010b 78
    0x181001158100f0070350b11882844101d8803441000f0b003e00c0b50a10401e0414140c4817114000d91400d03280d5180c1049500014200e900750304410260180000c0041002501400c0003001420741d004203213003010f051003030406a4a015078203100400202c3d0401240903d03203100800c0b038040c1c0702d40703514440f4580e00f1442d40040300160710024011036140800c2c0d0140007151240f18502e039420608500b44030a4410601c03980e1180c40a1035105580340706207a802d00c007014002d820207404e041c0c0180c18200355040710210100032403581c05050201e0f03482409114040e00b005002458214a4000000c00501c00104803900300c013800b29116086590620860321040705075542020905540070481000b42000c0c4500d210f55807802d4001c400031070250310f80c10309120000a4032414442207400650290103d0106001005000b18010908500100d42c000090500c0c650042c0c0342d10f024000038546c540c8843d452000c03002124100700001e00441c80304440059040040c042c02c00071500142e0150507041d0303145 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 40678736 1250 40677486 40677493
    0x309150f03040605100611060f06190f1409070207060e0a0b030906060f040b1c02030102121801060f030503090d0501020906040602011a01090f030b04030c0f03030c0e0a0f06030b040e 80
    0x184200c1e6084130780203088000a8444c2240d03111001d1721161052100b81c56540c000f4800120310400c3c1c090050380c0044003410350382f005407000c41c440c0020300c855000045400c0381075074184614820061411800c6206807002c042c0d40c2044607000e980e840040c0708000400610b1113604240392a280080d000404031500300b641c80e801d101c1c40d12b54482508031083c9000710302d1720480e0101c0c0d150038001c102541030080c181c50150341c01800c40210360b840408080e6015034081000d0307114030b0315801c2c2040c404d04019860001001c51202c0ea5825115594424078903087c00074814804100c0100c11540c0a40040326560700107401c92034802d000e40200008154418404640054aa030701034004003210050000f034440c503c0008801510010b50078041c60b5520305041038103000003280f030070300503401900030700305604107508a030307149842080c00722000c40000b6142d460510b420303038102e1a13104408000319440c00310b060400709112212909440b03000d042544030382008119440c2c030303444000f01041c1e50003035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 40679986 1250 40678736 40678741
    0x31b010509090708061008070e1903080c1e060402130207060603051c030f0c09060c14030a0e04050703050702120d0905030f190905030a2414010f05040e0309150f03 72
    0x10f841c0c4541121751a00500101d803801500910a0301c4c000e11603080b80c0c031054446414641030044085003109142104403100c0c80101c04607260078003501007908020003c02d603070307000021500107040ca0780e1030200040d48a0024040141e070340000e030002401c0d1040d0010b8a403081c1d4280080507002c0d0343e10162560150841c0014083d406412000301303110b950300d041c0003886020660200702c42d01c0980640001d00300c4002804542e00c203603401040140030301c2042c41181201c800007810347c0d001e5031501000ca07001e941c0e880c441e41001e00134681d0004190400f00810b140c4400c0294a07116035456181c49210000f50f5103a13200081d9110304030383d6400c0822243c45208074049a211540110100b040001900034207401079449402d40d84155000034029120080456a03540d80c0c070341c0900b4403052814002e0094012114041c8501c4c0e00720700800762441c0c65949006643d00083c06d041d04624000e500302104005411400000c0380c1c00740c08240c40d81d460034803502c440c01c41c40740104270054403c000700009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 40681236 1250 40679986 40680001
    0x32503020d0f021f110304052b050d05070204180302060a0b0d0f06050f0f01060516080d050a06090c05090d110103060e070203040302090f06010f080a2004090605010905031b01050909 80
    0x105114181d581c4c0b43d0b442105e6440c400c0565030b007d50711900394400c3c00382004400d010110f805900c03005c9840c0b582416001150b0303640d40c0c05c00854051a07000030710040703009820361500740900c0b190801c802503d240c8030102600c0082d19a200205900003041d1144424070480d00e40b0321200c41a01d41040c651200f4800610b8a00007900003540d604280240440100c1c064416880840b8100c2c0c1d1545c41c0c181c0380400080054140105003481950301900a1106240c00710701c45c001c648c841c0703400e10300c001045820a468401150303402400c8104009040c00906010f84861034640c1901d5006040400d044012100480c007608142c0c112081c42004a8203200a954000010300300340ca02c2110b02d8055503540ca4002c0300c6038034088a189000607048041411890300442c102c6407c06031030360011800ba0f405410701e140031002c400c0c808071111000501003100d41302c07903c190400750000340b03040c01e0b00a25000000366981c219991110710207003512025101ca81c05002200c40e44800500b0002c202c0c07824030b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 40682486 1250 40681236 40681279
    0xb18210d0f050f060402030601090608060307090e0d02061b0412050a080a0c050f030322020f12070303030b0306070507030f020c0904060902011709071e17060105032503020d0f02 78
    0x19255000c94124101256281c902802588d100d01410b0f91080707000343c641002150340460150905405010741503010030117011a0081c1400000a90000c10b00e608480d0802403424400410031031240c81c0801d03c1c0030340384414500703c3d41298990201d100501708a800c1c12400c041052400a020b103100081031140c2c150450b52400003d400f45081c0d59010112a804503105c1c40b040345e102e070744540303c0110140105101c400011403680050501442c484a03134010035500a9405d207050302d1680700442c100105541350041102a4805401400391410b2252001d4401d01031000000d05000c1d0490035081d18510230040b04038036640051240d001c908090400400400b03d0240c1640010a68050ba00907264041c0f000c42c00794040900910b0b03800d16140440810640746801c080c0407640d081000a0f031a0b9842142070098030040014001da5458282014035007030004d0420340d28500e902e54004c0704486900c24440440385c040c4c4d4400c42d00351552405841e280b503c003500030740c00070030102c1c034254241002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 40683736 1250 40682486 40682491
    0xf0507050708100902180c0d02030901090203010e2802060a20120d0f140a021602030f01020a03060501260a0e010c020708010f06051e0402090901120b18210d0f05 71
    0x203440140030b1050504051101e4581207c901c03405981c1088061000340c119401545c0c025107540000030364160f01c1c0d0019007134503c40c2c2142e400d01e80c0308030000401d1a0441480040c0291a096004107513280c40d0b000c16028024804c0704010701080340008440c01c1d0100150070843c06401050720024100e044400280d50000410348404501c2c1c406461100e01aa00c80e0b401c0b40c00510b444001303640e945500d00006507010801c62180d480b06249103800684080002205016001c1d0015844000c0e1600080841e05a83d01c014100300d03042c400c41d0716040c100040c88060151200204079a0b1713a540d490b031030242840600c4420258a0b284014041d02d50100d0340001350348451000740502b544180c0e14005039603140c050180c0c84202c2041c4101806203214040c1d95211000c0c00240c1455420400100c614000340d0080b1035903542c0384c007171004101403946e200b544407030b80c4400b4140608101000690b12004407410740300304081da0815804521525003030f6005020b90300810700c401c105241500020f040e06 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 40684986 1250 40683736 40683739
    0x8070e0406051006020a060c020c031006080606060702010804080703030605060a02011d03030c0901080411090f010e090109080706180615050301060b0717031e0406020304110904030f0507050708100902 88
    0x28100840d0001e44062054811139445600502100c101511500010400c1d0450b0300198441c07103802e80c3c41918240126040060030a6000a40310301d1f081241d4182000100000e2081500b000481c0050b0307003040d141c1d038004d82c00218060326903075a460164000c007040c2d000690701001c045800010990f054001d20500c3c0b003a40c040c0400e2084800c846039880c04244d84000f80c1c0d090500000040c0c0d4410b504003030340700380038103441c20281384141c01040701c03c43c06440000c6840000b0340148124070b800c05840e074004000200800200c2010340703841080b4024808000c040729105c002c407001c4070300403a6500803150b40108040201003401c0030031462400c80c1c1e01c90350307009509084d0001030001c42c42c03041e90f0129030000600903607031060500820079980b000709401b480f00c0305200c000402d42c190000b068480e621a540050f030302e082c181841100c0c2c40c00d580c0c1c02449240d84d0750811002941c061038001d000401c80c248581c0b00c200030320385242401d000f9000410180b154a1804402c90b4a035000102050700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 40686236 1250 40684986 40684991
    0x3040f02130501030803011206060e07020706080903180d0203011407020606040b060906040b0309070b07030306050f09060d060b060c03120f090d0806060a050702030321060406030203071701020408070e0406 90
    0x181c0011205a07042484081e00400050004000c0ca80006500c00d401d18031889000940744d450b908141b41c030070b00030703035500c401640000802c0c042181c000c1d044580040581009606001c016840484140d0031a04418020102e250040c811900c0941080c40070354480201c02c0d0b0b4a162102000756901406c8401521603414044041602d0400c9011a215807602a0146141c5824843e100b0f201ea400601010740038400c5010010701005210050220b081c030964010500301d141804200050290114061291a1a0090040a5071501500030380503078170003004a144d0409400140042c005e040b440301140c080011250025421142620301c600c0c1c00031007000d88c40c1c4400d0141a41d8a140c8030320301c8040b902140108c2d800e480c000300505031884503458000c0c5410499808203081d5000001246000d82482215040810007860404e50014081e5000c100c8a49075400003651506d0501c5440542c2c0c06520954803c03100a4040760040d010150450301c142d540e6503c0544455011903086d00d0030351 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40687486 1250 40686236 40686259
    0xf0f0d18061e0b09160c0c060203030a0b01030b030d080718180501060e061206150406051201080d02190c0308070b090d1805091e0108100e010b0d0818040203040f02 72
    0x1a42e51050010b40360000e4104138660b85c4007400b04589065030408241800103400e11440054a00348421002c1d100310340c09191a418800c49950958409041042c145810545100540d0f02c00049400b100340142c64880059102c0690580e48141317010452650380c1d0306890042401c00c1c1114241d101c49402000400c011b0f0380c0e50a04556032000c045131103502c9032040008d1850300e00601900c64201c0300c0244107040145085246840d41d510990080c80400c0021a4030064141808140750040400c0e2002d000c884001c0d4a00035212142450210005c50040c4040c0381801140c40f030303010182d54045056503440703030705041c0341000302c40403030303010340603100303010040034103d10580040e060901840b24816005040504000c0c2c0700200400003000c3e00c5038400b4100b08284207440542c000c1011a01034601d0564601c0c000d0151850200b8000362a030405403c003440707445a2661805140e0050350302c5440f00011201c50b842c200042d81416813060001c0248070a004210151100480c821245101c0c040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 40688736 1250 40687486 40687541
    0x8060409030c020607030306080a03080a1b091a07050109050609070b0f1207121b090501090e06010e0d0605010303170609102c010e0403140f0f0d1806 66
    0x160000e02008000500e81c514200060030088081e008440c1310741000305005858200c003c2c0343c42480e020603000510900306000c42d201c2c59114804860a1500495040040d240c5000d0180013a82c850307203c50050b501c11060b910250101621103c943c014000d119150050410340d5842c0001d5820761058080d200d400501c45400d10121806030800048441c20043d965000011321038006210606010b28506e81c004024050310034807418200c075001860903003070541d0004068080540245040c801c140c10240704681c0300000044d802030003403030840c02056103400800c1004040100050078281001d0000c01019000020f000c0f000d881b070811001155244c000f04904510151a182012001044103101043d1454400d0103a005001d010501c0039490740781c0c0203140a0240d000c81b221560344024403080681c401465001704501610841c00d0008110700c0d420719204841040c41213030000114006079840381e07000303206c200c100c2c81c06001070702040d03013009000751403980d20800703d00b41e04a141c1c0000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 40689986 1250 40688736 40688741
    0x303080105010c0f080f071b140103020a0516020111030a0306061d011e030219020604060f091e020301110409020a02010f020c0a0b0c0f192d0f0909050c0901080604 72
    0xf25034020f10340d21400b002c691110002c5602a041c1980c850204101510105807a42060201d202e00d511a6800e0185014114a6042101d0884074101401008420001a808029904a254084403502e9103030038520069698809030030000803d40008215402180e030103a004200300c3c1e2054940020f554a4900e080240c15140c4201c0d40c0480e445162248558061101d01400c0c981c81d030900510340240050307001031080000398023100603801a01000100821409806000003c0c0102403051206940d9880060b400045980d4031411044840200b555808d4000f40f000700c0180303008a98858880c143d503000303580444070751000f40d070a010101c0c221382158030171510422800300c080c1c072945865907038080d010b000c09015217416900134010001d08075540300080a0403048901c80c0143c48e000002c001d480d4031040c009094401c50001e40d0f1850101032881031050f400319516002c8030710b0042c0304051b1408445900101e0215182c80200000b200322080201224030098890b0030165032500c08000030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 40691236 1250 40689986 40690007
    0x240501050109030b010618170307110405010b03070f0216060804050c0a08030f0a020109021302040e010807030f110418030216140609040b0112050a0b10020102030402010e01050c0c030f07030308010501 88
    0x200302040e138010448544500810406904144085031141e56a200c00038140c01a18a00b2000b6400024040d03080000d00030441c020b8100a0750140f00c01c0d85011000c080700d0000506c0c031014003505454074004079200f440310b2480105c8110856600545941005050000461b0102c60500c201c4003004110f25064061004884c0b0703c40c020352420214403140f00c03064101c5c07034228040d50348408140c00140d030b0300c3d00c0c8a00c0b0710002100050b199490480c0c00542c946061b802240700342c12010007400442c2c3d1190024004903044248480520041004070340288208410b04400700708a0a00404040e03012030a2140c100407040400b003519120310345081c0500700111055400a020405080203090940002e0b0200405050404040380540c3c481029902b00703c9150002170381d51041c4509500d05207810f905044220b200840c110700e040d0740080c240507403050b1090306102021500030340c0000200000d41c02000081c06a1315040f0008840e10342d0341121b404220041003d0000220703581d482251040c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 40692486 1250 40691236 40691243
    0x60e010201090c0303140408060f1012050d0e060405060c0a0b06060406020714042d061a03060409081605150106020607020307080c0c0a03110405070201021305040506030a24050105010903 82
    0x44106240d036070181d4a01180c2c41c6801b2910f10144400540083d0600480f4421a868a40000b240c80c14144006100f04103402500035003148000d41400b040000912401c2e80b904d03401c040482c4180c000c001078850003940c2c006944040c00152030010450081580e204080c0319900701c0c03d9070f4442c84200070081c00745009030001a444501c0400c284040c66001e410b040c4009080019000140100b0100d0b45000054002003068004048001d00600344a40d400a10400c02c5070b003144641d84d1108042031001030306540c803440c0c445c003454080c040380c4002c5a14000c503901804488419900c0c1c45c50f02ca580601030144490044800011024000b003889441146d15501440c503007150340e03440d01e0898002e5800c84507e84140801c5c0c0b00e040e128802d0f40c002460144520a10074824402000256a4001c101c41c00316401030140c103481e54280c0c0520f105640c1c0403140070829036a00b40100745040f245907000b074000200c4408604110349440554400c41c10144001d10251780c07a000103507500034140c40b004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 40693736 1250 40692486 40692503
    0xb010306051215180114010e0a02031902130e13030905030706020c120109170c1006060e010c020d0605040804030b0703021608160b040302011d0105060a090b0a0f08010501060e01020109 81
    0x52035075994510700d40d9404240c132051080b0b140d0f05140700368215480940002c050603e0380c0c0c018850500c1200002e98058880070003989540b41240109082c52104541c4440030b907004201504620412145203003c1c0c007a0002d428010711300f42845010304400588245e011560205012407142404a00082614001c0e001000d0341040b80b41030040c0110903210305580c035541c514071540025101801e0004451a900000b912060320107489130030804899129940c0600e0400100f0225801450302c0c1803660b02402c2204a43d5054004100d81da03490010041609140000300000c011040d00500243e0b40100d000740c40302c1d41d0707c0744107404910070740e010401c0003280708103e4000500c82800038800702c440c0d601a002032802070354134441048816a0110701503519858851510074813200d00c60460422a03000744041d0420344045107443c41d80d8010b80707014030340b2107040c0040764a0f11100b0000518505800c88ad24540d1820024000c08080c0600400034810000c2c0594662050041d044480c0c0c014080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 40694986 1250 40693736 40693753
    0x1b0607050307030e0a0306050702070e090d080705030a150b04031407030302061302040f0f0509010b0f0d0b07020102040816090f0209090f0405010e03160606050d03051903020403020a0602010b0103060512 89
    0x140c40354010603091680c400d174010000301c0001d509002d81e40c0948a150002c1c00070710706021142480c0c0400504448882d4413964004400c00c0e03101030301c43d8100c6d1407410129601d0b15500440c5020380f20004042c8409074040000040001c8480c0c01801100d00034606402d00038110950300707440359440e100140040e4000d4000c1a06201c1c01d07000c040009100800c0040e90707688800341201503c1080c20810b40c0141d50328100701d03610b41c01b80280380424404413030031036480050200151000c407149c0070144c0b62090450002c1c02c1d0038002d604640c09001101e044035444400368040903c0400b0600030b07185203500380010100d119001d40241d80303801000400c42400d594030303c6010191104010000d40303440d074842c3c0040110300c000348010300d0f4501492036650982041030078000156000703a400940101c841ca501000840d87c44020740d48220066005044490401035049001c0d0156410213035208000101c0098103e030150701100090707800b030700d041c49000d031764800308246412222410b50154204400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 40696236 1250 40694986 40694993
    0x6011503020a17010305060402090105030c0a06051308011b03140106050a050c010605100302130f12020607050c09010603090618030f0e0103020706020c01020405010809010510051e09091b0607050307 87
    0x14001c510071901d0408440c410b10161060b505000ba48146c03040d802c020103000650030300700b10b8140900b100754000d19000d80c0d00c0003c182d4107060740c41070500300180450401207024020303800900030160340b002482008407082c104040121201c0d1030502091078010302c10802e00c000c0314941d04880079a00c500382409014942a552684900b1543c42e06540e00c032404181c0f691003803d80d607281491a07500503203c44035039403c01c500481981051030358010000c810011540c0c01110000c105a055643c581c481d40180b03802031074007400b510055441404000045000b503410303480780c0300c114061001030025280d41303400000c203800303082c80140008a4100c10b407200355001d2112080d4003601032400600d032a02c0c948881049820420b1449110394000a080180b0b43e4000c1300160007030390400c002c11a90610074007906c1030304102d100340b41c003d040c1c1c0d820340e881149601101c02c030303800d1000e0f00201d010302d0a159542c0c4c5a881007007a403110321000c080700c00410b04103042642c40b400da0050007180781c00051348 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 40697486 1250 40696236 40696241
    0x501020c09070521070e0a030519050708010603120813051e10050a061505030705030a0b01090302210111040b0403060f0b03030d0902010801060c150b01110106080a0b0906011503 78
    0x1040714040c444100800644004008200700a95000c40200d810900300041d001b454680e003001d05620410f1606d17814004509c010036203030b000d400e0148500503204002c0c0b40036400c0411591001c81d25500e0f24000200340000d0341c0f000844080c0c566241c902903130b55034907031800e150500c1e0000742450f8440d50780b41d5141d1840407082050150040f049409000e0560004000c3c0d450850300c0400d0103440e00004c00c200c0305080290303a0340c40b066061940c218640410700401900000b800c040026854883c001c98590180c42d0709005183c000c2c08041e10303181004840b1300080f595050b0b196a96190030740d40071180c00c00100b47d41c00d943e5200c50442ca0030345140c440a02401210003403121150342c4000484041d64208014000e001c035010300419003c40358000503180003c140d02070802d100185003103000081da03200701035805500500c40010300c140f0190040b1444039018103801d180398603100000c1440c400c00610001e081c1d04c030700071804c0241d803a102e0311912038a0a02c19489003060b101001c062990298 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 40698736 1250 40697486 40697491
    0x7080a05060a05040c0903060c03020322060207080304030e091005130203100b03100e070305130206030a0b09011706150a060f0509040504030801090c020d091809020d030201020c0d090501020c09 85
    0x103260301d800580f01d0740050102c480e1041e91030041a0251420070400655000300101c0b00c00f41d0a0440c02e40c82d0018103c504200200c5a9a0445117032034070700010024a40e05840059410011440e181c2c82c0500d0b0160050b1061641d5600c100304110000d810b10606494242c03ea60f000707000700054652080c4020081e400103401c500a0111171f03540480e01c408128003441c0300c0c40080c42c0074948103141c03801070a482003002d4600c1007014201401c2081191480c40801c050960603602203035296200c1c1e1240c3c00400c00c1050284d404a509170001843d0740c0c5c2222040100168501a51420349500c200d4100440e102840d06800c4102010300700246405820244118840da090003840c1002c10070020b411141f0444044000c03d080304014400d00166200c2c03040741c030000340000c040c001e1032002c0c05001000c4500c121440c44100702801060900150410006154007502d15000340c0b0b25441d02a0103074000086400e100e100701d1044212583c483c0c84c05404494068010b0b04032250024240980090f00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 40699986 1250 40698736 40698739
    0x608120d0f050c07030809061017010216030207050f03010203040f0b0405030d021603090503030a0210050702100608070501030c0801350a060915110405091003051015050907080a0506 80
    0x100c0c02040010000c600542e48500303001400d56a46036000e02c2c0c050600b44024002c06800c1c2e03c070b00d00304030604018214003801e4840c0c0c044035126481c600c280040c064402e1a000c50b1082103e110034004154001582600380c0390100ea00a000c0d4280005040c201c2c0000c54010f42900344030302039034001c2104000000d80250148098900c0c1041315a00d00042c0c4c0d00c0943c000244607004810141815404500c5002811048010b50b2500802d02c0c0001c2d6a11041120a9011959100403c5299008000502d01505524818001c031951610055200d0f01c5030b21545001c80c0c1494030351284903210709a443d050781e0114104804074010300c05c406803940b01d6142d10000c0001205100840c0e110304114410400307100d8000414422402e00c0c100084c499010020b0065904240c0d45d544442ca41c10181c606845069800c9602079030b400b000c54845003400d51001e001c0380110a1032940302000c0c0e070828006600c0c1c0c802d080b50499079800038048c84a800b01ca10b280000c007081c010074a400080e4001c1a0440c20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 40701236 1250 40699986 40699991
    0x120a0c0809150703120606050301120605060a1a0c0c0402030405030a14090406080c0f060a0c0609080906070c14060a050f0d1b02011e0203060102060609040f0605180f010608120d 78
    0x8005680041d243d01407202600403d405d00404100501036002e00c8014001901d0300c1e500b15450100301581d058056a0300610b00d5807030310001903054444080311740007031402c21030201032000c0480000080d0303485680403000038000d40160a1107800d250080300c0c05540d010000f58541103091504991512112546040081c8100000303c500d40d141d004681c09003c0007009131181c080410100048510041d840c83c0c0505024071484110740d4018100e0501290003034404030390106103280040382407164003101b50740424041900b100340000401e0b010182d03401c12050100814480c0e04000c0540204110100040c404020815488001030050006540480c10108001d80c0c84074910405152507000702d00140c2d9161203080d03020842007038103000343e40d08900c214a5800d09100007529810000e002c14002ca0030b0b000490100031068140000f000e070000001c004d0ba050082e241400780408201d5034226104c0c50559013041c0906104d808211003003580100000e2001d114012542d810199100909a9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 40702486 1250 40701236 40701259
    0x70809010f06090f0e0703170a1b03020c1005040506040621060305030c070506090307030204021606020403121709070608060a0306020c0105040b131707020a081b03120a0c0809 77
    0x1030060282c800038103500d480c003090b84050000b600088500d00000c0886540c02a80c2c1040440c0e480780400000c42c002d5030206031b032640c000105443c4c000c0000040c000042000402a003810b6000c40ca118000d60200c840904110548034111505c0c041d40c0a80717940400200403c110003405042c0c507200c080c03080003280030800d906031524800c0715401d034025195500000703201070f00190140204070191808403851801d00da0ba40e80441d03a43c0d030142c08001e008540c00904281c4503085400400c0e181c0381d0008044d13545a03140e2410038022019901c20384045107082001d4450384006000080c8500040c400818803a03280090494820700f000c0e2000c0d81281c0103c00200104525000034680520784400120f0390b4106843c00d1340b85414020710300c00030030032076804c5100080c060031402d520301c4005206590311010140005100040300380e000c8150b43c42201d17144504984900c4000c4007182c0c0c11000d981d0203000007005c205041c4140080e0a0020700000c24680000d01e036000a000d002e0b001811800340032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 40703736 1250 40702486 40702511
    0x60503060709150507051504050102090d0807020102011a1e010e03030a030518030a090303080c04150c020102010c050930060711011b080609040510060909110306010e07080901 77
    0x8801c1d1010000a000644207000110030152810000c460514000d40703407a00a4482c035480b40308a11543e101c01002102080503c0002d40507100c02000051004100c14060700d80f2000310380c81080c0c220f025500304031100001c41c1c605544980641e03c00780c8152142c8c10701d80034804850071500d01281c1404000080c41c24140c500b080030704001074a0791400a0107041000030b441040f203103010511480d500422a8685c101e0b40300b81c241048a6040c20076012075125203204962074022a00820359032101c140103868169070103004030035014003c6c0c008010020b0491000c90b03207031007040c0030180c00c484005060101101c18801c1c00002c400714210018110b40c62003c040d0400388103079012000038111030388003032640c2c03400e208016520444903e00800040d4124000e040c0703001c001c010324824044540060144401400020130610309a00c08100c5241c548055400408200300151036481c0c0307058151759203040000e0f40340c2c141c44421440c0c080c10b940340f81d170403a03004c40700a00039032140d500c41100c0d0080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 40704986 1250 40703736 40703743
    0x2100507030b011e1e090306020d091109040809060f090a030c050109080a0507060f0c0203060f07030f0b0306040b0402030f0105010b091203090108010603020901030905060a1505031b040906060503 86
    0x200d00c036030341c04120484840001806040f11445040c011591000141d44260304281001c4c180182c1d5a082c03c001500c244050350400000c0d4800781c4130350300000e01e40380e8a440d41e40c44621100d205400c1503610f200640103104101c1e20403030700200848020007600c0107501c0c04802030994070300840286880c03c8142e0000c5505044141d108a0750446150814801980c204102801605060f802020b9104094680c1599502184100c80130310402000c045002407141060140b03458000d02203a40b036042c0340b01303d04032001045807501d00003407400c072079403d86280c640500c141034500107004000c1350b110750715005820100500101c0c2d01d8860764032150344c524420700600d402807144600700b80d1100100424810002d900580120198004220b03d4040b6038004000a0543d00c1b10300d00140c4030303c104401603005001202024081d8403448080201c40c954540041105525444503005001e1303035030052580e40c01900340d40c00560240d80110011a007450b6014807001030084001190160361800824103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 40706236 1250 40704986 40704991
    0xa0e160e06030109060e0105010602061f030b0c0721030b0109030803011e0806090a03260f040213020f03040c05040c1709100603050c01080f01050604031b08031b0d08060a030f03021005 81
    0x400b6516140108041a0103120840d40084038a5210043781c0100344041c05156071400000c081000c0b11003c101d40c01204001d540705240d0250b815500a1818400c40c100d440c2e00b088440002400c29641e00b071030b544504181400c807980440420706590800107058030880e003a2400441007585040000b803240c20811403540605174a0000c0d00343d03500740d42401400741c4211410104015180445428403210018040d6402a8881e92460468031140b00140d41c140b84803065a4029001040d1580700001ea0f200a6005600ca149403405140c4e80b01d043c801643c0141c074507507001c648600000381501c0c440702030740d943c00040c050564000c40704140b81e51003200c120390030070b4840b81d001c4180c098055820003040e50f009620f04000f140e45615104c0064400d2281340001040c154607502500e0b10941e4010a4002a00f00e00c7c06503174072001c103001e400d9200c0182501c00d02c01031082d103906845260044550a00038040035152140e0700b42141c03180d50a03840505000c504501c90781040286114240c820f060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 40707486 1250 40706236 40706261
    0x2040605040906050607020604050f04330816060c0507080a030903111503070318050601080c090a0506011b0305070c03080306040e070b300702060a0e160e0603010906 73
    0x5890354107001c82c140880300240c001074003e26040045001607900d0501790790486004944d0b44264015180100300548641d00810161400c103100012080d100314500c084030b101141380091030f0541d82c3e81c04a98920f901346515030011001c803010b00c41d0a228807030b01c05042e40241d00300d81ea1642d83d00c03449840c2600f200020b400241c40c00e84d060003009203034080402c03142011980107404c0f1200b201481c2241c88003030301040a240d66255180030411080304d61520007a000000e0300c080790383d900b0707085441e40304c03610041d880313059407600040400c170151050a002e05811380d00c12282d20760700841c1e1524a0162001070301488000d101d203a0025480d031410001944c400c40402c0c0d203d04106051005807650340610b040d56030800034041c41880c043d8000d0714020f605407100c0b089100c0c1c410010300548900000302d941f40107400c1040101c42900000c0031400750864120401588060100c0749844203100815006848052841041016504800c0c2d60b00103400500018510301c599035240111408440c98a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 40708736 1250 40707486 40707497
    0x110a170318040c0801060f120203011d0c1e0d0f0507030b12010603020303090405040f020d0503090a1a09120f0d021e0304030f060903050405040f02121602120c0c0301020406 76
    0x3a103042000003441c1c003140c00203a905100d8402445405450b9120500500040202411039024914030500101e85601840c250840d540d507114a40b8040c17105003030980c2c010004501020900d0303400c809040b245510b00001c80c148103070b14240c40f800b650303602164564a1a9403200d03240044c1607024130805009041940b0700080c042c101c0010300c4070458204d210048540d140640c10409600c0100c2180c02e941c00803280001c0c0c40e84c0d60700d46088128060080a908500100401410801d00100074a02c6a600320303000c0c103138199507190305600c3c007211180c141c500c5202400021034030708014000b41c00016001003074580c2000c614990900d41440894440d00580c00300c0d00130310b465110045865542c9000b000558585401c680b12200d2a900e4028000e16850761112350300d050503c52400d5801600300100305000c80030500b401b64000c2e40111640752607485243d80811445006100c2c50015801180c000d4003005904d0300102c182da0700050f000000d070740a40300c82041281d5080c4000c0000d45080c0d06d84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 40709986 1250 40708736 40708747
    0x9090d080601050a0e010e040f0203040f06060503010204060909020702040905190b0f09060106050a022401143705060a0324080a060209012303090d02011404110a1703 73
    0x10030a50001d0000d0341808002c120030208140e20804e49480c400742070800000030001603010a00900004941c41510741c404000c0c001003002c00c80d4040c940a0284109111003a00d590805080b44181d05c80c0d240407800f0390b40100b08107602600a40401c07800113000007030101664903140c0c144404e21001d901c42d0a0450402400c00100d0802d658000e080059030940c10301c0c00f0b82249a441c070042c080d2405001006ca907190804e03108100d070b02c111010a480c0000d5007600148281001c100038010f98080d03c43c0c4a64003800c40c105030242c03008a510b8200030342c10301125002082c18045080710b182900000642001c61143c680d540207180c001c04541e0006149199400c00640c020b0740f07482102044250004104254000004d103103c40507040709006940b00046801660a030188000c90200d0019807114810102d04002c06940304a1003001030b83e510490b01e401c120700300c442500c0e903803014080701400305001c135901320101d000c030850181c40072600b580c84001e0102c5422141c0c503441c0703650340000b48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 40711236 1250 40709986 40710013
    0x30615040e060402031207051f0507030606170403030f06030204110909060a03050a0b0c090405040c060e0a06051204030201060803031f06050304050d032403110f0603040203030a0f05090909 83
    0x408400119010207401d050606900090b00c030061103004441b61000481c0c5102400307400d100d41c0901c00c08100c098520400e8980c0b984001d030600f26028408646441c038002046402040134814124007401104841d5845179010750041114854094206a803020040010780351840740860001c800b00d4516250700e030316001c0000c0c1c0704000f04500c1c02000114420000100300080e0002034a510044009290f540e04c5000c1c004c50207580c80703003a03009017894144410700c0143c203d46c80c107582ea56502e8aa42141d283e0603c01c19000c2d503c503220005104101c40091126200c030800d4020b0f02c60b20001c500c1c0d85d6075840592464100707903801941c0300802c54140c1c150720078841800c8018807250500e0307829031030320341c850742d88500c41c010b105018507448400b0020040f160107811423404e01c501500510464036030400c1d11030545003e4440d4054640094621a98030388034080e00d201c0c983c002c0c01989005514a0b007211400c996040d0001403003c2801016807540c3c680b001c0070303c0350702c0e607030010300e84030940b480c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 40712486 1250 40711236 40711241
    0x140d090c05030109020d0305030a09020a031505010b03070c080904060e010e10090902100813050607030f051506040b0708070c12050c011125050d03050408060108010b010203070b0403050903061504 86
    0x50041d88070b0380c98004500010389454106491403030700350403d55125580d0b8400c3c94050b180c07020000354011940400442040801100400c51020401080003940c1e03d400301c090b40e92005940b144042040e4904400001c0d5621008001800001e08003040d05aa02e0090222101003030704203010204100d410000005240380f1a2030042034208410300c0f05421640208130b5800b15916024100500c031000101c485800f080c04401e00303a8481d04a03101450001c0004000704010899650001c0c20400441c0100600d944030300c241d200d009088924092426112040c283d10400d801c40321540140302d00008101003c2c00304000384600c51f206454a43c65142041c10240c2e60a0300c903061268020f80d44440e03400004041e01d0100094607030b101d41a100030391101d01c0312030b90b62080e41c1c03102e0700506001c10540c0c0000038004489101007282c1071070340c83d800f0090903a0340847c075840c01a030043c400d14000c00c20b150029504140a81802d03840c203452400880c1c10200c040380c109068820303150b08500a801d252 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 40713736 1250 40712486 40712489
    0x403150504051c12020306040e100209010306050d050706030903021507020c010905031501030209071101090606080607230307050c15010501020c0a120b060f09040605070e150d0c140d090c 82
    0x84005005402d1803c2c05406000030a41c07907004164003000094082c0c607641d020800d107100000850305849407100c4118069403000410794002130030301000107000d00700000c03100c001c6175211014008580c1081000c40007020b03104020380451003035040400801c640100c00d18000d002c2c69015101d10514000050030345038940d031110303001c1ea1240840118440740d403140b00d41076030350440d41d20269032581402111251641c0302c075004d19500c0c1440c40800c000c2190302543c201c070104001e960309950707514000ea5802102c84084104162801880302203110000d006584c0012281000d41c20b004c0c054590902d00039180030340542801681e0014000d030744e0100a14001d104003200c140f04180d0520b9a1300b2518852410024007001d404004101d0320b80d111131030440d0468001c0d00c036080e28541030520354041c1500f9241c0304041504040c500300f560404402da42c0c0ca03201440300c11850200c2c49010f200041400d0005842049081954018456980002094a290111800310780540c0b0790400603a01b2605 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 40714986 1250 40713736 40713763
    0x3030f1005030604020f0411040f030c0510051602031f050a0608070b07021203040b0c070905060d081801020708030c072c010e0a090b01090603120c020102070b0708040315050405 78
    0x100d8010003281c1e038006030150384140c0c10b4400c109095006070210b0060400d00d0140450403601103804a407000c40b032007c200450340503035054907005035600103018064511164410000d0410420030800c844c6002001d10060700c090100d03100d003440c00078100e44070955684004103c64a59050091045503400703030310302030003442000d03180c03c528200c64550180b04900001340a21104001c1415032a02442607800509081191640c0c900c80405120b449a016010365140f00d0301c0e000209429040540c821040703154400c10752032400d40c111081141d0500010100b50451292410201c1c001e00b0a00c0607100309070100d001800385600301080c040b000100d1400094800b62006c4111840c10b108204075070440d40c4484001401e80c40b045028400713840c0c2281e02900a0070040700014200303040764050405c8038018501d180010054035070484140e1104500a80185e00c000d07402c0c031441c0f4102005083c00c900c40c0c12940e2615039255a04080c9007500385503920803507600d004200601c901800f03500c504424 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 40716236 1250 40714986 40715011
    0x60903020105071409040c0207080304120b160503010b1c09050102030603010b010c0c0608060a0b0705060105090109050907050603281b020a0b0a050703090204090c06090506041406181203030f 84
    0xd5091183c1600540c4205c84c8501d0711f030900c4054283c000d120450203410b42d4030569076140d03203e0940e600b07812407000040311480b0072000040d20448607007000075010b0742217503a15031450b46444a40351030b6800c0b803c6000c600d46540f00c15410f02449a119800d081482072001688070b00d055010142112180c0304140e06000103100b074400000d075001d0800096074139508083c4100e484007001300c0c0906070183c00405c03001c000081d140b130503c1000074401c3d04035070040369680c4550384c0310075121094802c00e540c8400c080c0d003c0318042c801c81c9032900c05190700c4280c14190080d0020f00c0b9404000304d220051003a404035582c0c04520013032038480f140e0030070390203070300d000400403140203640300082214000c08035400a569803001c01c002622a03000f18015640040040c440c4120740d0a24140d000818400c500116110080c0001c1a013000070a032412160300b610301c60450f0201034144025230b40000e1400074520004e4845042954444c1605c525032400107004549900d01409040700301c000103402c01d091000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 40717486 1250 40716236 40716257
    0x50c09010210091a0403050c060c1812032703010506030c030601151e030e0c03070506040909020a050a06050d050907030c0b09011707120b040203040206030103020d0f0b0406090302010507 82
    0x760001044200115640d60004000c19a401e00c1011203070103404080a020644040c8000d0551010190200d003032844161140368940031141c0c0503e00c5a8684645003c3c40558518104d20f41443c1c464040400c00c0252840c00042041280306c0b003101241d009040c10340d81c0400c07a80c0742000d11034243d02c00700039030051241c0107640c000203540e080f0510640030032800740740d1448030032445502603211a0b602e02688007041402d001004e405021000c184042610500000c125a031400041d8001140c0780584101e2900b070030003001c800500407644c0c081e40c00448001002449840e26080354009044a03500c0d01d449100a9009000b5a2006400440103030b000c0041407001c981141c0120b0200c0d040f071184190744000c1200103a4980c0c3c04a50680801c0d90080c0c204440c01e03401075211a02030080040c100004c0c0700c400100000c0380016180030390425000e000500050400c0042c4110a50040713400b0805000d90303650b00f242d1603a04490450b01540c44002e4401015024061070b9008038290410400342c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 40718736 1250 40717486 40717489
    0xe100f09050c0f030702030d090c031a0c0a120204080a050601031205030c09100210060807080f0106080c010809030c030d0606090e04020d17040302120307020a29070201090e130501050c09 82
    0x3d000e00203003822003000000125444600030000c80e4410344003034000780220059810003000780c000910050303038070500320b40c3c0340200c10f803141e290300f44640d0100f43c0305420a02c10100446601c0307104d2003441c1c9915820800823a00707074800c00c5640a40d6116400401a42d81946400321080c0c0c4840c03580d1003409024010f00c030700007c40b202650100c44080d1001046621078040c00ca2402540d22815110541752960100d070010022800100b694513000480341c4034102c8125142c2240c4891040071041e0308106100c2d002988196150368018030b0007000c890070480f0014006084d64482400c00300c640b81d4803035080080325001b885140051442d03941d0405a4540b90b008100c035240001c400405000340721009040c0c6480010584000d550040c00034030103950721030082c0d90b49601c040810381c410304d424040010601034100c4505d5a800001c003100c11403020310760a80000d508403140807810b108a1060114108031111821485880c14182d0384a0404150404c40d0031114060520703001500e0400210115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40719986 1250 40718736 40718761
    0x40303020c030a11060306060702090a050609060303070b06040c020a080309010b13090f170c1b03100c23070b07030203060415050307180e030a02030304060b0901050d0605100e100f0905 81
    0x1400b642d5260303071b0382d071201c0010700c26204180c0300941c0b00c0700506c140804076401e544141d00c02d0740144c81a801944450041680c0e84c0901003005145040380000203c0c5414250810200e100ea11300450b00c1c0e1008175034640c0610b800c00c80d914115a035580040011030316204550401c15030311031604010700d000039190f1003030024000001402c8070300c1041c4e007515103a100c101221103090501d02510415075800c19910700c460013258099200f44614500500400e00521840e40284c01035107c03500c2031a02102907000f02043c54600c403284040901c0b070140800e404664030740c4102c07516030300140e5914000003000100c9082040c04288800c510030240641d8078005104000c2d1141c102c1d07544e83d032080241c3c025024007041e50b02035505010100340b0301e46080d0000042d40c00345204140030301c0180f09580074451050340c24071a1541c8a80446900c00108a03154011500311283d0704c41481a161900d00b24041d0f144140c40c105005059102c0400461030380541802c05065182d0003070002c0e003001e68103500d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40721236 1250 40719986 40720013
    0x11010512041101020703082704051005010f0201090203010f0e15010f061d040e0a0b09060403020d03090203010b12031e09090105150d0606050306100203030403080403030c020c15040303020c030a 85
    0x2c0c000341c82900c1102c43c1c1c000c02001c0000d5a10003000c1c0e0703880c0d11101e00030004a803102881200e0319518134407402149082d0080d24070072900ca0301c0703c000c4a8503040044480100042240d000d555a078513190016803002e004503050812444d0000c129210351b060440e150165000312501d0701e090040041c00880704a81c140e808442c25450100b002c450030125102206150301c0003290b106c1d2070404816201d60010600d108054010f40f6800f2427641d94080903900d414007140d0080c0140c210000003d4224003a6120440711400600001401c2c0480703008100705041c52814017000fa031010403200802104c0d42004c209141604d11803a041031401004580840b00600466214221180002d401303110b034402503400341c0e092014184101961080c0c050f01950013951054001c001c103040000005000104890160750b1595910150780e807181c60880040181c20000d2045001c1c040c2440581ea40c0c0142c0300380c0000c03c80e0705942c1d9680c65440c0191034070061403c01d60103900601d05800100311014007000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40722486 1250 40721236 40721243
    0x5090702210904020d0f06060c030e061605010e15060d0308040f02030a0b0a050114010516020d0206040803040605031603050105180403030609050712050109150915090908071101051204 81
    0x1900500c07001c41c44009000b40c01c08a508288081800520604103400800b074050000301c08200f19900e42108850000c0703c1c59001d0701140c455030920310581080001003000d89001100c1002c04002a030390b05094a280081030903540c2e01c0075103025002c0f20508840c540200c0215520042244940e9000d4045c56000380003a040c2480e0b10270300415500c06202c07542155600c5182054940341025540e002030400f80502d6071110941100340304694082c1d4101c0305034060244004041e00156402c1102c65a810082242c003d00300748070000340303c030040020f44007030921078640c6912840c10281a000000319501004101800c0400401213601d604050138a28015107501d90f185549509040d8007800f13060748190415458041001400c603441101c503070f28141100000c0c44aa40da60b05040261780d84041990f540c1000d440040000e60410ba00020f00422208090400a640e5090307600c2110034144013038038120700000d0500100030903414a000175140c00d00702281416140c0c8070f40201114000c1005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40723736 1250 40722486 40722523
    0x70902041d060f0406030b1902071e020d080f073807020a0c031a070908030d0e07080a060608061008030a030203040201020f0f1c0905030a08160b1302010905090702 72
    0x203034440d20f800d003032a031038142c0151050240c285c0ea880c001c65141d80445100304070030200c0300c0000721740300140205c0701c00c6500108140501a4009500c808482c0301c49400c0b640401d150940b40d00041c0044042c1194090800702c503501e420260601d0300c00d4000c000b00200402c3c030000d8040d01d0810960800d02d05036180c900803c0290703600c00e20203230300c2c1c00d03004c4801500d4400340001c000704000365003003ca0041d180c04415152244c480c00341c00e548181c00c9018080f403d0b0400d012404020b1070a501040d041115003046801c1140d50791078080c104591084141c0d440c5403110010321410380d0803c409a08038003000c14030009185424422922400740250b00d41c10160000b01040543e80b08000d4031088004610540d080c00e60300700309260b85c0b0006800248524482c0c0600790f0411409200150215078000d4003520003545990b0741d1a8280c0c0c4106640600c000b100d06c0f40c9030100b18980c04440c850041113840d45820741590002400c0340784c80360f1001c0d1284110030200244a030740850307402c20328204001d05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40724986 1250 40723736 40723741
    0x80f0a0609030504080601030606060e0f031c2708010b0607050c0103021b0d030b120f030f030c041703070204111c0903020f12030109050c040f0e07090302040c080702070902041d 78
    0x103e4a5100303035403211311076200310b03c00801800050b0b0720484c119a4640c40b6a5003d552113414000081130b101d120551580100000b028103102d0420000c40008162400780b1702c44280c40039180d00040d00b0f12041000d01800442803103289000d110b1041c0514040702d10303d04090f0030390348142e40c0b560078a4215040540114001c215050113114400b11409020191400042c02000040003040b00440d25481b03a400c202010005400105e55403a50a02041c041c45c41c1552022014950b030340084c15080025104200000c0c0007a000041b40a080d04010080c1d030343c40c1d036140100002c0d101490742c15040741004005040e1104c22048440d680700b1a140e9011503480e91506059050001d0742061401c18000d071141038403000d00c00710082d4140c50501c2c0040206032901d000c00031440c020b50041c84101407040409101215003012110351261a5141500c07941d9140d0340854291440940c4d0394000c61034050038030080c03c3d0180820000f810286404500307091038194034005140e42d03024030215500030b2101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40726236 1250 40724986 40724993
    0x607022a04060906080105040b10050607060515030d0504031202030a050d0c02070302060a0e0307080102040b07020918190605060f0303040902090303071707030801120c030204110d0903020d0306080f0a0609 90
    0xb2034001032207008802c0015955038120640a0300c01124200c0d000302081c00060049607068101b8405d03202c0181440b410b01c0c805036641d000403c406000e000a8034480790325000c072564108458080c104076561920340701c80c518070344651901100f0181600390340080c0301c052609a80300040e102084005500400d1080e000d207402c4e400d100442d0070194106800243c9648001c0d0803205500c000403081d8100c070740b0350f6502c1100781d01b02e000c0ca0103040c1070070b182001400050301c1c000003110341020a01504465481c036101e83c007443c02028280d1003400001c030325201001d202051155136413200050300d0b140d4440e001c00c00041e480348160300424200c943e01180e110341c2c40c7c030100213071540780c0d078481103d820588005c00e00880a401c9102c003140052403500020480c5032081d011054166807207140446c00c10f0842d4208409092010f415040842060082030290321040c01110320700c9000f500980079407014240000c066460641003006650302c15000040c4118000590040f99130700306900166201540c503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40727486 1250 40726236 40726241
    0xa290409060c030204080d03050103120818010903030c080901090506010e09010b091f05010c0f110103020d020d05010302031c05071704050a0306020c06010504050906040b0a0e010603030905030607022a04 89
    0x110064100c500c2c0491008209826900420036141c0d900c00b21000361183d40c0303085094407003d01004041c122012001c000050040360000d411000c0181c031070b850b00c0c440c1a8030310b0851341030f41030540010380c803055105060307600035028a03000b1203000001d0102c60801d448440d40c1d0075040c89840386174402d0000240b905602941305440303001f0300a059403030301d00f80360b4080350506d0041c04001028441e20080002d803903001e41443c1480aa01094490595003e5212000714180328072420f0305050b000c0100b002d01045074401090000006500003400d54114014503103001304500f030300401020808075602c8100e401100b500e00d0290300a0140610020740200c0c80740c03c0c0a1603210b2070304612807a10100130001650043c048111840c000c44949a0b0f1710b108110555105403002b95240d00003c0104011840303003100668410150b01000c0b502c400c007011414210755840c0d0085d00020926901400700c1c0c5810300040c0d410043d00c0c4020240c0c05680f440c05019402945140d40340c500302c4000140309900d0302e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40728736 1250 40727486 40727501
    0xf08090c0d0f0209010806060a09021c0204030602070c0605092b05030406020607080c0f090d02040b060d06080106050d020109060f09090c27031212090f030201020705060a2904 77
    0x40c1c50035000410380c1c0307402e190400d540c1c807080703125400d520f00204480d0f00002d6843d2280c1001000000640d04d04016200203600180c000d400c0e503140825000c03c04801c0380020700007036110320300040c1c1c0d41401c0e043c004c2d074081030b41c2c0100b41080b00400c40310145a03201031002060a14441c44280101825050040c00784011100101140008240060040e401080c40b0344500120385076800140e503800c920982c9807103540302c1e002c0c2c0ca00c0144440034060030181541c2c45e0041c405040040d140910100203586a0884440c0b8002c40da16403106200c605c000780100402807406030360941c40200a0350001c0e2807481c807400360208221082c800216220301c01e00039400200030410041043e0030403000020725002c8403005069400c024801603140d0025415549803c0325041244658800340c42981111a04c1580302007180e09038440c10f41c1004502c4d4190404289440713a0001030b601c031910301c1e0075420300134000c4c08034801c240f40102d00f4080070489940108040346042118a48404110000e802480003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40729986 1250 40728736 40728739
    0x2040609020a0f0e0303030705030403020f06041203060e010e0a0b0d062a0e0102120a030603080c03070209010e010803070b0a02300a0c021b060403120309060f050103030f08090c 78
    0x2400000a10a4900e03802081020300a41c0c61a07400750400c2c9044c0c8500890380c80c0a030301036104000280c0c0d160710507406950454840d20584810710803542e40039107400420b031800c1e143d05040444001702d0903014800c03003004000c002007124540d89005070304582c1000080c507044140b0b455041400041d950105800d00350396100c2c01c00c000c00061185804c0000540d80c1c085140103072500036a0b01c20728095050b28003120b00503801022084d040324134000407500a03014000a00d078680c00040002542d00019004410820008507102c40e2640104511024180d101c804103104207801480041c0000c8220f03000241c100280f42c10313a031910180c41c40248940111001503103000307000c00c000c1d0886040014002d10807410314480035120418030720300301d50b2040c1c0004051b80c820030a40410140d03000070074164901c014609420559030380c03550100800d295800000003545c40540c0001c02c03c40e807003040b038010034143d4200101c0d8150b40d0301401c8034807810601c90500600da00000d401d45ca0410403000450350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40731236 1250 40729986 40729991
    0x71d0a0c1803060203061305010b0712030b1008090c01030e070605030405030403140102030601031406030a0609051e06070201061e0302060310090606030603020f040e070308030901060e011410030501030203030406050906070204 99
    0x55078140f080081d00140c0b205840748a034040042c1c108255401034074169031000c501d030344c640102c0340c2d1842c11040d0b1004bc0e80c07061680340c203600d00259503440701d0f030307000318179076450b001c81314940300d0340d071504145828807040d041c18902500704500003000161442916040d09000303517a61960304007d45940120790000b02407151200707000c464190190003442c0107160a032405d001d04003411400411300403044481c40d426901c1a614640828000c0e0400c100300c41c007030000d540301111101e02d8213440400400120703485c1d902880030300441560900c18440185501c861600c030503181103106842142091101900c20320012001c0740107101428003500042c0707115a403c0107199035441c0082c000d00410711080c0e1044400380552210307802c00780184c110003040000907203081401c41d6103032009504044c111601565a800340440c000703140b400190301030300281031030403418102d2004029140b00c040405800309810301c401000143c078000161307070903200142089a103841c4040040b90081c02041d102030360190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40732486 1250 40731236 40731239
    0x112030e03120d0509060601050306210303040605010312020f0304060806061b071406041802160b01080105040c09021e0c010f110a0e0604060504030206130e04050708071d0a0c18 78
    0x320041c004000144814002566241345e102d841d002c049035014003158040002800904d840030303ca400c2a1100fa447c41e108511542c80c80345542c1003110106d402c5681d410061041c03001b8032010380a0050b01c2d100401400340000d441300e07201d00a170f01c6102c09101c101001303c2c8859540c101511000100701d50404501103000032141d540f15034a1007a41d03000118680700d10003600b000800c907803d40701c0d02c0f1039041342038a040c04084025402003c0303540c0b4141c402c0c03d4040c0004d022244641c004c042180020405d414941418100d20380c0f1640042410783c410488200707485820030050300404852084651070b6140500d485015100d018a0301c01010b103000000c0140d441c03050b01070705c03d4900641e43c1e4480000546c042c0055407040f4000c110110b18180002c00052801d10000c00000130001400300b070655a461600e035030f0410581e4100d409401121080c400301c101000303001c000b0704010740ea5502500d045003907241c07102000b803d0940e440d9240e040d4041c845004000c000560810340142d100c0c6103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40733736 1250 40732486 40732513
    0x150a080a0606050408030f030a0b06030a0e06070c030f0c050f030703051201060302040302060409090606050a03030f1d0f0603100b120106020706030603030503131b080c040609140112030e03 83
    0x810044442200c6545440341c007007080b600c51810740d4255090341009626003041811046459040101034228954803925000c0250300d034280518051010709502080d4002c03500550b90420800600160400c05032003200304c0841c0d40045611000c105034107003a20046580e0410504041c1118500c4101c1c0c07000003543d504155002c401020f82000c00751a10b02a0398031490100c0680c4641c0c031010307600881c140810b1202c0180f641c40b01c2001f902c03d101c006150b0380d40d4004540a01756960051300440e5504505a020a4000a48100c52030142054000902004e00007810464924040c180200c002000044007180341600440c007405842e4003294840d406101d403441405003d008400040c0503158001607903501138001c400035250700d5224142140d9401c55511a83d610420098400c03c0060741034450801d500b003400344c00707848544050643c1030038810600c41540c140c2d620440c20986007184601d0f5403204208142d0540c1e1850719061030290300303410101c0b00c1d050000c00d116414010400ca29418 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40734986 1250 40733736 40733747
    0x3200307030924050a05090a09020919052409040e0a0201020f03070803010b0306010512010f17030309070504020c0a0c0602070611340e04080301140901060f0c02150a 73
    0x1e1080d528404101e0311202600e5080b0450140b1800e004011009100c41900070400f8110541c01c9141031820190060002420030f1041d0b40700c2c4449550010301810142408400701c43c4480088014110b00381c03034540401c0100c1c01c0d01e0011205004108800c0748400031401c1211518a0014401d200300d0719082c0d1015114682100c0c124054450406041e05400020007541c50080e0400803150540c0e10301a61807402d0fa100030076143c1002130400414010a07050300301c00e4081c0c50b8601c400140541480d12880c0c02c080300e80b03520700c4030354014810030004160008000d1b09480081c0c2e005600e68100d01001e92400b13a41c41d0000781203c078081004248a640029200129223056886414580f0b108038443e465500140b0303500104002189404080248a0500281101081a81e21000c0c7d82d40f044000d101d0800d8130308440001c4000010041c0c10344060410000c090200c07000d0016524206016040c042d00d01040001e1080c07003800d00f000c0d99615140b060740045941c03080365076a440c11100600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40736236 1250 40734986 40734997
    0x204050a080a030504060e060d0509010f06080a020901050d0c051c0b06010c020d021002030f13080c0405010f0e061c050a050f06070c0204050c0c03210a11040b07032003 74
    0x1a03000210001501c030400141d031030100d901500d0701c40c03400d401e0440c03c840e25024100c2039900400104250741d030400c1244107003480b5405900c000540110590042070644085500102d6640d210211000150395085142ca044400403507400c122484c0c2d5107040b032441480d40d4405584881c400c1041c01e41c255410402e0003003a842040d11900b5699454019200710500c0200039401c400e844032101c0c01070515450b1400c02a1003401101c0c00c100c0024504401c41e07100828403c0c910000301b10130846034104004e2050f03070110132103084c0701039814801c07035400c0c114051060700d10503100700d0082505901c17101482c035601c180d0348450a2040e80203040141d40c0701500d0000301c5680c801c11201c0000c00002244030381c0285c8459440b40b6011320345400304400b07050042c2c01540445810000b420301c0400400c01800c01c0c2c8078040320031050808046404500520007040c105055081082681f00300080350109e400340c8103d010b401d9121951402c0881c3c41c51002054000c0448120701c903c2c1e00c0010000c013030075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40737486 1250 40736236 40736239
    0xd18140f10050f0a022214090109050c1903020705070303030b011209031418090f042901030f0f050106141203091c03141303030e0303090f0910030b0406020405 70
    0x5019500752007000c821110225040c03981c0d40d0240d4042840001c140c1c0007000c40000c211185d500c882a6055100c0381c64000342d1141301d40e80c06c402400c032114207081d01101d0042c502c2020801a514082c03141440f180f18104400f0040480880aa0318a9000e503040d628440d40200c102c070355940e01d9207030160042204118150100e045130b90198041c030002d0003035460066140d038480c40b2004103000080019041014800c50120400b5420b907040d480d000c46041c0300d107240c0c0004040301d0034103042080600c0603020204030003584207040c1d080080c1c0d000001303e045076486045040c0e0901d46040282500c40c0e0208010055424240000303108ad892140e800070142040368172a03031101245149590380e106403600e00d07400030299100f03d99050200c407951418180607050004022034401031300c45041d840311a0802110a410f00240305042d48034503021010724081c1c000318503101b01040055a0014460840e9103d4584a00010f5100140e00d0b1807500441d0b0144e404425405d0914084010350800d01502d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40738736 1250 40737486 40737493
    0x90f06090506100e06030703020f0705010209011107030f0206091201050a060302120c0112050c070206040305150601080702150c0409060f0305060c03060105070f050307080a0201090204110f0d18140f 87
    0x400e64507200420a4001c2d0441c0c5400c1c0054150304140605e68000400440c2459801e00c01424074440d928010300c0d10901c1000016a9010a04000b500c150684060401c0652001c0303820300004828544090389a41c0442d9040d448401c942c0c00280c4c0c1c130010411011155007442d0501c5110395054101c41e054900c21210691002e411703034801030b698008150028006400d40d070609641440e0703944466003003846002c84614001c9150041092548264812112903000c00c00c0811030005c1044140d400800900e0b10501501745a6402581e4203840d80f030401181c000203021900d05818042141c3c002c0c00b86090a00900d0f0f43d40c846a6902240c600c4140c901740911000620300140541c1120320480c4141c4801d410320302c1c26200c00022400c00c040031109403104215a1001c41c0c9035138040d000c941495400441c5410043c8140403d840d0103440d400f10b101028842c90030041c80311005d403066205070590026003103500d950142c0451503600c2001e4000704a19080504200b00411380c0224440140c048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40739986 1250 40738736 40738741
    0x4050d0c23160510170a0b0409240501030f030302090102010b0301180c0b0910110307020319060b01080408030a0b01031805031b06010b160602093c0307030209090304090f060905 78
    0x601804400300c2c504613001803c01400e1442c17840003194070b640c0060301400b001400c41d05140101e4203c0f556810103850060101c681d4a640202c40c00c811074107040f40c0e44081c000d55146a5445003a44a03080303009081c580c0110b41000303143d100754030010300300500800a0140710b600451654a803404c00c601910407a503811800b00740c041010044555040c0c0c040c0948290001155040307071101802010031106000421000001d03039000c0041100b8242c011504800351b81060ad80b010031500700c0c014882c1406440744c1000003041c00d8405481d40184903020208150062000403402400d014401050a0300c4d43d1036503105024000025121044021070307000d1182e6020203400d540c0300c400f4803c1c1a445401049803100c80340301040700042a910170f004c0582403400e048005a200c8100b07607420740031020446a4031070700c0080ca5040d08440c0b20802c49081c03a101144020076160441800081c1c0160b103a50040b5105a40c100120b034028100c42904114058041050030054142c91044104960400c401f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40741236 1250 40739986 40739989
    0x602010c021917040b0d061d0402090106052d030f070c050303010303180e04060f0f060b04050607030905090a05040c06080f1612090605040c06050304050d0c231605 72
    0x5046441e500b01401c00b110000095403000110300880c2c0541c0b01c491814400040c2e0307414001c018110350008841d011030340d542004160710b400341e01c482c100c07000c41954070140310160700c1e0011410705480491800980c0c0d030403001c03810942440030303501850102811410424860a0f040082c500581c903400104c251510340e030b01d0464503806100c0c000b800a400800c01080041d000c1e03204900400700a0741282c3e003081d40c0e040541d40d2080d0858083d180107490300401300304500342d0b01c26101c4c152a024410044a402c1c041051402d02a60044500503000000c1c403100381409400f000000303100c020058803061030407820780405004c007900d0403942c26940a4003c1150f034020303c102481006004940c481d550740311200041d04414440301c4101380804810740c8600c144d10360040c1203901c6d0066402040078181441c0c0303401c0ac00420360000c820030400f031051000040000c40c100347c0c2a02c10b46070180c0c140030a03041464000c00000d03040520701c1c648503a4040700440124105141400052401ca13003242d4440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40742486 1250 40741236 40741243
    0x509011205060c030405070306090b0402040c080c07020f060d0204120b1302090408070f0209010603020a08060906100c11040213090b0103050c0919080105090616030b06030a02091c03090602010c02 86
    0x300c0050594004000152240007100702441d402030140741241c0c0d03415a40e841e0340084458007542510700f180118108801e60815019011050700c96141007400c0b850107000600032402280d8000f80306480d207501d07041c010f56408045d1140e80d00840c90855555030f80300130100034607440280846610b416040050300c2e10742c071500d1002502d6000307001d184660340d903030f6200040c540c800e03182241e804071540000ca0240c2c07141c9010501802580c0c400503034990000034064001c4a0007405079102e803406008000081d29003c0c00b880c4080d0643c10400c2041c4030714901110748800c0c400d04190082e1002c52220b00209066940404684010324108581c0984c0c40c0110190741040303490100c100000c2280c0034550070900e80d40b4600c2101d22096000d007680758071400d42550410fa0301d64050798440c1c001c0c044408451018000d141042e0b09040189640840200e07145000041c4240c40840e401305002d401900d0355802107075483c0856034428140680c5240c054040c005d54080c4038015071030f04902c84642400003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40743736 1250 40742486 40742519
    0x20a09120209070804051c08090c030a020f0603040c09110703030501050402121501050715020d06080304030308010915080d09090606050403050c06090103021903060312080f0714160c050901 83
    0x281402e00a6990202e081d241000f01410441305441441c0c1003011003248411aa2540101035a0340c1e44a4103000c06024a800c080d5068140710380c102c03118035801070f60f81c070f200044004401d035100c5482c6c1c0d82d181441101d40b04640c5c004080310341001880c02503d800310300108502c0744039441c200101c1c1d8a640a0008034059034165241400100000c40e07000f44d018040405550014501207103000c91035038500c01031802d0b0708440b5400940116070030000c4080c600503240039002c3d04c4001c50a0502d9600c0050414606204070700d00340796246601c0604481a81106021b828030030100e841407042d48000811a007103610403108668680803000c608648140f082310122904a8001c040d011145020400c4650001d801c1c5410305500300074a08609603c0848031b40000791548001560900d1410442c0289120211200400c4034400800c0100c40980c0c003900e8104401d460000c1404d426595041075034400c00301090000152403601d58204140034000c101514010383c1e964940e642d0f04c00307410200b1102d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40744986 1250 40743736 40743739
    0x30c15010e10080a031103090402070b060909010b0d0803100b040602031803010509030901030b03070f08160b0304020d060507230418090507050118050405010902121501080c070f05010e01020a091202 87
    0x1344002000300344907140700e10b41d4001714000d69240410004c006000c130b03401040304481812901e01000040d18042540f02d5100107200000d100d02c55a220000b4900000c08100804c0380354084041101200501520000340000258595446840c0c5402a41e01e400c07609180350000601c108042e038a0a040c05040d0141a904000b14200444c401c0107401500c400307010140c0521401d44000fa28404600002d8000e1180d030016140b50001d050b01a40c20f025640c116002d4141c04000f8000142c403443d0200300e4817600030600081613103995500b2130b50140c42c1d0054088041d040c0746190100c0740034100400844400a01c010a0f0361880c0b4511403e4500c40e4030f0107070081d000b4400c10059035001c1c0001503903101c01d0340740c2c0046c001d4803140050704940c020380007008040c1e0301140c4225240b013910a2150060b00000324240d4140c0d10f640020b094110003071585142e2000458142c1c1000701c80b24016070029844802480420b1310186001d00079000a40458002025148001102400007090541d1980c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40746236 1250 40744986 40744993
    0xb03010605010917030f07030f080703110f0d090501050403110f0f030f0c030f0406081006050316050a030b03031923180a030807110a09020406050403060e030c15010e1008 75
    0x82c0c00d04c120400003403884000c0c5140401c1103c0101c42c8155402010000e200c0d4541c17207403100718078000911003800105001d05161600300c045d240c0e02c8042d02a5980a050320388480d6948144101c2240a000d410400825641c02e200c20701c020143c00074451061684034204072001d203080510003581c4ca0747e41411440143d002002090300d6645480000e0240c08401070491b0b19003170103d4040304031540a5800580058114000c3c00064040c214402004000c00d01d00581107050645451102c03a000b200d0b21401c0c003000259040450340241c0102c028030310010300342c03034440d03900710540b2624080e40c00c040070001d403044022400e0310a00e80c03149000104888200707410010240b81e29021102039000050340003840303150000c0043c0703040000340714207882422004071b19208041404203018070780d0082c02e81280144000c0c040786a20001f0785080b2900500003050720b01441d803a450452089500d541c3c5240507020b840e44c1c400040c844914125080030394000191f039a1a0210742030140c03907004810300e503003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40747486 1250 40746236 40746239
    0x12020d29011b021507050102071208071209050c0d08090901050103090819020703080c0c0f040e190602090307080714030703110111010f051302010219080306060d0605031902040b030106050109 84
    0x191080c10b03002c0701620161040f001c0309010981d03030305160000c100c103c80580d0002130100801c9030136420f0321403900351402c00c44c40c24100000301410f0810550402c207c0550740b8080242441002c00c030740365001e100030346459406585420101403640c000000b840c041c04100000191551181c0301d49802c40f40c0001c1c4050401d0641600404080307407101d0413404521550070048040703036005004041c001404402070a07011410000c0c405480c2d40c549440344611300e42200300300101000b00d4542c00103820010701c800d60421a00d00341d40280a60102107406100e5100c02150315040012110203944920b00e50700c0b400c040040030035070344050a010080c419a43d003800307040107500035040f6038940d069000001c1582803150607003004849003110350b482c1e160095003190040d540c0512015100c0036004c91120380500c5245c460f40d015200140820740a04000500c1d240059426400000034001c018192400844500f10000c00d030b0706185405d91103240b400c0424001172030144109003c854041c1c5601c034809 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40748736 1250 40747486 40747517
    0x30b190b030403020c13020a0e1f110313030501090c1208070210050c0a03080610111509070e0901060504111206010e120718060605030c04050d020112020d2901 70
    0x7908040c104909520521441ea8840d50366116070510080c009040140c4908030340c1c100500d10391102074410301500c0909411070704c072140b80d43c40301185046400c10401101e12130b01754a1440c800c0c40c030301030003000c00004007104004040d007040030181e0040d400d1060698450004490f0401c100f400100740d91000c001c108018101007150756045800b5050050a001005983c9030400c00e9094040f00022007510400c80145003680b83d00c0d4810b44503240500004140301011035603003000c001d400e00200e502e0740c00602103200821690000c0d0288440c10103403410100c0c121406081c075806207a10803400c0421820b9041030f5401511f00003a07851b28501c8040d11014015584942c0c074482c0c1c23542008911102030360a040c208007407030040103550001c0c0f10a0940c0361030380085a0113078005000b081020000d1150201c0c81c441a241590fa0444940902050f9840181d49a604504204550038004140b504a0409070b900c0103000032480e0700021400305e6881d00d2a02e40c8030070301e0351450101d100020242185e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40749986 1250 40748736 40748759
    0x3020115231503040c0e07110304030605100807031103010b040209060a0807030e010c0c060b0604030f1515060e0a0519090506030a0215031e0601090e0901060510030903030b19 77
    0x80c0d00000e4500c00388041d2205200302c0c1036204980a850041c419401003004034811440c0d554000c0c16880d0100885151a120645902c40c40c1b1003d096503842d04003003030310307000680055002080d52004a40c0d81c00c0c1d6a1a00128501c81d08280502c25442d205101d1000d050500031109942402051185003448101e41900c0c2451f000d030403c1c3c01c0654400172086412424445c46d41d030741c1c0864540350985200741c5020300644000d00041e60203400c050008100181c00d54041055060f440f044030310040100500c07000090030f89071180001010640c10001d8560f03084140c60340803120075203441c2c8847c1e803250140840d90200c81c9215020300c1d131001040010141991219811131801030550760020304a80005591100b4581c0203128a000041840040015410450740c0f500040502c0140341c504200041c1090b002ca1140a54402c0c0b4000010002c00081d8842c4002d044010555241c00304900c0009004001848003100464501900c800c480d190007200c4000d00d104845e0076074045410301c1d041c0200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40751236 1250 40749986 40750049
    0x705010504031e050102180a0b04140d14030301030b040201020d0206011503020d0f020a050306090f0c0703080402011701030c0609060503010e0615070c0b1207050a020a060b030f060a0903020115 85
    0x80c00f007454007050000031420b000070107840a12800c20041a281e600400036103000c0c41c0d22810000d00c04003c00c0001c040c1c010b85080c00035002f100c400f00040d4007030402d0001410380741d10955550200100100402808205072030140d0300071382c202e804041001c030003680da0b15000e01903010010050322541c0b80380d901c660010440e105100c400402e40d00001c45501d400e82c0c021024100118101000308035450a240d500103074405000d003802c0201e8148048018518030420384050100b184d500c0001d42076900800704c29496011205000629682d213042c024000e0940d4011403000444507503000400f80c3c840c2c0c044c2c80c1620f00f00b02e000c0000362641800c010b0322214100c00c0c1d488101d42440307030070040381c40c1801d0341d8000c1c502c1c141002c0d07903034402d54401e11180800600303020900c0800d01416500310750004040b01c07500d501200c0011080612800039103018071440c281440d0f807203145c00300004e2002e5a00540351581c0700c1d8000f403001d00d01040700040340c0007032800740b240d441000c03140041c44041085036a28 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40752486 1250 40751236 40751273
    0xa0f060b01020304080102041401020613120503040206070b070806031b01141e120103050c10020d030b0303190201021201060219240f0e07050406050a0e0603031911070602070501050403 81
    0x78501a03550481741e0980c0c0040d480182c07034854089080000f541c05002d80d9611000d40e0302c901c610343e00c0a03980e8110030524070101104021020001400f10740b1004101d903011500302c1070200541c60320500c01400858111000c5000c1d0140481400c17000381c0c500f03c0440301a805861f0f005140b04000203141c0c8a421524201c103045100450122005950000400b008511141880b01c40e42c1181400e502d0b290de81c0817a030303001d8011003544802255012031101400e100c186004541c0101e07210000b46107005010400110384030b80707030741c1d281020340541c01001c81404035110300710b10341e0307072a035060343c58803400e815041c40c4610070f44a0000050104501c124110003a8288100e941c4009000d44212402c04440800e07840c1d540c81c80101c60042040040c0081034200e4043c0141410000460081c00c010f00c546400d0084000c04210760b0307a4240150b500d02401d07507042e50121558038100078281910490009954001c04a010803c0341c80841d41405996068645600d040e25640c3c0e1001c0500c03489200702d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40753736 1250 40752486 40752493
    0x190203100207030f140f030601030905070302060310030204050a0c02030f030c040e040c180c0e04020c031c06051f020a0b04060b0a0902040602120705070603021e07050307140a0f060b0102 82
    0x6000d229440038040c194065510100c20040b8010068070311070503044080d0800c00103004800b08001c0d0202140d512090a02e0b0100340c0315540d142051400010340c1009500c981d002c41089041880c1a44607412030380200d4041c0070341d4a031109070307004a0b4a012030308001030300100407800c0c04203003070401140c100c0c50703041d003452400340c1c0d0740e414551000c3c0a41d82241c134a80c4500c7d040128440c12125940e0801c455401003005440c01070003e009010085201400340d500071403640240c040610030f80e0ba610400030007036140c0b15002c1e2451001040c075401903d100d840410149444224a2860340190242503001841d090515440c2d81d1280d00c0700a10441d42c8035180c1503080c45680b2580000380007400c85140158a075410301c4806410b202a4a84002c3c050006200c280d0201e400086e40004980f0317103040c010b9554034221040a00c2c2c0e4504680304d00e110b400021341100300400000184121405985010280100c5a00c05900c8d1902a54050b291640b142040c40c00700340513520071441940140101e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40754986 1250 40753736 40753753
    0x10608040c0b030403080a051e0402010e01210209040e0f10020d06091407230306060a05090604030305070b0a110d15050310050103020f060a080106110705150315010809190203 77
    0x4003219600c102c400301c5c0003444050621802c40c106006440c0c01ca02542e050300341e1407a16a005004001d0000d002034100b12910b00c1070403069000f0140b0340c816080b801c604501828038904860042d5001c42d04c443d0049162020500070540d011031301381605d00078000078010b043c04000c3c1280180d00042d02600a25580d2040081c14502c0c2c1e11a0070072803000305903402c030946424400544044003201d00509203c4400784090b200c025250100ea46c411402c03284281c0303403080001c080707440d1701400a419802007000500401407540110207014101d01c641d107103150760f81d640b0007440c1c280d414940d0b5030000c0303020900c806c00000155410a101080115049064160713845000030319010084000f20078140e62100148154103100880c0805500162241c0707241840390a801001144144940020403114507810410b4010621118006200080100d00001103555040003070f0303171003501c500b0300e1250051107550b030340d50244408602c10031645002d00b500c0302c040f20500d041503225041c00c0381d050280320b04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40756236 1250 40754986 40754999
    0x711070e06040b040e0114010b030c0f0705010222090c1706060a020c0a2603070201080403050706060509040605091006050a06030e100509030a0206150d0f050a0203010f050a0b04090209010608040c 86
    0x20340003483c841c0300c000301f194107890284041d4007206811041000a041040100b501007002c00c4840d9400b10700314850fa10a680e003001ca0090040744800b40354103030254000e0315100c0c0e80c0c81940d0700b42c4444480400907050400016a62405502804000c452014001400a15019002e0034408680d030066404114500000450b03007241504448555a01003180220150f50610480d480c41c440a00a5281c0303d1160006401d41d10014401001c02800140304c0741000340c1900240c1c02024040e204200f14101883d10402900049402100c144a100c400300c02e9000107000e450205d80c1c02400c80c1c15242e0529008502038481503103105541e225003c64104030f54628440c2034840c07620b02018603141d480c2c41c20700a041101c0a4596031090418100081065444004c0280701c664840c0c00c070b104842040c43c25604002c00710002039410751900900e0002006150886441051841000c014101180c030400c0110f034a1800060340051401005104082c000c01140e600503000f8018041910365525 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40757486 1250 40756236 40756241
    0xd0201031d07150305100e090a050109080316031802060f040f031104050c03011809030c0203151008030a080c03061207030f02030c0d150b04020f040f0e0711070e06040b04 75
    0x3544850150311018040121440b00142c4034040503081c0780600082c1811b0100e400b2a5005000c1c04660305011800301ea24603400700200900654000000d1052085030704258880e90411541039035240f64090b444150343e40b09100c1c40c0401049403486000040c50f540034802550000f41588210101c104070110b040640e05101b88015031240c1d11200e0001494410711050707540103064582800c5003072005000c240030784a20228001c1300c048000440303030481d00f8220b910058a5101035010301582003182c189a07110051148603108801c416004e0075a035941d0280d0724441c14034036200041c04200803032482c50781c120040d600040020705054a1220030315206060550b90b600443d01c0e10200c5c0000b10850805000c100204441120b12183c13500450b2981060310b800000f04612041d42ea0391901860307500caa041c5c8a01c06201c61649465581b02d20140341840540d0182c501c40f600c2507400650310910808005405010100107401c0c0e0ba480d08041c11442c540c0603080c60b0b0300c02c0c0c81d480c128103140c42e01c1c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40758736 1250 40757486 40757531
    0x5090f040c081f0606080705030412030b0d08090306090607020a02010c1b0605070b070306060e04050601120f061a03151509030a0b01090c020705030309060703030207050303040807022704020d020103 87
    0x491000d40300c4000c902c0483c100d40541e0f0041d414001c10104220003180c0080c1580e900130f8000035100e03088284280b0417030040a0480340d8540c40420124103405000200001d4000d50f1010f80803107000740c48007985030307a0b01d003030407204180141d016010190065100d5020b11664a00c18202e0000c42044201c2c2c0c0c3e80340b0303000f40c3c001e000010000300d003000610001010103074104080d804d007000702da4144a4014107a80c0c1040003240500c1e1544041552a48031340c0c0e003641e00401e01c070010852046101a5035003c1d02ca60310418103480184a0300031241103888040f00d000748030803050351006003515420301c0a5106207451800c03445209014031003071601c060007180b01c26442a00303000f25031b40c1406094012500300a50800c1107520500c810301441d10000215801e0300f00c04c60740381e61149901e140c00c03000b0780b03d0f50400600601000c4140020802d21401401c02c1034805c5415091208070b0745003140000e060211a1196241c90401040250400c100c0768204540107142c0440c5492003031254005010a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40759986 1250 40758736 40758763
    0x405031005070207060e0f0402210412020c04050121050a050a0503030105091303020d050f1b0a0308180601060804061b020c09070507172a071404050105090f040c08 72
    0x860742081400c0340d060003004081d0038542000301d010b0100d04040380800105c41d0009000740d50005407a00c0015808105c00d80c0728801046054462403d4a40302c5508920342030803502501c10010342c05550700c0d085c0246816240c04000410102981c8007040c00c0301000e5080554035030045416081c041401400f00e119068080c0c8000c5680754509410b008006d400200035280c0b005214103400c0029501095040030784545150003500e803200c0300300d050010310810100c001c020300c0c81c00800451401c0410b803040c8241c0207440d182078545d1a88130703580b001b501c98000070030190400c5005009050003101501e401c140141000541411a88065000140c0c158400780144e801005403005a240c88c3c800b40d58407540e10304c0d21a051140f26038400c501d0402c0c05510b003441920104041100035200b5041004042d640c01640307108944070042c898803000c41e80a020900b8803140000000fa040c90b010317082c1210000303040c5091559a00c1c090100140f0040d05c00c480b00721202d40001401d1804214481d04c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40761236 1250 40759986 40759991
    0x21060209012601030c0f06050304020d020102072d050102030406020d0c0507180902030c04150e18030304080a120c050304030c020109050a06030b0906120a02091f090605040e0a05030f070804050310 86
    0x641c117004814603c00ea008400c10b003600501800116480000c1d0f0b03400c1941070f2500a140e49161006034280f0b400c0d60880081d050265a55030700c4001000920742c0c40200d094107c8d9020350f181c20049889104902511015038081c00c070f00c1503690300c94000090424040c405491007030b500c0b01580032207135500c104440401900c4005920070741c0b4040c00f94003403441045804100400446020221004441c4200d86489120348002840e052896400b09040d4285500b520b68900d0300303180c5650260001e40c0c0240001c3e80d401c03c2543e04503d0f070300c07400c680c103000c035100d0600310b50351941c04039103000041e04200e04001c0200d1001400d0340780d40c04204d01815042c0c0b40441c0d00d48602040c881d9418008025510a00d030082d6648000d81e00820300b5510650152015460740c1e4035042c01c1030000081454031002c00803203003000038003004554413407003d0315001c135414003c428000c01c800303985440c983d40250064000300031030203039910160010400103110311a4a800c05949200003410030f40b0011315011410b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40762486 1250 40761236 40761239
    0x1e031407030221010e15030304030206030c03010305060f0403120203070c060e1c0315030b04020328031704030909051305030309070f0506030708010605070c0519080721060209012601 80
    0x1000f0161000400c18411006062980b50000315424001c0281214000c0d5203600d0228180d07840910032100515000340440c1d5a9051a948050003135000344019a01070082c0c2000c03c0403007442480fa640a00d81580d910740c211803e03440ea0360b000b0351025142c0b009001e13040803c040014114040c0002800c44500075207440c40301001d02c010011000c0d0440c00c00c043c84d084044141e0380c80500380d182540d401c02a1142d0a556520101c1e00e014881103600c1515092200446480c15603402e02c600928883c0d0340760340c0c0305840e001156052840030340303004020900d048018443c0610310b9000e151700442e5214003404e10ac841d80c5030342d400d5500540d0b100c87c568001c644140040400e071014480140b0060341c4052561402c060010300c00b2806000c0c110402500064640912180110400107014000c1c5144502280d03408155600f1407030b031150b6450340c000e20a00082e04694481e04442d102d0030302040000045c03190350344034020f500c5108503905001d2400b201c50b11a85003e244929608860f640c0c640265 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40763736 1250 40762486 40762507
    0xd0b06040e090f1f15180e010b030c0a090504020406050901031103190b06090c1308010b040615080103030f140f0d05060604350708070303030e01060b0f0c0a08030c09011d011e0314070302 82
    0x140d04001403276000360300103404007900341c445000090448030010700025203901c41e4800074001d001c060b0301099001408000101c1400002c0940442404040741221000304007188100c059841003600a0100c032000d6000603854101805000d905c0f03007460b05071500c0c008a2076120103113640560012501070703554903004102400e05200381d501601c0c12850304054100206801822580140030081c204262528640c40250091045980104041c80e000d42c40d088501d8051586400280d120404c00b420a00800c180741400402c8405030b4092549200c410900348440c0710b1540e171010b83c41c0c000b01c2400d12202502000030310102001c1c0880402804000b40b071810000d0a13a2405284248244d2402e4820000e1414180c12514120010907078180c5030b041c00c1480c28100400b852000d45150000400c002d0308810300710040084135000d813544c003201d8421041c0d111038a404030340043c0c0420070880700d204540c004106192642e402e6032401241004c00d07103010010401f020768803030010980100e02009007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40764986 1250 40763736 40763741
    0x503190806090103020306181f0b09071404060c03020f010507020105040b0c0a020606010e01030b041109010912021309021f02071503150603020d0b06040e090f1f15180e01 75
    0x4504460b111900c1d4110340010307071104009000c459582481c4c185000612509004005c090300e100d030311400c007529035a034245c4040c0c84d140c0c6201d84202c146c00700081140c0c1c060b603100c0c01500b040c1c0c1c51040c10142040301c203554250080c1002da0651090b001e14180540c42400b80922442140d40042240e0505140858000902400c50400b8450600800480c02d600052066024100b442d00b6241c0140000040e002410a080c00c1a000360402c1070505000e44400003d051440b02aa101c06140d40c0d40c0340a045407035143d04000f0341c4074030720791040000354225410140d0514001000000714540c0d004400080c1814014030390090b030000542080b03800141500d01c60310312a41c0c20144440081c1032400030403040e8601907902410344c0807800c030402c1c869952054213480d1019103040d5036503485214030030411004a802006c54401e01540303503050301d40820700d0034044500110800e44040c8034000d0300302a20750000168200c1e41c000380005007a912007564000e0303852000300000b03008089140b4041c00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40766236 1250 40764986 40764991
    0x305100c021b09100305060a0501080c0114120c0c070603050108011b020d0c0c09060603020d1a010c08071104020d050603070608060f040908120910060609030c0b070c0305031908 78
    0x654201c030000b0b070000310000e8101041c109044520400310350f1910304208003078a15070009401c51180d64100114007409501450588200a0448001c0b555400044400c252080d044c400031540030720524007510011000035801c040d02070300701414007400070507841c80c00545910010009131208010030640c1e00a00c02c404560340440005c803010a008000079554110060080c03081144030300f4040c09000c42c0020410182c0b240071000d0000c190354400c010084c1d00601d02103e0f44914004000c52181c14040f03800010041c1a1250744041850352500c80003a044005c1c151882d03c2d01c500248503c0e13485200030000036040100020301424100203040c0703070030843d03000a42446200e8060004c1d0b569030380344d0301201010440340494a2000e03032078151140e000d190710120710115418107110407040003141790140d034008508100302a80d500d000407162243c003488041d04019045e202840a116840c0080c21118020030b00700a145942e590740c2e92450380820482180c1402c070742d5100c072600b58440140ba4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40767486 1250 40766236 40766261
    0x61501030506060901050702040b03011503030215091f020c150a1a0102070510051e27060f07050c03070b0306030f01110904091a070201020307030e010c020d0806030309040501030510 80
    0x341d0326210000c40d840340b1881075400d040c000c0205100342150380342c1d0040b0070030000c0a0f001303202e10420391900112099207400b00b20050700500e101015000192111103103d0302da210010004039440c180391440d80c003604802c52888580801104c1c01c0f00b40c0401800c40c031041a0314024085150100d00d0340210341800542d46050b0903c2d500d0009030340e81c0001e110081d500c0440c2c0014203040242802e950750311640049a030407402c200a854100944107006d0140341005001139003d54168030080e22207064000c1e0f02a621843c00c1c002c80c41c2403011a0090a4881e00c19011141d9010700c0500103841d00d4420703841190315100000c01c1000d1428140084800ba00b0300708001d000162240d800ca40190003013140c4d0074000d40d61400b601e410301c10040401c4a210791050707041c0030340382020345009010350b01c1107410802183c1003804c9050304040500c200d4552084550240c100040340d000100e64900000c0c1c003150b407520040c06010142d0741c4a104090095102d0300082c2203400b1140c900701c040c0c40704403100307a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40768736 1250 40767486 40767491
    0x612010c0509040e0c1f050403060e060105040e0307030c08070204020408030c0c0a080d050f180a09090501060e0403050706050a0e010e03070b06151204021309050a060510061202030615070506150103 87
    0x40545e521049034024650040c030300d4078042c0305180c441c00c80d50f0b40502d52000d8000d90510740300f6601c4100c082001410785805882c1071021170003a007910f0b607480c4280d8030300600041000604401203000c04019040e020701c018400351503d031361880103501d1070300f000700c0018803a008400809510302d400810000204162000360071040190240540140610304c00c1e03d0007400c001900181a40c14a0000d4854500c010190010b2984855040307000b07008890080b5142c0d8a8400c0208001c02c00c074500900c035a0345591a985068502d90710b81e006800d01801b503440884d00c51a101002d03190a008000000304890000c54817076920b4101602e40c2d24001e00141e024a5080e500c080040641200301c4407011050804020140c90314400300e4541c1c1d154030104c0b00064074103840d1204020020030340890072800341000384590b07101c11100d00755607aa14458800410084030320816120443e4000c1e6602101c0240030b0316843c0c400040031085a4000e100032035654020404102000000d43c6802c039051000380ba04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40769986 1250 40768736 40768753
    0x210060611100c0e0603040f0f080a0e03070f06111606050918061f020a05100501030b10051c06061d0f090c010212030406091403030a06080312040204050612010c0509040e 75
    0x1d0890604d003d030190244d0340004c006014032141c0280c10015640c001d00c845400314850408113210340090001e80005200c0b14440251850001035140641e070256071810f10003841c1050503504c1d100c420034502d4a80c02049042c45104200c284800c00030443c64458581e03e0913900d04020046024840c3c840d00c8540400c144a1980c60324400b0600c11003154401c92107038902014181c1c40c00c0d440e0034000f40701d0b00c1403640340100b20100303802450480b40320b850003145548a4480c1140c007180c40c1d015854100300401c40c0a402808100c1015003114052140080c055484441c1101c3c000d10f00c07503000c0148454141401504401c03200443d500490307820140415401f0000000d49880d2120a021440f10010011034240f243c907902c05c3c0d01031640314111b001051408008070380c40b07400488000224514240300000c1e4268044100e0300403e850034524030069a030740e0300b0080180405460184c104214000c030400b091070134807503c400450152650760711040c0410401060b1140c10f01d240d003084c3c0160b00e4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40771236 1250 40769986 40770011
    0x140903180319030c0f0c0603090c090c080703050c071505040203060106180b0a051b150106020a030806040906090b040311010b0d0f03110f01060e01080d03020403080706020901021006061110 83
    0x410b0026605243c40b41c22864541004d41240d180355001400c0600d404200040c00358260b4131200e4090701c40d440003401c040d542d443c1c660031a13082003088404a64403d0010380c00f40d21950207180c0c0000c806481c6403d10180ea21442c00344e800907080540141c1d6103005100540c5020040039004203003500c2c00f0440c00440c42c0324004240228803070200070f01d0b008202030103940d00810586000d10b00b4820b0280391a524001060740e194000d40300690a0540f81c1d0011841c1480810610212500b40d12032090720344a060603c8014400d0311000e4405603a01c100810014600c4d2410030b0203180241d07101d802400000c1c07000350840325940c00c118403c040094032100041c010f240045c08158041c241011407003001400c0074142040401c140c2655440c040b804a0440d04040105041c5d40541007180c82e0b2449440b407d404a120750b00015128840500002c000034400d03030000c20003410103205031072000301d8602c0c40f40c0a4503502d03001680800e4815125801c1000e081000d1480702813100d4043c00300c940f0404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40772486 1250 40771236 40771273
    0xb10020304140f090405030a11060c09011404050301050403050c0105070e0f040c111002040603050603010c0504051201021c020705011b0e01140c0303040506010e0a0e0607030f1409031803 82
    0x7152444907044102440d4030b580c2d541444040301c120240c40f8420700c1c07803e0700d00302da01c0c3c5d80303c1e01091010845185108410440c00103100e032044940f00f404502d032010180055400c0c04051003401070b0418200300205591300c003801b5041c000ea1080c0c940c940c842c20f02031900d60a40714010644c404129000c0620410781c6e4500f01d05003414482a80c0008507041c1d5004110340e1494506804040340c420701244000c3c0303070103582c0100100c603450398080200d62108001c260a0710401100c500000308148005d00a6103003101c183d040f100f40650006180642c010040c06075040c01c0c0e20014a0310b03502007841c9051190a0158040340340041c48040008507a07080080c00c0a030140c40703164104100030710042402c01000e007c8400c42c00c0c0c408112600d91920f1b15000c0c0e5a444240901e1800d040fa01020400c850b096000e28558800c9900140010340d50300c540c110002e080c203100046080344c46001075070358980710012142c0030b101c1e01d801965a44007d01c07010300d1803d0703035a20b04030f000340d00942605d4014244407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40773736 1250 40772486 40772489
    0x21203070203030c070203030c0d0503091e0a0813090905070501090b070c0e09010603050115030c06020a0503030103110607060f1413020f040207050124210b130c0f0602100b10020304 80
    0x11131800d4a03010180082481c0d8042c01101c00c10354465200e22110309500039020718445c2c2080001c8901d8003021034210800d11070b154051546a0303010a101c00d00089941c1c005e040c0c0c003010241e0719210700343d44403010800d4070a01d18080c2c0d104e81002c1d02c00d001559021b0100c1024000544031140b9040302d0f039a6451400302284913201e1221030604c0880e10740710003074010300300654205000303201c01c401404140010765045e200840d2601c1c205680040c01600128000100750b4100d00614296031070340d200c100070982c014407100e030700000411010000403060721940080035140301000031074620a004200d81e40340b0150091505a518a650000503a54a801c20718860342c00c5d02c000d6241d89203803400b10301424995521a544451030407602608001240c0d0010844008901450075114a001fa45889803c04880a41401070800000754000d85006030480c13070038400e0b2180c5404941d03030540180781c0d4140707400a41c01a004044030f8003490740b00380101d4402d03140c12180b1340c0140083c00d1000c3e5807071185 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40774986 1250 40773736 40773751
    0x6090e040f050106080a140d0206091903020a0b070237031407060501170118030507030c0201110714030714030c09150406090b040f0504030f05070204060b040f0602120307020303 78
    0x1801c109010800290050401004c04504403000b103c1310303150048104003032400c181a00c0c850202000c03409480001c105008d90f480e10042c0007444040020140580b80451040c0c2c258428085040001030b100e4003902d00c03556075640502210500328201d066144c44403403e4101041d44403990903182181c036282204000e0b80b40c1055038000f00300745035003501d0b8080c80001402a0b0f2810000091580e20940d035402d243c01e24000801c2480f0b622802c040052518040140010b1400e001060019014142400300d5500504050100b42d04100600b8a01f400701e4104200b0700d0107080c1d40900b02d04041008102800c4510183c5183c403a4290200c3d0342d801d061165503204e89a0b8001140c408810500e102c19544009402404055180e820f60000351040d194081c0c0606d1825950f541c04502a10485014503415034401040030403081c030440305600005003c0c1d0b40142c0c1c8076000112440004000d00c0145920110708090f1440c1c61406800d0201c001c0200400c0f1500300708101101e1750100440c0e030b00c0910f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40776236 1250 40774986 40775003
    0xf01050403020c100908030703031b03051302040506060706050405010e0c0102070305030d0c180303050702010f080f0a0e0f01020705010606080c040b0904020d02090301050a1406030a0f0f080702031504060606090e04 94
    0x1349030004841182580e44506c410b40070001c1d408040c164141c0140715014000c6500310038420321100200c003114011105001d1100d203040c0404014503003504020b0700070300c0080146081240ba522240304444082c1e0b8115480da541d1680700c010f1a605000107920040c0c00d00140c4411880d507101c2940328400d100006810741e40d2020202040c074002c001030022483c8907120f0f001590389a20340900f036030348160410fa000c03400200ea035071000340c82502400e1149000c0c41180310103481d0308404001030300c04080700d0f03e4140140b1030017030a4110700b40b010301041406400045101890080c010b809000050304800d4800790801003401071003030040c116000c29800380c80042c0d80b150700c442d01c00005d0003018211581942400240008440300b41c100380d6510514003205200e94a80c4070815694402c070540007084840070406145c0030a200050b022106d0303000f00440c038500400c40d80024142446c040410074510f5080050001340f000c68400c250242000c1e00300400c80d1745c05c00d09065110440104010101030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40777486 1250 40776236 40776259
    0x901020106120305041e080a060504080409090c0509070804030207120203030d0603030f020124090b0a0f15080f04020a170f121c090b070c05010b150a020f01050403020c 74
    0x91003580004024601c002ca6102605850303d801446030344948110780c1445a04200d42e00d6008158003003000300d680400081610400b20703910000604401482500c484000340b0001820000500419080600c60b0a140c00c08034280807c02104985c06464401044108410040000e0300001d0000c00d44507062846000f440103880040e16511402e50b0002e50241084800020190030a981c000110116002400003d03402c1c03121851aa40c019030000e144c803111002000f484825901c8814000f0000c3d0105400e02e44805c074240300b10f030056104030000d1810100d030480d90780e03100c1a159000040d030741302c107a06410725400144030300280d8007801e255285809d440440051007000740d0140d001030b50007920500035101c0c1d00c003113180d088140400c0e6442c00801d07038142d003940a4030418011507800302c0c0d506800d44078907608440492050320100c0e910340da81e441c00005541d17140c1d4113120380a0041115036440042c80e1000341450a900408082681070105200011340c002c1814000c05c0c200383c4a40c800017 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40778736 1250 40777486 40777489
    0xf0506030f1005040f0f0e12031501020109060e03040317030c040308030711070618050909070b0306011103070c1701020307020a0201120212010b1b0601060e040c030b040c0e030c030111030c09 84
    0x100072070760241e503009150102c05106041142c1003002000c1b000c0c842000403100e16105940c48040c00c1ea075003a0510001c00000c0c0b41c00740300c8a90804020018400094510a160b85103000c40d0300480d40724800c0d604c00700c0d08000300710300c00841080c0140d508050754214100704002605501460000400188020001a07681d912a017031a8003802407910489002a13983c903005421541c0303034400004805150714000c0b4803420304541560140054200a00845141000d044c0e01a0005865603040011884405940c602c080001d800f2250151149249070f610b0482601d4140700c001c030201d8140c2e401801001856038000c00c022001540a080c920074007041540b161003384200320803450075402c40340011840065440207880d01100c920280b0600340d244c1140c00d81d40714400d1144000090b0401461041c80c18039030010b400000e107074100400c0e00382c4031400003001e5031a6501d6643c0042c0140550404a00c6c1c10003000001c0d0000344c3c000c11208006016501c85844014043c041c12100000d0034283c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40779986 1250 40778736 40778761
    0x70c1401031103100f0b0a090e0402031908090406090b01210209040f020301080d020f211201060e0406060305070c02090408090411070c060801051c050f190c0f0506030f 74
    0x8140b0b0070612140d40c0d01d04580d90414101c2c0d14042c08040140341c5d40d0210741c00351a04111080c81029849080245150a9025800c070b00c00400483e09802014020080c060003031801d0b00b0032074805c107295906c0f11001c20512080b2072280d032003040080d0401000f41c20903604401d01a40c100758001c0c4001c55010210f43d410060310441b411150080d103000c480528552a681c00384d41038980b18419507031480001103049030b0301c0380710703212100b0650440000030300d240c2d0340ca040c2103003e0b5016445203820480d00450b07082d862032f0240c0c4140045040104949150318151050078090702c0c150404000030306003210010184608450003d0281e100310340441c042c1b001c011306590b4554002401486061204825800c8030f4001500480d000280020003240744c50143c0105070583c0c3c8064086905034141c4030060b6180345903071b0400e0701c0b030703001fa0500c2d40086241030050340c0f011101007000710042004c5103454030083c1a903034413046c03489044181c20f0142d6942c000460f034210b00c458103d200b09480c0c0070340b042c41c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40781236 1250 40779986 40780001
    0x40506041a01030b16140f0405010201060e010b1b10091101170f010605091f03090219030b0705161a0702070b040b0306040209060c060a0911030d02060a1d06130501060b070c140103 79
    0x203000d01040341104001841c0041080d12720a0313000b03010441d07036500d0f901e0101000703010b01005110240001c40c09200041f540c0c0101c1440e20085420806001507850700325070741f40c8003d9459a4409030403e03415600f00c000826200c45441c0780034150b203000c0003c454105010700070b01042140c0090130903102e83d1001b450301d00d0900074103041d0545111040300a0010a09000100e0041103070512000350b00b68540322007000c4a0300f2203270941040e914200c044500da0f0091505104410304001400049a5104070940703060f01895001e00a80c2044070000e8900001c036070046904d2582000306004100a1209680d00b0107400d803000b50312403030301e0070024041e4015039200350301034402c4004000c100c044603000269110300840030203482102200a041c0c50760600d48010025a000c0c0c808110041000e602000262181d00f000c0b21000c66510155800c000003a01c100c107152040c548c0c400280902882240028000880e080c1e00c0c00c05240e682070010300d4507100d81c074400fa281c1a54000c20380d02035001640c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40782486 1250 40781236 40781267
    0x30b0303070b0f0f010b070c060e06120403090e0604090215030606040806190b01030b090708090316030305162303090312010312030e0303010b040506070515040506041a01030b16 78
    0x14a1403e940a041011030448a1807841c40328003000084000c000d104070b03560980c0000212400c0c9003800381c03c1d14440075844a06400c550104551070384c59009202c41d5024a21036501c0b1003030640b41c0800100c04d44400f0302941e12a6140c5001440180d581950603224040038110060316903540700700040050140d035010310700034055001001050f2410740882c10307010031001400c01500b509800110112000c084941d5006800c1c0700101d40d54030300907100e140d840040041280d1400440c44040342c40418450022030100c2e44a0050041400c0e004524808141c06840d040520040301d001800b16040545043c04c40d0400c0007000c590b40310bc0910803a140e203d14400d900009503500e10b040c45108403001414000030b860a107225001d4030b404012203040b40d004c151407906103410401003000a61010104640340d1095184822440039603411541c85180120050425450a801c01c50300780307400004000324040010005000060080345459002821101d00b915040079407a01611400c0a591000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40783736 1250 40782486 40782503
    0xd0e1e0301090203070608040c09061d10080304060e010801081203061207031e0201020609010501060503061c050604030302030115030203060102030a0f0309020306010806010602120403020d030311040b0c0309011716030b030307 99
    0x128040d600711f454603000d54403882d15500c030700d81d441280d54200d940c1d41c060118591182d0000b00e8004032030610403a00404081a001c002954030407407a4a10362065214401141c6040015041580c02103049401400007202a00c20070f005505403496511000701f12134821080000b250f01804402c02c012000b4691040c40020081840c00c100c400794258503904034011b100384d000080a100c01801618100d41980c3c41d4581140ca9100400082c6901d041c810311008030103000f000007082041000501035070081d1401a070f20350600503c84107048441d01c0c900245401001844640d036070010803030b120345c1d0561030036101c80a003504085024010125010758144100800420b0440300455058100c5006400701c4001c055034042210080c011840065805540103002d440424000c0d040100050119600946000d4448034503654a4001d00d40e400e40541c004101c0401c6c95070415000321200c80002908038541c50801c400206010144210004160306e41c0e610900c9501d0820070b4920703250b803140c4038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40784986 1250 40783736 40783739
    0x40c120302010605040c050901091502010906020d0f110f04030314040504020c060702010605040c0516110306010303050d050c161502160303091b06080a0b01120f0903020d0e1e030109020307 83
    0xb4080c140e90b01406100703600c1e100d400206240284100c510042e07040c2c55075080c00303103040b080e040300388201d00010040d55243c0584400040d580c1c030003000e1103120f5240000d40e5a906010031811a98560303e283c0580d1b4003080705030a00780070070042e101280d030300d440c1c00c51441500588468082c0151b03170095421a001103841c407000a404507401d80f00c0c0307e103030f03000f0880d85581e88104019600b0941b09040418010804000300814400115907101d0148028442c43c0000764042858254241c2c01540001c80101325065410441e000d010f402c601181142c0d4144401d00c600d03282800741d2904014080c42c50095040b80007156030301511546a50b008564804959609000e8040c00c0340410032119050307558642c29034a4440042c2c0400ea6030165508013640e501c40c0d82c00801041b1300c131829814010040c0001d01001c0c03003030241403446482c00d0000b00d665501460f020f03203007155001d200c8050183c079111000c0d042d00d4101012481004a610640c0080c0240010078010a01300c00c02035054050b40a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40786236 1250 40784986 40784993
    0xd0b0a030f0204050a110a031104030210091a0f0a031d0102030a020408010b0901080604020910050d0804031110020d0e010e0909010501030312020c06131515062003090603040c12 78
    0x11440e0140b4000e4034140210f0b40ca15032580308079000c0c0805094000d505004000b0903500c25408a036040e00c01c140514941a143d400203022148822000c2c03001a295083c140420348103080d181e0300c03031183c01d030856042103004001c01c041030007090081020103550f1038a0a80c1d4605550b0403003900c002100c001c540c0c909041400001079403081c0222000341d03003484001c00103401c08130407990480780c901c805462661200e07403c201c14403a000d0100720f1000340840c4082501d45c1d80a541c10304080c841c111090750303240385203850b103646140e030001944070701c850444864095401140a407021692407400c4002d41042c1d0005940c15407180032500d81042e03000c401c01002110540c8683d050324080e85800c0080c4140000c104264130801e0740e8407109400c04004555000a81e11001026503c15400701d05a10300d860401c0b4101c0712041e05142080e401ca69041001c2134006040c0c40c060303c1c00481d40c074140c50f500050240d591003100c42040c0030380000000241441804594800942483d10058a022800d400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40787486 1250 40786236 40786253
    0x13060608010f0f0308030403030209060c07060201091e0302100e12131a07030c02060a11030d05061009080303011e0305030a080709050f030d0f12180b01060201020c120d0b0a03 77
    0x40c2c100c0064501e50106200b60031030042c0007102d81c00b040c218a140e40300e680c100c010390000741d402600408144110114450203204c024054000ea600006041d070090410130320840501c00d6002951021030300d141c000c01d9000c5190030003850b12100c04600200e00c240610b01c2c010600144444500700401d0186420084d40d1001c021145940d0464034a840b408514204511540c4d00050211f015517200b1001405c1c40e20180010b80f01c903040010030044481030351411a480313000004040c59a800420202d07103008a8500c034080c8192400b90416402d00900035503078030060280d82846403260341201d00c0f01c102c1139807880146500505680d01c5201142000e07040d24400d540b0319020604001020501e810000310001b01d84c500100249810942d80106486900605140000304900b501001420303040e0b17070040300000c4000c0080d0100720449800d0003400150180c1003041164010005205074160004440d111403281c01c914956503500303587c1c104010410504460307081082100008240141071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40788736 1250 40787486 40787489
    0x5190c05011a060414010215071107080304050f01030b0f0d0b01090506030307030e0108100306180309120302060708090f0a063e0706060302040501171204030f030e1306060801 77
    0x380001c0c000035016114a00119618807401c5400c488140800c1041000c6410f1401c030a04042c0143da0f00842025080b0101d00402c4416002050102921241b070600030880b04004040f8003000e0340c241030031b0a00003052504107000c140d04240d1108103407500360f500e4482d40141284002c0c14803085100b14a403400048400b4401c07080160324042c0007032a03a04010088545881d80b5642d480d00c2c0c2c511000064034504006020440038000449020001985030300ca08544017098883c020b00e0b82c503072460014480f260b00d8001002480301414801c0000e5000220290465800d0400040301d41c0c80c1c0f2201403404036411260364071441503491550601003164410034441c100d4030000300c40004246d000704404003990103500c00d030440481c071241c07a0045c00405400c0262290101040703843ea40d800181c00da03082a0042618451142c10040c650001004054020102824068201880d5841d0403440803441e0030b02409120300300b0380d40580b640d80c2d900c03400001e2035013100401c2501d0301c81d10000e1070741009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40789986 1250 40788736 40788743
    0x6040203060f04050c040c0e0406260705060711060717130b03090a0318031401050105040501060c0506161b050a0201090602010e070b0a0306030c15090b090108070309020105190c 78
    0x1008089841d5150109002e442140c1040050107903540410520005003508845041000b030419004052942d81740070341c6009002501e018820740001400d403c00418254009803100e604c40d1004005030307194102500d900301d40000380c283c0005004401724100c0d02c42d05030020700d8444116075800304c1c2881507028204400c0c0504000c00a02d454041070342d0f05101c140d880031746c00c1d4006444c210000c0d00c91488800c104800c40e410641c02c5030f81e0b40d6401a4001c020101200503512140140302c2402d02e8482c8900401e40d52032f041d2001e185a4803216196040540f146820007050409060070314040c040301d4440e882305031000c1c01a0781180c00c149440b01c205120881c00074559900004e001c0f44140241c0c201071039968080d00100e803402188040507408401c0700b0003415290745000011480c26912100100018094070100d208070420080145825800c406003824051198030300c1640d00000c01d0740d0000b140e06000031041007900060b516030080c0c41454070814091481411801d40c041c800c0880c6621 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40791236 1250 40789986 40789993
    0x120506010306050f2808030301030b06040501150c03030207080301080303060406140303040909050a05010626010603210e060307031d0316021302040803040b03150301061401120209040203040506040203 88
    0x5800004505440741031141c180d21105044248500d07180420224107101c00350700385044072000d514400d01d00300505620100c00d81c0c10100c01002030006a48440c1d60007030080790100706641c1808104040d140001e0380c030b40204145441d40204050003581111711175078000c1391aa40b00d686d64600b00f9030b07075401215418010341c184100040c1c51802c80900c02d800920050145040074104500107005165551055505204801c15100892800c2c0f1545026001404014071544211007100403021b5a003580707808143e04d00101080480c02c2c000d8074040301607440d80700c1c0245001c14401100c00c4425840303599441607000080c0000b1940540c06008465082ca2031100302c010b030080c1d0300c0c1d1030f80076108800320550003844440005160500e101580d43c8440c0c00014200740c3c0303a200d042e00d107030050380101c200840300000b4040304040c01262200c0204003200280300490030301c1c0380c551011a60803c036a06201044000c004200040d406441240078044d20442d01c0345840d042240c0d9618081c0c405902902 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40792486 1250 40791236 40791241
    0x3120509091303230301090c020304051c020102070e070527030f0607031109090f06030f0304031b150905060309070909051006080a0b0115050408011803020d0f020c060903120403031205 81
    0x4913800a800c1e03e030b02000540a0031686440c842c400035000c0d208041003140420080802c80741d03200300030b03415414414101410b41c001c5500c00686010015040b003035010600c00d041141895200c406c485205000310300c0b4802c05e10740e8883d554032150004d05d0311136050103441e8412906280019000f80721b0482c1c2d54091010540001050340039100b050b641d00c0d00401075000042102d008500c0c0203800000140c01c4500c25010400f43c2411034010fa04200c0d442d10f001404504594240071101000c0c1454a4640119214010011341111814854507002e1507001c000034880c034405000010007800410000c0c80031110034a0a95160704202500c1c0f003c0c3ca01e4040c1c045800140000c03031046c0d00b40e120000001c0c030b9090191021102c00c441084108200d0108804182c02600b8021407041c8050742c1941007021803103140c00303403c2084a4030b1780f50411a81c6d50f1602041580003d2000c080d4105a803101d07900c1c071100d00401c0c1081c01082c08008859030000d00042090b41c84150710f02c404568030300400140c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40793736 1250 40792486 40792517
    0x61b03071209060c0c09020a02070b03010f09060b0a02031206031e0312070e01050301090906091202061509091b0d120207080709061d060307030519020102060603010c0903120509091303 81
    0x200641c005c0c204802c10101170000e404103900a151030342c13442c01182e1603035549170000911503000340c01005e000da048941c1080719655502440e03001d042204802824400703021f41c02035407405545503210150381c21034040740d8152014071400300d09401d040d041654505000355555902c1e88440601d40c40300c80844001148a0310402a1b030840b460140e450a295074607001d2080b01070981105d0641d01c07641d68078080c100040d0124480a0101e1031034002c0c02040c0340c02180600c00381e19170081c03d805124007400b00413000c500498000041101000340701502d29000c00400e0b8070002104008049071a01320340c648282d50005940c50450748104101c0f04ca02e9110310821042c2c0741c2c240304554456013510b904410740c0c049002e00310380c0004050100c440306503498650b0740c0740801c081c003980c1032104d83c882e5050665906003e110f0344031800340c00a010241034248010090b40c141e10028241c0030300180c1ca40c8031107205108590141d80d005207044442c0c24043d2103c070020198000481c041855150059000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40794986 1250 40793736 40793747
    0xb06060c0607110106120309030b06010c170a030e060702011401060f020d0305091c05180a08030909070908060709054b0303030a09050c0a0b0306061b0307120906 71
    0xc0c0c0140c0000d05159140d902e015030301c00710040f003405965502c030480410b0111010704201d5200d4040d55658000c60310b1800c002100c0319010b060103040211102c00d000104bc0e142d90542c40c890741e280c603519640c046056003100100104045801c0700d000e4102803015003681500046400300000010f0755660343d88100584164200b50380340e40140e0000204403da40b40030358800c552044001d03080d02c0d07000e20b0080440541c2c621030030010b4040386020403031110030038201c0003201c00311106581d1042c11909040c001a030302d00440061a20070010100020791940c451400c640081c08414121681401d01040117400e42904d40207050064050340001484080d0712241c20703070101a0301102c0c00c001d911451808195020380d0021345190406260343c00d5036500c01f080154410084124001509001490494140340c001c00c2250b1003403d00b030906000c0390b2040c6080300d40080c021551141e440340341040803c0300407116400000c10b40030203e850800c0c410024414801140156540360300562a004281c81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40796236 1250 40794986 40794997
    0x40801090b072a02010905090901050f090a020102070504050403050f030c03040201032901180f0803070614040308150d0602031302030601091509020c0102090402040f030b0105040212060d0212010e0106030b0606 92
    0xd43e02600c00b0103840c40d000301190683c4460040c90592a0315442d68042200700e80c066403082c4060399607504002042003640134180c5c1161121015248440035600000e42d2a076031405800d01c916510008502090300540c2103403c2610328540c101c0e283d241c090130701c0a480d0400c03582030b40844d00340114811112851f001d181c0003034050b1b90f80d51483d04c2d010702c01120120400201c25000786c000f00c50224107036050714084401025907000070f42ea151050314089081e81c07c1070920300348011010013480006500850000d90251111500103110b04040740040e03546110b520740544074501c0007080c030180f4400d591608401174020b804840321641c0e20401e2000f03c2c0e151300321805202251403802c5c4400e6416400814178003405100260030a61041c000030126401540180c01840050800b00200144d1084440c010182251700b10705118654030b0342c3c041d403c03004000521401603012428111360b070302c0c04441403850450000308030381051a50414001c044a02080e02c480000070002a21487c1543c100c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40797486 1250 40796236 40796267
    0x2210c06040f12060906020d15050402030c0a080901020d02040e01050f0f0f040b0303070c0b0306150406020601090c03020d0507120b0303160f0525030309050306040c05060c0102040b040801090b07 86
    0x1060b94608043c0b026201c0030800d049550940316907403200814000d00142940c1c030000d040000300e4900e181d041003030450080e40180e00441c0140104141e1107200c4054580f510300a080c17409540c1d80340042507009101d0348820083c15480030401060719003010340ba0314140d810544400d1080f0310300300100442e0709142d0f0182640003600484480c46030510f42c00419800303001400300c1307007007055594407070000901f070ba0008440c4240c0841041802c0c07905c0d010001110808403085071a060030450f00946440d014060500802e0311103c0141c80c03540b29a04440210344000010030070340c10840001003034402d500c1d40300281c00b801c044a002c5c80745000700489040320406448030f022031407d540c6018810000c080c0c103075814042c190100c4d2803298104070705004007106032485400941940f401600c10066600480d0199004804110000d00303510400f4003514000c0340c8094031182c4000380d4502a2056410110a0407000700b40000d604c035054202c04600f0388944210b00440d5103400c01200c001080f8503284 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40798736 1250 40797486 40797509
    0x3150a020f0d050a0207030f080403170c04150e1201060609140a031e050712030f110115060201140a0b0604030605070210050c0c071a0a05090a0302210c0604 69
    0x42950005034001c046504441d00d00c681001c0b242808031089074811141132841c2a0001815410550310050010007030785c150800c0c400c0340c101900c0080a002c0091031a06090000101040000d501802500c005043e082050006005003002c0142903004120140d40100080e042c854525030301809890151000780d03880314105403034480c2140000502c0b206540d0090045500400810681016004040c00301400810203001a203400703454148180d002c00710b44d07100e940428002030350181d20440e41050a2070704c050100c007140703030322401000300c5034100a283e00e4120f00011075a4041d000010320103c0302c40c65900302d80e140c600d84001d6560f410341c61a441a41000103000281c105c1c1c0c0041d030081940d20468800480b440e43c41c00c22a08280d03140542c2410110714003000a80c100500009003c5481c1852200c19160100030614003845441c00f06110012442000c1610b0b403114810046070000c04500c8540c440028400c0fa44003510900e032503901841150fa842418080e08560484070700c102031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40799986 1250 40798736 40798741
    0x4060e2a010e06040906030807031d10050306030c0a080c12060601050702150405040603030908190503090409050c090c040e1f03121214011805150424060203040f050315 74
    0x45070141c854802030303944254240404175501041e481284046c61180041ca6590101030501803c480404040c844a5031251203060140f40c80f00401c40320603c107142041610387d01c8010000382080210b0035070726008031000000203499440007034000220801078030f03a14101c441495040f07445038000c0312f041e0f001c600c0c1080359200509040d010040d090001c04074035400c00d0f84a00001e0140c0d141680160f000641010051003181170902c441300e40d007100340c0312030403260100b80d441945078026485d84521640d6184180c4043c00f00030b022690741e07850010a81400c03460007040c2002c580c0c02a000f40d0010904c801c000411506200310b00364680d800489425142a1941d034895540044a070101ca0801408054030900c0080901402ca2051039002c0c03885541e604000c1d64030b040c284e80340301c00e410a03424007052200e2070000720081940010252408a086189000d5044c0003800d00c0e4100d100c280c01c40440006c4165010002c2c005844070740b24911545941d840c10141d40c0c540c40c1c00b156120f036415001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40801236 1250 40799986 40799989
    0x1b010f08161107030501050c270a05090a0207080c100b10020c090a02090301020a0c0506091207060c02070e04080405090105060304082b020a020a0510051003060b010c060504060e2a 79
    0x14184441402c00202c6030403030b40f40e64580703081d12015204000d0070f840124451018071030500c022864a030b4001251201b540c400d0f800104041e810341f2540b805075200c800416040542074049a00068204000e55610810241c49690302c580035940c0c03143c0307185414a51800c915101c00000040c0c143c96009044c1d0188072000c101c00410081c214202e140d40c208003495594800380050b00001056880344465a00d031410401d081640040100c0c5070b541001002e41c0f0500d003000240c51032907420080000d1580000c0005901d842c0c01c503040710450039000c3c1c041004100d4410000d00940d4800c0d01c42c103036542d83c0c5009000a87c0015640101286c400f8007030180c807150b00e18110045100d03400d0b00030040a600140303140807a44003184902c01604044089030510500b0000550311800502040201d898500e031419450040f0b808000d2070702e2b49034810245568171455040a1083c0c10003020401c0e4109071500c000102000c403105c00d078500a2062601810107200381d05821000d8642c0240000c0d0300700c80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40802486 1250 40801236 40801247
    0x2a0106030b0a020d0609090f05010c08070c0f020d020319050c0102060402010e09150613030b1003020102070b3001062d110a0503030424021306030902121b010f0816 72
    0x44000000c10745d0b4410024103d0040d00405109038010743e946c00c0c0d8041181051400d4820340c1841c0c605100071b8106204202d6440364624140f25081071000028104510018182c9081da070340c042d50502c94102c0b59100c401c000e80c60500c2d0141b0540484119956110059840e0202268081c0c081948000310b044141440e1407160b41c050461813102c400c4514900000d0800d82040e00308c0032041c040c2400900400c5410b080080c0c105203c0810541001e14549c0000d590303107420300451110141c0400c144202507500c3d1500361664254403c170802d4403250030214000c0e40424498032000840c642c0d82c4142800d0386540c00640b504030380c203540141c0d100c2440c040c3c40144d0f0710507051016204a00b1464082030090010314002c500c03414205401600c3c001005407030070080d00a000d25644100040d030ba142d6240d4502c64102c4100b4100407640d018280006503d03861402c070804003900400081083c3c0c4012400c1c010540c240981300c0b0b40f800c04624074101d40048003155608100c11b42441183d0409e0300a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40803736 1250 40802486 40802497
    0x40501030902041404120f090308191206090207020a1d1b041701060603050606120103030e040b03010903030b0a090218040504230601030519150e03090301022a0106030b0a02 76
    0x78002044d204000580c2c070180d20300c101ca0558102003241c510440341c1e17070f01c21441c0b000002e00d46001c0361094190384030400a8031402003c19507203140030149401a82c00382c2121480c403281b12008000840e40c1c0d44044e0040c2d03110036400c902c140700ca00e6000c1066030300450700c0d500608000c0781d00c08455603100c025000c003540402c15040080e1080c000003d2600c005000d4044400191001080e418034042000e407e80b07030003a0189206070000e02400c100c41619400050440c0c2e010302c3d01c584a0707020900490010008010110b03010350814070080c1c181a010f8004080d240001d0720405801a614140e542c202c2c00b0f1070314400601400210111401c0c50103421254100740902032000d00344000f02070680c6003001c1c040e00a00e464000384c00400902c04103000c4070201c1e0007145100c3d00050070598860111040b200b6801d50341503500c256450f84228100103030741080001400031540e6040c2d01c3c4540a903034400307441781f441c40103207a0720480c0d080806001c0c003000c0380d601c0380341030103a41c450507032070b0b4081d4006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40804986 1250 40803736 40803739
    0x3071202120a050c0105010e0601080f07030b0a031a0f0c041a1204050609120306010503010501030915020319050603030c030304080703030f050c120a050405060106180e09010c09060306060203040501030902 90
    0xd01c0c030714800c4070744500000c2c901041d9940700c955444450211103403d41380164014940c40c0340c1d880401002c0c0e60011074803079105100c081003028a0b42c4e040703020740050082008040d0072801c149008800c0005c000b45c040107298050f81c443e140742d900d81401c1001c1034021907030301000d054140020003072881104842030800e00301c070100508140a2150180810104460903552580308005000c1021800c0c032600a0203050520554514540007001802c184010b2086d10f04061341c801558040c030915000f4100c00c085412000e568a003065040321810101c1b160303030b03caa010303d00004100c0d0b5160001c219480742a40d070f40518116540ca484031085500925026010b241c0c4855071780c0e00000d8140300306489401d06520700c030b880e144081e4040720a60070003817500800d40d18086c00c0c8004500001882411030b00c003490091040c541c00b42c46c4031622562607002404442540701844000302064201c044c843c000750703030b07400c129540da0041142900d01e244110800350f001004140250b51190700450300b921300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40806236 1250 40804986 40804993
    0x90c0d03020f12070b10030f0803070c0212010c021e15090f010c02060f130b040602180d0c080c030d080109021b0607030b0901050d0c0e040c0e0903070b100803071202 73
    0x3840381c1c1641040d5045031400c03030520f4009428010404001d505607001103030302c0d40080b401420340d50781c000c00c4490381c50082e00c000408000200b55521810360909169800fa10030310301c0709910320310720380030f005540345d45400b41c01440707a1103001d01800c01481850f941010000c02c84079490b4a285008a100a040c00005015540b49080700150900480c001c908196004100307615025101d00242c6101404040c0070b603d4108110001c41c3c0c800c071030300c0d8210341c00c41e0005a50380c0c0d080c039010140400c00c05620b5008a200c04150041c01140701036801226141e005032084c1c44814002c042d03e64400b0106d001c0800d00c01c100600061140d90f02070020364554080814442803e591198509801241d2480005e61030710360300e09007030420890050040800380e0f000203240104d942c441003510803d020328402040c11800081c240141c0604500060408040301c0c01903041c18440980c9903484103030240d030585016004580e0710750410301e1480031148100040d40c10401150340e440d900d00ca40421030b608520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40807486 1250 40806236 40806253
    0x6090f0a03050f0604110103050403050d1e0f06031202010b090403210219030c030c0f14090a0806090124030308070c060216030e03121c020d020304080c0114090c0d0302 74
    0x10b00030080b1400500103080140701c5807500349003040051189006890415007050140800a600701041e11904030301c4900200300c9200a054100401c0031451920500c02e007031480c4c11302c0d81000c40c1d000d0020740e80600e0ba950ba003540301c188180d0a82c0e0820011a410000b8407002070f010900c1040a40c0d0301c0c9014080c2c010700040040724540030b88c1c00c2040c220801e903120701134422603a0303054450b000914004d414107000c6201c20140142041c08034444540901401c40c20b00148100048111619010010554601c29484e0b11079507582e910200c5000b0030319032a0640da050741c400e5050220704281d030000340011b140c6040d90b8085450700030140101d801c0c030500e1800b0b840094810300150541ca08280d106415040c0c541c01c0c0107011446410405000303401048618003100203030411210381141480440781c0c150000f600c180d00901c1880c2071020417a10200901c001c03c40f405000341000d810210082c044000005044030700d42c00c090340c0016107a4040c002c040341c0713810b004941030442e60290042d0f55128 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40808736 1250 40807486 40807493
    0x1205060a1e030f060605090f01030209180a0606080c0a0b040f030809040f09031d01050717070201051201030c032a0504111e090111070602030313020a0503100504020405070201090206090f0a03 84
    0x41c3e910160031200584c840c2001d00540c140b030300005500c8440b2000300055545986c000c204005d50190100c10440e03603025283d440510100b2002090b0743c0c2c03044080040c2079440c0c00843d200c0380789191003441260f8140c1c001510b8941c18040d07070151081690046960341c510380ea0600d04c0e40c45050700c1600f040c0c03500140001a0718034400d4407602c9019845852500501c00603203001c0384000c00ea241d0501406002c0348004c40d252140c00410405042c0b8040d5403540f450006a4441c012a80e2094100305c65038004004c0004403620340003100e101d844202510401c0801c550666425100080c682e501b00d04401c01203840d00d6007110510407511040c080c541180e0138984070209a4403141d00b2070012000494041b9564459040b910a1000c2009000c4090900c5402500c03031201600100240b41511216010355403a22070110040c8030080441c0e04020917594540301414040714180d1041d481d080000307444c1c90043c0603400856a008100f5441c0ca40c81c1c0040004806813407101036003040b513048012000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40809986 1250 40808736 40808753
    0x1308091e060325021902040b031203040606062c011404090603050105010512030c19032a0201021c09050418080a02060a0509070e0115020f03191205060a1e03 69
    0x21003001c0f0382c3d40100003003400049050288101003004540c000381701ca50a80385084501805140e04940c00b06420b03064400213480c240080d80043c1c507091000052204010040d0320a00072540e440d05c0b622102031900911400b503440a000e01900701040020450b400d61054a04204ea82c011009a5007407503140d80e01d0b242115070305d410894032a0740d180014405172403c3c044c2226161801c00007146002200903256882d1280b803400c450f080c5907000860010180030340365007500b401111080507550702207880018900b00d5085d00982c0540207040122118103c0c85180c0030321003211303403950040d040ca800c080c44010803550401c04058a2964001c0c00051540700040a2b4040340d43d0090500c0d0412140f410121032015000055030751011004214505255002d5070450710011312450031407040c03440070390500d02d90b04891052808005915588803c202455201802e0036a590155086020704840e04548096401c160b120629080800c59155429802c0190780c05103a500e90b10f00703640e42e90744d00c103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40811236 1250 40809986 40809991
    0x5030a09060e010b0a0b0f0406120207081204150c0207050d03140c0c090a060312030504020607021002030c0f070e040609020a031a060f030a120e030c060403080c01051308091e0603 79
    0x90b01d07512a13034800694640960040041c2c03900103103a074980324911103090450b200380d02c110024405c0010f04440c0031038081d41070b07c902540002d5065a114100c002008642908503002c44a22802262189000c941849640701340c00494009011003401c1c0000c001c0504140803046080046800303a00c01d1654440d009040c44a81341001040d030b0030900820002214001010b00b00c001c0d10304403003040800c01850a041800c012800c0000d1a41c5032400412114030441100ae13400c002602840540c0702d13400401481c0c8480a07205680460340702442558640500d4401d0500072040680072501240550f400001424401450314011940d80e41d81c0c03402d00000010200d645002c2e2004020090515503403800103902c044000d0b009903005951501d1600c4d040000c040204070441007418150b803002c00c20302c0c910f03a07001041251620b90f6860085115407151041c0b07041d65081c02c2c080350100d650720052060280d4071404c0039080c82d81c0b400600c60a04400c032540700900b04040a80030140c1c580300011350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40812486 1250 40811236 40811261
    0x90608030406081605030105100e0405070206060906010e0f0609010302040e10050307150503071101060b0c011505010201060308030a020315120307061a0117040f050303071107080604030f05030a0906 87
    0x58a40e440c2c014003070443c40004186614000390701586035081544070b800c581c1074440884403d001e0104544084642c171128180c01c070b07001480c01007408510b5400141ca076202d91000c035008071481c4d50303a030300448484c14984051600011107a03c0c180d401e20f000c030060024094185001420b1658400761074105140540e0440c1c0100083d400a0200d81000d0180c00d000c2c0c840390b892001c01c4120220000c0651100428150410480a61100303807103201390000742c0188032098580b07495014640b00c1500900c818102c00200315003441740080d10b9401806018100e070307041010a0f0459880300b079000e029500041c500d911400d81e448080c18280d071551a5070000440c82001035480d5811840d0950840300c852440300042000709081261707c2e82d02211640c1481c01e0441c141d0203c0d151883c05030000400144020704a020100030841c500b9441005004003034981c200719514130f651045640d1300d6420035035010700040c1512840341d03441030242c002550400014079001034004059151030084590121034030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40813736 1250 40812486 40812493
    0x140303010e1503030310060c050114070201020d06050922030e03011b021014010b070309120f05070b0301030f140a0c030804150207050d0b1b1206090903090315060307090608 76
    0x4910031441c200b8401d6520541c011491400c00c40c010410f004a944501c03410003418500300d804100c001e402a0300c41012a5440796205c3c02d01d8400a4080e412202c40508594504440000c0720714102c503540d40119181454280c580b801c4245041603046548000d9003404580307058008281c809115021034507580000d0000700d40c400903c024205503a2039506480345042c8504424154a071840c40d60444132604c2003983d991209180a03507110009600101c41c0303c03032801c0078030107103c0300010764100d15220b44291081c445d101c0c080490f07980820301014080c0000b0a03044000100320204101d980050304080385c0035400160341c1e40400340259082140c030341001103010088042c0307407440c2d10802219030000d009481e0419000ca80a001c1d10880688081b8500d0003040c064038047c01103001604e200c600d2596907402e0030780030f071503105000d41c0c29901846d400300010f84601c502009480c041540140a0075000c0c200740064a241c9102909056042c002c0c0300c00080c1c80c500728440c000c0103141041c041d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40814986 1250 40813736 40813741
    0x70f0305040e0901020703020607080726010906051905040f0e0118060c02012304030e1003060e0606160b06010e030a0c05030c090105030d050307021608010504020f060903030d0504140303010e 84
    0x1030340000b00c00074152584607801404800000f030b80102d00e00d40d02c0b04041c41e100e0006c1d0340750201180c56646107914418204180f41c41c4a0311b00d0407801c00541681c002030010703c02307640d4071000d01100140d07000c2060201e40208a050009181507080141602000c84002ca2101c1c445c07407d075402c60ba030340142c501c0c07105900103552003046a1400b0b0101104003074002006085062035641d41640030903000810340c0380c82100010201409801491450714000d0004a082d21603140090002c0209010700c0c3c4071115808001503041c40d082d402ca54000c1d030569102000700340c0c5a0364681010704003170500c9040c8850340c0e541c0105030301d041200001d00c5002d9929100c2c00d501c1c24060500f81058000201c0c010040f0900501554078006000c1d048407080d860301643c0d0b036030303a860700300d0410141074034425905207104000911b2440540205014900854a040e22070072203c080280500c10303859003a4140d0414010300c0c82201e1103a00c010340c064061a1049a03040c0d10403149170460740242c00c2202c0b4508071505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40816236 1250 40814986 40814999
    0x3080108060f070203270a060f0909020a210f1517060709030201050703030b060d1a0f010e01050d09020a0b030708101a0c0106050402040b0a090803090108041e02030607030209041109090f0408070f030504 89
    0xc032b10050006900841c54030554031002080e41c1080c16111035040381e0440781d00700c4d14503254030820703600d4a0420308002030a80520181050081441b40040b00540094402e030148000b0600c1402094542c450380da6035441c59005480c1d54000703401c154141580d803500002d00303840d104014003482c5000d543c00220001c0d1000420100c2c84981100c1340200c0724481d0300580d598101002000b141000d0074015110001b15240340b02810a03108002e4010303442d00c0c0001201007105000d58042c848a4460800a5540b003c0400d071740c21079403195940c6404091055001542c180005204100e103050010507000e1321580070609981c415400482944c00c0041d224034460b601c0f8036000c02030001a40036525000b19007000802076100071300b001c2c140c904289064a2124078800c00c8114166010703083d1121441c01044c0a0b00035081501340c10301a0f410080114050782b220004c4400645009140034000c1c1c40d00a010b2044081c01070044802681c1001608007282c64032941b8128680701382d0322075583e90b04140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40817486 1250 40816236 40816247
    0xf0f010609140f0403051e070f0b01171c1101180302010b030304030b06091510030605010206010f03031d010c02031203060a09061203081f0303080108060f070203270a060f 75
    0xc480440d02c003000d0080c0400750005980e400d40040d0549007107a150780d4052460f00e0726031074200d8940d5604000041210400020b210f0f66158140a05144a01aa170342c20103c5d040082510441e02c1c99042294858051040ea2000c003002c5500d034030f8103801030070707620290b1400c4510300d40303009074000345400b041400c040d424001c5820210054001e0360400f8a16900d00008200c0038110358486c000080001d4039a0b035001d515101c4084c1c00406110780c801c51180c02400402035030103003900500a0000114810b0b40300c200c0242266495520500c60912441301c001c84c45210544080c100070141d805400960b408211410652070301104c0b02c7d680307061420030003100c00025131085007000d00f400c008008039202c414080036100d41506007080580d0322a03454404030180904104050342400b00088249944840e805050f90302140c100c50180c2c030b0300100f855407094100e42c0400180d100704010488200124050301e05150100040002541c84030000303a10044141c00510014501403000c40c405980807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40818736 1250 40817486 40817501
    0x2061909050d15150b0a034a010b010e120c0910060e0102010c05040302010c02150c030d050a020306030706110304080307061a0d08030c07080705070306020406020f0303060d0f03020f0f010609 84
    0x41c031407010010701d0141030b101980186c4100000b49a665048141c0c02400d11080b42c580004a44240c0b00720804900786000c10200d070002c048141c51501d2901c0b21a0b6814070541d032020304161141c80940000710f041100c56240800074411074000d254455019403510030b0014000d15620520002c0641084001011a13042c0c14520f8110fa0400c0e20780ca181c00e8010302203070107483c0c080c0f070a0080802d85002003428000102c0d401c1c1d42c003240005882d08805404000b0344610704c07080b4418007450702d400317044005034081511100c1c0d15400011003048820f000758420700074549903505503401c0c2a070785e80d0440d0441c2c1080c402541d545807203c603003680b40404c1c462904c981000441d0540641542500c900031039000080c400c1c90701c0c90000400386c00f804114019107009a07401000c641e842038030791600c28060b40181c421440540308031030144080d410080266880b07001c014018881442242c0c4940341280045242901940030b840221200e100b0180701009500c89103a00106031a440c1c82d00810131a2100d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40819986 1250 40818736 40818761
    0x70605190903081b0313090e0f120306061606050a0b0a060215070518060c010207110603091504060e01020a020721030503060d1b06030c08010e0402061909050d15 71
    0x703038002400028103c0c410790b0300340000501400c4141411000eaa841d52181d07400881d2031400e0000002003290443c1c1010720614840c4040c1c03015000c900c08190780e1a6251000840d0700c035414000902103080420284c03404c040182c0c1c2d0f09041c40e0711a11000f003100d00640b03081039129140c0a0601c2c8a0034008540b9009004503c0144407c030400d0181042c8850b010340300d070301003001c0014034460080d401d51052400d60402013200c1d503130344000380d0658000d5120035021145902d00d10303c2110145000001c1e02e108049850140c002081043d0301d5059403500180704441c40d550310015140c000400340701801c0d44c2551900100b2a690610545004c41c2e00081e00b50381002c0b0041c0416030000ba0b01c141034030f030440010f4520122211040c601245410054898800d0030145098005070b11981a04100c1c1c0c0e039505900e411000741d03224100c0c640c2c5d094040350041d4200c0d200700710900b502c0350b00310140d551800c0e00c1e00c0e000d2901034840c1d0007d41c524640070420303560380300111104214003219200d8a06104003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 40821236 1250 40819986 40819997
    0x1801050c030a0c0201030e0d080907050603090a0609080d060915050f0d0b040819180803090d1211030301060c0302060a0510030f1401060f0918030801090b06070507060519 75
    0x4200d40300c0381c1d02e115000c006030800c28500081000c40e4001e03000000c0d0420303140c00340c4104004003103004000050848202d0414030500000103603c1c14003600300c034001c4040b0000340070300368560307298000909040102291340c2c5200b00316480085803648038103c080c1c416004046080422504d25560070f40c0141c109038420490101d900c61681d0314540400282a4810400072190342c03a802e00301c2c0799001d488644c40c0b5109140801180d030662290540502c00400704103013900a484d030541695078010103e00b1500440c60f1002000413462941001c3c989880071b1030401c2e40e00108003113160441c1c00c02e81c801d001150100502c1400c040e014029143c1c0325035140c01c20045e83c6007941d1564800c2d64030340b0000e48101500301c401000c3c00340701501c4070b86211100c00240034655031781120b06c1903202180304217594107203003007185040310701198484049142c0581d10700c01240d0030694001c0081c0405079815030702107801c1202e01c00140080c440305000301255102d0545400240d50405036040a0000c013004005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 40822486 1250 40821236 40821247
    0x27050106110606220f020409020d020901020d0203040e01170a1403090307050904020607031b08070b01050f120c0f010504240311070b0106030c0309050a050606011202130504150317180105 82
    0x1180d5540284d8086074054001c100d48402d403442400910558100003003040c00080c021160980c0364004200254003a800c85000a1403800c04a031203011703a0007100005070308000100100760712110600c44100810301aa80340c62003a5488241c1c0d19250b595030000c94002140044c1c1926080c007020008003000d4481a260340340ca94000b6482e4130a00340001c083c0102000c80c0c004203052806001c0409510001c1c40f95109518104052030340b01c01d20405201e115046d000450742d041c0010300c86041d1040d4070040c0884040001088490f0310740d41080303030400c4402d02c400201c01d51700c01642e5031013822204801d002500d0300e19006058501c0940b420080708020055040000c072080c040504440262800150815003c2d4045018040002c000703400f501c502110340c0148840442c001e030103640240ca1720058a076010103807205030f00460010389a0440804400c210600301034014807442c00701083c5000b00303a9103036034641c9006120000c5145a140c00418003800400350055540041d038000d003066030405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 40823736 1250 40822486 40822519
    0xc0203040b160c1d0c0901080a0504020f040f0212010b210c070c06020d0807030c0c0b090111030106020a120507020a120507030506090309190305060127050106110606 73
    0x244501d1040c0307200450000340300d62020500025100200d90702c9104108000d9480c0704040a102c90010807850791200030b00410507050003001105d00342103068481c811540d40f1510100300402006000343d8104482032200300e819505c51203080b00170ba8256400503164490b00d44400300701d80e8160051000b1140c100020442c14100d403810b0b01d080c05094000155a0ba6070a59460480c040c05600600b0303600c0c4107001280c090380201d0900b103000b50f980e4501d11181d64110049007600d000f141303508041003c6090b40e0002c601031b010100ea1020b5410f00101d000e01c0b03014501700705940264029001604848404020000e9003400c41d004071040e8a0074a003016100d40000380e00710b6040c454820340d0743c654132082c810450140b200c00000d5410a0544250340340808010751664440103681d07104144a40692008161852400c02902d81082c02000c19a08100c1c401030300c060080440c45c0803080c802400e010104031b42c02214003810f019138646450326003600ca40c62802c0000341001d88034400c031002e0b00244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 40824986 1250 40823736 40823743
    0x302030307080a02030d0f020405040b04060e0a0e0f0304030b07120509060f150d080a0e1e0105070302070f031101031a010c020f01111b0306010b040315050a110d0f0501090c02 77
    0x11074100c2c00041e5603840d8a041649148214070b00000c030a41000080b40f100007855015000b25982500d040c083c0305a50000c1008903801130154203807100ca82008280f04940e10350203480e124a03120110750400e041143c2e1a8030710b0300903130310032200744411908200c845a4429111500c01815403070074800c509080a0840e10380d1001490800100b110700002440440303d0700c81510025406842c14400d0007030f500300340900d42c2c80301d43c182010030040381c40c40076a03003001980702c007103010010100c508840b00440111021b501210781136045218009011801c8400e203000c0c1c600541c8528101d010b402c120900260541e0382d0140005403801d416854011666000b189410f80150704a03410b1214508420040e917407120f820707001c00818480d02e038050711102044000300403048000c17000c072042607036200f941201600c51070100621040c1000b10500900c0029002903400401d004004903121020461035001a040a8803140c802d64075195001c1c0b0104282c800d0a02411880d14107001c0302210040207581e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 40826236 1250 40824986 40824997
    0x90a1b0f05031f0308030702060a0b0105040b0906030c040314060103021e0306060d03050f040605030a06080d12090501060506071101110106120318090e0d080105010305010509011206060305030f07050111030103020303 95
    0x143c814062082c810307006400f081c02c0040d56015201c140c4a0528600095a41c0021241540c015151480100355503000e0f4040d5030031200020f200b1890850307804180f06440d003010701078445004085c480440010001064003407001c101c50006d002944c95801003104640a0920200154011741c42c05074494501003030080c1c0c468030517224003c07140d10510b0704039414031407140d180104100120b00420310990120003980030f41500181407125030703201e0050a840c1c410422100c0302007404000f2a03c0409825041610a28002ca0000038110350b00d00102e4442d500c400011100d000300000c5181d5190380181d0807a40e8060060000c010341800d000710507011274016200903050008025241c60308086d05501ca5003c0e0030944d2081c44651251110300b0340c2c80c03100310803920106208000201e03480d4440e10403107040321001070411030070780d103004418494204400310079038540b40c46003408808500c080005044680e1249085e582c0c56800c1d0400b1401c5440d2480507c610110400041014ac0e030f001050701d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 40827342 1106 40826236 40826251
    0xf07090c02071d07140c070906030b0a09020604050121060e18120d0c050c12091806062203050607090e0a23070e090a1b0f0503 56
    0x41080c1c420066081c1e41000c4100050b414500c41e81c0c0780c100c0001045012854a114106d5150400019801c200220b0f138403004100f040210014810794040700d0480c01300711802e0582d0000700184107511a060401500c40d8003140d0722202e140f10040e0f07040700600d08200d0295030301c0516628441c12622540000300c3d0307282000144d5004210085141c0c1d26403038561400c0c2200520400803d41652070701c1c2040300a006058403c1c8040106484d00c03051207004a884209850810a07209200401700f03084020510511115403241c1096403100000b02e2128120710030310259021840d1107175440900280b140d9014884030390b170031103c40b0080e00c0d09038010400300c1d42e41142d060190313581c9002880010f13400c07543c141808005011700941143d500e2505e140105000310008501c0c0000b518141841036032082d41c2490b0b105142040044403034a810079117011011042d0291040c04028040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 40647486 40827342 := by
  have h0 := BRFrame.cov_init 40647486
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40647486 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 40647486 ≤ n) (h2 : n < 40827342) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
