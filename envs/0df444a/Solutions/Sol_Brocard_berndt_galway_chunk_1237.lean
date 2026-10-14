-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:55:08.220089+00:00
-- url     : https://prove2.me/submissions/af53a331-0674-4501-98dd-124861c638a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 222302158 ≤ n < 222482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 222303408 1250 222302158 222302161
    0x14070f3807020603061807020a0606050a0b340c05100e060a0f1115071e020601031211010f050a0b1c121e0306031104091205090402040806090a0605090d08 68
    0x5041c20f0005507007019001c2c014048805103070600300a00c820a40310080160030030250b100620001d0b0041502400040703a07001c130380c1450045690320303034410030165059440e4031035422011118622005291400c040e4010b001e82421494902c12960160107074500c5800e044001094061007681400d14210300603081070b14110b211070040c0c6000d1041c2600744108180c0c0c03007124400c111b06001278030742443e070941c0044003410084d1740030b400000100201c92034480c49007000007000740d0001c1e2048c112a041005184044000c40f400c45614001032204642e5600f4941000701e240d950790f1081d84503c071101e000b000034140c220104450511910a180724165030b9100c170744046070080e02481c40307031a0345040c6024004125074912038101c0d0091803800103c3e603148400c10030300c002102070000b1100212420404030350341d95202c042e00c105004080c020044003145d00c822548840e411034001e808a10111071083c81c02c0201030346d68800146040324401d08080c0440d24860b000184030903003c00e5500c2d1042139 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 222304658 1250 222303408 222303413
    0x8010902070b04060513051209030f0d08010b0d0f02070c050405010b090a0314011b030615090303020d0c170403290108070303050d0603120f08010e1314070f3807 71
    0x103800003034062480c0003406c0d244c0c000080c20030884203529030324424103a606c49840004050410700801710055450f00240138540f2107aa1101020b4103550080d94225140c079500119500145030b16803003585900c0c0300243c128140700300004032100f282c03401c84003889581c0e01d442144606000e000441078124803960028000908008031b09041103d02e8000015140460300d40c02c1c407041c60007096240807960754074041c000c2c03c0000c0c404240760348031424528405407455400a40c3d600346c4c62810803c1001040c00c13003042082e4040141a601021014161101c0d2a41801002c24154403564092103142d09038145d00441c501031024101e8909002038040a071441e00c3c1503600c0c3d400320218089113940d030302002c400540b04174906007294055030380f00001840230003c054011081a0052144081e96004001003070104e0b441083c036080d4020003512a17036845818480c0b40140030b0300b1041c0c0c4400c00c08004101890f4070503105445000b4040b5407409d03014090305003072405503014490346d540e030001c02086c1301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 222305908 1250 222304658 222304661
    0x50a170307021906080606091806150a11210a0507030318030809010b03011a0f1909020304170909010e090c0301110a03150b091513140108010902070b0406 68
    0x5150220000d40e8988200e55001401210200341c10b015909500300e000d006103940b1585031540100140c0b4000d242080c50320010b48680702c1124440c00301100000042c0c40f9880c2c01203000c01c50442281c003103440304070b4140c1c0540b413030041c0c1c500712490b8403d000510559804803810507040809440449151540c1c448049829510191044c1d05054480315502c0c1071071800d014001d05c6078000d81d504815030801c04d6601d802d44554001d0a842030381006900b41042c04103003030710300c070040080f02c4008103100030502237400200070700d00c01c903032403420072074000f802e401c00f0b4005520440c401c110701075003803007a02582c1503e03008041c0c0b25904440d0460040c40f45031030324231042d501b19441104a0b51420001d00c00642034580355400070030b0300d1001180c64330303500b0f03018044d96420525031040c0300c0c2c0250800500d0715407070040c41c10841c4141250a88240c05650b500112080c40e860326400ca00000e4851020046080c4101205c6002034514000024403c0c030b140300303440c0c45941c00540707407500da16183c41c0c050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 222307158 1250 222305908 222305939
    0x1f0c05190f1808011407030504051b040b0405090a0507050904080d1a09040f140d0c0f020409020d0b070807080601050a0f0201020d0612170309192303180406050a 71
    0x6091041d115810740d01d01c0d0b280c41c1c09800410f2014000b05050075081084181110301400758800d143c1002c091100007440448da00d642c112030750328404a51011040040d026100c402520350f0050314000a00c241e06c1804200c6c5e40d600d500078001c445c86144c0d680140a00c80300101d0f8080e01800301800503440c0d61005030000c844085441c0c2c51812104c40c0000001d111ba18240c1d0221012a03884207413a040180f4040c101d0250100380000e00400507150360054298501d04000a01c501c903088003002c21543c980e40030651482d009450001c904000303150110301c1120544080c4086440d03e000a10380e10305c107450442c4609010782d40c83e400e041301001c2c1a03504c40c40c07155060040d55001d10050b00711070030320f1042c14003c0100803403400118183d03081500b1128091a042e9105001c20070402c912200c000070800b240121024003081c150071306081c805d61040c0c1c011100100700804020f00c28801d0400400382c41c4008441c00c0c0005400c3d01762080000f111034500c2100c1e000f0328410760070000f281c0e0601c00f11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 222308408 1250 222307158 222307187
    0x61203131202060d06080d080115050d05041e150e0a020d08032a0a0306050301020708091203040305030f0315010804051c05130824070c02090601050c1f0c0519 70
    0x95050140030304107202030b0391154111b6920f80d80400e0120103603680c0080c00c6030041218090707680c003806030b07080010098894415510381c201d881d0400b0808102e03461440b0469803a030410b08602141c0c0910700300d0f0311442d00c0321345030204031708040c10882203860119146446550040c1390f180121031580d94907546810042510750300c4244a0b42c5107a000c1078840d40e024215125181d03070380e0756040e0044050101c4010750415400b0b40e10501c00ae0000504000c03c4904024044420440c60016681d12600d1841540c0004080e03010200c0d194464010501c05107028101801e203000c000b102030703401100c0306041158060a01d80c401d04170a8030150317800c0e2410007101c480d440c219280c070b4852410302003107450541c0100320507408480d419001d1141c80201850584555031700b800141050b200c02085202c549001a00c901a941c0205e003243c0c3c028002c03650210244800d44e8034540c0d502c4006003071300c1c03001020448a141131410000200380b0400499a210b401d4103008109035400c50000c90300242080c502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 222309658 1250 222308408 222308419
    0x209100f1101050403030b0a0806010f09020702060f0a020c010e060909190e0a0c1d15060901170a050103020a091e0509070e0108061006050301060c0605070212070803061203131202 79
    0xc01d020008203005880c4154003d8a02241c0c144038501032060005136540300100715080701c07005000e82d80100c40341600f141c2d900840962100003078000125940311f000344080e0700440002e08000071503004103402d007030860262035410507100701e4030500000744146400c42e0b0f8842d16200024141c109805d8808581d01510f910000305000101112454008021000d0f5903255040c1c00810500401814182401c1c0040f0104a42c3e0b04020f298a60380c4e10701c580c0114400c010100ba0211140d2080e8041d0903540e2402c61030f0030b0136051906503040180300c207020070380c001c840b900310200303804c1d1282c040c144020100d03400480400c480144c1802c01024007030a004080e004141e00002d03486e14294005001e00802c078043c110034142184207036030884169206a007803080078401000110f40200500c02082d1304950080341a641c0d0351812820f100d0214800816000081900390500001c1000b40d44100c034152080c60b88480c0480c10716540c0e0080105d140d0107c058040c0c140025a038034100c24001d00c0c80a0803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 222310908 1250 222309658 222309677
    0x6061009050d03020102250512030a1104060f02010605040e2805060403050d150311060a1413050f0301110f0c010603021e090f160f050d0606170a0209100f 68
    0x902e403140884040c0c1c0141c1d0041450803082501007004a4185020300e0610800a0303159a4951100d1b071801850000ca01c0110006840d13500540041c0031001c055600300da82c80b43ca130600949492808805030b0015031030020045038078106031040b00380d00d020044c010001400408401c881e1708610785648020035181d0117860000a00400106010300d1194030340c103449814644102c0112081c0405460a412421380200b000c03601c0400080b031015001d42d904d40e41d83d482c0c42810780c1d0003c4140541c80c20988006a6161031040b101d100c40203813502100c1c0001000130039010582030310303e2290004c0e0005000c0000c040c00103001c1000300030303215010001044141d500c1c1c0000d01c001040f104802030b114002d00c0540b00c50304d401102240d02200505c5002458101680540340c60004111201e0a020030790081409040c060390559000102648c0203005d01900c038000145902140e08a14041030001004a41074510754002d545071440080e0140e002819100300c21140310502202000c04d2010380341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 222312158 1250 222310908 222310919
    0x1410031a07120b1206280908040905150d0506010501020709140606090a08060a02190809060f090c060706020c06012126030a06080606010c0c091a06130905060a0806061009 75
    0x2400344294406e00c560b00300100c03150130f00c011115000d0000c00c00c8034500380190002900900030b850070750b1000b1800040356510300c0021040e005d4492078180e4000000002e081c20080c0c00109503043e00d2007070303003554841503655045200340ca2903101982e40c1c004c9800700055003030501501400d0711f01c4000344920009a5280f58560800320f040d140301d951640c000481e1003404052150303080034540030b40b41038241c44c0342507003180d81ca031840034000804081080f00814007540e01004be002080c28010455903441e003051520800079803052403a050107010720800059516690145805410003441c2901c1710282d643d0b40c0c505610954400d1414024108491410180700082c00707103101d021900c0c0d001600a0401c9150391601400519440c100141006801c000400d0003800c441202c90b000c0000c18200300026401c81141483c00e1950f400401c0818106200540700c0003c10440c1c0c01101c080200d41ca4032801d00c40c01003040e0056984940c0003030041030046c10a03040c4a043d000741c51030064038075522003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 222313408 1250 222312158 222312163
    0x21150108030414181306020f0d09050d02070f030638040b030c130509010b180414150103120903080d0b19030f03121410031a07120b12 59
    0xa80052460741d00100d4140302148461104200d040021104c100341c41c14012402c00c2e5001004203030b42c0f020094a0403000401003160180c0c0c45442000b010280c48001c5100d04100400c41940c0c00d903400d1141c3c02000c5410760001c034011082d1041110103d8050b41541c6500016112840307030810702d004003130842c1224141b40668400481198083d140341128103004000a980c011800785220380c0094a48804541d1103a070b5441c9503c8068101050780c0d41c4200601d401000000b40780c51b000304807030b51100c2d0702d10083c0c18580d108a128019000510b40140461a540c2d0303984209024450600390041c004186e004a04d4820000c031842c0c0141c845440740d6400b041c0750040d01100d00483c1d11154000543e2502d950b000185424600110103040e10f1038440d004507010000d0041c0611040b110f085901038816000012600712400740f420041c103000c031003510040081c1c8815241c6018880b5041c01b40a451010b5501a007410741d03c40515004003203c61000704503801c0815413000401c0c4001e101035505 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 222314658 1250 222313408 222313411
    0x1605030d090c0306140601020304050418061d100902030a1401150b0d06080a050a020910120b07030b01030b03071e090510050319080f0702010507050109120e04020403022115 76
    0x70380002100510b18540b400c155002c0240030f510080d645d8041080e80e07603001050b030341203800440d000300743c0128200113204d680705040d4002e00b00c40c2c20418024a508080000d0f00c2204c0942e0044984449900e2031500850324901c800961581110a4950209084e4034081d00c07550301400000071500b0600010081500720381d4401d03042214042007030a0360300b00b188a80b10007440300a02030310401550b84d46140e1503074205207000303124000b00800700d10b0380601041244060081081070000c14162400d1801004600b00e9a18001034148415421254440e004522403010050000d0010606141181101124802030380d0504074101400240b840c2260007040d0184a002c0001c603901402c060900d41012400d0711411030b0001c03031004000c00600b0711401c6504d0846d811400e69242c011a2004035841c1c03055000141c115800d104414085c4458000b6800826206840d8504013003204403d200c00d0340107911020758880c0c030f007603131004203159001804a482101c5e50300b070700c0030741c40c0c140482c2425140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 222315908 1250 222314658 222314663
    0x224030403080405010515030604140c13090b100605190e101106060312030403180f081f06050609120a0c030b1f0b1c1b0c0c050a05061605030d09 64
    0x808100344014001c1c288903040e040103034003c0a02c441f403202c2c40031a94498016000400b03110046000c1300d81640c0a2104000b08000207105078103520132148a030010b40441c1001391084400c4070082140143d4007a400070446003291102810100c83c0c0400414000304ca03258202442545001c086882d0780d00309002c0c806800030b407101402d201010100b649040340c010002030196005074003042c00b181c200030550340d10035031600d0030781c4402c514100350200e1040f6076403000901c41c0b1092030200351000042800e030540c0d44005020001003c0a54069040d100c0510500b0341000c0200080702035030070001140201c1c424640102c07100e0043d20f940d070100d9210b80380e1003075485e5143c800900c0f00100c4c1c245900c94408000d90715451940e414070722008010320a203200c2180f0780986030300c0c000c1c0c40c26080c0c1081c00c4c50020408103000d811800c070070103040e103043c444084460110031900843c4a160440350207007a80c038040d000341d040c030008034022510441e40703800a40c0c0a00c414000201c041c241c9015103d0b04070b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 222317158 1250 222315908 222315917
    0x1d090c09010e130f0f02030f180124032a051003061d040b010803030f01170f0607090f08030f070803040c0305161409040b071b06060e0114010c0f0224030403 69
    0x84c50002c5400803140c040c1004a95240104284540700c042c04600f01d410194983d020348150703103003580c15801402c1d2040b600c411a040c00510004041480c41014200ca000313001420480c07031403030b100424403103007550121615801c1540612603800c1550b900d414000d264103000070300ca6110340031800b45c0c1c499008446920900001000100f10110400c503004201c6c2900440c01c41c1420f1001010f21141409440e1210240764541806041c040203800100d107140c0c410f9072082c4c1410034005000794107500620302c8100142030b000030321800001c105e502d05002012528140b60065403041102d61000d441510565a0703840003102003001844440d1500800148410040d440c05020f0344c9103084500e007103449043c1100400002c14034031501c0551104043c40c0c900d03c10444103c5800d078841d803014028200321702d4980041030300507400f801741c3e05a45d40c094074800ca00440a004507000d24280e900200341c00c140440c44401814a85001c11901b10304400c42c02d0b08011416503203046070000c0300c0503000036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 222318408 1250 222317158 222317171
    0x1060b030c19170c130e0403080109110915030c04030210030212100312121b030e0601290702010c0f08130b030721060512030a1d090c09010e13 63
    0x2182203401c0144500b503062645480b40c0680000325821001811044550400900808510102103480e4040c120b0901486010b0500c1c0c14010070782038003401420001841c00e825401a82c0c810016200520002401541013038040c522030101904050415000128240300201c01690f076031403854583c402d035684c0181ca031114125031541c5441c014040769440c2c8604541400030038103804540950705140c4c01d00751320700310b44140f4110080c050049841d161103021780c0102e80341981600300080003410101182c5181e621221040c0b001e5848040044481040340ca105580220250180521500504151495031001d8840c1494907292940440e12214006919034003525105103030009401903501941c02c45c03400c01c1000d015103101800c1141c0c20b440c5110441690342c9650810006803074054404001c60000205440e6207801241c084d01c0410110385a140d46506058021500c1d10001407520f451500d841006000d50303801000c0c403e040022103c4000d0840e20f40400728904480441c2c80010705 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 222319658 1250 222318408 222318427
    0x18011805060108060d110112050117070510080412050705070902120a110a03020d0b10030903170919050a1704170304030f0209091c0305071d09011701060b030c 70
    0x1140d000500c002c0c140714203241442920b4031005503040f442c6a0052011304665070510060341c20303195010300c6055940c100400460410740c50f1440307104c61600a81210105c64899041100c059024946400000d004100041c0410349012a02c2032031078079824441e10f05682078a0b014144241c0e50800e140440d00000e00c0c01c2d10880303203103030554001c41a140400c101c80b04940140064429686180d0825801040c01e00e07102c0700703540c4030401c4c4481c0203204d040300d41c54010003d4064181e450080d401704084071101585a040351603868403c09824014100000908001c0746c038840080000307488600c1986002000103848016603821402103a00a645031450914902105540e8030451501904207120800009035410301031100564116100e40b04d5035502d100041c6000d80c54039403030200d0060248400d85103900765008134018807513961503224680404d0316040e00954600c0e402d6403ca40450010012221b5400555918603100f000105100e507480c1c03140d60301c9070001d490101c00180b001908214 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 222320908 1250 222319658 222319661
    0x1b03040501140a02060a0e01020405040f050f06010c0c030201050703030b060a0815031b09060f060f070b06041a0d02064501050412050a0803040b09010608030c0d0c02180118 76
    0x450005041002d883c0450503407000391594006403a0254442c0c456498a0407440700390161000303040007030020800ca4039190940f102034a415038110110590f41e901256040d417140c5c070803490301c5400c08a4418401c3c40c42e801180e49174001c001c25004c0541d1800000d18a036269001080401e116130b42d00f903201d0811044421001c090703540307803a10a0f070048600c171071f441c3d00d001c01042c0003400407241c400b06551604003045458079072003101a4001d40c00500f4407400410180500b0845000b481c2122031603035172005000072600188600b100c0c0100c0c5210050700e0b13182411090a009101a0110381444a070310764000005a200f0004041411030b81c8141900801e5400f10b16980441582000c1c049510080080c090784038500450001d880c1c8003d08500340070741046030000e9140d024281d50303907d141600b0085051750b415240306026509180e40000c000d103001003903c0d0890701d500c02500d08082d2190003070380c641d00c40321400c0340c1194201586e100600d02141c2040d00800c8641940550103912010580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 222322158 1250 222320908 222320927
    0x513030305090c210a06150806060102010b0d021c020405010902070501180b04080a02070b0a030519060b040501050702040b0603011202090106210518070b0c0d051c09081b03040501 79
    0x103580c001c0f03d030030803d41d8030520f81140100c0721000a0505000181d81e03181045131007035000d044542458001e101c05100c110402d8200c654100a8501648070f100c012801e072440340903140d0740500d40c401400094541540b090703040d40e241e80301405207007900e5030126003a00c50990006010f5580404c1e0881072000a000d14200700010b40d0220030701c0402a982e55080f9880a04064444078010945001c002d008100ca0000b408040310941e03151030388840000c001d40b0301225042000b10048403501e5070307140c4a02692040d10807071040f44c2e00381410000110f07100d07000308000741d074000d4441d49003c1080e12020001c501034480c0c024080540c0303a5034014414180c43c180d01c00d0b406c2081501c817002682c40c079000c0a140a41c0c1443c40413405444000028010b58854000f000c0300e030103030103000201c01c100036000304400190402901c941c03260710751003603405001c2c0c1410001d141032059084511591142d00c511050b42c4240c00311410304081801c445080208941c40641c00d50000501307210315a04015441d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 222323408 1250 222322158 222322171
    0x3060b030f0106080402060d1a1f0905040c0302090d06060603050f0709060807050702040510030501150b0f07030c0c060302041806080a0b0601091208030103170703210f0513030305 79
    0x25203142041101007020080c144102800c00560074003040456544a0480d495849010030600c203440c40c070346150303198001c0e40c06418071801600408a00c0e042c9121a6103406117104e844800480d0302d04802e01019001d03554452082580c00c00070b1003629070700d00e01c8403a001400b0b400c1c009000c0b400e000e00a021a031018242d40081e030816000c00001f242d018180105903105440d2055144e2144001920180500c4d01e000390f200f0304040400020181840703181e803ca034000d0740240303e8540c03818050a004002d5010f4103114040030000c1468103418103000f000940e1003490310305002352007903e801d825110290050000650006410480600030160b03800d41088550b804001c61450705081544e101015117000305400d00c1000022901d80c001e61862000b00801d0740c0c05030780e0464514001e5204e42c02400101d919503096800356084492100949078802d40c10f8903000d0060081f404909038292a40750080340158803424840310500182c01020300800e5104286504042ca0b45000b405039030300100031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 222324658 1250 222323408 222323429
    0x30806030d050f030a020a09090513150507020c090426040303120204050a14030a0606090f1a09011e1503020c0d08040c0b0703020705120705100807140f0910020c010306 74
    0x41100105507803088035000b0f8000d05c40141d40710320b115029100d68226600c21807402d880d20003002819174841030b20b91500d40c41000c20250082900c00c10104441050b030350400140c1c840003041e40761381010260300e80c0041c0503080c001d510030100000c10b04000603403075000d424007001240410400d41c20001004941c0b040c00010750600307041c0404180e002d2403d12840c488422024052141e544007440102c3d034080e00404140b0101d9213410304000503007000000c4040071490950342c10f00070011803080300b0910070000d0060304075034030307155049002a42d1410b02021098948400103400f19110103442c0f414801928050780b249025056035043c506030b40e09030b40c14414100100070000d442d000c00d000903520710742c101da41c40d154141000c074541406034014503040707400c5085083d901030000850500b151403c6814641661240104403000d400585210340425a1820885900b680c140094400041e001003c0c50801c2045000908013001e21030813600540c025040300441e07540c1c1805400301600c0d40424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 222325908 1250 222324658 222324667
    0x9080c0f012d02061e06010c080d09030e120307050601031713060804031e020d030c020316060e0106060f0c0b06010e030a150609180b061c050f010c0c2001110109030806030d05 77
    0x17105186820003400e69041011000041042204110a0310740d40381d01040f04006100c800c0c50081c0505000445a601c200e0002d413032038960810000403071320040d5204018200c2c5034a5540d9100101100c40140f4034800010300c001c0450004441c090340041c850b81d40e442c001c500302410f029000360b1210583c003421080140a40006d59000602c0480040d0585400149200010001c85c2140900c403c017031030096020200400740101900282c0c40c8001600080108598468043e5410120500c01c05c0106601c00243d00105e2100e220059111b101030400c01c5424441200180c01e1500241044402e07903503501312201c0c3d2000c2403043d04007a0420700800c0007500f4901c04081204441000d009004a2020b40085c08a03120003411503000c807042028034000101c1841c120751194241ea24140d200e43c07030482032143c800d1144454010303254000c00c8060f0645950343d40140c2c003144044055050080300d9040151006091042e000742902076034400302c4a00300a4105800c0061010100041103001c1c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 222327158 1250 222325908 222325951
    0x40f120f0c15110406030506030c0f090a0207050705060f0a0201150803090607060209060a020a051519050603010b0603130b010e0423070b070c06080709080c0f012d0206 74
    0x1400307582064110b1030456040b1a180040800351080c03e18071441c00d000070400043d46a0580c20041c0110030480c26507546003920814890661078400c00650311502000216224151a070b00808206005000f550101e50300d42011900c6035219400380001c000300000c188205940c21301c00c1f10105841003d0140b46585004219035883c01482c80042c030607040041e0031020000c6036411181610009401181c03902d50707110001c0c1d11882d4191007500e4500955442100a0320f83c0018941b10303d61a200d0011828481120030000300742c01021660190350315100c00d01940da0b1680554031a1020b82c1c011028034003246030001c02d0a406a1050741c290503030f00e080c8000102100c401c040d10019080208002000c0070a07907620f0705655900c02502c1c0c1d01c00203910414400d202e412041036801d142c0b2a800c0c181c0380c000b001c544030b039058800c3c2d081c1d40e0405031380ca0880b0300c0e10b01240d0b800300c60140b40520008080940b4102c10400400002c603001c101450345140b000c3c1c0600c201503010b82442140c04286a20300c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 222328408 1250 222327158 222327167
    0x50106020c040b0a0504240602010e061902130e0a0605040e100e16091407080405070306020c0307150507020d0c0503030a0b0d0609050c0a080102041202060304080c0303040f120f 78
    0xc030300c0d544940c2c0c41d41c41c0710b1016107032a5403000007000001e0082c1309807108010111500040c152500311f150009803404140385005020f044c0030240c00302e006010640e1280d14208440e45049c0a407002c140d002c1110142d080500100d04019007850003500040382401c040c000122046507000c0c1d4040c42c104503089150321404518840029039044003c608142103d0003c0d0030285600030700c2e00c0c00080784502103002070007903000e400f0f404102c8910504680319400252a151001c6400912644c88007400b40001180c4e500030304044500e900440e410103405564100d400224283e10b0705802da501c4003000321859041000c01c901c081c8a0506110f80721aa4030b4007910703440010801e001080d1540030064090706e0301200d07115840c0e0840c0d030030020610240380094842050007c1240304a0310340c1c80208c0c0015061003118100d034142c41100c440c0300403d60a100701034200500603541100c0c1409501c080d01d200384019403085103c0c01c88124412020b18180b1004030419003008100032901e2410f91529411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 222329658 1250 222328408 222328423
    0x501020d1d010e031e040e01080a150905060414030f0403031815080a0c050d05090307020a06020601060207140a1d04150b0a06030905011d1608030a050a0c0f060212061305010602 78
    0x4101840c0f0040b0000c090b600744606c1168001555201c21038000503020343d002c1460350300244a04007800003054a84642e40a0b60020301024005802000101d00000c4520703042c0c0c80c00e07002c40000e80c0e00744000350742c00b41c4039600301e070307200ba408180e08813040340c2ca102140e0341c440040c0480317030020b42c41004426001031020314010321543e20720f5580c411004079075014a0540d00300409800c03051202c2d00e40000699105d800100080b03001e188244000b140c1c03503002107102c81c140c84c041d60041800313a103010030100148107010440d941080e045100400c5015844000b9a000c0c1d09251402401d4206841c0410750110740c3d111804505252504c085e05a03074906402008450031880e01045407442d0341095070062450200401c51032040b101400c90740c0e60041901100054004140d41005079601c07051522482450110750024400b04072018003a4020020720740c200340510400b8a01c100c2c3d650b50002282d10030b20301640190500740400c81c080c58a00702e8681c03002c52502040c4810351401c60060351b605030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 222330908 1250 222329658 222329677
    0x513060f020f03011205030426061608190b0307091b02060c040303050c1f0b01031a0607030c140a0507090608150f13020a15020124051306030501020d1d010e03 70
    0x400e45c480c0018800c040003a01c018002139181c0ea1000c2445a400c0c52800030042840307607841c000d000c00038a40d00004003800d404100980c81c0c2565030307035400100402c11282265025121941c0d044005100c0e241080200b01400c99050006a0f0030f400c181e000c07202d08008030b410400c42d8418810851507d00f4201500c00301c1c3c0d490306000c0d0f15140720004035820174110015180c4240c01800023344d5540320f6400183e07003807400383c07810000030003408003101782503032443d84098002404001a00c0040d10602d91500d100e8007803413946000544815815060442e20001500d15038000e00c02800500c405d8816100140800401009458142d10001b50202402010000f05d90503010000d08140c0d00c10304a003010941c000c118551581e224121403942c0340c0b204c62050015842c082d8581e44e207030440e80700d654255480110080e0400e00d400c080180716040702c688a62410380316813001000800074009050f0141c1444000310f100003a1005100d03035020704180d03004280c0c7c100540f19174100030100482c3c1404d00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 222332158 1250 222330908 222330929
    0x20114090705210d020132160903080a080105010207050a05090714090621010e01032d0f20100e061605030c0615040b060d0c02010603060513060f020f0301 68
    0x40c03080300f005080e00443d5001440c41c003403003003d09109075066101c559044192052000c15400c000c0034000016600b91000340008000c00104151548490f80c0c0700a001c100c0c600405040c0c0c5aa4072075035660001c401c140042802c0d107005010941c0c0522219020700400d80344101c07814686400a4a4800050181414007040b2007800814407150400c035429240e020b0015541d4158080d01c11081220010391007481da0304039000480d01078001010141269000b00310f2148001c1d10702c0c070005243ea0001105044186c0d1031003075100060602c500c000055001e800c0c0043c51315a41c0446218241c0c112071003920440c003000a03568402e0704864009060300d0244c4040780c4444075450403040032044001c000e0510301c0b000c19540d98070080055091f1088a1800c2044441c00b900410300054139100400107500850030700c00c9100756840d9a0181e01442c05910001c10b00c0743c0d80b5214803003107542c152583d04024222910140c1440018011281030f4003200004614040709001c00a02d02c0c04103028103440c11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 222333408 1250 222332158 222332179
    0x903050c0d022805150406020606040c09030b0705070b0408030402131512020a090e01052e0b0d090b01090b01020c011b0305090303040305060a051005010503100501140409060312020114090705 84
    0x4004030040303d0050000900602ca040e440c080c4207a01d650014454180188540000940746042c42d024a11820408d500c4603c4500e0441e6602140c04070014416810040d042c0b04203404034410b0f2001714003503402006569600d04003401440304440c0c104480044490070a000400000d000090920803104035101e10340164601d8800500c0c0b48260341e0007100300c80c1c2401c00121414606600180c06102c5800c0200c202e60810078041c250060711000b00c285510607010200700c1e42070f4040051501c0e01e400400040c0b90030459031504003908081e04042a40c1e560740214201550701046171540c40002401d1410821414056800302440d000b100142008004605074905403010820f440186600005556030b0f480d0000f0300701e000705002c4a001d000624a51000203855000d0304c1180d000b411010f002c0d00440e800c090065408040d401e00c0c3e818015420000000c40701140c0c41032402551017145c164400f07140e0f07510001e0035101051054810b4440c01420b00091a00001d8004221041555400c256 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 222334658 1250 222333408 222333469
    0x190503040b190207082206021609020a09050d20040e03071e12020a05062409090709020a0315050301230406200304020910080d200d0903050c0d02 64
    0x44e0003541801007a6035404204034064104c1e8041c80d07010b8207060002030444c1d0390384c0c84040381d441824842c40158150380440a100108094005000302d214074204012100c0d0f89002140303104074503800548a0000501c03000403c1c1003804031451300180111824022080070620980e26407007103038001480c0301d0071050714090400329840c9200c0e820350803240e800ca40100401000c2d40f1a868000100c80c40e001d10380004084559000fa08070744100b04401d44000c00740c104c8240030a280d00079141825900c0b1700080002e4080c0280018032030304159aa02190585c0360482c0030495803a25088544030341d050282e500c01c2c00480a03212102202500c0490030680c4450400c4401000000421003c950300c41c000401c075000c0701001103008501c240ca200741d1507a40c003902c03410041c00d03034060070045406c12140b402c2098419460a400e01514092803420000595079540c50140c0c04c0c10b04802040c00e0306c404000780103052004041450b002e4503210683c0c0b84030781c0014102c50354008107032209211403100800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 222335908 1250 222334658 222334661
    0x90105130b040b0c0601091103040b0417180a05040c020c101b0809010e0307080601051302130e01050a06020a0201020307020105031302090a0b041812200303010b190503040b19 77
    0x1001d914414540d0795480e00303149081940000c410391814801c0400000380341d052845090010070002076041c0c103548540e0780d0700000c0d0b400030700295044a01080740701c07400400c40c4001c190001c1380207880303030724014060240305803100158003c0e07220301d285c190050b824035000b103800e410102045581024084041c28161a82042135400c80c4102c00c2c81a41001000701d20340040c010f4030800d072a22560900200f04143e0360388210f020b0039070150400401007200b410701401c02c904e2114101405810240e00018841e25801e095101415919204004108905040700307400040e09941c4003802013140180c0021355039128040380281000000400038480105d040d030888511540185880094105a200d401c0a0103001c0e190521440c5041e00c503120b0700c50040d24000601ea4000c031003181811410505072481c0105c2c0c2c40180034560140440d120104044c802180601404190151151400031402d00c0015000b6080c100f8070404006000109070700f411480d5011000c80580000b04d05452286030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 222337158 1250 222335908 222335947
    0xd1a0328080a12020c010204031a1003110f030102070501150506070818220902010311070f06020906040510020d180e1503161715071b02191206061703090105 69
    0x410f803d2011420710040344040d0010011a406213050b0542e0600c80140042c02000948150780c440c11201d900304001075a55a00c000940d2004040303800c080d40c075102003400c1e640022000c032a565510551105003080c1c0c01008000351106403221400c00c8815665101c1a20a1841c0e440050680c454001c04a0382c83c07480300e0b50740450b0a40f0300c5000720000c0021201504212604901180c141900d01d41c1801081c810396840542018a11900c9815515208000c1d071000f100f0305d0300800104004202e50f01c40340007280e440da0043d8010710b000c8803032075801080c290758290760b03107040c20003a00100200040c000055800007000d84002ca036110500000034034184980e81c04c2ca8a10038104c0380015824030015600003600380c5c3c030f000d554403040075540346811801c0440b005008200e50b0390013480aa090311b049410914030103002c03036102ea00303078440010f2a01d0940d4001c041452030304d00d05400f04015400b46a00608038007001c00c1e59400d082c0505034980c020001c20504200021070000c41070340900b6000c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 222338408 1250 222337158 222337187
    0x240714120a0201020c0c1f030b150703021b01020c0d11010c150b01110c0108040b04050102040509011701141902071104020409020c070f030201090306020c030d1a0328080a 75
    0x541d480c04000d802074041e41112001d1120381c040c1c6500509241030800c80d003031030405601d03083d20a910340440140c00030b09046610383c0c0c02c0b5600150820742612040c0c002c08000303019400038030074041c0f840c0c00d50100036054081c0b641150040c185030901034030b03907000b00c0c1c643c90f50101a481d82c2c840000b0040314640784901d406400da0031000c240925601482e405007482074000e0b070743d00c04261090600310365100b06004c4e0365400600760303000090208011000960300305201d0302c00549001e83c0d0380000b480041c000e07004102e0071071811081c154130010901c2102e000c00c0c1e240060f0109403034250b58001e0908500c1415060541c1c00042880c1041458807103583d40c0341d0010001c5403102d482c2c6407000029000089200b4203446180340110f01500b100b009642220380c16540c0308807460071566014003a41000c1d100d00707800e00c41840700d4500e582050049083c0c6000b00c8000000814810040510b8080140c1d00020000340201038048010b0054000d1109941c010a941e95545a600c1c800c907403043e0034083e80d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 222339658 1250 222338408 222338443
    0x4020307020f0d08090c150f090310051006121811010c1e0512041406090609040c030f0f090302122208031206010905030a14072102240714 61
    0x940e0406804c02442c40c0510400c904451441c9a0a004d104040c0c80d4a040d5080f002c00600010022104400c018a0450f2014050341c070803604560101054440591300320001403000c01084c419170354000959881c0e900d403020140080c4c144400c4142c4669a601d40c041c00303400640c0d0148c813050b4012241101c2e11580082000c018070785041003826008042e5a00f00c0e003034000c0e1140f90202d01c201509407010303a00a480c00d80d410310741c0c140402189074801c140240d0071642c14401091981e40d43d12410161a240391004111401d070300c2c251004548d10010041300103458682010007099000480c3c03552684452030865641503c0c51002000409024440714000951900403405403800300140030480e0840a80304c4590700c1d001c0040d02d51181c180101da0301030740102c513984082803905905580c400c4543d0140c62409488a42d0014452501d4105c112107800c02d0156004600303001214210412140510f140310903036038420040b50f40324004002c0d18056868101224031541401a1700300c0303500b4481c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 222340908 1250 222339658 222339673
    0x9033f0518030403030206010e040501200d0e06011203050306040e0307120806090c03040b040c0911040503060a09020d020d050316060b01030e1c030f060803040e041209080304030204020307020f 85
    0x1800400303404100c1d80044641d00641c4a8006003000005642c10b03641d041c4c001c1e2007035030b082c0316120350800802001610250f40344d0030606e043d540105a0762450661203201e041d690301c10a00c1890665043c607050540a0740224010440d840c40002c951069a41c0340c84d0081d62500d4920006016162082a5440350700000071041c0801c190780e20074202c0032529881d05102d541d195002c200b807105c8220748503030044038104005400a00c40d04070003a4820300c41c00000d0044d54032189040102e40c26545100e02501d0005014015440c0402099070b1012850300c09200b00c61a0fa030110781200b5601c40c00034080c040c0b4a00b40720030040c050050350382d5400c60702c10790719040b107941c10004d01078000c0d8010325010901e4143c200c8104003000c01c802854448051100d90950700d152400c800804245030700d100800c7e03980c04041907043d8148001c0008100f5001d0070079403800c00d800c02072180081e0b00060030910050800810110314040309a80489404940040e02c0c0e54464038203a0900083c81e2045030680140c85 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 222342158 1250 222340908 222341027
    0xe0321031b09091302010c23070906140418051212060d020d030e0f0904050307031e0c03030b06160609030219020306010515040e0a06180903 62
    0x40518400c924460010011032054000c80c4200d110b8216015001114007000442c0001468070032207003544180340c20342c003466032611100a00264180d0040e601c2c1c01c40310034410201030070803141d800342c20204020041103280c4030305414400c0105d0001e5024030380320040701d040d0fa100c1405543c203507500002624a8480100000040da41c0245640400840200d001c9034550030840342c0c140101c1d6028188219410003500d0036949002d5076082e070341c1d0001c00c60307505801c00d450381c0070460300540c8590011600d07411281360141c0b10307401000b00c1e8004030b0a62540003074000c0e404602600b44507050300700000d5460b15080825005d01c80c07003050704100c405000250041000c240d101c8444103001707a013034819030b48895200444100f60098082d5050740114014085440e04000314952520700440840c509903aa190460742c55130201c804640c1107039103003400c02811004501880001d0020541004040030669002d8041010301c40800c1c0e801c0031280c2c05041c4e400c11032b01d084800e044d4403012312400e03500340c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 222343408 1250 222342158 222342223
    0x3060e0a1e0608211605060405060105100f11010204050409030f4802090408030703060812190e040f06030309300501090615050f011706010e03 63
    0x110003060005007801103003a04220a118000584112002a01d01c5800c0c0d403040b8444107910007541c1c51055000c003d90b240d171074406214940d00900c90006001d0b01d1515040c12800c10a05070300481c0078070140c4200f6502d45074051007030000400f0908000415128040905009008942000d901f0030320340040c000034950400d00c102650919a070f0741c0741215141e035100e403c101c8031a03c2c240c90f9002d4444448a6540d000740a07a4501022524101190805540004005400540d0256100c10000041c000e01d6603044c01481c002d41030703000003403d060102000760b000d01c0c890005006161181c0310540c0c08001d118440e1541d6a040083c01070003640013002c0360b9070007001c051104a010030581080003406007480501c01f0003d404e01005146028981c023072094400802035411513055503259074100001c4c81512404d9048860300300c47c0300a01d418001440030b2541cac20101141801402081c4220b040c09415441c0c0c0d00440a1130007608512010000c6403030007440103098802d00c40d01c034141c0441d41028 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222344658 1250 222343408 222343421
    0x1050a0c02030a030c1515060c051204030303091205030103031b051c1d0f0a090b130204080109020a09020711040e03093307080306060715050a0f0510060206060f0103060e0a 76
    0x9100c0d2884018000746d461402c84460b1a2001d02099411504001090180e190f904401d40101c0c00d942d40512024094103080d0310030b030030032004a40c0d103030b15800a001e04044144e680380f81c14140140b5550444d1030103842001410346403406030350b00c40210780800109002c00098001e01030001182484c400c000a042c2c6d00da12007016982104c0c0e045820514030701f50307400621004000c4c0c5030b001d11a040c469088c0180c80c3c075010894221150f194003d2400c42c03c0c1c401000102503540000038000031900c10000c008a5541c0000c450a00610110340800c8403480c074484034400846002813900e40c1e504d249429409481d9451340e00c02c03080544203c0d010034020003601c1142201c1140c116032440342d21008c5040c0103140d4054490b1105100251903818040c0c01441e100740100e42819207410034110320341c00e0b00c2007106c005601d584c6070014445008128010150000041003c0c45082428800700950303882000349046d204200d50b180310a1541d0103030703100c10050210031100c140d1030310340327440d4210140c408c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 222345908 1250 222344658 222344663
    0xb1f03022706030c0d06020310050603010b04051503190c0e040c08010905010e090a06110d0c030207020901062105180708070303020d02011104061d130c030e0c06030601050a0c02030a030c 82
    0x1070207000140245000700c0c0c48404484000d0090002c44591b48440000390001030a100180300044400b0510b5580c01380510b00a000138203156a07031b0303400c040501035807504400045407640305c10700500910040d803030b140d40003005804100040d80e10704400101c6140103608251030300185460f00b01c4c4c0405601c07808007810385803e002c05200743d0f40d0320310407071401610444412032581c000403240c900003641504161545503c41403507030b04028800e19404102d407500507104000c81e9001445404501301541164010001800c0070303140c00741101100621895007a0710710103016070ba0340000d0b100b4007a40c0c04000340a54484122086e460b00c802400d69039200d107020a40241c0300b44424405c046105008949a4564440b03c003814540382810569400784a10b40c0c00020403241d003000c4070191921210092045a105004a1b0380025403e000c1d084030311540800b104c540148524404039120340040b260080420718140b43d036a05100740460300c042803400002e515004070940e0105144d804901c000d0980d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 222347158 1250 222345908 222345979
    0x306080606030c0607030f02011b0305070e040b03030a050a051b01021312020d03031109030d030b1207050901030305030601120c030b010e011701030b100b2205010203070b1f0302 78
    0x4607241e04055850100c48000f5621881c100a51000039220b8101144002104e000120302c0d5009201c0d4400444001800d0400007a9114100a4095032001408940764400e9408100c0c582200c800320703489108110f0040d09000c1d000a0072410035103d101124600042a02803810040e06c0f40c00c0c140c040d500c038031102c143d00c41759113401190340341e0200520392440d42e0040050500ba55103036802d4000c0d045503442000341c10360500c04007506031001d100d0305800060b555400100030910408119403c0d00f54000480301e42e110340350078046a114507032650b0540b03801d0704000c1d840340d0342c1c800103c44101c0074800051800d070500e071090841c1509900080c0caa2482600c400e0b071100c841000442d45501102007c000e024184401040407a030189240364001507003d00c0034070312039100c12500c0c44079071110301800c8a03c07024160410014401d02101e40107880d0074409585031001940340c034907000e0070181265524401c00030300445424845c1d140b420085501510809040d545081c89115400c0e19078401900e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 222348408 1250 222347158 222347161
    0x30b070807050301090513050618011805100f020f0706270b041709120c130908041503020910050d060503071505071109090f010c02010c080613060902040603060806 72
    0x14000d0010303a20031003456a03181c3c116864000c05802812000e0913582009041401d10380200da8240a4644150b411103800c0c0c1c0c109070002c240300e084981601a84072070780821018140041d8000c0b50f60b2040d504400008184440d808039000000c4c859465034000040000442e4800c100d0245c10801c005100b21228400c00f400c83e00b6001080101664010041c500540000300022821003030400c58002d01040a4240785920000c200c2c3d03c0c900300031040580d8000c000d06d40d02032030a110328000c1030300c5054041c4040c900f107036500301c51409039005071420310404111a1440c035109505803001c0e0540100100c5d0000e044500c003074410f0b4071445025200311309104011955040009010040320840240c402201d807405c00c01f220550480380048820a401103e0340a1559441004501407000c0038041e186400c1141592803c64034012800350540e410000548280c0303400041d070650140050701d403080c201c0c0d00c441c0000300801d03641c0c0100443c01e20110f00410956407507408103007a01d0303206088031003d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 222349658 1250 222348408 222348421
    0x8010b01050304030f0516061e201603050c030f090103050601030c05030a0b010e040c031d0a020a0302090a0207050f0f0706030204030c091d01050103050a020f0f0a09021e070c030b 79
    0x9120444020340400e48031700060003090700c0780e002800b889002d111070014500c00c5685041c2074a090350281c910004072240040c0300001d0b1b51140c1900c940141c80394111501c2c08145044031402400c1e5120001d030910b04104050600480407210315251950540343e030f81211140401c05604100e592034000b0745040e00284e07481d402803141d10344483c281c4c0c4170383e0704680d103000d83e06000d0b001e200100c0341041408000170460351142c3c0202c40c070300341150310042402108005034081090030b00b806c1e601c056100d00c540304056240c03440d05805032901a41c681d00c0560b1002c80e40d2002c0e21403030000401034070548a22000707400003c611b0003812840c0b8010b441445a0b81d100c00c90a07402103000c094080e0701c1c2180100901c00d100c2d4498049079080d2400c42d003105d50f03400301c900e0071503038245d01c195001d401280d807a808510f4030f80c84c040b4040344221003042814000c0c0d40400c40518090003604461540060441a4407503503203015501001e10014095035203100b40b5128000b1015807000721103402112001c90b45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 222350908 1250 222349658 222349667
    0x40f140a0618121b0803060a0515071b0b070b0a0207050f0c010207051e04050a23040c0e0f060f01180b040806070e03120d09080f120106030204051309060e030a080108010b01 76
    0xe1a01507281c2903000c070030360307840d028806e5001505040d8440c554242c00502a2510b03101060301b0304407515403d80301c08040c100b200e40c2c85c2911202c0012486580424005e1600d03142c01c1d10941c0f50000c00c403080320b45d980403080000b8400c03848080c081d4420322205001810000030400001da0342a800d80e007030300740d0f11300030700084c80d28540710f06072021600c400b400c0040c1850b90041d540012401d2000c40c2c11100c0c046140507220240d01603502d82070b441c00402c03080c0a0140c82e00c41c0100010014139889103070280c4038010600d00580001d02c161500400030b0b00580c420020880c00c80903250200391026a1650100144c0d031203889600d60300d001d503100161070300d07015501000c01c68030b0140181c11264458202418941e104031614440c4982ea548854045951800030380071041001e45450354519842032240200b00c0146e01c40002c05004200600282e200c40c8903082d80049031401c042520720240c80c00c00050603110616144078800480e6009020354403030082c0c1d04940f400d9000f001080000d600444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 222352158 1250 222350908 222350927
    0x30106061103040923070f03060803070c030201031503050d0302120609010f0509070207080601120311072714040501141b0301170c0a03080c0c0306040f140a061812 72
    0x801c0d820610041040040541011400d8800c01d2000c20fa00014250b2103007003100b05690741d00003e107030300d0b15050006805104940251851000440c107040003607032030f8000081076000003810103031581c031f034a00302401019100025680c044161961920103e40080007500800110381180b210000456407e050010311203040e907141641c02000780c0c0c10542482001c48014000000314480d0701400076003000c080c495a40680781c10840000e500e0001c0c00c000b0f0a00c2c64000e0008102d400040c0100000601245969044041c1e15952042e80c403007101040010032445103001d01a240100c00c01007003040c103600c42c40085007032403404c810070740710907040034000c000300507e40312849404c00050042a000c0408489000903000c102d9460070034906c04107041c04d9959000310780d001d50225044034500403d11141903041d9064000f8041840c0036100c80000c410801d42c047c0c00350704403508840c400328041c400103d10300d821081c14001d2118180c810303103950004039000d450035480070424045240c840c10019 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 222353408 1250 222352158 222352187
    0x1602030d0305150d080403171605060117150a05340314131e1416171009030c050712051b01051b19050304080c0102011b05130306021803010606 63
    0x103d0519081d90f84001c4d01000c0982e805223160302c2030111000c11402d100180068034421130251841d07502d010030750b18040c0046400c48540b5000540701d854a119088219a803107240010040307210344903500c8400301d1650502120f4001001017008003101c0d40e000844083c00f03081550100110001c06050f80d103001c030207803081c4001840050055000c50300c00b400b40140c60b0740750004041007080310398951010002009100d156600403540d0380b0b21591800111034010484000580d514440404280c0d448400c50440c26100c1035644c4503c0d420316104140051600d42c0c0b04040b0f4400984039919003030f0010315280c086400784600c001d6134030311400e40c0c02c543c0350000040c2c4500d4180100c0310541c02140784038500548441c82080c41080e0f540700074600010344240290044d40c0c0e80c9003403407241ca04000b00c15042d54156810020034000360980704035142e41c1208246080d607201d82d05038440381c0070a0526400504102d0000c110b80104608202403441c264038220000c00c00e06a80d004180c4078070440b100301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 222354658 1250 222353408 222353423
    0x3061b0207080d0e0105090409060902010e03060105010906110a060e0703050d2c1504060e09060915060d021909050f040c080105040218060f091005041a1602030d0305150d 75
    0x41da100303031340070741c01449903801c05040c40341c00c100c1c8080125003141e0301c600080c0c55071a01ca18440042d075803c018442e01c1e4541c01d40c05000c840d13040c10000381c045d9003117228000030070420000307034108000c0500c0170401381075010205000510000729201d54410707450005541e680030b4600c242d141903004442c8116075454034150b1082507840c0250b56816403c0b81030555800051807031802e00b03c4129403000700090401520340000d04003450003070051056004050a0041c030b80003080c030540e815800303003180301030070101e408a80d12442543d03000041d004251026004400d40e480b008031040c0c0264010055134020b850441d83c0e06d40c410204001e407400001d15401040c000b03001031145007441e07001818a0300d0309440740801c010315a00802e8030303a40190007802c4e20310000b2403140030354580302440b40e030010b00c1490031505243c1010390844003074140c00452182a140001e40c048036000d07002c1d481103403e800a081d540c0703065081c0c00c0603002d010200d070a08002c101c043d1503540180b4007030004031480b0b60002007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 222355908 1250 222354658 222354673
    0x18041704150807020a0b070201061a0405091815090d120b092a160507060503090d2010061a0414060901052713140a0b010e0a03061b020708 61
    0x500b5540d02c00003070040d10031802208a0a40410b0f88810814000c060036400010014904000c90350402c460b06075106410500300010021561444400c5d900b042d0040000c804407030200350840c1c50a82c02c4911004024100c4040020020b000700701502031080301e480c3c0c0503403809054010750448240c1d1544a5021300000049146100003500740445090804500110003c10f4541000140c200300e441d0039a81e4040f0780d402c0200401801042c1c01010b050800c01d05601b8100d44458845255200850800c5084502c0c81c501003800070741200700101c00f005803084c0074011100000a803006000e141d240c0400510701c80719440090007194100d034060b507014a2103103030400810566030f100303140a034100302e001d002c0902400d0000f0030b9103403c2c0703100707075010302d0801c004005202d10000c0107680e014200345010426800716601d000b52036400034000c2ca000440e00c108100690300680c114203034980180b107084010040082c41c1c6d1080320b400390401240f1101c00302042c0300300e0703441d0075034010600d4a803c41003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 222357158 1250 222355908 222355949
    0xf050c09031504170409021c05091207020a030b0406021803070617090709061508100e0c0703031e0903080c03090a140c03030a05041e03110d050a0218041704 69
    0x1a4250440d20030018a80c0c1c5020b21042c5a101c2e8100703410549100361f0026941c1550701c100390802000d017119103003d1155140c580701c0542ca519180c0f0000b0481580001c1c3e0b04c2c21950349800c4a00610303440b024100321401d180c103108009402c8251410b01901480802035914600001d000084801035513482501900c940000b011801001e800f8802c24420721002190780c4000b8004d20740a840b81420007140a0b02089000380328030000790660680c03041e0a1410f108910701c407640c496000d1991448070395034000610b4200d00800410024200032910031150850b00030160300030800182c040d5827043c03030f640c41d9007040038040d120645a400c0a5803107442a14009840c00364003803801b06c194401c0d0766200e5000d02c0440d055510031040003000031000034040c0b10b0310a001c0341604079594141c000203a1103003966200040301400e42100b42c0300b8001618200d08002d0204105441c0c1c3c1d6010380b24008080103c2010b0b001d68500b582c00b01c6642071038010002c1c18608410a807011034000504060403458150f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 222358408 1250 222357158 222357193
    0x18150a0c030207050d030e09071707050c15070e030f2d0a0f080a030f1b140706020d09050c011119030909091104110903120d1407030f050c0903 63
    0x3020100c095000740e0100254954815035030341405406a201c03c40f40e5445001008145403008122006108843d5604803521001081d615440000b9042480d03446402c600307401e1034601c4050407038624114080400484542c0b001603031800000540c1160000c0c80701788205030311280d070f071010030811103500d1003039600da480843c0d01c42144568280940d0381400407504c4007039100c1e240300400c0c1c1d0204400608003a05940c58070914080c074031100000c018010700118444000f8803011642e908014400300800400c41e150b500310740740c8662001046668603101c0c518170300a4620764200391118010194100c19a500410b000c440f00c26245011300a01d8840b0a1011000741c1c0c42c1c40280c040014442012031942054480c0b4105540102c0380c050b50780c007a010420055445050012100c00c4013848861226200080c150f40c0701305022800fa61210000d9140400030f00035000b200134020b041ca41403152160b0154800801ca0f402d007801800b0030341d922000c0d039100307110390565542c040d44407401c42c02c044500b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 222359658 1250 222358408 222358427
    0x6090f09040c030203060703020306010912050d030c05090d050a06050915010e040611070501150501140a0305060f06121906051302030702011e0c0801150801060c06140a0218150a 78
    0x1110b45595050301c0380c003c24944007007151420086a07002003444413540e0442c5051004007a14400024a01640c3c1d07101c076264221104913006168841e01401d032800d000308191510403001508405864030309003000d9642d100c40d04c3d410344440c1c0c80c0c2008121191008500e440d0302144001c4419142d0340b07020700070329084100030003c1d100b1942d6501c05400c0d06001034010716805004400105411100b0761441c034030340a03d030340207506100b0780c0d0707020a0005510f40240c444030003060900042c030741c0d641c01c013150310801002d40041d480940010301c0500f02507288080350107080700c0011402c0342da40284050b01150701c0743c01038070b902c080e2070074004c0120803540d0025644008a880003103000804100740f074050300c80306080c60b1200d60b00d52960002c072640c04400d080c0140100074140c0300c8140000030242c104481030041e070080040c2806a441400100c0d001510110300c2002110018504490040025003180d40f0a0f51440741450800c82603160400ca084e0008120070ba40d240b6000b0040025111680c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222360908 1250 222359658 222359663
    0x303040512030405040213080d09061d030705030a03031b02030306060f07030e0a0e01140306060a0509180304180c020d12051306051515040e010303051608031603060506090f0904 78
    0x20422000c01c40d51206d00107001d42c14610104074140d5414503800a082c1043c0300b144a080110300c580c10440b03140d0241c00c4042622502400104c42d9201e0f002003410011584c102c55054401c80300c0200c01c01d581940007803101380308a00c035040661110340303040307860748000da0308594070050600c0314120040d000c030300400690341300e420101e118061090100c1c210380303032607400911a00d111400400c00c0240d9400a1041c0300000c5011307041074071b0880c0015940340024084c2c03e0092602d100000d122028901c85442c0c0303110f4010072262690355900d80c0c0901a85c4504800450906080703803018403900009200e5050903054803651088042c1003031200c02401b00a00460300c1e547c010104c040420a24800c1c5070051040e0508072031400320070024001206a031400180ea900b0702008200803c814921680b419070780c0c5440d19aa840950408072a0705c413240d0340010f0710402c2e00009110601818101040d001b440c5c0c0d40341403081d1a5030700200856805444469030300b01544645001d0389281c0207100300d9000e071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222362158 1250 222360908 222360913
    0x7120e0d0c02040b04020f0d0b030304081507140316030b031c030203090105060d0206030f1b0c0a03080603120a11010608060c04030c1e051e15090a0f050303040512 72
    0x4004418180c904a103040852011650500d8032905500b414040c8440d0440142c0d015071900705a206074180c0f0748100c03112040e84507a503911404031b82e603040c812203004112040407580911490b00c0c0c2d0f0b012459040c0e4070403001c40c882c20000700104810400740ca20508080c0d8020550054040003580501010a00e0340d42c14050465105a40c401181410510350084d03500140c89180100c8400d0841d0b4024040c40d100701500004500165910000c40740d0101b80da100d48003e5855805911921448010780e400d544100410a401d08800000754050820f00990707615100352603d03070070700d17840303244043c3c1101c901c00c0100400b08802e40240072601d085250345000080c216641c819290402d103041c8c1c0d40804c82900084c04005001e044540798001d4032406102c442e03000b01c2c10182c441281c0d038034070130715000354102d100c215010103041042210303500003d00b00514400117298401c8150b0300400c1040d00c5200b9042000c154481011005002d80310080c00a61a1500340410000c1003519540000200e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222363408 1250 222362158 222362171
    0x309080c0102070302060a020c07030f0f0b04110907030b0310150302060a02010606081b0403110f0a0305010c0224070c08071502041802130b09040605030f0d021c02060712 75
    0x52181001840d1903109600010b032180f01a1070b00070306115000e4080361b0a80c0c011710a80c20a13201c045002c4003240e600c44025002248a45001c1005010300701e0041c05004c0c6c1441088140480900c104241e03070400c1f1440038996544000503000c9a0082d50126055030000324070568003502540003054883c0800b1652400c1c0e507403580090a00c0d4043e800040040c0d4494404000071a045070b6880d0300304c54250080700e0104200304241010b80510710000e00302005145d00c100c10f0b51900303001c2d114550800381406102545900300280a00b40e030f0400c7c40c006124107000a1007014407190001080c0d800000e5000d25a03c84034011600061071010a4501400030401500080d0b80480b00c0358810044c000c01503141d6150030021100c1c54902c43c51354240c90300400a5a03034a1132440d05040a5945a900b950340301c2c158100890001c240f10380000b6014454500c0001401c08002012011307001c1750b50031200c0400d050002407240b81140c80c42c00300035900c52000300c0c079003034003400d041c41c0442139110740003800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222364658 1250 222363408 222363413
    0x80106080c010f031a0f03070e1503070609120308270c012601030f051204080f06060a061704080f0412140102041a030705070f14010507030b0f040209040212100f0509070c120309 78
    0x65500c00c0d100310b00d078005000084051400c007440000010522420014850340c174280b00063f0806003c00e0050410520a001913040000181a01a1002d50349010200c01c0030304103009170390303e22045215000c03450308040001f800c030311720001070881d000c10410b401c86646140d5600c2440005c06500b11141d006221003552a02038000152000301100d42c0201481c405142849081c00c1019220b00d0140c80e01039007c2c080650801c4a840001c90301082040c000d1343d6030301b44a2000e014007680c020103480c00050010b411100c000c14401da050007004c8001c03c0c9208505c07214200e106510645aa04140910100021411380091a4404080d080c99443e182080e03650880c0c5012481c0216500c0c4c0071143d40f1003804009108540e40155a41010000008910001100e007000186814031581d000181c80070f80b5242d0350152039090400c9080004c40f4201000c3c1c11110399518080c010300f6545500d030008403460020b1805e80500d42580390000c60800a8403110085400400804141034590314001e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222365908 1250 222364658 222364679
    0xc0d02030c15042102090609041a24030106031a0415020703030203012c0c1b01060609082b141b030c1b0303030c030709080106080c010f031a0f0307 65
    0x165001009100c1e5158204243e842e1000504410500d050302c0e100103610046e2101d5020941202d4100d55280d4141e90300d143c81d0b540c00401306035074040d072007042e020300101108620701400c0d07104016000000f10a1088103140c04ca5103d0301c00a45030408212000419000d4460225007080c00b51400100940c00c01c2d91b1704050340d000a00440001c2d500000400c00c00c0c9104c05404800c42c0c0c0122240b0b144502c0d00070020507140003800c00000007000140d10442c0195113f0684c51a58250000f44200c540e1203401500d000d0803031080c03001c54029102421105a01602c4001e014203410502d000c0c408544181215805050768881500c0300c01041007420a002009600e01d4006101004581d00c04905070400d0828030004581642c0c488031491b500e00c99036010040d00ea00490a000503622542c4845007207800e030030300b50302070003031540381c140d000c1035142012481e800e1042086c1c071401e800c600c50380307002c13000ca07040000b8402c13849200502c21191440c058440c9543c02400404a03150b142d01d5540055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222367158 1250 222365908 222365929
    0x412050d150312080603070b0f0c0f1e06040803011404020f0c061b0408070b03070306030c0605190e0d0f06240906060318060203060301060308120709050609030c0d02030c 75
    0x40e0302080c0705070304204000f000c12403c188803101e803401e0407160130814003280c2e49130014054440c02c0340d0003054806816010805039100350203c03c003111909003c04200c9510f40c8038007a01d0340700400c0c1c49180346041c00400034005028640c481c030a1490342e8a07121400c0c0c0124a1004084d601c00d8080141c042005100c0700038001024646001c0c0c000350420800400c41c0c1c20408800f10708900090104005816000ca0000225409629019985d0b0f031445030803002825190802000510b0b007010115545506c01c002c3c260500800c50940d5500c00302584c2560042508001e0980c040651b032441c00c009407000203040d01040c8101c08c0421101055000000150700c188422000c0c0000032074100540003090154500511503414104007050340b076000e54449010344400603080c20303000030101d07000b6242540f19000568104030703000c0d01c401030500d0400c441c480c152090000920300c1100801c0f9450301c5003c50300b03540801401032040100880512404291000c003e076490f0091003003003c001d8540d4912030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222368408 1250 222367158 222367181
    0xf1f18060603050607020c12070306021315020a061811010f301512021903050d030b01080f1909140105180f0607080f090c10020607260412050d 63
    0x9021514141c0002450300410947c05403203000c0d81843d01042c0301001c512034050b26001180503950342c04540d10031940000c0c60344581c0d04070349002c4800ca0002d6020821880d400d21072901441103d04900d03009604c2e5109603c00750582e000c0446840207903001c0d8a40700160009400d114000e403141546030030400c0502014902000c54103840207107040c001c0d20525024188181c00d60b45468140400c0000760803003040028010b003070072912068581e01d0410040003c65000e811146074004c51034006020f001000e00180c045961000469055810552204d1185c1a010342c411381542072420808040c0c004040c098407001c00d040001c286200d0207004142c031842c6d00c5c1e02480c9680168245482c0b070b101d5080200c003459000383d0203200146510990442c0c00c00c5092250424a4465850850806600c0348900d41d0108413081c0c625440b54010580341d100b802561280c0030396160303440d0501c4240c0d03003484c0d041c1c41c905401d5000a00041c5000303120f01c900095441d1103410403400360700c0c0307a040f03400709883e2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222369658 1250 222368408 222368413
    0xe06120706090f09051911040909030c0605060306060f01030b060c060408030403091a030402010e060c030d050a0f0c0c02120a0c08030403051e0316240e0f1f1806060305 74
    0x9200031100b0009540042c200c02c40200038614000e40014a4000841c401440c002c0d00c500c45900c01d4401d610a540113446000c902b042151003628028181005006040700e5a82c00d001c0040c101d8034012820314402c80001d032155101050400045000300344019003144d01c820700340003c1007215820800785105038420005165603040909014004410310f51241400883d2140b41802c18078406041d00e812079420b00304070226043c40d90002e541c90003500d103400034500c004103564041e40760076000b05003c2d0b50614010482d43c40f4000c0307100c040d52075288224000c11040d050080c01420100900ba00050750101034820344581503440026039409580f1081c05076001080520920109100221158000410050300c0300c485010749a01e0b401665800c04811400c40c800b5402c2c480c2c1200200c883e1725008081c0e82d881105501c0000c002c1070482c4980113180f08419081d10131040005050481d502c840005074420a2555a100302400c922031044c2103d01c0c1100c1e40900042c054040c00c0081c520a501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222370908 1250 222369658 222369677
    0xc1a0703061e08010f0c0f05030907090219030c0207080a020618120a03110118030804150e030706050c09150309010e01020f0c010b0f091602071d060315100e06120706 73
    0xc460170344215894081d07800d803800d00300300c0d0625004420f507844c801d80e50a000341c0302d5882c4441039091030801c0c2c0c040003240340002104282174a00074102041074806882c104041c41942070f00300e9603044140940101584480303d41c801500c0c080c0042c00d120f100b0042c101c2c0702c60002101040c920700203001c61a00c254082065207081541215200301c41c010050000c0183c40d4000c00752500104031441e01a060208020200f400c1c00405440c001c1c1d82c1c4403451040c0240c800f180341d000c0d580e6114000658056107040b01144135503113a1400c480072004000c144e02c0941d07401040d40103959001400004056699404d20301c2c00f00404e0001d049044484480c9a4664281154640c01d5034541e5455603ca030407882d566140300e030307949420150020050903047d030440120410592a00d40c40b5000b1401d40d00b00103801404c903289609403144102020340a940c054a4a85600c800c0440192081c22180072481828414407044040050384224000c080c1c00c1c0200c02104030302d040c000c85030400c60001c0c04046 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222372158 1250 222370908 222370919
    0x207020111030f1b01020d0e030a0906020f0c01111c0903020906091b03130b0a0203010f1502030f03060a05061801020706020334020909010e010b010c1a0703061e 71
    0x501c0c10003007018480070b5458050100a44020b520507082140031a40100d4082d00c4502002d5044d81c2e140c16081804201000100d100c4560380e400c114940700016039201e00104402d84042aa00c15550700200240046c01c40b40b401520100c11007401c0344140c0c400d42c042a0200c40c0c072240d0408013a003058503040d21007400d5006204504400800d05070046900c0303002c2c07224a031404403240e00c000e421741c40020f8880d190341950015966488c14050b00903416101402442542640118100c070420000120020340d10400002d944140003601d00141c0c06c184205001d4040c41d50045a000388010709002805485100203640c54100c01039511940186040a14040d60108031000281c05240011402d2064038100559071100142032032800032100d484807914010400d420828641c0c0c010702c0449549400820740b4024403013409a01499030a140c46c0c2c0c1010b500851080c00083d802c9a403501712486040c45503075500740e01034080002c02d41e07603160000c3c05900350f8064507226181030b03402920842ca0030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222373408 1250 222372158 222372167
    0xd0506150f0f0d03110c04140a240b0a0905090103030215091605060c210703021212160c0212010b0406050a121e06060306050402030f011a060c010209060c0102070201 73
    0x8900a41c0100300c0c002c020511551000400305240b54145001100c9030200a501c1e401c000e5901d9529030003a04201d10f006104203404d501d42e1050414103c104500005c05410780ba0100d108070081c041405540c005001e540103580041001c00f160f41002444640e8540102d046c3c1d40c400d91042e030060f08191180d02410f4250240b568100316004020100c03080f028003000e41311501c52150750b01c80c060001d040b0007005d0f414044002102c9000024441030711102c0c04a03602c0d0740c41440100c00600542d102d1000940e40041510800302500c1c4113802103555429100c0c0d2881d481026800c203101040350b201005030b8803030421054041510780046240000d11b01404140c0d05140c2041d8454514a90240300304140da86c40414165044020640170443c1d4101e507a0803410301792009083e01e03041403804070500544d500704d0390140e4404c2c6c04030390400c2c002c280708074201e9503451032505003001c466082144510300703980174113080c0c4201c00005103030a900c14001915076205840811050b5004134990301590b070070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222374658 1250 222373408 222373429
    0x1503140d110d0f11150405100501060c03030b030f1f0b040902060702040c050706060b0703080c0304020108010509060a08010213150908060c0a0311070c05100f020703110d050615 78
    0x25082418441ca00d1110068482c10710b42400c0e8100014a0801507601e4491900d0038005419203040d141d04030907450124548020484056030329114003408094840c2c00f80c401d042c100c500a070b5890a4105003658210050001c50a0540e4540310340234140c40d04400074460390b00e0b150201088100c0c100941c1c2c801406440d4204c80040c0308034a0002c83c0005610b8000442e80c0d160343c12a000102c14050003000e540034000d071400070304010715040001c5034881c1a44000d20340603000c0e455480b03a580e07501c0303041641480112002070014000c48010449414121185504104020000e80a032915400c0460890f00f10750903160240c404010304115207207800c150160340380b00301d14001c020301d802e004041c0e070355040180515000120002e43c01c54603501c01e9000c45810f070511560a6544d0780c00d801c000d8030859040c0078031441402c90ba40e9040440e802045920020300254010b40140f0340f840d1180d032410030900c281940c001400d072403040001081881f000e44200c54680c09001040c6024041c441100e06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222375908 1250 222374658 222374683
    0x140610020d0905040f11070c080105010f120204050a020c01020d050609060d02030a0803070c0609030806210a0212010207053018060c0a020907021f110418150314 71
    0x7218079800005540201480103075030040c3e03004038840d200d04405100600d44440c0001c5008400708480c410080501c10250444014030000c0c0542e9803926001e041c85c80340d5104040f0f0811aa40c0e12000500b46074000300e50000c414840141071a50207111103007664842044c02e098907542d201000007500c0e00f112400d8001c03400355404e14040d42e10754046540c801ca00600600301c1c180100000c2c00840c40303840603a0410740c0c411000d000a24a07440c0c060321410094034003511031840002107014010744001145c014012030b02c018401001c1c140c0a0200d030454100341e2000ca5502004a480814000c02c01c1c0c04040012100103410210104000d1840c04209040c0c1e2520f4103007080b0012074140040c80054011008980b0103039181000c108043ca4060307182c030020340000140081149031b070740106403083c002c0446a004071055002d44005021a03c004c2419104440d0600c01031042c0320070202948003450701c0e900c000540c54450f9144d0091444c0c554421154042c103c80b804c20400c9061000e80030003203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222377158 1250 222375908 222375913
    0x20403050f0114130f080426012901030603020a0e040c0801020f1207020c0409060203090708070315090f06060b03041e02010f080619080f011b0801051e030114061002 73
    0x19030308041810020005402080640300f080c13159000c1c42034a1001007041580840d031141d903140c2c0c440740b03221120440c3d21b14101c00170843c04c17031000894060003840518a8201d80c519120341d01500303014403070018001c180e41010b5a86030301000684070076030f0242c080c0c10f400c1c20383c034114940340c9480c032503078001908030072010b13401803128011a406c901c3c180c500c070490100c3d03080ca099807050800c0340f40c5242c903004182e002d401d00540105220140d401503008180d03541c11f0341e621a031506a032a60321a220710004181546881e40e01b922405298800400f641c0b15001d017030a0054a6210b071000d5a0080d0040c4000d200008240000c128022054000001110f40c11407403003810354001a115030011019401070010b000001140c660f40c01c8262689211042d070043c4c14103403a0702001d59240c1c1c9409076403421750301c2c02240c1105903481c03285000d800780082d07403050a00e0b800d08041c024280d40003a840c0660315220812520580d03000e008054244800b5080c80a0707900d0403504001003a640403141d5070654 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222378408 1250 222377158 222377171
    0xa02130807180b1203130f060e0303030a181b08010b15030406053313020c060112060204030c0b1c0203011508090307020324150901060c05070801050a020403050f01 72
    0x445000302c1c1ca0009052001c03002a41c001607001240d10014841011416400001681c056020a40c3c08800644210700910b40030162103440554101e940b810500d40d141d03005000040c0c40320307442d8014680300000092070089529480d9507000014191058210381144004018480503d00744103005907104102c42d5048010082d01c0240d80c24070014101914094680002483d0112102112048030803882c030003003180c0c2c4c0310350004200c210070009000d108007801c2d12616416102e40c0281c40c0d60118190141910b41d1820340b01d1801c407010281c0841d41c090f020320002002c41c0110040400800d5001e241d00d90781e141c1b0305c1c1526014407150f034085c482e40d88184014018400c2c10006075034503c1e030505043c0c015495105d1024954010340b28020b5062084400003040b401c0d5501444001c401ca0b1342c0841c0860315403070189601e1011703140d419500081c04100401c0454800d80320021064020000d035815151900256030075070344112a0404610b030002400c004204040186d1821038040348000c1014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222379658 1250 222378408 222378419
    0x305061c02010e0316080102090108060409110d05070e0a0b01081003200a12030207080d0305090c010e120114060f120c01050705070b070b070809061b0a0201060504050a02130807 78
    0x500014030800790410401141c840032588041094014205400d840031000b5030362004110f01030740c002020b00b4001000c90010801c42d00301402500c0385281d1203441108020288400e020403001140c5c0140c0f900c0c0b150752000151480070000c1903009100d40e20001c1150031609002401000c00074000e0904000800c070100040352030f1034441e28a01050700d069240400b4841c00062180d1210382000350328141c1900b03080c2c10550005941d004031504042501c4400401034415000c41c0d030112507000d565004180101410b40c45a04000400c800060801d03403015564901c480c215074641c1303c0b08030000c0301d640038048503190640f0aa10311081c22600ba1440103038200308161a01441d000c0c190500001003080c07130411030240501d1001d0000c0754101d903101e11180c00c3c55420b1060640c0c80300081088000030070060b400c08101280f15094160130001d60904e02c82004205510500d141400c65581e4800458259524014540035280d5441c3c0983c03071344154031114078001c0c880e42c4040a2a409090208034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222380908 1250 222379658 222379699
    0xf0b0906180616210e01090203010605121b120a12120c17070c02030a0b01032d0b0405010e0109050304030b0c090a090f09020a0e180d05160c08070e07030506 69
    0x40e002491400ca213080c034503d002e002070800c0c02c04940300a181410303801540620154001300310305008600031320915655005200b000003681e900300d840350700800300d0303200d02d40c2c4410006507000001500c1c440c013241000390601d0400d2a2030324210b4600714a00c02200565510803000c104d9a081c1641c100660342c419600a08062646a0102c0d90300c0c2100c80040c542c02d0081c040030055680280c2a61101c1c01103107446503203404240070445210800540030030464060341c2804600000196030f0f4070301c408107900da440c003810005004651075901c600109607888420700030145040d100e240195221410740c40c0a001c428001440d0920280040c0038080565450b4603000d422208009000141ca140100c06034014140e2000080d400a031400c078006182207000700102d1041402c4404411308044038404240c86883c041c8040d80010010b00400b24111100301559800903c14040c0c0a203a603600d1650340e00f444000c0e0310500414126400700102c50f0341602035250703c103070211044190090314040c21039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222382158 1250 222380908 222380941
    0x8070203090d050708120a1d0603010b031312030608010e06090601050d08130f060e030d02030f130503060c03040311060403020a06020d15091e05040b040605040f0b09061806 76
    0xa1165480b94640d005100040c040320000d00310420560748148000c0d4400c00c41e82c0c0c000d2101d180010240712440d0b00781040c00700a0110213000070a040e1969282c0503140c0c17520380019040c1e004501407604404001146507158100209039918040317000e510b4445807600b110950f859440064000000700068101c002c58900d054980071240714482d06101d060800490060141c2c203183c1445101011800680107030000c42283c1c0c1c95940c0f406204000414151203603410810354000d64014014070003500c11110103401c0342220b845208503c60340d2036001a25050045e604d1800103c1c000051006043d8017148103111401e40740d0041c002800d03d41e030001d40d10f041d01a406456142c0c0401c070075001e01c4c1a0341200910144151000a00989888056005001e40030603854070340c40d46203021123406c18034002d4500c280e401c41401309403940c0381d450303030009040d006004558030319200b810a40024912038000d0b008140d0440108418504010013003000d000c9a100d088aa90144080100c911540038002c1e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222383408 1250 222382158 222382177
    0x201030c02100e0714060c070b0f0d18020f090403050a0810150819060515130308070c03050613050d030c09051507200109090b240d0c08070203 63
    0x16211005036400c90822104000e00c0380356509081001c0c6030082c0c00200380b0f040d100d1311941044868000803c00034a48070318512035041c1e0300954010403802160101a0070240711021400d46810305200140c8101d403801ba0b04041c070010b60820741000d41c1041d40d20a0420316041e2004516403c058038007401500520310010308119190000404c1d074000c102c9020b004049072141d0b00d040fa080808054095101243c001a060f019000061082c41942c0580006c40c0e03000b40040e1001c54445101d52840c2d400b2408602c0300003903841d000400505101c004140c95400380c2102e180580c00c5103445800c2c91805803040f1407071900c10310810041100403440307011200243c00c00060042d0703040320a8070000c2e2942d00480e4842e2a007105038038081007080041075110300c00c1000050540c5002d24508004107084d07245030025120b40020f12640700503500001c3c140390000c111070f00c8600301e01e8003103500742800d504500202d800451410034020041c000c608100f8003074107140c04140303041140203549010b10341c0d05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222384658 1250 222383408 222383411
    0x2220803070321090204050a020705010b03011505150c0303090313060305010b030a0203060d0c170c03060717090309030a030e011b02280506030709030308010f031a06030102091002010b011b0f020103 87
    0x11072500d042584103004d0580d0140c800c3c803c0e80380c8030f500700c40250804d04080d51079500f002c1116400b0320301031103840d0078107a003d03600d11040c901f41802c2c0020b001030500c2590f582c100400140441440400246200b043d11500844da41c1c1c0146270b07001f1607181a07a000205250a04e001407242031500421b80303130f00107100c8071b00584a54411001a4091200d800d000d82010108103011a008030704080c04945060444112081c0d50181824150f940c0000ca6072807000446250a2600300c000400c01280c00c00d580408403810300d0016400241007481140044012072241d0007100815601310b40300c5c40b078582e20303001000d0a1640a0b0040f85080307013981840c08603140110440e04003e20010221005040080e00e107586918010101602c0d520b25404203a011601c010000911442100c41c0b030300c00c1c0ca9105841c21030140c0000c0c142c0300c2d005809003a5a03499502071001d4035458641e20f400002d8494542e00100c0c9072100f20001401c440d80c0846100b20950219a003000410904000340c400d041d070a03c0c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222385908 1250 222384658 222384707
    0xb13030302090406140114090904023604290a0b0d05070902090301110c0c1e09090d0905040e1f02130806070f1b0201031e022208030703 60
    0x10220024498400d40329406444c168001c80c44161a0000c2041e290302070701c4104280ca80f011800000780117554440c1c6e48808031900080040c100f000460b00710440c1f10008a01040781c10982e2a03c031001d600c00364288074220800c0205021805450440b0415441e07413090060940d0710b05800003d00080c000711085407160001d2056440e08845e0420658005090311480c43e110001000650b02400d190b81c03080d820b0903900f811002d605c00c100e03603807001c4140050a0407840b038424056942c9010030304080e0a80410b100407001d1f01c60b91120740c07117840204080d103070010041d1400341022085800180c0600c3c6849054a2040780000e031044a07000700001808110402040e0200070703200304a4050030f0400c0384200003880100000f4035900808461b01c4084111061038801c880043c1c100c0486250303107035003c2018015500070740c400118107541d0008050250f07028100c1d40c00380d80c0460701100e146414800042030849020000c400031307100810156103085025280200200307000700c1c821402e4035800c40c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222387158 1250 222385908 222385913
    0xc0f031e030306040b0f0a06080c1603020d1101181704080a05031810080f0907150c0201140c1c111219030510090b040e0604111c0b13 59
    0x1000480c5040c0541050358100d40e0000952a0703001a00c0150040782400807011941ca005410329912510181c1008080c900c0e1240880328442d001e40040012807007001000740342e0101891a00744980070b40c005081c1841c0030708006090355204203140429925220002c0a211000058000110741100007a4054154060740c0c81403482075610031442c500c103001d40d160422030301101400380e02c1d001c000d02000c8480558188060010308004200020700e4400014030010780c8821219040761600b811504c029882d40102d0001c8421142905c0100f24220854801c541e030001700c50a0349a52015001d0404144071035007583c40780e005503111602c6085010780c04031244245030411718400c0541c200c071800180348460a80a5112584000000d81540c103581c2486019004041c01007808560080866103410706460080c01c44180c0290322980303d5414000d40d50040090600941c0200c1e4101c0305150032000b040400c03200c628a442c0b81c0c961800c562004035000e429a60342c4007000070081c0f081c4400c00d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222388408 1250 222387158 222387163
    0x102030405120f0601090b060304031b050d05090a060e0f101407080d0b061309150e1014010c05030901030b0d0210090e0106020f0a110414190b0d03020c0f03 69
    0x10340180d034012455003540c20790b5000002d103040400100e80283c450b0b50b601c4044650650301c00c142001c3c0c1200080000c14006031081d4140007203510900e40c3c1000203a11503507020b00f07005401030104005800496510040e18007e80390300010902c43c200130004000803008600c942c132503060898425500000300b03401c0075020f402404205042e07031759030b01d658481c00d1031b10f08010740008802010b01d6243c2400c1d140c6d00c2c1024811500d600f640b600c4860340c070a1405c81442e01810100d640b50307400e0b035581d5000081c00e04c0c50710b2a40c0c1c0188040ca2614404d54100780401010340401204181044404125031020500c00710450300c180c9020710b8081200746400c07010a00c1d1442100000390041405000b200015912000070402c1d5106182e903042141da80751000c0f80e032088d0b070a43c0152035801aa80344030000d08a10040185013101a0000c41d029009404001c043c810446401144071045080004074114030b1160f9683c0da1001c0f910b5004001c0304c0e46000750b850034407801c0b841c000c00d8001481805642c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222389658 1250 222388408 222388417
    0x306040207050a24090b130507120822050a030f02011412060a140a210f050307050d08010b030f04051204170c10050f07080c0106090902090a06051e010203 68
    0x122040f96070003410740c98255100790700c03410030821841060f0450151a541c50040d04002908074140342902d480d48000101c0f4410001e41c02c407494486c080c030028400580104101036240540c03c10307500c59900000704a0024a041d00d40a641c05c0d8800003405a50f580d040040280d03074020b0f101204a200a00c0180c40032928a042c00c070115401103100f488060146010902c06c80007035504040c050b0740c500106200740740e1000c3d419845501080c0c1400320141d00c51000e1100400251240d1401400351640d0b104c5480c0b040054500390800650413050000800042c6840c98483c5041f0100d9072400e80d01e24a13900010b40325910b0382d000e071000b02c0d052020400103ca0541140f4800da030b9151303aa05100309510460303450b00140c0e4080d6415000c10752814913129074540047d91070b050b10b030050540f00007040354482c0c0c034201c401800521455214040920400c400340c140b117a07000904244900400ca4842401411015903504084003400291601c10410824000300cad0500c01171b018500005038118000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222390908 1250 222389658 222389663
    0xc02121e12060f030a021c030201091e14030f070303020a0309021e04060801150509071e021506120a0206160605040b1f08060402090703020d0c0f09150c06020306040207 74
    0xc200c40d403580d911940070038001c0d41c04030340307101c840c075601800d064442d0045040654000b2002c50140200000680b400200d03a2180c4000034000d246075032840c42551100160349040205100c0200412012180c0d400043d0740b03a400a505010000551078450f1241070001010950040b8034041f010780a80c1040e1820ba90040c0705d10650014030030040406003100410364802c9040c80340000b0000b4062040700d0041c0042e4500b0304649040006211072030300302030204802c00c2046a40454000e0b410041502501030030350240c03000c00c0e00d00600308103501e0b002e8003040c440e03500304008042c02440041d07459082c40c0c0c165840b070380f104010301c040ca249071010103015121071700340f00400041207414140740b8070405154204030312f030380c04201e00455080d1003801041350b03039401400400c02600d05940142d600c50707218900946800c50118110042d01c2c5071404550200303225145c0362480703540040881005e021011500d0014034240030004106c40f01d5010054905580000480c1a98540e42c0465000a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222392158 1250 222390908 222390967
    0xf0b0603090c0a140904060902030a1401060e01060e01020a06050907080d05070209130b01060c15020c010c0f02120a081f2c100e0a0b04061e090c0212 66
    0x26041e004240c0321400202843d125841c180004244200b46242d00440188042c012034007580d2680d48000040c488030000b42e9151007590b095070001000f4840417045406203400101d5007510b0510030010f10342c0c041c0c1140042c04205040201540d03800104802c04503040782c4003090780e8440000040c144070f12500b0015141c010031080404845d000001403010b54401c2d10091465a00c00041d8124040351110080038a030a42c801004210710070302403111820700179043c4903648564001800b040364486281010305035141e403183c404440d0072003500984d902141c006440e6602c079142003000e43d807007400800c5061020440100c2c104105840c03a01043d01d092410491541d40c80344882c61400e150303082542164410b560400b10125404290940282c0740d100842100e80e040010020a400c4014100b030301710343d5109910819542c03107020b404010405444040700b0110b4100301109034040c940c00c0110301340d0030301c80c40d40c1445600161340c4011840d02c90070315440c2d0701504114070488988099404501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222393408 1250 222392158 222392161
    0x1b0304060b0d080a2a030c0822030c180c09060c08070f030305010503120c030306060a0c1a0703110705211b031c0b0108061203090901080610170309040f0b0603 70
    0x542181c5e42c0c0d07109000018400a0341a04003241d641048614000100007541390044c103000110b038032015150071100302030a07100a8900c00f2900540d1601a070065807080c1907082c04000c0c0c510411f0007007d02d6241d050007071000a200d0719000d003070325009100d95010000060900010f1180303410a07180002e0b130001d1203146050f19810000e001c0d000a000c1ca03072003802001303450100703259000122031500500502450555403548100490303031300012507820500c0180c00030080000c510044040d0842e9002c11014a2800c0c5141c0042c11503106071020a251801000600017080b00020b1408001044002042403500d040483c21841c3c003401c07a1b8188182c001500070a00d003400032014040014a60342e080c4002c4258441181c103988a104002d80420038003c0841c42c0c0e1b0806041c51210004840116490503d0f00700100300039607000da0003441e00d500401e06020b060781e1f204d40e07640018903240d0141054011391071261500c074456000038620656171580b0b8a100c4109079085032001038030003801d56850303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222394658 1250 222393408 222393427
    0x12070902030c0a0305070c21030b03030c25080c04050915071d04050c030613060812120f010e0f060a03060606110f0102030709050d05030702091306051b0304060b0d08 73
    0x10364002a8400e408241400e00103450188100c45d64147d194000310b410b00d80b410240010f482840d0600600c600301916091110718548080000f0600b106450000f1b19048000c018039000b1306140216a52000700404800c0150400c00903180060980843e400185501c859240a10b815402c00c6072040380e00b9034204002000b50003602954840c00170131290305501041ca001c00044500c00c864203c9516000d101082e180c2c04c100710310054002c030300320b00095000e449402007881c100c40c1400c3d031900903400155001d4100d07000b19046422080c0641c801c91654180301407600d5400303006203958001002c800000f4072564900003240c000310740000781080a41d4032940010402008142480c0309881115695004140d0500c06c4910400c1b0f650f440201450030081004100346403020181e03140e2100744041c04c056514201002c1c0900011014100c66141a1415506031000100b60b14000e0140c880c10038a14600c0c45d04580e0700c1a0b122000040d044823100014140d5404105c0140240c031022404101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222395908 1250 222394658 222394681
    0x1201030c0e0c0a0f0c050c03070902090f03010b0604060c0602090414180d0f181d160507111201021306050d0609060b040308130b07030201140705090a051207090203 72
    0x1958002540c100c11a0b482d220010150320466620a0000e558414143d0425204004242545100c0d5096400311001e980000380760103095080000e2550303001401201900c0e10310a1192081d02c03d8000b4000c120b01359000440c4c50040744641820301c20700c1881d010401115504a4002d10b2004004008001c034030410020701b0801202d0064002410754201c55501c030000640701c00300c88655540c110421046601142e103421140186550010300100114441a001c14240d1b12030300b811610340c8072890301c1005040c0311344a00d81c003141442010401c90020840305d00b02c20740c000c00140d60782c0359212040c074052802440b6552681003540c0c26803102044443c1d0100082010882007801448129143d1040c00304952280c071481207008010401000010402d10180010310002c50b0721561b03080e500c040c07020031076010820072401031b507603019540010565154500d8001501d85000c40c200b244150100d1101d0301c050143c1803060b820811750250464003004404040e1800b01801d41d140e00f03041e2160803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222397158 1250 222395908 222395933
    0x31a1e060d060b03040605070c02030d03020d1404060b010206070f0807080721140a061d060d020901240305010509042003031602030705010305091b0409020a03050a031d06040614120103 81
    0x660701410709002c91510f40c803889d02c001314990010058035450301942001e80080d4440c10303500c2c650a49900c0720030268a051070001707104502481c408a0680601000203051550007801442400340008241d80c1c0c60394886511a8011510704154240352a50070007940d551002d46040c03403034030b100c2c4d10040e00c418503aa0080041c0c88506c4880c3c1455840b080003130300a40307403107018402a00401c0e0601e0042c400c150b04510b50485400b40c06802c10240c2d50b004168038403000d030443c4403001d01d10201100e009a040070b41ca44006c08034601000994101400650740440c00b41c00a01425000a003100c0301642c192510682c50000400300c0342e81e9080f28800c2512440d114000f64031a01403050300042d030354080e0152070b03c1004820060080e00004440d054086918141e0382908180e44690b820016160201594007460143c2c006140c40d071030a15000344007911138151405190885e4132050403079107421041d6030645030b4074280252000d5046400c84200c0c0514502c070345c40105501c0002081c022070b00d6042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222398408 1250 222397158 222397163
    0x4051507110c030d0203090915040207030c03020c01050702100c0c080706020d021504022215090b1e09010603020c1f020c1002040e0c0304020111060702010b01031a1e060d060b0304 79
    0x84141c01c00c0c22007056110640c0c20703503010242c6c004010502d2140342c00403180b83c0c081080003202400c41d202c038011038201d800c0002c0890114040e01d1044d001c1c15010001000001e00034030f802803400969070302140e0350440c4590700906105500404508101140042c000509031030300442e051140d4500e0025901c0c00d48660301c1c0054050120144031b62021141c4580c880c98010308000381c00c00b1000c100b00d0603882c902c910307000b420380da0b00c0100c0442e500709058003004000030700c4041040c0b102d000400680d1014160440f1103064000040409a250a0115811a03055003401622603081c0d00c04641014500ca15610311030b590b255241006060350760141010b02c0380c240c01c0760b45032490303500c80a0032882140160350740408d43e030300041c0c01044010002d42c0e03c10301c189802e04000e2801d0710390f5440c204041c0c0c3c0c14400350751210240c10042d6414820703107014000c0c4101410502c27000304c0100d003d210a04580305820311000503964031a40b101411a03909440980003013015070342d20982d5001035002074508 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222399658 1250 222398408 222398413
    0xc02090f010f060c05060c0309030c07080d0806030606130e07031403030103120203040b09060f0c031b061b07021c0f0605040515061023040b07060605060a090306050405150711 77
    0x403401c51311800ca446100c503881030051800d9280c1600e2280940c1000700812000e02c010400c5041520b4240700d100f000b4801d00c0e00034100000740f08009002c0e00c00050030301d400b9520500401c81c044c1d90741054602c80b60100f03d0002980152031054034240a655040680701c1004044121107100703002004604807030091460095843d42c0041c101d80b6482180700b00301c13346d00c09004202c41c51408c203008114012614640743c4c60404402404ca00759008400c1e030710109009007054003000d400900c0713099408100395122030340951f05e07140181954010076202030b00034601c82e481c25000d0418604a1410240c000b0801c02c1101c40c10f2a054024000890b0102c54a001d0205400911100b51005600841d001410261483d000741011545c07981503101f048a080185612180c91115941c001c1002c2d000041d003842d640c0b42c0303d042c600b09403015544058060b80007008800b2103d80c0c400320f40402d813a417010f80451107860300c1c00c02c01c0c5010324030300310802c1e10a40c50045c407000d01d811880c102c0e40b0034002400d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222400908 1250 222399658 222399689
    0x908010c051b0f0a030e130f0b03071e060503130f140d020724090b030703090209061c02061b010c0f02011401060206180a05030a0e0117090c100c02090f01 68
    0x10015122800000f01100070740c02002d420002034040d540d03600e02c5440190100c03c84e100c600c10001e003640c86285204240781ea4174034048103a82014844000586140c0b0380c2c00da0545840d651032109250144591300400c031000c000b20700c0c0d40100004080c521508188482100c01480c20803443c1001c0d105018810740c03151700007461000d400072a03004120741144510754000301c949507200d114590303240c88410402507000340c0030840400d1f18010390302500c5942d90007d00c451952044c00b031000d0b009810304d84200b451071161b9a105a1182c403035a00307141d06450032a140c002007074124a89400b4002c40d00030a5007401000c07491940d0203800e074601300d85139034024070401d50103105103020810203000307000041e0005d10002d825038512282169121480d0720448052542548881d801c43d001225524000f48000406102e0394dc2d02c407a04003070b0650701182510050400364251a540c0442c01d5005001d500082880300c40795015102142e0f100f80c0103410389889203007880d000c2c00300c650301f4000c40b0600c514509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222402158 1250 222400908 222400957
    0x20406121b050a031407020c0102011406090114030709061d0f04030c0305131806030c0501052502061204050606151602120c120102040e061206070c030908010c05 71
    0x3803201c036074041d00c0000c40d15051150044501c0d6002103494420704d40c95a00c2c40c265410000e08841c8113521980c0074001d81442d9000090135a0b940740c40401c030411082c800d0007090340d52040b105044405043c03e244403080040b02282c14542ca0340d21940c002d514103440000c0d903600b428101c10b0581000c102c00740c82582d0307540d4040c040801c203480150004140d041d8400000b40240c0050900e0400300041c2c4444d903036950024100540340c48456484551690300400170801c110788203a01400e401d00f0494240b0b4030301c00003008040220150000e045803c00703552015500c9142c201c1e900c3c0e4015080c044a82d02c0d0509040c2d03a148401d55901e4000d4004071b03101c1c825100c1c40c00075a0808001001103c0034500b00790204802c54044d240c1c0f004260160420314000782e91188269041070f15007e0015864034a800700f00e442c8500300625043c001c40c58140c11460000012414035403000356420203010002190404a0303400c03400e60810b41d203940ca0006811101c58010024000014001c0e206540445211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222403408 1250 222402158 222402161
    0xd09060b0103090b04020f150d411b03070c020a080601061202030a020d02070f12090b1b011d0a06110c07030b04030512071d030708060610090504090602040612 70
    0x7083c01a11030495440450010b10b001040c030809400020b10480b080c0044e4081144203a001004455010380e40d4185051805041e19990079108076181c040d00b501819080600702110f80f10030b24a814480705000264406e044041843c2d00202000c15561240b4013048007030718800300c0c020709071310444032444c0c0011003800000b4218140c845550b64002100900301a04011750805086064001c4d002d01c0202048480303031003d0f00c48a4002d0340242000300190070020340d601500c00640c420080c01040078040e4051040460740c0c90804403269050600a440754036006254012000c000980c0502889804441c0040d001c3c40c414050881000b9014408559080d0307441020700c0300704903030041342c81000030400c400c02481d07129001f404d160b8908182c51001c05d031212001c80f0010085581d1031000480c03150200719184040200750000d0407034034100108107070344560082c000d81c4201032110b1000600d0f4842d901031401001c0251003400a0320b0285085400381d0040d0041c10300190a0008031400000076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222404658 1250 222403408 222403421
    0x1060b0c012412020a030f06140723280503070e030c030d0e031f0213080a050c040e0309130515060406090614040e0a0501050301050a0e060c0304060e030d09060b0103 73
    0x20030b62542101803500d400112203d40c08003099a014010385e00010109400701c0c00e049505100e07c0002402589001260005a002804020800160402031342b070301c0024200f0004c10039a08008151642c140c41c8400201c8451900030246080d2002c0b00b00324060340000245018035926150000e0f410400340a0558403143c41e41540c1d41540084d4004000a00030262480d1070f2034041d082d150942e51155101c0100b00c0c2141581c190700b80d0010f21040e113441400200340c0981100d0000d85032900c0342e510b415984454041c00c03184500d98030707816808864400c01c2110b0303140700c01808059504c603480c00c410b0024001141d085068030300100c012803051030110101c8040c0d415503110440000e00700081216000182010080020001c01011803680b60182015118041c0f040300400c0545c1800c080c9425200050702c2070806a050120172080407101145140c1d02900c003d005a40301e03a076600b030090241210399240b1020740030000d1980301c640495007160b40740f240592014003a04440400440480700b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222405908 1250 222404658 222404711
    0x11a04080a030c12030b1804031b1212141611240106081611100f020c1002090319060221010608060108040308010909060917070c0b0406080c1b01060b0c01 68
    0x1000900405050802981581150084ca4014081d02e2b807103c003001c05620180c82038482c03c203451010044560301c407400f13554001030038409104050814040c014070040c05800d01c2d0300a0f2203580b900d000c0d18840d032402d9a0f500403140460340c505c154a5035913901c0b130801c20904c117a840c44460000c141c150003201c0c0140180d0302890305000178201c0300c1080f1440d03080000c000580303000351801c0c7c540e462601d002d0074544c0d11580c0c900581c1c680081507038500d0700880000b54042030b80140107000c00e0755004103d03030869030000460a2899407070752803d40020711420350003610009040906040800680f0b820606850030380d25440e4144e125000199480002110300800280c041001400124800d07003119000c0d070312030980811541c3d45c0d41c1d508404d4000002da00d044040003c194401440308003c42d0f580244139800074907181905221005150712001810450b0f207010005850114440c042e0f42c0300c1c1c0001400000700159602c90821643c00da001c0c0132070700075a60070484440140608050441c20605 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222407158 1250 222405908 222405919
    0x608010516080714040303050c010506010305241c0609140307050d03111201030312200304030813050105010905160e030c2119170c06011a04080a030c12030b 69
    0x5016080c02c0350b1a040042c4103100304940304070080b15504038100500061482034032135544504100c0140c0782140c0006001ca41090b0030700003031254440916080c1006000b981000d450340d580000081020b0300e20b41c058a01101810864400500429611030703100c480c800c022090b101e40c00d051080f50f0b00e0007040409400c13a00800540c4081d98000c4c0e0102d440142000b220a0400140390007244030500c00741c0c0150003191002680c03480c0c2c030059221345881d408001042c4003000c0200c0c1b082c0c0072603010081008040c0320980c8081560081d46100f01040a40d20800a014568440c110803024100540341e8050011424090500090080b0017246424402400030b0402c07502d84020400a82c400c24400700344c19811291020380c1c401c062200890701c480640305070148040c03a18290f0341c1c0d0b981080b0140b01c4200c0901084410000102e02d00f41103e11450300380700c024009024284451140e0350000c0c8107440340c002024105904080181601d03030003100d01181000313030307039805800340e4600c494100d5021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222408408 1250 222407158 222407191
    0x1b0f0a061b080a05040c050d060b12030f0708160f0510050609040206160602090604080c15040f090c02011404050c12010506130e0703050105090601080d0f050f0a0c0c170106080105 79
    0x540d130140e41e001c4d015440f01c6219990b501c0208504800049098840c240c540102c4181420000009400107001c90021882c0c90034007900c07001039000301c8400030303c1d11000040c1c8190140c07101100c1700619800c0041c550340341e412450038039034503a1482030f005255801c21340000d201e40b134505042c500c01c5802800035880c02045900b608000e050700c440032903440750300b0302800c4050f0b15802c02801c040c12050005041d03000700d0808000050101910030050b14208010500c28071900b02665000c840b586c01c001310313412116203c01c2e07000d01020841c05120051950420082c407600003011320000320242c03079101c184810070981c00d0a80d01c08440380ca8000422045d1100044085e0b444100c1e60070006007603a016075282d07074402d82500c200f69185200ca611240050102171301c00e000c903100400b07172810410303c00701000401038001d015911518809800120381140140e000f510b031901540d0780513140004450311800b610702d11504030741040000703610703115012801030814402c02d40601c69003550031005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222409658 1250 222408408 222408421
    0x81501060906030e0709020f0a03060503010207020315040312020a05120a0606050313020f06070b0714030403020a020108060402070c1e17030706050402180109050f060f0a0504021b0f0a061b08 84
    0x2d03124150039110130340700e042400101c1040c07a20203481419010221256034946030140242a00c0c010b4124501c0fa92041111200590b030009484100b0034125000031038030342c0d45003003c0c0c40da003082403446848540001040c1d9500d50348100140003508007442c01c070308036842d5540c22200710f8617203000d07143c041401000810215030100081c0582584000d01101e0a507840f4008070b00f55400c8600304035594060b03541030000c41500014042110502c8402180c2945080c0e00c00a503030b6a0b0b2407502030705000a050104d0196280d980440740d0403500040c0c0c080c00d85541c1c0c200500e05d8020003a0b0244038150120011402d1103403111002a5200704100440c14012a52a40d90081034060002c0344d011040d4500c3c1b080b0600d00c0854280205118071000510713260813240407014440003410f243c851003460049030b0080c1c4d54402c00c5019110180e80c01a00c0322005403001a034054036034600a100e20403520081b140d020001b4020802d54401c0701e040c030403014a022030890700c650341015200421080c0001524 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222410908 1250 222409658 222409661
    0x605010e090a03050d06031a07200a020d11030105090a030206010b1c0c09050306010311130e031606240812040b0d0c260f01051005270a0f08150106090603 68
    0x1404008040004400d6a280daa80c400040f003428005102c0001c0d07000c00007200c0d001504ac410804c034105d0303540b9108016019094442040c00f4000307200d0000d90041e8014401c000300e4000200c00040c0003009a424500c40c1d407540e034441c800d0110010304c100c4001103483d4643c02c058401c12001c40700c945900c101822030300d10203401e81c4507642e41000382c50580001d10381e070108121030080d8001c601000500490100f4465030104040e420202c3d0ba003000c0610300700860000440302c09902048221800c804640380402c007808111241000303418505109001d240144501d1604a0704004111120b071322480844000704d010364418112440b00034001c100d00d10103980c100101c0c4544600d85640d000c00103a02c0031002840c80b403074040640c0c414000700b00c0c542042407045405450220369020a0501c1d03031000415134402d01b0f21035042807244000d91a07003290200c9844c41422001010464182d072200c04100001c42c5500c960402c510584902c81e810b404549025816904695100c002150616005a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222412158 1250 222410908 222410917
    0xd0510180e060c090a060305090309040501290f3907090b0405042a080d0f030e010501080615130c080405210d05091005010b0405102c1f020a0605010e090a0305 70
    0x10014001000940104c0d5101d21403e0702a00350321011542c030408004481c0100f04000004031042c02c001c10038030430f1503207294042c3e54a907006005085070701a10007052015240c003002c281314a9a040301100a0500400f2822405035008107008101c0303141003034100010740c0c10550300901549144410302c0400c0b14441e284200203050103480800c0d540d503c4044518091540300004001072100c10f800c6462545402088078800c1c40380c00070700003035040070031440d19030101919107403414904001040c071940b22400c80d40400da20b981c108200d01d070000315001c1d0074200b0840382200c09002e405801070b0402d0307250361130710761110b400e10407203007084c018a10440c000c1c40041c16400c003610400b03011603240c80c09809814044c10200000326112032404082c8140f0518404000c400d01c090140030520301401c8594002d0344c080c080c04182c00c0301005c3e00108010601107100b260710110f500a50304005034000840500c244d2296904100d580e996a255031040308040d40d0000d96900401d100302c01080c4908084c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222413408 1250 222412158 222412171
    0x1e01120f1a010e040b01051207090c11030d0605040501170a0204020a030f09030e01090603020a02030d0908040302030a0605040c0506091018080a030309060c140d0510180e060c090a060305 82
    0x2481101c80c640064556228241c0c042c2207002c04180030002001040c00780c1c24014181a41d030048107022080da015106c10040c020144803d50344c81c2000d40d498420070884520652030707810341c1d5a4845201030000a05094010b6030f004074113290000850a903040c81043c7c81c003040a000c3d110f245060f80c20040a98080b0b00c0070700070152540c140d1b24400005100d4801400d10035180ca4620200d4800003500e03480090b0f05c45014148144015681d05802104840551504142c0001d040f41d031440c151200c0c4c080c941020750180300740507400f010041e250744583d010342e00508950b0700c0707a95500d04004845c4905103046810010124815a0303c1d1700400c030034075174524082c00c10030716643c40c2c0402034a4000800c00c1900002e4440040030180b10f514810454a0016482c000941007440030b070b842a24483c003100c0101b40c42c1d1304c2000074107200740c444690015080d8005101040d00000c241d500c0508034400c42c50525024640100342c10040f02811140c1040c030207024080d0740d900d0000182c00804009102 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222414658 1250 222413408 222413423
    0x80706020304170319050c0307020a0206090d050607020d181a090a030203101514060712030e030307090503010b010c0201081801110a05190f021c050705151e01120f 72
    0x7025490080d12010398418003001ca05c070811004804951015220050000c0c564240100b080c0004079078007250034600c49070182e45856503001c001000c9569401c22031405000c90091409003c841d80c0e01061030b00240a0342c1da944141e05c441d0180415484883e48158101c40c04001c000000c4c0f25100d102500d00c40c0c1d001421400711594903004281004002031061090707980c1c0340143c0009061507915000a0203100081d14240600390300840d640d84240c19000e0321140791402c0d925880c2d881390700214a01500c51040d03a0705c03400c1182d0040c01240b0366020b154483e5003003904c1e0740c14951250011422454059642e20000d844d440303480354141c1802c80d030349140e9540f07034402550310a141c2d200034540d43d0940d9540b103655013000c4a03054403050444044404102c54081d501400b680d0004550b180d0842e12884020a141000003d035410b00c554100285240125901000c2200d580440b5074801d55008110504c01c00450310450102e075824003441d00303103001644540c0c01080c0b0303827041d208549114104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222415908 1250 222414658 222414683
    0x10f140a03271b170a060203220c0501110610031103071d091e0a3c1b03030507080d021b0601080715020c0103150b0c060105100903080706020304 64
    0x400e072107088900441600c160301a4050003a1494480c8082001003207400260b94000c03180c41400c6458250710700000e011343e600400881c0141c0c124828105540c42c0030000351850827040e29107090050a54807902d8081000d0003c00441d40c100418040d1188a00c1c1d010758019500f550389040c580d41c0b544210a40612560001040403c1f41040b100c40080a200b141802840e20841880ca02481280c010044070101b08047e07810882c000740c11943c09a0020611072342c20441d0451a13895204001060350440c4006030f9805d5044100c034490324017070301500c0c0070341100454111038480c08110b444004d000440c02c210000c0414207040103030214060391203001d46080407284006c3c03e90b5440241c10b90305501711600400c020341c0d040100400030308043c00e281c5003051540c40b0180d01c901078203540b03906140e290300c2c2c5650065028610b5002624000c40b10701c0e211400700c03001c5a52842c0900445000b0105c0d00648400c0314080c2c000c0d0307000c9075440000e1918110041c1c0e03540c0065000503208840e101401c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222417158 1250 222415908 222415961
    0x3080612031b01020316020a0c090902060906040b0706050f01120b04060f11041e030b0109020306030c03010e0d23030c0a05090607030c1203110a0309020f030604030e010f140a03 78
    0xe88000b80300240000b41e05c0b41004800d205138500480b140c1000d640c0114002800203000c032a181080300e02030300e0002040380d558004502184512b00c16503a00140015000c03914500f0500540010b170301a100800c5140d98151031601700c0307a400c3c0109400c458502560f100001d00311200c441e1b10512402005c241005e83e03007100f0040d0f50302d00a40f4900c0c0240030505010002d514a004c41c410307403100c043d10517454550b88441030b080c241030003141d003030f1600000000c1a540b400c01c80390688401c0030b0020400e02c071502072141d40f964003800e004000140c43c1c610b810720340880c00c0e1100051003140740d042851a11350120700c07002c13948042d003664248542445801c03c20350303402c806481000d0103621103051401032858204884602450302c80181031400043c4408540c07036a00b0b403500f40f0100c0c1070001d0403110078000201e00d12070301402d10380d03d882481c0800040684c448800c03c0300003000e0320b500e03040340203840c1d0030f40d640a0320000300907842500740a011107061198220203488541c0607402143c881111 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222418408 1250 222417158 222417187
    0xb190b0a050c1c120506010503060103090201020a1b05040b0109050f0d0201090b03040305030709080a050a020f0409150c08070c1115090916020c0d0c09150e010e0717040308061203 79
    0x20f201041410b80421003012207802c40224440320f00c8480301040280b800e81d001800da40130162002c1e04244d941c44038007046900030008555125000780600b12061140d03841c11090300454010700d40550700313040e591070455006044001c207486c1c0082400520035551014031101300000301e000d9040000700340001400c16902c800543c011401b07907407070319a43d20f015a806082c4040c5544000b000b5400080000c021607008244501160360403180d043c986c03518032000401030200680090b201c0c0000503105040e02803240c4c03260011001644415203150ba60000541d03101c5c00000001c1c040f04800da000c41c00d58544520103000c40201c50130319500300741100b03020404501c01202c111100d03460303000e0040d1410f9010845034601280460310340c0a526003541c0d0398500c405031807046050130381d241c40005101d91500402c14003c5d013401e9901070720640c0d4503100480c0ba04010307154503000c600000e10040200205116481c8100d80545500040707484c0c440902c488941c1c4240903009500041c4400111a240e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222419658 1250 222418408 222418423
    0x315060301060f030501240f02070504020406020a0204060e1b030c0706050906060405221e050109050a0611041401270602071d0907060c080d0606080106030b190b0a050c 74
    0x25558100c03a10900720f002030129141070304040c440d040303a298680d0300801d5a281003c0c035035480340340444100a641e5000d0f803a0803100d8109952080c008030780852502c0d40000c2110a9500884003848201d50f41e4000c3c5614060030342d08201164880543d580600f8030010040d0340001c9079460603403514a86440e86422a402600c401545800ca681480340f60f24040c001c035234100758500c44000380c004060648121108803a007004000c030106030380c008031480040c0388851b07415803c44000c2c8004030b0b1a18145445a031b1403281102c000d032510044a49402c01141554241c0c1e154034420001d0a0003540192189001c0702545520380103407403004e5804050320514500200400e40007070001c1e50615241614407101c50710241a10348101d0f08110307845000054031b10494245041400303c0c61710500b0b00808a105902074840b01c1c504100380000d5090780005280e04a40e0b036541c082001501c010200603d10300d003141d040c512014401c6c0b00703020640b40d0030014010400300342006807030b015040d00c42600303000c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222420908 1250 222419658 222419669
    0x90f0e01080607030b0f040e01090b100609081204050d080d0f05090c06030c09010c020d060504030e090c0903100b0d050a1406060108011d0615030a0603110114040b0315060301 77
    0x254001008000400c01c100e540141c2c40d41000e100391011100490042c0c820508014807498442e98a10503882c02980070729109134120200c04590300d00620301140030701176032144100107180ca1f0400125418085068441d40324034001003840c1516010030407610f18900301c0e040d41c101404115002c4528058442c1c0064100150008a542c2c40c08140f0070b42081d0195a41d64041c5008204021800b403648046031200c81003421b1002c0b8461090020030412201c8020007440c1c81d00e0b103000d02051540040c3d000c410311008907100803080c0d0710848408694010150184c2e0964408600d94000051070340118840c01004cd09400703025a0b1130711024a00b00d980002585d140b4006100101180e03c00d001d030560040e803c1c00c000e03006502d003000c081000100300b8041c1c15401c0e40c07100440c0081d650002d00e5810040700710122900d9060a483c401c0090040348401c40b25100d4030106c0541d154011049065080c9c02d02c0704042c1040d01d8240407100380da10040a480d002484401e8a03001e40c1d036584e014502800713 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222422158 1250 222420908 222420929
    0xd0f2d02070807050d03090b03070203040b030c041e06080a0b0111030d020309010507031806020702011209140f01061508060a090608060406061a0f1309110c210316090f 74
    0x1031602c50320078200300b42600200e0260800c0703070200c80404d41180b40070302111300e43c01d0620342d6603440c032001720308501440e042a1200d0b0000414030203a1041600074000b03540c1e000810b4036160b141810304045015052065402140c0c0000009200c40b54070f034010381a401042c1004d0220300030711380f902c50442d03020400c1000c00660210600c4a211380c244140c980c00050344c2400c1090b110640e40d240c14501400c2c10040480380c00203050821640700300034107100400e42250a1089244c1c0b403a103d00c44410a2550141a22884100380e001c0c100c140140c408640a40007a03044107065802c0c01c0300c011a0050808d90040421740000420741a588036140040c00108060449800c00b8640001034414035401801000894503010b02d00840c060300700c42900e06170034249542c030b21880c14407160820996211850701403078854820009080031000b0486e07c10300c2c3d802e48000692130104218144024600304001141c01e0000076000526504200d401c0360079410030701c0000d540e40c5052101003041780c00000b52807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222423408 1250 222422158 222422173
    0x30216080d0905030a030507080a020102040e01091b0c030f180e0114030d09051503060f040e010c02010b04060e06092e03030905090f361b01020d0f2d02 67
    0x350b00000c0d2402a20048014143c06031442c2c500500c01d0143ca8006030000c00001806c00c1524000d60445008000031007600c41d0300c0da550746d5000002c100c4456251003000d858444141c21a114021020000b81d0680b5000c88a51040340e040f40d100071a154a601002508a004074002c40040c1c400c90003401c0401031488014490130600d4181070001c0d04a0040c03201d0400f05006607513810038820f01030100901c031180c80750f484c0000152aa00701e82c2c84550054a02094071912100c1908014100b02e955002804031680c46001c1c007085510520a034510164080c01080075032910411090300840b0090440c40c0302c6600c01e8180625101a48400c800d1014144080007010f80185064000303110465001c0a14a0b0034081e10386d0350f04004011034005840700f0700c13030305c003070440075164481c441041c83d41a010310380c0c17000c15a40d030b96080c803404100c3c00300b04041c0c0c21017035840096000c1c1620a80e40d100000c04544141c169220514140e42d012221244a4009120001c8104505401030243d004040c81d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222424658 1250 222423408 222423433
    0x140304080403020f0d0b0f07050412030806010201050c04210512030a060302011b0302030d200a030f06050f0a0e0915070c0c0608090703020d0c0302032a0f100c03021608 74
    0x1300003650141c40c80c6000040810050b2040f20f500c0314039040300e05103541c0d0701e8004442621071508561044140c10b5486400e0542c084051440b5210a800030020750b200c08428458a0195219500043d00c0b14900300d0110001c1d11b0303606451900c100c0c101c40b00081d12600001076074000711141032440380d482900304150b41c0d000248581070390f581c1d15030010121305510001d489118480c5061041b80d218541d1080507010f982d883d0032210005800c442d1200f81d441b030010041c000102100d00000d00b0480e001c04c50789400e5213840f604640c000c01c0b10f94030b14a02034082030004c400400101c0280581c0480c4c0d404101403a2070980b24041d02d0340c804141e00a140b07005000f4440310b8020b6020040d00b4070402c151100002006002e4070f4040302c464103121524980200e6213a025007009405000ea460000d00050480c0b10142e05119913400c040c04140500b1f040c000d03d0700c00101d8075a40b1031801d882410a00e40107801501e1810f009205407580d420380c1000800ca415803680c0300e40741e1030b400601030b4140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222425908 1250 222424658 222424669
    0x9062104120309030503010e0415020d0c08010902090d0210030212010906081b09130807080f0304150b010504030311100509030c24070503070908060127020901080f0714030408040302 80
    0x30440460034104608990f60301d00400d64001405801843d804003008602882a6102c030541000c1c00440103559800a44d21013a000c2c0044089a41c0422040d40c0007255415150080e2107040d0005400c080c51680c5940800c01c1152505000d5014941e00b0403665000c0e500041c0f219018000001c0e02044039460711403840c3c9403010f50450074200344140c0e195402c0559a00703038155009106400c1c60b4000b5446410660a68480c1d508004c000d4440007400b2504226550080e6200f00d001c1c007100d9a0040e4143d14503010b81c1c02400307140d40051800c210900009001c2c04907400e89214a4088030080510100140200c0c0c034247c402a4144d880462102c0d2120000c0040c03608010759915140101d0039031000f42054050007504017000d106c804800074154031301c81c284250080004c00100c0b103107941d441860036080003c0384170810102e121484942840754441c0200c524121042e510200259196200c1803443c0c02e000e4845000c110403251010740100c0520007a40c00b0368010144c1d5640c0701c0c41c2d03104200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222427158 1250 222425908 222425933
    0x6030f0c0d06091e2f0c0601090608071a040603050703020d0c09170a080403060f0e0d0c0b0106080702060604090602090a2d050d03050c120a08100e0108070b09062104 73
    0x25a9007011250b0243d1300380200490081000c2c45841240d180e01c1d400da850340c5d4012405c4400080c45042d00002d01c0c00c9140d0402c0b801c80d00e6107000d46201c00d45507401c0c4003a02c0d41030084c44480720743c100b10800c22140319901250f0301c0345041c0707030060030640c107400c2502c00d81d00c42250b0b60002031800d01c41840b204118035140c46e51140b480d80200000d2496989807003ca0080d4440074007c55a9a2240e110450998000c2e064850000042d034001401c22800500352007900300040d24a98850350001c200e4074002d4034014054100381e001080c0d942e9031041080040d04034040d0848a0b82e4080c84481f80d245c842c41c9150740640030811045080e00242c004200040320b5942200c03c54170b00f602c100300403a4403000a43e00741203416203052556103409007556854902c4d04500521b0030000019401000e070340c05003d0314010a201c111000459581d281c200140c0d26081c011000c05401500042010302100401030a1415029050360700b414202001c541544c6911002030f144424902c0410041000e1076143c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222428408 1250 222427158 222427211
    0x50a0b0a06030b180613020307020d0e06180d050703080f0405011209020108040b091603080d0b010306030b060402070c0f0603020703020d080f040f05010b090a020a0201180206030f0c0d0609 83
    0x800149a001000503070103000e07455030782d034030f444c0a502080242e1643d1010320040c20070150b0941d51790400042c0256990114803000d40028180025500e5500d4203e08441d0020300174a01c1100e2054444c040040f400100001103da61140c684000000340c040c60160a2011320602c440d0307182ea10744400504103040244046d840d0515180740c100c0140c1c5c02249190704181c105030002030a136101003507a03180042c110355015820908020001c204583e01b001882c401200382c80c02c0c0019040080154280d80e5103000041c00c07005a070b030002e4441e0405138058206103000d04044a81595582d140444d0f445480d04004002600000d2000502d601001805003844613423810203a5450125115603900781b024200800390f040d051045000e000e4250400d61540078002d000b6829400c00c61380400080d17000c051a4000b550824904030000004451400c1d40320ba0080c000a142d56100d482000c11900300600958450b0400d0290000000f141d101d004003800c200c28001400350748403900a82541c080710441c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222429658 1250 222428408 222428411
    0xb221a0d050601060e0d1a04060e03070c06030209030c090408090301061d0105101e0815010e01051c0603080d05041a070c030f0201110c16090c021b010c06050a0b0a0603 74
    0x2800c001070400a1403d0440301e0518120585400d0180090300c05c0380c290740090a010301a115100940340082c090fa40180c0c80340d0000c00941a0701da118940300e00036a000a0100c0381905001c0003400c0c000d0f0018441c0c0314000b425241204520000182040405d407401d4580110200c1c000805040c01d02c6034201900d81402400110300034440070b101380b807005006483c02541c1826504106600540c1801089021064030126990007800c00030640c400444e0408c00700c0c90b8510391041107500400e540324a00c0410703582c0d140382c0790341032603800c0d4113500d800e200c824070b41d40c6c0f04030000c007091032f42002c0c04200c0c004e03040c0030940e410103003407039500c4400a80001a200c5d12403403e00000d180c00c81da1410140e1b40c181042074845908003420b9006054008500720103a1001031030080c0c0c1100032490450b40141c1b0021000850389076040e40040b00d2500c964000540d002c12207203510300c080400400454001450501c059a016079107050a4540680c2c56041540d2502d280441078900001081c000d4800c5240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222430908 1250 222429658 222429679
    0x919030b090a02030a1e0c180c1125260c03060c03012607151e0c0b041412091c0203120c0307080703020309011b020607060b221a 57
    0x190300c0f08045c0000074449000765201c0b9021840e54049206207640105048120070b9450740e103504c0c90140511849010340c0f400e400096940c6c003030404090148220802860304a00c1c0458444045004045801c0070008a410004400c1e40400344142c002081d41000882d100100088038900075407410024882d0b000f4104000c0c14050319015241110130b200020300c441f400e207141110812054650300b0046015490012910110740803403644170740416980d13045041418a020302e0800080e0500c0b0000034034030500c686c04102c0d07044110b5002801034104204100280c0c201b035240c012900454010404007083c060802d20b460542030b5424410041c48480b01e00c05d0b5030000342c4884100340c02100ca10b07004a41a044010204250341000d0390040c9000da89007070a080185d03603a0804c41045001234240c4201c8032005103c00318401c0d1030381e409410309082ca82c1c01d6503084050b0007110030039600412860081074400761042c005070f134010100303040000c0c0d09042c10325009503500855010b030300034031700f001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222432158 1250 222430908 222430913
    0x30c1a030103081c0f09121202030105090115110304060804060f0b0108071b020909100c020703111309062301090b010509040b0303040b0d021312050a0f02060919030b090a 75
    0x4031640f01107140700760f010b00c00038008004d0051510704140d80215140540d9642006000c151624048000f03071199200328480c1c44000c41079110900405801041807401003107c00e051f15078400c052911814116074105c8000c06c83c901d03581040d8002300c00548100184414040f05101300d40741019015014807400e5000c1001800d402800303003030f0700c0400c120000d50950098003001f11441240e030040c580c40e11030a1540300c03944d0f00c003010130303800f0850307441d107440906001e0000480000300c907030000f1a0402072000300d00300015a402103100d15011600c1d0703680c030000240684541a24003203110120400014403a0b4500b1503e00d0581080385240e1900b40a85026030b08602500c3c00003108442c00304a41c003200d800b0900314092036000c0c1d00c901c0e5000c0b40e103503d0109a50003512224540c500b40004c401d0f51402d04032409402403001400b42c0c2c000344400300c04900c00740c1c1010b000311300282400b81340c151b030714000c208030900c4103840d1000415102c07014000c10510181c0a500440c000c4000c10301c0750210f4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222433408 1250 222432158 222432173
    0x10e030324060906070f02120109050307110901080601091e180b070503150f04110703020d020607050703050f220807050306060406080705101b141501061b0c050604030c1a030103 78
    0x51170b003d010045040718000c110341d0341441c4541d00c02003040c024800203401d0b04e40255a6008440304a0340f007d800e0401030420f0400c2c541050480380c140000703007400d03460709140c503000340307032088015030036003401c0e2403140d004d00d014058281014101d210311a1001014240100a01c10161100f02009010800c3c4444400420302000003840111032003000c0012036000100180786280300290041404038203081410340200d4800304079000c079000e446d2180d030b030711100300d561b40725008006020810600260780c00b0206540513101114081c1c41001802040a41e11413100c161640100025804500140a5402d061010702d40000c01a10244146403d0042043d00d50700306009550058030142d0065035880d01c1401c0859628804500c800c2b0762181500740500070b45c0243c05418602e11a10f10025840b140203d1094101d03a09555a0128242003803c00c900314003494400355030392490103c0c0800d041d62101c0003040114801e400c40d074601c500c2c1440c0101040b588802001540405000400118400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222434658 1250 222433408 222433417
    0x6080421120f0f050a060f06050f0313051908130603050c16021c0c211101140d060e07090b04080709020901140a02151501090b070203010e030324060906 67
    0x8074a000c0b481400050005000700382d000110103902d410074052008080c1c5c5503012000341c8407850740300010a134031340c142500c0500c101c400c1d080601740704000040c1c2d141c2d50080e9401c0b00b02c1c4100d007500c01010304201511903c5050720b03804c1d588a500000c0e0755000c640380b16400710042c40b090905000b1440c00c1074440d0360138024180c41806903649103c40c041155204051410f49191072034181d0380300303410340c00d10100424040c022224900b03074403000b003800c81d500540a041d6280e401210722180707500900045aa00714080880c445005081c000c03540023200c903000d1000030344020f1041144503e880c50005103204080e91001c01d0094081006114907800403d01c071050b01c003000c0c00982e03a4681b500040311040c0f102d1584640c003140100d00c408003075901151600d0b4169110541052544407080201d08030400e03110141d0201c0c090640400c142207200c00500703402070000300005882031015030090f06641c42204e40101000d030350300e60383c00154003840c00c81d80c0440080c0c4209040c508440041800d9124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222435908 1250 222434658 222434687
    0x250c0f020904050f030a091d04021c03030b030a03020c03011d0a110f0a0608160809100504050307080a082d060108040507030c08070f0e06280302090106080421 70
    0x80c03141c000380c18410f08012601d10f42c218481101d545070f407031000041603805c05029a10001c0300c0e040081402d98000c080b0240a142c00418a100c08110741c0e40c01414042e1601d0100d003499280c0301c0246d0b5940d02400100c04040c06034002d080c9a488190070142180d52800e100c140c00300c000303031303008494920020340302080e41c0d8400280c85002e900900054413502d0540c03800c0e82c0c010b00d03843d008240283e01041c4507005a0080007003400914080342c054440050858040d105940b224000c0c0320003203e0781c2c000f10342040c05001540d01d0320300561101c00040e0300c04501b103000300b4000c006002002501c114034050717008406200a041244640d48030300050b002a08503810801c400010030140042800250700039a441007081c880a940c0740301c11900ca070190300c40c1c2da41d4070207040000905542801908c52242ca40104003181c10f400341162107011711140c030403095413501448000710041c2c03140c041050103004280c541088034505031509a9004170b002c04003801c040c828800340001290018080c040005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222437158 1250 222435908 222435919
    0x90c0703020c1003140106110c090c090103020703180e0708012709020102100603050105090c0f03030a03020304080d0606050d180c06200709050702070f0308040315020c06250c0f02 79
    0xc0f00d82000c6016002d80c50010380c0444001000180d000d8003c20f030b40003400d0410040d64801300100f0100030113040b048590020003802044041140d610a9008054580c82418002081e449001c04548807000c9900301d284811240020b003c40c080e006029140140040030566082c041c500d480c409140d01c0c2541c00039149511360404108581c024448003045100602c01040345076a6401c0280c06454160751046c020301400008442c0c82c103280c400003d0001c0058019440c0c1b80d4150002c40c0250700044c0261480380051014580c810070600541c802056140c0d0b50703680710210180034038112480002900000300452014100040c600200031044651a0816821300d84070300d080404a030700300e06502501c600440c0c0c004508042c01c1c1c0d01482c06000b0f02c1c3d00b15001d8545850120500030114040504600814802000000c0c1c0026090b03812850b4200d0150030805140c04092030100c00756001e40c8075525581c00c40401b080800441d140d03070540303454042c2c01e40a558450204021840001030301a6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222438408 1250 222437158 222437179
    0x30606290706020d061509090c050f04030b060a03050a0c060212040e0f07052a06010b040605040b07230d17060a030f05071e030510020405130c020705090703020702090c0703020c 78
    0xe6005901c0000141071b4140300d610714030018500100003c4183c050f00e0003243c90140384100181c4210306a920001c1303400c103240d250904540320400c03601d41c014026a8042c3c1d0701000840013600030300031800e44c18401d050450845003090760190902c072481c10000c1907460103010800000d0030903841690480f505440c0c01210352914070080711184580481c0d099000a400e0781c8200781b042294003043c070040010f050b11304598841c0010004c510440c4034000002e24284014045510ba0300010980035104a40e0b001040c66003804c4141169928007407684213070031168a2042c1c071030300407182c0d407030114003d0240641c61800034001002c1880170700001d807035503081d080d201c030400a08000580280503aa801c442000d00410031100707110085000803a854010616002d02035070583c002e6405441c0e000300b50489502c05035440070010f200f0410b035081107204030304000485403102074040e40145d00c1c036a40540da0303810a005000002c440a0b0800d014044100030780c001003540416048078444040301c000404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222439658 1250 222438408 222438427
    0x91f05070c1e060b060c060403110a0c351f090204020f1e0a021228090504060b03090309040203180706020c330307030f0603060629070602 61
    0x8011180c8000c1004403070b40d081c01501903101503070002c220710420082c0059001d820620000d0b004040102c19103074044804240060b0185851030b500900394001c959030360f8900d0315180e2009529922000b455214031000c1c44081140300b8080e8858007580c40d03840040f901c810030303882d075440c49400004100c804141c0c03010710403a22a04401070054008005540b07075000910009810791022988890300c400707652a100c4003a218400303503401440244c001e050b030307102c1c1941495400c1c4e102e04161380c0b00e80c020032400069059014820004402180c1d0b03844040c60400b01880210b0b802c94120141c118420b00030030005100000c01c0780e458200c2500c1c0981c9035241c00861040017183c4d010140d009004615000c1042c0d03900142003100c1d040c0803911420008601c1a04002800201405080c0f035480040c282400c24141e000442d0005443e1400142004c0301c001004101da04d11b8008031411901c030b003400c1168441c07e021030301c2c5c404149000c28081141d46007654015200310b11004280f10340100d10101c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222440908 1250 222439658 222439667
    0x1d1c030b030304080312010f080606040b0d060905060108063102010c0f06050f0606030103030e040b010516050f1b011b060b040f020702040e0304051003050a150308070b091f0507 78
    0x914040074046944403601c0c2c40b0090744036000316007141a051981e000002d4809405100102100c50703c00107005180c8680003440068000c09070b0f1076070404141140f80001501902c40d1400c0030b4002c0028148035410600703014105070010313081c0c00440e040100d0189140640002403020300c0c0704009000500862440141c0b40b5500208001d40016150b080c0303801801110b4100a2040d241d080360f4420941d142000c00056002c20f00016000952192198009040540c4130318044281410000d0400450090074218002121011250b91b04403115601d40804200180710440030110f110006600075640000d0910140f5600b64865007005d058110600043e54070110722204040c3c070500030f00e490020520065030007103001305d0041d03181c04902611490003006a034203403480140400c1c03200c40c183c82d0460181101504ca007603413a5a8a040350000c4a804e94110020b52084c480d658981c602c0b0300340030f00b070781600902400c219000038400600c2e4101c2200d40d910300215281d000101c603210400203e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222442158 1250 222440908 222440921
    0x510050a08090c090910201c091b0303110f061303030e10050726060f06040509040f020307081c080421120b040b090c0705031c0f1d1c03 60
    0x250000210340c14402c6a07080403400800840440e0b2003801301c610001503c40e80c0318001010f040300000c0a0088610794200c0442c00c0100600c1e40c923001c152442c1a8450344031b1015891400150711202c22010010160848400140000d004002e4a078081801c5600d94891000030f200b103842d0005a6403503010580240d00946540218808481244520b000c1d0300c1c0040500383d98000104583c0340f00360040f9240038810a040d00c42486012000d0f481d24400e200041454000a940c4080c0501c000b09007034075142e4503544103034000c450030f060b81405801813604010040e046032000390490080018440705807a10b11003442098540720728030742c1d20b5080901c085a03955100a04d080d400c0d891003001c40703a219240045031481010308120300c0403107804110480e105400c00321781000c0204001489000b82601070700310300c2d0190040d0707440c22418414212500b00c0c42d0540c1851555a00f1180d03401c041e071445105500c410445c280c0d40040d0102d41c000ea074a5622103490032000f6840c0c10346804081c881d4200302c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222443408 1250 222442158 222442183
    0xe070e07020312150108090f0c01110c0d0b011409040305040b0f0d0c20010204050109140d0c09091b051e041503050109060b0109030201051b0a0c08030901090510050a0809 75
    0x801e404c0104026a40204508245001036a8040030584100300440c010021b40390080091002e110308000540f41981501c1d0b200085000b0a030800896865089054000511a607040e80d440d41c100820041c12041201c40c841c040d8010030100030000360032500300c4090301e00101040d52164210f2802d204103215402d0040241810624100351441d08050080c410a501582c22040d0700c0384001c0c018200d015901c540f80c00074007051400c10654a20001400603c1005002034114580c03035260751410394001d0340050301182c1d0b0f8030b40d030701c042c80700c220a00400140000032803001246850002030790f0b9080032181c2040c181590b4085036142d6520313400070410f0541c100130000a65a00d0070018020a003024061321401c0c01c02c030700040d00758400c80340e400035031b94140c5030b040c242108128186040c0314a4100c61040d0b21a10000c2004101c04145c0c10000b044142e00840d074400f0404001403062250754030080c01064001070f2101d0042e00101508d2040203140f600c81c01b1a0344500c40e091901c00710007480c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222444658 1250 222443408 222443437
    0x206070602031503010b0a120c0e010803031506030412120e060702030c0f0604030f050705010b0310060303120908041202010203070609030306031406010b0301090e0115090219030e070e070203 84
    0xa59003002140d401a600c101030440045014807440700c141070a80e180b8040096001e0b07420f1006108820076000c100d45c40d24040c20820910300e4450189602130442a0080e8526600c0130080048452004442000e02081aa203503800d50800360b90f0748440c000002c20420a02c042402182c0ca01070032030b88070103801c0c0c2c01c0c5411a0502d0031f050f40c0280d00e0750322088034403020380500742c0701c481034040010308070740155859a950342110380d000b001100d0940001c0000c8403d9500d400e410f414540d8200030300a016141500000307034091840c0b034080d2140800c2041e5400050030880310401061090007500c2c12100315402c05540c0c000729100407070951181c0480102007038607203c80d800c141a41a440001560300c10000003126030904904107030703903100901c104100054104018440f05a03d50813040d4001c8403240003040f40b94074000c034900d0803449600300e8040301c0d0b80802e152001c05442a01240040c05a00f000c015040d1440d00c3ea0380c41c1c9206d40104501c0d1111603010600e1548200229010311000d50b18 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222445908 1250 222444658 222444667
    0x3070f0e070c030c0c033c020603060112090c091a102102120406050903040b07060c0e090f040b1305101a0a15080a020333030a05070503011802090c0706090206 70
    0xe024214050411810003029140f0007a60460f5061040348240c0e180f81f032850480a6074290308020155200803c0340d810444018070041000509000c0d004503076102c4c92003224010304058025080390402c4000c0c238202241445800c1840d114514441a071240500e0312108000c1900c0f6000040350f140030300404200d2000800501d000180d42429020ba40b0400c818061a03c4514105940c0c1c0564010401350b6002088194001851503200c118081c0d170318107000d039841311600c0015945a00c01c6514810b05400101000200f0a9440130103612141c00310302e1495014013a01d5850342e841052106a81540e41d40040c14414018201409190180101800e800c0303900c84610340624264807503002c3c08188880081032605c0407078004d8a10418600254185d800340520b0900240c0403022000d1000d515000f401c41c020381c800b030180102003801b8800804810b840c0c54103142c211944020b03480340c134034168040d00e001039540c0d40380c65400812407000e40b626104207042c000000d00b00010000d611030000038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222447158 1250 222445908 222445913
    0x17060d02190816060c03021509070e010b09100915030e01140106090801110702011b020d060509010606140a0c03120f140613050f2d1503070f0e070c030c0c03 69
    0x50300c0e281c3d20180755500c4403a80e541c5506403140f503541140200960001210401804044800c40342c4c40b010300701c100e030700700e5031b403860300058545003070704281ca000800003030b241c0c0c242c20070009030000c403003261030801801841d24078070030119280c0e404c045082588602501c21011000d4000d8400c101201404025a5030749100160144103644202d024950805225403e00c0d020b00d0151008950103031101585918100d41c5109142c8641130220f0740089904250800300381030f4811580304100b04030001807404e05020010b406801c9000b861400780c1401c1104615281c2d00c082d06041107681404c000111051200702d120140c074090601000c1c041c94100c0960f40d40f404400c21724000c40084c3e40000c204c00c000c085c0c0c507003030b1841165490300e004403000204020a00b003c0d000c03241030781941d01c601d9000064401c0100303005030945044110701401501c820f0a0300d0140a000018502d038009003000d1342c948500c000d1140b400924800902404c11a076800381805103084000d400d601a80ea141410b4813071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222448408 1250 222447158 222447163
    0x40b0907110609060606090d0305070515060a0e0c07030320030403090e0708090c09090a0204090605040b311e05011e1e020304020f0a0602070303030c17060d021908 72
    0xa0799800c809109641c0841c290500110303806001d00380290446241c40f090600703005c0a8000d00c04114104201040307031002103a001e22950961442c20011030303015007040f10822010468a030400201d00c40c03014180710305420100203c51403039915060201d0350003c40c021000c4c2c0502c0d0089204500c10000082004250344520f0700300580d4100941800c00e611100802c4558000440b0300b850150f01418081c0399500c0d020700c1e03c5600614110803500803c05682c003103802d640100104441503600d0303c0c00d1004100d42006020791203084840c036208869202c0c007114070002c40c050a48440b0004d44903600052141c0320340000c0e0443c00c0400120b681800d80d1a04900804030903100d4510760144805402c942c00a40c0104007405400200c654581140141c61000940c000b60040341c0c020031040800f9105e440344403806c401854079401802616185040180580c1e80d01d907501c904101180320f85c1c0c524150104500394021a00b500c180d81701e2051071020600c0da580c040101a52547d14510008065000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222449658 1250 222448408 222448427
    0x105130605030a0b0a14090d030f0609020708070b060d02060d0207020f060f03070801050a120303020c0705031c1d060403060b01140d06061205010e06060d020403060527070b18040b0907 81
    0x3841042110b4510102803c1b4000010341e4550b1540d0482c0b030070700b10980d1003500618000b420040b40040d20540e550406c0e401c80c0d010020480382440045056000d000740114070651005042c2c84d280c0501e40c0a03030006000340308088510720102d50106a1070155200e5440517641050b01a0555680306000c1c00d030310500750004c641c25800548070400100705424080c1d00031040310419001030000000c81c0d503060380079401c00e44208010340310ba00d4000810ba6402c20080001e101940c00809032038a0898004001103400714000f0941e03003d0080c6140d00d51943c03012907089030b03000080001c000503135100482d2002d248801003004514045055010781c040360b80464100e940d41d031224455024020400700c2030300d000348211512088210001021414400010408200b00c5800103103007584075903644040700d0064608081c0301101c4c103110500d00c0302120f200c01010b00d84c00c0c003c00c1c10741d1400c8002e01c502d10800036203ca8404804401c00c02c15200c0340c00c61200400d005100030b5840c6003000000300398041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222450908 1250 222449658 222449671
    0xc0c040609140907081f0b0d0605092b050901021e0102041502190201110307050a08090f240d0b06030f09060705070c0605090a0b031602010c11060105130605030a0b 72
    0x3403900841e5880b040007448078101c07170164014003000e0340740300c0d030845041d0140f8000211554440d5201d80e481d65603150140c5015218820005550900c2c2042600d401c01e0b80c1440b800303c500340a0310044c03071301c0344000e000403000980c9803141da02c0344200c0c0101d0804078800702d0400e205d0302e901c00c003d02090040d000b42c000d4407040c3e81f0b484400600100100d0f03075200000019030403006510500405540701d84682141c0007100802c803441c0804a40c1e8032482c10b1031035407003542c0700400418600320a26080d98007206012080b5492845050740c0700655094165041a032034454900003040c000d400c03099042241c40a6004110545925180b20031030043c3c4021034504c1e9640c040d81c40001d006a001c2c0d0151034441d900480303074801e82d80c00c0000603520780e80016441580b0030149200010704400e03001c001c501c95021000c11003202c0d841c0b0300000e42910b0001400c0340502c040208032401a8000007801411208221110200c3e4501d00c00c01e000285195000320790940078144020042c451400d410f54020760 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222452158 1250 222450908 222450941
    0x711030c040c0504031e050a0f030201060e0601021005090c030d0507060501050603100b0d1803030e0c0a1a090d0218010e060d0305071101031b0e0108010803130303050c0c040609 78
    0x35004401c2000320390541d80c81d0300102d40240310074404520700c56100c0f0002c004100c1403e1840303030b042d02e0745407500c1b541d20000c840819045015101b05982170084030001c100007204030141d420400001b075112035800141c070b403002e6501e000251059008102c0588840030240c01e48060084151006046901018041d00ea060a2000010f40390400d002103900c50031102c0703c040442418060521159880040c1d180c1c603094641208802c9070505055000440380f013502c0020300110a948054201900c55107440d100d0000d278a01003103e89555202e41d144800b40c546601e5507007400c0340005020245d15680650081c0b140000010b0440c0ca521606045e02c1c0000100c4040c1e0b6601c40c10480e803d07528078402400140d0612440c40000c00101142d00c03e46814100415010000300c0510034101c80d6900e42c0c0006a95412444191758000328403078054020b0f640030750b182001c0c030010b5400c684468800101040000500710140940601c007010318150005c10070302040340d030f610180d000790015190301c0e0180b9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222453408 1250 222452158 222452173
    0x418060f03020105071e0b1006020f01051017070902040308040e090d020c0f010309051506120105060a1e0e010803040f0603020901170c07020405040602030907081204030f1106071103 80
    0x303500518040c000c80e5416528180b40034107542d51040c2d0716100c000c0c52140c503940c0c403900c04000780c1c030501021700c50400714541122451810f50001e1030b061006464844a924180621041100c50f03041d02d404e40707281c25000c1c2800e00c05041c02600c0c156003640300094941c40414080108111030004004940c07003440210341c2500c50204c4251501500d18003000036a001c3d511010040c10b0202091122250504001802000c99100d803400d280c3c020441e40c00106d04201008014508402c0d80c0d201d6001c07010080240b880c102001c5035001070349000d02c0c1c0440d421000300d807407030380540c284420103031405103801c0785d06507903940d292a07403a0064051070401210300740300401e40034420310a03141c407010141e5a070118030700000c48850b11201d024100b2030160400308041c0e40542c507680074450040344a00d20069807450484002410482c070743d04500d04980115013a1602e10083c0b00642d070503a6040702c109520407104e45025080c159604088a4200c03d01140150901001c1440c8012004082c1c0079070300407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222454658 1250 222453408 222453419
    0x90f0b060303030112031b060c020601060f1704080322060c0f1d040b031023060a05060406140d0627021e0c0321090d0903110d050c06041806 62
    0xd0380824080c65440060511924001c680300c0c241509003007100440074821011f00c1d4070340d901034400019244000d03a0103840104007103a404002440e2516462905400c5d620720000b81c1d01d40a980608094190b42c2c01001007504c7e8020440644459490003003401401c4d0807514141010f4102081070a021982141685013041c2c010103054840d00c07808043d0080b9198181c04210082038601a0b654051058001e5000e0642d0030388518402c0201c8811a680381941c026241c20900d00010801e5004110f403c004020b99201d4605a03405d03a0f409061a9804003038410342012107005400c034000c103541c1031020004401c80d195050f4028041144000f808100c2002c0c801e500781d02c00d0800031000045d11607031441404900340040d02d82540f0050640717260100910313885044051008111003c004803409000c00c0390400c00404450514508202c610580745844a512240070614850b02444024081008010080c844040504001080c1c1a01c030360f200e40000d08120bc4180042035660300d00f4602107030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222455908 1250 222454658 222454663
    0x10e040803060d110a0906140303090d08070f08070f02011d0a06050f040312030204081501060c1403090d030f020d020622050313080a211706010203040306090f0b0603 73
    0x208503000a0501e140d034442e070302032060002d480001910501c803042e041c0744013591400c13298002481161004941d01303080860741200c2d180745a030f80c10b01c41d0b8002c00c60004281c441500c0541c16980001c1c0151300e5440354148100510308031b41e00101010400200d2000b0841c901c0c403d086418000c0c0c0e40e1510b50542200315003160390800500d203500c00e407035070700400165104030020004507503030715901da08103541c1c0e56035400400707030400302440843e40200b8240020081004105030301e8000c1d40b41104e03154501380014200c0590b0b20009010606140220504180b013001200c000700310140a5200c50001402c008201000b0000400d005004105005010798030002d0f01d00e024400c90180c0800041d040c07c00b040c03e9101d03020048130680418041004c1e070201d41010140200356000282c0100100c51800c070602c80c036900502c01e0070701c2403140700d00c1d80a40d20010000d8a550303101c101d182ca036195080141c1ca180255070000b0512402c000004003000700940424509500c1100103000d00d071244002c064 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222457158 1250 222455908 222455911
    0xc0703051515030604080901030b0d110102060601021209060d0204080a12090b04030c0b1b1f050703060806070c03022113080c0d12030902101706040225022115010e 72
    0x76403640c0301380041004951000014160148141070000381441c5d1100030a2003d585828281d8907920b4512140000b941c05224460b4000310920161070310898038403146895000c0d03211400c1c060040803428a110100c41e504031009007030a40708a82000c811890550704070180d1244100c002907010354001602c038903900580e401d496110b400100c5c81c07808d041000c502608010380c2c02018007940302a4a030120030510121103100d45a81300e204200c50251034480030b07100d028206000300f62805204000e02c402c04522180c220340b503840c20132100034990404030315043d00c40c002d40102d2852890700c08901030f10720f4010501c0003982d044000000ea0764540c42ca07120703a100001ea40c1c102e0201c0c5800f10010302034210501c828503160038006200302c40c0e900411b040496a980074000300343c0c40d61206c510010b507800079680c0600e00f21801d61904500400c907100002c0200c0015000ea204042d440d411913035151015140c2052030b11004c82c00626807685241d542e0b402c8050030420540b10030000c40d0f03080728000350f079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222458408 1250 222457158 222457201
    0x31103030d0e0105072c060304060605040603030914062107270302041d0304030b0406060306020f091c0305041a04180b10170c160b1f0e040f060507050c07030515 71
    0x12041b00421b2000c0c00315540c0000c00807070781140d58000100e030983d564401c1501540c040d80e103c124a90625503071160545400007003134031035402400241165035051407294030003000c0d1802d80c0250380f5405000d03110000c2c101c17540400300c40910304003108a043ca20b03d07501224000c607807d04c1120090150b0b0544070604041e1084c0603001004180013184610700000d4009101c1c0b0303000210907650b51190301c02ca070001c0d8080044280c0c0003c43c40028901484150a041c48202034007030004080c0d50003070f2181c072039441404800343c6040c425211031004403007a1801800d1011040340000b072050408001460307030f2030030503215000091226071fa580c4204d8140c5481d84005140a9150b200c802e00b4086680044030302c2e41803441d200c0a1240000c45030940300d8004c0c2030029803840451502e400490b101e19182d000100c0003410b0801b004041901100c2400a054108500040a4848100840e0a842206046c0741d043c401c0240000c10010005400b00040404440004054540c0002110650344481d2030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222459658 1250 222458408 222458477
    0x6030213060c030c05060702100f0e0601030204050618010803040e070f08072d0903060b0d0317040f0807150501050f1305090c0406030b01080f0604020a031103030d0e010507 76
    0x284a201c0c01002c410811074000c3c01c04100302801551940d1406a0484204006030008016201d9040341802400403032048650144820014280d2403656010148070107881551124081945602d07910b8230564418809040d00300c1a60311120721545c3d990140c0f107081c00310050103000030342d01382c803e4081c400c3c48000c65940300c000e43c0700c2a804550a2404110405807940150124a000c00b0718429180c105c0c42c00340c6030042e1003803950a258089a100d0801c040c0521054000300c00002e61042c10f0035402640c45210109545030f509050403000402040285050310006008050111a000320f0000e03103019402403040d680c03118240445090054103440d0481c9110305401c016403001c0d000b042d070024040c41254103509000740040c00b0b845207030f070064a410050701d00501c000300091082040682c9040024034403410503501241c60361446101c00740c0b140510001c041100d0b5014000c481c80da0706044818000303103a90702080c900911050700c01e000820255a00300320800a1152107080c02c0041651 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 222460908 1250 222459658 222459697
    0x2001080601080f0601090905070e1203032e0305151f03080d2301120309090501030b010513020c03191806020303070513030204090c05150909010501030902040219020115060302 77
    0x3c0103800000240c0352505000c1d907800049440040380c498248201c03000d644500c19031700c5000600c5490039a1480030340d0300e030b0410001c01994220300500010010410f802900c0d080d00301d41e01c2e80003000081e400042c0140a078031465440d4034410008180078442d41101c0004855402d4404c3c011500ca81c4070003040c500c02030000030910442540300d41c80c0c0782e41c50310704882040103400c8240c54800098000300c408000030700c01c5509250380460301c00040c1c20032a10400081d4116180c0e83c0103171205104071441480945c071020128116501640e10780b5030003004807602d0f07000c088209058075400220380c0d000907000180b10f0015070814103900c001c89600390007645c50744c0c4440400710fa07542e108a02017403411414203000001a22241705503c082406251200e40f51402c002c10070118880740040c3c0002082c0510901d0a155100400329044030400d00b030001c0c00c58814408107010b4000c0e132080e10b88001080f074121900c150103400260300e102d800c1207464842604c4102c190102e00072500c10000640302042e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 222462158 1250 222460908 222460921
    0x1206010501090b03041511031b030114060a14180f03150a0b21030a0e010c1205091314060306010801110304121112090108011a090f0a090207200108060108 68
    0x2008680050086d0380c5c4c0484010408180000d07980c12028010341000d0000801c8813034000d00b00442a1184621100d03459541350104000c0102004602c0501c80d0f0000100007180724084c6041243e07640d0841c90321610760b014000d039601c0b0442c088603045d0003091244504a12807502041031100c2c41d280000e0907100740c4402c40b03c80d004105c1c11240743e0b0041002071110b0b400003450341907481400c9441c0c004503030b1580a00d00c01801c0c071100c000309a043c06000c01d00300700081c240803640701c032100c1f192810b50b845014903000102c041400750020a9140d15000c10f40c0410800c006050b44646030235011981180d9807022540c0c200d030700301c0049220410003440818001401852015040140c514101030500002884581400031040e40f04080f00000111151a541c1000c2002e0040c0481d0040c0b50000a08100c5c04110b44138801070345105011110404440ba940d588480d000340c1400b140854545d204d9290081e480c1000c4c0182e080c1c0c00d10705101140156101d07180441c40340b001031f5200c0c4041d4403000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 222463408 1250 222462158 222462179
    0x3020d03120b0a0801021b060c030f09030904050a0906050907270905011805011505010c0b060d1211010b0402071110020c0603040b041101140901140405060c010506120601050109 78
    0x116120201e00d6203401c4028040e550b800d90401c00390803184001070390355080d10200000000b217149140416048030701000301203905101034950124a0420283c0156101c0c1b0308582103105210b0030301c5d4054540810301c40380800c5940144185449200100020b80307070160640d503a80d000d071141c0106140c607501400c4000c0b0800007288030b07201812901161182cce23182d07291420b642c40d200303e200c0b007030040c503c0340c5062003402d015100c030710481d40c0d014003503403814140020a014a06e5002408140344071011070910303200c0b40e2030b02d00320741d0300700190f02c110304810702000340050344e2021900e07400e60074480140420325140c03013146c19642e4803007103007007001c0e4407030041c011010b40c150300350415405011040f4006071038040040d84540e100740710226441c41c1600d482070400710081303159410010110000c4801c60706242c01c035181c1141c2401c041213a188042d44003102480b8035000300d03401000119010540c1401500054003689048417210080030450441d9a0350380ba0034442c060000301c0500b0b0030800351101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 222464658 1250 222463408 222463427
    0x1401050f0114071a0106050909072a060f270209091218180402280503100e01180b270d0e0f0301021e0a0207170601180603020d03 57
    0x10704081110310102490032040c3d4210000c00d440603101c10b601c0042c400c010001c00c3c1d02404035402c05034145030020b0301040c1c2240c0000e1a940c00d000c5000000110041d10210344010b0201601201e02d003070140d881c2c0310f0040d010510145030414107207038403c1d0305c0026811420328403001101805405003c180c08001e02c0100141220240f0300400119200c4894040300600308200c144c070b42d01821400b03440074042d1441100314100b2810344440148001a61903800d040d0744141500d0310078015016600341608be400c400d40c0803039414800c194403111008000e4000d900c80580d580c0080050080601c200b50305c0302e052100c02820380300f503580001e01201605403031105010301c1d00b40c04000050308401085ca8001e200040d0b00101341218012141458901c20b0383c6400401540254184001c14044804e41c04010415100fa00f5020070b48800103482001081c00504441c0107110500f01805243ca48511007802003910240e907050105004103410301a2000b103a9002e4078000d0080c9046c0c6088030812103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 222465908 1250 222464658 222464689
    0xc060703050c06090c150306010c0209060111010905070503010b0d0b0406050c0f0f1e0f0d02031807030311060901020a141e04080709050108010903050301151b0c18140105 75
    0x40a00c0108641c41082010fa4801c1c00d000004011020b5103004100680c0c5903c800d040c3c040b9010006c00544d80d0740700140000842d4141c6501900b51513800058400740c1080c44604910340c03030651203c0c2807190004500c0f040b92030580003008013611003000c1c8a40d080207200007400684126000c100050019844207602c0482030b9404e0313003131980c4180307034042c00e0348078810b06070028034041002800001c01a99400c0320006e0010711031f1902c4d14003220805203020b080c7c0c03140700069021000803000040311415100e6240010140c4206e29100c0ca005403841c440081d41e40709078400c0c100020244030051085425211150b00c0c0c0160812803d50700c810039a01100d150b81006100c5208030142004507409017010f00345440181c040b06060041d02411104142c0c810541d0340c0c148418140400c1e0010100c07819107601d09103009504800e96401d81e12006004100003240006003d600140035604c203580f01540c41c040d02da01140d02042c506582a07a100320060840710a015004100f90724204c010680002c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 222467158 1250 222465908 222465917
    0x6080309132703081f05010f0909050c0712030207051e2505010f030603020f010c0201050403050d030c08060303190809070b04080c0102010e0607080c1305090403030b090a0e0c060703 80
    0x2101c180740118002e01078008400c80841c60460b2400f056040001a98081080d10700c0c0c6030054048001c01ea10144140701e0a8140814685510300c0d01c0d02c00c51040000d0040d541080c001801e0020603650a90b1085100381e50050307024000320040c500c030f402180c0c03113a60000c000b450a02402c120060aa040c0f001464200d0300c2060841044000d4480b9805180400c0055041e141d03458080013412076440c010602c01010318009040c401680c0d0041640340441007031034030060742c040300e20040e2110701c2a074101038130f9403042d039030b8088070641c0c9a00442c01160081c3d50b0045543c52784418150350f8002c10700e00903104e003802c5401b04a40340c440e4001a40c008840c00884001d00e54600701c1101d548d0103500b00600359041508124070550702405080942d140403c0103050034581072500600381003010f807409500c1c10000902c1440030b00055541c2001c1c100c0104505010308252401500030840852503a00500d20740b8001403c0501d248a221021a4218050441d1407043c4007001000c6e400300c0320440511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 222468408 1250 222467158 222467171
    0x110a09090b1f0c110a0b1206030703020a0e100501050f0a03050c190e090106050a09060c02130629040b0d022a030408070b04050a09090f02041a0a08010608030913 71
    0x160465040d000b0020616142c98400000030b08011100e19000100e00780141d003a40c030104404d0030000200e0b2186000400081c1083d26600c3c0000c6c1060040e90010b0350204019102040012a5200e00c6014034005054880580c3d5510010360703160080c03c45041204a0511103052034034041d4001550006c00e03030300201d20345441c0c0514a03844c50b82c182c4917240003c09101101c40e15040003295140980002d0a1103410035071040d00040400c40f050050100b001b000420501c03c54941248820902203425018001e46844003481446100d8286200026107550f44024a0880c1410201d405603929444030343e00d0401915800b20195000c150f40f11000d1000b800001c0180c10b54408443c030b1040c4031400745039198a07141e0001c2c6004c08075085000d501400300420481036803540c0c0d204088404259020a01402d9401d04400341c040e842806034105052290321039907010b0307460030013440c20811a00d82c0702083d180c9905c00e0884185010b41c2e00c440c0c1c02000b4668491610100780800e80380088400700341c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 222469658 1250 222468408 222468439
    0x403020106093602030c1e0a06030b010e0d020a09020a0507060e01020705120a0804030f120c2102070f0b06120f1c080709061206050904080409110a09090b 68
    0x2200c6003011140600311808503c080700c841005881804081c510160051124160300001c0d104c64003400c0603440751515544200103403401100803402d181c401081d100c295581c030038026002c0d1100d88401c03030006a800007111941d00e040703040315a0040d00500710320302c0c141c200a4080d000354041e02803401403184c2409090001042d60042c0c00212255400141e1540f015150503440d16a0320380306944c0889091201004541e0310444003680b00750940381c60f0000c0000c0c00015a40b480308a102e81c6500ca0a041a4100b481d0300441d820003132035102c0b405080400b8500141c3d204902401a0060000c65103a0f05140412031f0321b000140c01c02e030024450174006d150302c02060302d04101c401d41003880e5007110803056030103040314a440d00300050074248540c072403824603001000c65180d80184020301c04100207503d81d03a240756000c3c8001d00005050003005003041e0030078070070301c3d0098451211000e0405403000760b850044401e543c40048c7c951910500103050a03146c401504022060719084500703610007654 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 222470908 1250 222469658 222469661
    0xd1101020408071d0c160206090402070602030901140a0204140d0809090109060303080f040506060904050118080403120912030e011b0f02030c060901050d050901060314100516050d0203040302010609 87
    0x40043c00c04d4000d0094140c01680c4528800801d0340141480601c2501120784140044481c000d9044403525501e200c0751000030000e001700c9401424452000c0100007402005512030b9124143c44217100126980786201031050384664002d08140b0784110380141030f21b050410906144074401c0e21081c1c1000d00801c040341e5813040c241c3c0148100d40e200c9030200b081c59040091180c100d00b012410700d03001e01d041d4842907035621000d841680a42c1550b8001020310000394032000204e409400c2c00c81646020341008a07540d081808140c580c4040a060284480d000d0400c841c112841d0314105141850307680c4068510100d5a000301e8140003000085c1d03d40c02d0035940003c001144030310003403002d03039049005043c9007030f54119005025a8080114507044e81c0c0210594030401e120f103202044176612200c0440c00b406041d44028031040160060340ca251038041604000d410041501700b01c56591030603000342c4541b40b046001c010400800c585128140c15800859000340203000225040d41e8400c0c1220 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 222472158 1250 222470908 222470923
    0xb0604120c210f1b08030307050702010206090105220318180f0b09010504020c0a02030307050d020d03110301030209091c02010c03180b1303140c16050d03020d1101020408 75
    0x11801e60350300c80700b071241042203000450510148100c1680344002541c40042408040c80041e02d00c1c2c6000c48003a002915940d6040043e145490542e502c0f42040900946143c101c0c003400c9015014a100085460405114040c45665940c0c410300c41101080701581e12040f50b0350042d420440c0b04100c01485400b41c1004400402515000e90030309420060004100c40707a024a02480c581400c00c01000c0c5d41d900566507040d034404540c01030380d840721400078510704940e01034001e41501010ae1a4000d104022688071001c0b14bda03001d55211041521048044524000340d95119210520050000d4246003002661003030100046901500da4480c041c10024102e02d10000103039112081d400426601d80160409070340b294021102201503a661442c1068005141c0d42a040300501000c043c10b100350a9560781911146119a4542c62051b03542c0c1c80d42e99111030640000c03411200020030341444900b13403203044e400d54064281080140c1084a091007801100c42c610f640a10010031801310611900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 222473408 1250 222472158 222472163
    0xc06011716061701080109050601090509070806151816050a050d0e0a03022a04021e0a030b0301230f06030c03070902030103060c020f120c0327040b0f0a06030b060412 73
    0x40c0f072040c2e4001240c2001c8058110701d10603418910b00200280c400510309054500c0c045010036240c1d10303a201c3d20320348003c0f54085c2403a8810304041c030100b404161200d0a6420040e5140b4031010450414120103103416101240240c06424031000182e1103000541000d5440d03161582c60514904803440648113084800420364002028800415404110005a210085441d110040e85003100c120400851102c11802240c000034032807003841c04602c200000016120f1119280e600c0d24030003c0c000d1010004190007580382030409203081c5540d0310506607030302e4812010761041c7d640c00b4080340a03100281415406106078030700b081d4075650a000c1000a002001c1c00143c172580345043c40000d80e615900008155008070203204d910b8400442c13440115050b42d0031081d650144100c030145544120400c04d05c3c9000c0c000401c210b400450700400c1c10044e01104e090280c18414800c10050076160003120340e020000076000c00c2560700940080e0340030000244010f0402d5580d00807a04c0c3c1c0031100404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 222474658 1250 222473408 222473417
    0x1504020a031b020606030d0c0507080708070906060203091e0310050c070c0f1a0a120f0c08060405070905040c1209050a0c12080708090301021b0102130504020c0601171606 75
    0xd84440c03a07480324610b03440c01c101d200424450500d0b0300401d480344a81a44981081143c0300302006103c001c100700c01c01440c03845d041310342e0150703100203903915400030340a00d0074000d04014000444600c0001076403600e1000910450f510030070b124003c3d0101c0743c01182c0c19014007400100817001080c1d0b205240c0702d810404401c0340c2d0740c41d06240c14001d4640310380105080e149070220034090040389084400c99006541d88465603001c0c824030680b904440750003500c03070090829103103040204c581c1d000b04801219546a0980300d407504c0041009464040750814000b80c0000c404015624247d044880ea5445a0a141d109800340c10052010b582a1b4081990550312502c481c00410003250140c1d0010f02407402c40d079041504517900d2446e1440b038001c010340500000300d01c3c1051960294105c0b2420707001c51015a4a00303020300e0030380c3e020350000d900c21b20140022400000d2715080074022206408150805405540c0c2403030a09e40380710104003002e003494803901e942e149001002d040c54002801c800d84a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 222475908 1250 222474658 222474671
    0xa0f11040b0d0f030c02191503050a0e210c07120c0f08060c0a11061003150b061e0702120102130909030f08060111010903030e0601060e06040b031504020a03 69
    0x1400141d40010802a010301c80c00541c840101c1d030a020910031103945450f0121341c01c0e12034000911941a2a00b00182d010700000c4001ba680e07030116001c120780c10144d2000d01481d51000307100021210b400e800e59920b50005000e450101011680c01652080c80200c1c05007001c6034030014034a8070310550402440740301d00c10944002d200060500394024149080c0c41001281082251a00c44802070500d00c0e91510120310003018500440003002d1311326681044541d28038051100740c145128901c01524001064541c800319170080b030180800c101006411145810038405051105038100705100041000511480006030785803651040c5103a0402d001507202c00201c9010304e8030300b0b85544408441480c000854002903000b41c1001e0b41181302e400e003880349130b540c403006a50712400b040280c401c6500e41000b8400b0036406502050425242d601201c201d40c2e00c0c0c8000f5220006980940d540c8000203020401020300740d08001c540c0580c03491003030f11801c85100041070a03a00001e182c07001090301ca16 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 222477158 1250 222475908 222475943
    0x90914041218270b0907020706390209011a040e0a021e0705010606020d0c0605041104020f0408010b0303040f0e090c0a0b0901021921031506020105040b01080708030405120a0f 77
    0x2580c50340d51005c0b98120b069083c40400a503450585120745024400042841d01d1100c000031950801c405401500ca603040c000307401038942840e2100d008901c00c1c0150000800c0080d0801c01082c801e001c001d05040c5406c3c18042448410540140a500c0f6640c00708011900340c154840e91000c15600d400707135603441d00450300d4070600303660550f00803200710b500c840d00e20819541d2003e403040b0003a40110001a940c0c8590404140b51a41410515002400040c0c1c1030380031080e50000344121490400200040b00c01d520400d5100d02c550300c40d1814400d4480c0c0700b80304290302d0080d404c2d04800300e20300301d422083c0b04e4008115942629802180103410100e9a20901d5805021604800080500b10b0192406035581c14029018000c0808038041540310301d0010140031f5070000d15514070b01007013a044c00b03650790002406003900320303012182c0c0d40408000050401002075010b00f9140b0040182d8245420807043c05540361011181d902c0500c100907000010a407001d0942031142e000c0c2c0082c0488c404c644 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 222478408 1250 222477158 222477161
    0x10512190b180606030304050d1109040c1502060c0a110a05060702030301060807030c120c03090f050705040b06030c09220c080a11040501020c040c09031209091404121827 75
    0x40100300d25070f4101d0320401600e643c0120890b002d542040b140d03814407001c182007c43d52450110591a0800102c82c188014006000f1840d403c540c05034130b03c540010780f4000c0c12070311a001542c03040c4460906000c3ca551050060038085410480c11044440810031512000d19192080e03450700096000040103001c01980030b00360329404009800c1c184000303104c002006010210014500d6082692074103207480040c03003904007107415500100301c5a002c003218117089031504902c2c495070344620300e45080380a09080174410740c1e10480c11441c0003810b2548000c04e2000380244801e10f80c0100c00780e00303440101e1580318810010341c41d01c255100249480c1108112007220444184402c0508040c40100a00d03a4001400781100005990101c1d402005010075200e00711a03801c01801c510032500440001644011024100ca55540c0d051041346003803034201d6107400d0161000340c0800501d24000054034010400140820350120000301419503d07084101501000342505d20010000300d006404040907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 222479658 1250 222478408 222478441
    0x160e0a0b0405010b19110a03051908060904060b03070e0903120105030f1e01060f0608090d08010b0405060702150408070806010f0f05011d030303010609050117060603010512190b 78
    0x107840400095060201c42611030003113001240c41010070746200e2103410f11070b20340303054100003880458031048260b1030054425041525490356504046594103105441111864003072500a88011b40c280c0300c9441c0c51000d0200525041d4040c40341c64070020300b8000c9055a18451051000134645444121800b2000e8841c10fa10451003076001c1c084180c000c1c10042442401e60284070110302c1c1a280d04290710f1b024040c40d6100300790070340001c0c0000a86540150840c1d1050321040300381c6886032942c0358140d03107048081c042d01d4415a0140030512003410000010008980024101590314100280405a0f54406d4001003565040b0b450200310f0a5000c2100c140900820301c03100444178180340ca0070700c005400380314981c10007502c411751441da50480b0300d45080842000d000e0b69500d41e1240c101804c414084d1003031500040f211744c492903030b400c025520140240001083c8500d964a0201001203040240351038556038012100b41021741601d8004107440c0601c500a80011840d000381d2140c0c600f0704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 222480908 1250 222479658 222479681
    0x12070302120a11030a0b0a08060406021b0d020703060b030115080f0d11030306010c031e030c0e0105090d060c0e0402070b04170403050c060f120a0f0b0d0b010302040e160e0a 76
    0x3800c1c94083c01002840681c0c4d480401d40c140014400800300000301d1000c0c1ca0342c00805e550142a0600003440000c1d0010007401010900c803030080b610440101e44d0310800700d8400e10058210f4101800083d0190300540302100005001060700300c052602c40f8030039511540542d07142d5100e520081484002800051001c03001414501480309595185946912004060328108203901080504050050f00c501c0061004203d525141560405015008080890b286004101101c00c075242961107103048410072100544200328100840d41c4840c0900080e035500f00c140002104404031b10f4841344045e02d01035004460115031410035041000c110201e00d5801c2c003104c1d10801061000c80c1c40090320801a000a541c0e056882c208500c2c10192801036000021524446000b407002d40004d41d00020001d064000c810802c121101c0c0c100300c242c280ea540c0040c060300c0c086004202500d01741d844040768140300800d90742c14100c0d038040d41000707141907000202881098001d01c10b095120784201942c041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 222482014 1106 222480908 222480911
    0x80111040b090609030a050a08071a04151d010c020325020901180207080c1b040501060e060c030d11040303080a09030801150e09010b070314040b03041712070302120a 73
    0x40c2b04003c107480d030408802c12409184a03200076580182e0340a4202e01454000512070360192840d661018880c1200780110b0158940a004802400c002d95025540e01c51070741c03296080806000030090f114203401004140141c6034007070224152450a14400c0d0840002902c0001910512200a280d0800800d000902034400143c06400d0b2040a0441c06800c09840034041140c000344036003c0003070702004150f00c0a00303000008191250303510003a0303454649a0444101601d91040b42c0c018046d90010341001030503400b02000760810740303801040c8040ea10b143c034000e001c1401070286000c080c10f0001c180302903d004404d040b51441c0d0141c0240d03155a0b4a1608000c0d0340c001f107101343e0116540096146454071488115021f8400030300d1490f086854986500c0120204c0c1a87d40125a4080095480d084000101103210f40207640d8050707a5001401c08003411300d2005018005000e = true := by decide +kernel

theorem cover : BRFrame.Cov 222302158 222482014 := by
  have h0 := BRFrame.cov_init 222302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 222302158 ≤ n) (h2 : n < 222482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
