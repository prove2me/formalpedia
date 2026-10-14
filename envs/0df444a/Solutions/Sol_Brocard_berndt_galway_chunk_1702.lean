-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1702
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:21:52.338241+00:00
-- url     : https://prove2.me/submissions/c7a4ede9-24b3-48a6-a592-b065ccbb71dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305935251 ≤ n < 306115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305936501 1250 305935251 305935271
    0x2060f07050d1d030703210e0a020103050a0e010606120c02060907030807050f0f010b01031413060209030c0a03050c0108090a0b06040c0e030a03021e01020a1e05040302120309100905010210 83
    0x2100105148040f1064400058100c04040d80802c01c0f0315007441150351a01008030030102c604c1640c2e500c1d80250800d0b40100954000f641c0b00e81c002c640c00a05401c00080d180400c0200282035507050341240021580c0303003d9800500c0d41900c40d040c103607030891001e0b000c10b081846202d40c403003415110242ca00c1d08040b070b00800f40079043c882e898901281d20115105400c0b0010700314042d044006040f8042468410002d801150609042c0e100b00146c00b110019901c00703030764040094024a02142c2c04d0302c50320700c00b2905c0d516425000d4000e035015070006d02058122800040507a0001031003040190810b021000000307000785026908040c0840380070030200e450140841d4001c0f212400d55505210700000d000c1459008595440d404a0000082c90440500140c032400e134440c06880900040c3c5140c00c03001340c01d440b041321180d824894680701c0d14066603600023454030010441141d21940001800707840d507151081c03000403040214100075248600e0100080d4036040c01c222000a0161248901d407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305937751 1250 305936501 305936531
    0x130e070f080601050d02060909100f0b07080a030c020309040e1005130201020303070311070209010b03180c06070809031002030c0c0f060f041101090305161802030c19020a0b040f0302060f07050d 85
    0xa01150000f0300038420600d01200710b10030312b001c5441151a29290284081103119201088561a90700402130070300e040e0140c1802c600402c5107075070300011400140460b0005a4541c0908441d040d044001000e01c81c20445900c000c451000e040605684178415034203005076004420303245e0001e054200041d48079408074070800c8911030580020741c000c04500010401c101d010002d14060400c40441140303a1700040307540c0f03030740e07002d64804150302c00c03003c0c05404000340c0594010591400080c080e5007150a0b8000e4170340580e0803d440550030305030081052501e47d03008015410200c0c0c90751009200904142c019000c2c0204054000b400111000d0b80c0e81c10640d019106107401903038090200c440b10501d4440302e400d0a00c503405400c102c000c034100064000c6000d40242c0b4050340c0a1121180381415144000c66015840d9014400354004c2c4001c04010400e4881500d1089000e04182e03031743c861091038002d0604000400c0034261290104c03d01c0102580102940c0000b00c28490025003001048100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305939001 1250 305937751 305937757
    0x1110020f0d120f1505150c01060b120f041127090106060f050901091404150b090a08122d0c0c0f04090c030b060f0411090414040b190902130e070f080601050d0206 71
    0x20703402c0e40c20008005482b40f106801410485403120a501ea5520748080d54040742c001650040c000506910044025142c811806e50320020400440c2e42e000d5581407104d440c54508450998250359a80010401c41e90000c06030305102da058903285180c645030200103020b0819a000d10381c2151030f1188007070159203466210200d04185401c07e5000790f035840c0800d0045510401030b00e406907842d81c0001507004000124a06201035160616041120f40c0c0e03103080309192242c03084140719906202c00d0822003c09070080c20322240880250600c001c0b40b2041c442c03142d0900c6c1440d030285280c00380e4100444c0c0c170917002c40e082d25803000d0b1080d010b07212080010101c50744108020b50051400c0969a0a00390f080c009003440c0009450038800c44500f0903a08c0400e00003114003800c07031240140018440d01005c101c003818440f4801d00003480340403640101c0c550001c2c0b01208600c02d270791002c020b000074804100c3c8200805201d2541e14540342400e41064981d40c0c184541d502400851400108541d108026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305940251 1250 305939001 305939017
    0xc150302040b161b050306010b0a090f0f0302031c0f030c02390607080d020a14031602070f1208180904200d1110020f0d120f150515 58
    0x124580f200b5008021101e210454041101c2415240000400d2000700401d02000c455009014000b96032820b02080c40741ea205105850411500300c8010503001501c04010300541415031402e08a03500b50f106052034002d01c400e140c000d00c80346080400c1c8140d4000303000380031403241d481c000c40c08448441080e0714142418000c804c651039004540d4540c8090581032404032090903071004503140c07401382403000d03070704c41d00c4400b401d10103003084440c034070700c1054004003ea28110301d0100d0048450078140140ca400a481040d0303603014003441d2650a550411044000e800900c824601e06031a11005405041a080c8003c102e007102140b4007900c1c01004040740490700d03000d0070240040ca4985401035260707516107644000088121200c0320f079401d04140141d8883c3c1c0c0306a248003818044003c22810b00c0f00b88020700d0440c4a0480e180a00010501c41d2410080503511640602001d030313041d14098440382e8801e4000189403c00003181c64120380d51000c1100c40907141040c0d9900c0098a0500c00d1041c080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305941501 1250 305940251 305940269
    0x2190201110106150c0201020c0f03060c031b041502011b020c04110c0a052b1d0f040908210405030f0906040b1204030801120b0a0c0507050a0605010806010803070c15030204 76
    0x10320030004c150001c0d11030380e5541c401d07400d4680c170107010300c100081c85405840080e01580500001034600c81c4a0b002903810000400725050050ba400c40c03002d4041c5d000f40c00007021203118040080700c4980901869041e9002c1d948913200d95011680001c2d500e62180c0703015071240307880b04135a00901c1030300c004660844440d0740039103e503964181456503445805071402407003803012008444100c0b8002410003512001c030364500040585075461407101c4405643e42030f61041100481d0a99641e070b51040034080e6100710401034451801a034003d60b007410161980c00e45034800c008103c00100040200d441c5a62051038150311800008046074450207a0b0b00700c201407030303000a01501c90000c02140d0501c141d20a0782d600c0801da8a4900e00c15202400c1d1b2401481c0b41e000d0408900030b124150000c82420005103049030070581d1071386601d031070704e52050811360b0200d581d0380040c00020000c1c0f10960252000704004c6107000b80700d40c0d4241c204071461007000b403104541000810550701c6601100c0003001005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305942751 1250 305941501 305941529
    0x23060c01091b0b09180a021314030610350d030501030605090a02030307081602060d050910230601140f040311010f120504020a030605040302060621120d09020603040506090d02190201110106 83
    0x280c804880200d50321958402c2c407820300010080304c0c1d01001c2a04dd5549074807554007407521201c0404002c80d032041040e10080c001e003591000958200aa01c100b03248954020920f07501d98100038007110b04c054803c0d00e0300e400458003130002d80c034000121400c0691050050382e48038201d4010780300c046c8081400a40c4800002440c4241030b01c0780d0405405080090240d91041074180800e00440307510070760607800f00703000c10712400c1010200c00c41c541d80101c040c18954060034244150042c0c43e1b00a03c0516400c03180402c05105010094102c1d048103142801c00c20100c0e0707174000340502004020000201950707140c6c4002411500d07035011803401554410710501080c1054030b80030391159000c07070b8124000c05024004400e21078066903041c881116080140c01c00403d0203020008036030001009800144d201d00300c100068036043c000318801d9007c0e0300034280a04107105568104095090801d045600a2801104034042c9400c800110b60342400e024542280c9100800c0c05080c0c141e00c501075107120a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305944001 1250 305942751 305942759
    0x901051b1009120201050114152206090603051b03012c0f01171c0509040603080f0306010906110c0d050c040504060b0102070f23060c01091b0b09180a0213 68
    0x30103007072060b2283c0b0340c0090082c2da0f218694a50f550802c0c1505640c0401040c4c011407065070755a0080443c040d070b144160070041c029a8540c84100f0346a482030001807100c2104002d02075043c460640c20485907100c02d1b0540c040d90041200310302041c0500104620300c2e907810280c1c1039041003d0b483c0c03450705080c0700b016482d09a4001c05244400d101c1e288072a24078203400c008489000c00c140c088400b0110b0003492580070000102d0307175504202441500159540c00c04404034010801900c14181c0d450721565480c0340441c001005450254000d400740103d2021404402c2008540012059000d0750803420341101c0c1c1c03c20070714000140d0b107202d412030b1070601400180400d17600002400c02c4280c0031200300940d030700041c02103202c0b0b07442206440ea0042d0a10220000c4850406d51000c00c003c1205041801d0740e02c20134211407000000325025841101ca15600525a0f043e0400a0240e00d01c000d04207200e082c0401e032117140440e40395030030901d21800592441071590583d24406e4074221003002060f00c27 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305945251 1250 305944001 305944013
    0x30a020a0c0c0b1e030f0f130213020c0106060f0c021c0b041101090b070201020601090914070e0702100903052b090b01050f190b0901020a080f0a0e060901051b1009 72
    0x480440c010300407154000b0340001100204c100c9004690580e0000c0300c554950725080c4480c00050192144001d290340c4040260b48c84124040e481411901c2c01039913154030600e050700719156584408144000e5402c41c0c440350350403003403e40c50990140c512080100341244a0003800341040310040c0036441030424070007440022007002040d41000c0c3ca40c20205915074002c43c1041c000c1c402d00900503802400180300040300c03034108034103480c49807440400f501c2400300a41e003010000e03081394104517120410004040d038104a2034500182d4464100a20101a28014514440e40b07000401c000d407100140412484004944007a00c000d68008010f83e020b949020340d085682072203454450150b090300742d02507182c0303c540888203401481d101104249040700c00c180700c0c0c0105400b5415805140402d101080c0781030020800c441d10207070380780d0b994405048040c000100541d459801071605101380e0312a82d130440101c41c40c0360441c00000c00c002c00740d8031107685812104800d40b8500b0b410b18003c4010001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305946501 1250 305945251 305945257
    0x4060504260703140f0f18180a060e010f031b09060602010b031b09191509090203161a130b040303031401080d141804051009110f030a020a0c0c0b 64
    0x711903550308400032100703001101e04c1c1c02503842d254072100c0100000e89a0018a00c0207052160920809400c100c682c0c000084030340708418450714200006104004584d4131038481c02c4060403070181400703002d50520b101d060b41d0025500004007030300c090001001e91040c96181c0b01c1300a01041d03109105240c0c585000038040c00808070028024440e0081542c04540c2c0c0740a0204905005041090703a6074810100d100b1b00007078007805101d8103503104150700c001c030f013900345141c00760030300c0d200c007284007002d0b403050500c1d2a40a540360302c400507400d001880030251981c0c2500c0f0f8200001a80743d00e81d480500110500182644600c1041c200042c00200709034040c0c000000d601103042c4101711903a61640d146440d266000502d4000441030b0101103140c01e0003401500940c00141000b5100524a2011500300d0700280c034503082c0040c0d000000c00070010a8041d0012414545a0036418040915681016404041d1204500f00d03008a0249103152184035452129504941458030590390b412407194664 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305947751 1250 305946501 305946503
    0x6050d0c050c0a02010e0a0b0c0a020a140a050144061f03050a0b1809010e03070308010b0c0307050706080106020d08130f0809040c020f06061008040605042607 70
    0x904003400040d44500a000b982c031210385200140c1000c1c0c0c5203900450b181e00020510380c0d84003ea01c20042840d0b503050003c1c25080d02040014880e81180d401084000348856101041d0128403814402c0951140315585085076800e081900340d90b0110103584542e100403d010303001d2034400d401400c040c142c91440304480c0d00101681040103840b07031814816929203030600ca4040c620740e491914405c0303209038800c5a1049000c0000204000104c0004021004018034680601190000c1c0708102c0400e2003041e0260310750100442c682051690007804403041403250b041c4090001c101800280001d108403043c00303a2080c00d4883c4182c4448019105900a0190b40d006115a1036441c000714000c112080c001e820f0b604541141c003c10355681d07902101c5001040b42c00f00ca06111030200d941f12030040e08001d035455005000c00402c0240042e181150041c1582d1044030b205034600308080d00303c05e4440d001a006040881d9642d298144101070700340900350401d51440001d07101041c0812800036142d02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305949001 1250 305947751 305947777
    0x4090f110108060303030408030a06090c020610090612020d0f0501060303020a0b0901050415050a1d101b0e010503130b10062d0e190b090a0b030126160605 68
    0x3504403000450303003101c044610a426500c01c0012a0201d02d118000e1540841c845002103109916501044203940c405000100035038060418082d02500c442d4005014100ca10f1040044234640000503481c40100d54010780113800315560b04051181c0504010300c2c41390000020f02502d80d60f460001d503142d0030804182c4603442e4034004500406410302400380100c3d007085180110b4150026010020003019103c0705400756101c84644230045009091650445203e01800c0d4810812221000361107240f03062480346070100d21404002508205031103000103080c1b07440c0351a5a540c401d14000760746585d0000c0c118121050820030b44100d1707490010141e03441581c038030300e0400f241b41860032070805203090f515a0206003910061414402e50620300501d00080001286c03180406d091154240550404070409400045c807070403d00305000390000030710301028034528542c5818400e000e0101f00301d20601503500140d0f41c002c3d0b0b550041044007002240c00e54400f00484d640c2ca0050890745c4101c2d214019 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305950251 1250 305949001 305949023
    0x90405030901110303100e130605090f190807030e0d0c08100b01020102131703041d0103060b01021204090b041b0806040b0f01080f0a020c030d06061704020d06050403050904090f 78
    0xa50300f004020f503805032540794012104035041280c00724140034010b182d0440d2a80c1d4007010000706c1c2040c09520f000b055403a01501c059031030980e0aa00f4183c500d118051080c074058007020002d0314640469a0f1284c144c60261388100c0240700181342c0c01e00080b00a850380001400100b2000404100c0c3ca441c8401c81104024019865005900b070303010b0702c034510f46134141e8a0800c0004803000c855002d08900100300380c0c2c3c40e207611242d0012090a18600b10411a0b10140060013004003511880041e580c0034001000c2c4d042c010480e010300780c811401541403040e01e070400002180c413150041140180510389842e42d0034642c8030000d19600c82240c0c00e5101d18189000706101c0d0903e451181a0b2400603564003016580d4001c000c549a400900700009143e401c100c503060484040c400f07041c2c81c250890011860b036240c09030040041707101440042514103034606000c0160384e05c1100818282c0d2101011503196942d050030b03590740c01503050503508607080818810800c01c00022042e0309500c12144161 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305951501 1250 305950251 305950277
    0x905161814040201120e1e060601050c030307030c020127110a14220606020d0215012706080d090305010f020703081909020d08040e160905041a090405030901 69
    0x4155041c8400c082440035060000c10055403042070b041c00c03185d0800343e001c2401405120a81d1030207494607841d003c18102c42d181415190703400e005107600a072092030018180b600340d150300d40c0c980c4800341514040c10365911000021900030740296000504422074000840d41c211120031074603031480c01c22104200644880160742c58040440d030155403518002c142c14007102400c1c02030340c0c41c0c804185447c02c0a41c1440481042203030144030302900c40c0d0b501928595400d06406460b10280301d00c208130034040c50700107000c00380010210102e500081161110b01e00c02002d00c66004005c20b400c1546a4018945a660801e4010031101e046901c200001c00036407841c184850203c3c0240640180041c00d0380340420b401030b8202d01290b280b015240700000b18418194001011001d0030300c002c40707a0000120f0100040c07034a945034143d1001051200540d80152004000c0040715207001c1c45109555880c00074100c0c030304c1c0000c8021865009011600340d4203250501907925040059900e0004a030004402c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305952751 1250 305951501 305951549
    0xd080919060c0e101b0c0e09152215020c1002030601120b090402010c0c090c0e01030c080708160509120309281215051609050f180604090516 62
    0x10204e502d80d40c402003020b0b414131907402e0482854040d0b807101400b50000ca040c0c6052005240280c10450041c42130a25002c02500300410003010603110708031030b403010410701d00007142e41500075501c031881c00140c0c016005540000d018407a00069244034a4820140a81ca41d6000f9400344138241c030340340c0c0b020440030340c8031040d81e038050750b140e801c4204580804c0041d40070352240150ba80c40386840c545126141d210345821a1804000340000580070500d110700340d42c1601c40e14100307062916040d045850102401341c924400070b0700c003a5100b88061001c11042d4403c0d8142c61116000030110b040040900320f80d44c1e1341c0d0304111840c51041d22051105c852201c10103600c44480c80b44444030303030b4070b540c540700c2c9000384055154801da8414400323a9204248888500c036052003039500041798a1413002403c0010071078040b94000502071010a401040c4583c1c5e0711103603a20f69141100329016030303680c2c5e00210740500076203070000b4400e12601c4030004090705040703078030750668a41402d147c002c109000c4880d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305954001 1250 305952751 305952769
    0x105040c0e0402030601020309090a0203010905060d1e03030e070605030604051f0b13032f0103022104051e0604031103070f0809030106030209010f05130b030d080919060c0e 76
    0x5840400c0500c0c8101e070407070515801550703110300140181c034280358070800400c500c504e00f00c0300e100005a001005120a891920425401580c00c0c1c45101c0c0c000340540d90000072038000d00c0e11641840d1004503201c00c00d4802d400503018919000140ca1030a50303a03040181c0940c10036102e0394491403c0800181d00795840c003030540202558490310f01c1016160001104030355000c0c02c0c0e10b0045a42c0c000303004c0045840c1c3e80c00603040e5240e00009115050286140030090b08032615030758101401000000441810040c00750070f081603800070744034a52100d25010b86054955212403c000c0704103034904019950100c0c40754401c1d030107030710360580da444e07034038110b9459104810008050035000d03c071460100d859030000c0c080c8607401400001c1c5c1c50b901c0307030002030841109034013210132400d40b0042882a41060441198002e500300403d0042c50361050000b5165248403124000304481c42c40010980b8070200a01c1c90041445207188541c80d00070300f41305002c4c244001c400300c085a402138002c050781c1825812 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305955251 1250 305954001 305954021
    0x41b151214070c03020a211107030201091e0806070302030f07081909051e0714010201060f0e0402030a0f0c03111f050307090302060408070306050105150913020c010c0801050306010504 81
    0x15071641c0d50041510b600180381c100360114418500c0c5280015048602d840801c1040b00b06c284502000c00c81c0201006c01151032001c04d50003400c0c0400041c1d030882405016980214a4018080b801c010b8101c00d1001a50244a0610402082c8200c0c0c6415a00a44c0107448103181c0c0c01050b5030310b140a44081c40250362039403a00700315402400e141c451641c414508148945c0507138621100700902100403081004100905030000d000c01c22010710341e1344100e00d001900780002d100e440c3c1741404071600400341d0300ca4014818400400030b801c664051103075041a9920440c0c1e00c14120150400890b0054140400c469444500c6072242481c500091032081454042c12100000c650101048030550000352040303042c08202d20012005941e0000580b0240401000624001d451404c00750107944041c0d00c00c6008480c15820900c41240c41c1c402c9501820f0207030341d2610030f03181c01c0d041d0030002d205404050f1013951900b00b0040c24036a01c440e056040b40c41c11070403107444c0d0f45c0b2001003000701d0300c035404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305956501 1250 305955251 305955281
    0xc060a273017061c0308091606081503190605040b0606091e19030b091b03030f1e03010801090302010516090509040212031c060b0a0f08041b1512 64
    0x404041c801d0380b080c1c10b6a000c80041c007001c0404542000003007202000040480c00b1481c0e181c20461500d030704211090000484581e100c41062820401420944d4048e101a090704100b0144807a0350f1010000c08407080c42980080070b42d043d15052000c020310007035600301e0f401800079010410504d4408156800081c000300790a904012100d02c9040c01501c2c0b05045800c01e240307100215a1b4400c4a003210300860003020f003d500d078a407403100a400d100401c8044c0220f03c414402e82442502c00009841007501d560a106999402110003261028024002e00e40c0c212400000402c10181c190009440e491280d0000d204a441c1d00e500b907080048221059000119480000c103c546441450a600140068014840d42411850060a41d80150810110740300325400b81c503030901c441e1003a80d008002c40c4204904090001000514030030558511320100700000303000c54240002c0002c0485803803141c3c82501c0c20780d55215100c0d04c1d01c0c1c00544821000c2a1031408544108410380100c00c10741a17908 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305957751 1250 305956501 305956517
    0x8120a0e1b060705120d020c0601090e07061101060b03010f0302010201050f011a09010e04050703060303090e0103020607150f0c021f050c0304021c0f03090e0604020c060a2730 77
    0x801c2c464980c205070401c1d02c076440b8400500d032100341c030140104140b85145c14003603070b10f0b5801c40c005481c0503410790101e20160314115001d101c810002c22110240c8126103090b0540b482042c01a078050940d58100c0c8010607800400003805582c040104422030b40f003038000f404544e4441c0621042c8030000d01c54009440b400035031114010240000038540680305051003104541c0e04404076040f60350443e800c6010a40e6844c0038420b164200298000600807d81c1d24a999070455000c40e04a0040e03480003030500382040324034402900c40d500020120250781104104000c00100003d50b1f941e5680b42841c0c00b00b030188100b0380d44080c0c6000303491044511200301803440d04ca0b07a0034816100440040d5140d40080c1d4030601d0002151a0450002c00e4001c0d82c0f81d282c03007800c10150071428880503100605c27651040040d00c424038004910941d2018070840d0000e00c0c401580c0b041d0190004a54030365072030201c03010a2004009660000c1d00484c3c05000500074010400844120102001c1c0d0549010600705 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305959001 1250 305957751 305957803
    0x6060f0e12011104030b10080708030d05040609020d05160605090619021212040b010905070f0827011d15041b0b04090902040b010921020a0308120a0e 66
    0x240411a004041103000020700e40c240c0040b03900540c1180d0400c568101006041c0107c500740009100701078030b40d2001900e4010f161040103540d038402d18004092654030754001406000c25540007007204c41c0c0140070b44546002c2490001d485042c000d40220841032030460101f40d00d840346050341c08e5200702410b20b41c50041d000b80c500b01c480048200c0c02d0210701c150710b03022507009184405040e126400282005450805190481c1110f1050b00700d01812071500d030401a0040d4803081024905c000c43c10001c01d140c4404000c60400c2c03102152465402005a60070b24401d8415031101c84651030405c0300f01e0070052408090741d21488486d5011095280000110300840c4402007402c079407100c018621001d40b550b03482100e4880d0030076440028401d0f0b60300400320960500d4000e80000b20000d2038000081410501032858100103401d20300d8240361600c3c04a4110340710034014001540d0042d9065481e4011282c1c02c2c0440341d4100c8000b840c0c0c80c20100d0302e6001c2c5078000390041d400802c0120800c411214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305960251 1250 305959001 305959009
    0x50d0602123601060f03080c0d020c0604270510031e020d08180a09020315091b0f0702060310060f05030705041401020a0204062615010e060d050609060a06060f0e 71
    0xd202090702c05541c0c03a040011142c0f0a034080e83d004600c60b04000707448201303d07040c241c2008824411740c025500100c06c2e114281c0c1d2004100c80c2900c0b0b07a035513013021030050a840c507006030700d484010040f182c0c602000e000c0c18020340844802100e106149035510f4842940f400d2198500b86e0310001d4000a0303800020300054480e0700070b030000c290385645c95807250400c0300002d00c2da402d0790751094105543c00002d005140780c1c0055404145034007a03070344000310305100010724401e0354451920040800c001c90080032941c1040c0445060340d4004121940720b042207205100300803003c0c0300d490049041020035a0309a03001c1d0050324400c00303543d181e4605080c540300384082c200c41104207090450041c01c240100590300d41c443d41010f1b040030f041d0b050810407131420790700100e000d03082c1c1c2821035403212100c00012041b40380d0007410355200203001c16103a104c0310040341070241c004130000d00c070313016013002c00c10900c800107451032181c00d40120038000280ea418043e501d07204444c00d4040010070310b82403183c0301e083c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305961501 1250 305960251 305960341
    0x10020c0a1218090f0f09050d0503090309060409020c0c0d03090317040b0c0105010f2102060711030f01053c2d060a0501030522020a050d060212 63
    0x20785418a00490032181c96410912296074000790040307550381050740611026480b901d00d0204600c0010030075803405840300c9580c2d81c2d40801030000c001d40000010b014500501c2500c00e03103500500a1515603890f20001c4010317410000021885104412541c5120300e014801243c01d1509a16142ca0031811500c40b00340c04d00c92a018040460020000002c1300000d4000401070b210f0540000211541824400c006c840d00b507600c803103000b81300c10400c0d1114a10141c0c0f881042a811190715035141801d2030007114208860000c3c55040c0a4203046071444641900654450b6105909040310032143c03000d042d09252150003859008041c2c0e1443c1c0001980400d142900b05210502c00c8003032090681c3d06081d0090582114010f01141c84240150381c00d0185190004d0002400e060000d07280c0b15850f151070038203501c1da04046c0240803480c0d4080d91510099003005e400301420f9020142e449081500195101a200e43c0045407030700d0014000c1c400500d902c52001041d240c1080c007150b03212030440454a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305962751 1250 305961501 305961533
    0xc03040b0a0b06030a0e01060506040503070905092103040309050d11061608031302150c120a0302040302060307030504140f0c01031a0405040f0302060906010f06110a020a0303050c10020c0a 83
    0x1d42d480514254603900c01015502c41d040320304002c103401070404001030a6500f0b42d44001d0040c802400103024558001c42c0d402c0958500c07060008182d49d81c03451261134204a02c91446074001c00540c5404408502d10003940314600a032078100c5031aa442d400c1c0603403503600a1020748100480e00b80405180b07864030080400803421105548800f8060300c4140d056441a07940c2c8206100d03a03240c1c90118141040e41424100346004e0150400001c4440552070300e160500204540e6400030f03146c2141406541901c014540142500d40c49252400000e4010807044d5016124407002c1c00e0340400c40d0740d0026031041203a00c000090640681c8410056000d01443d4034810403072000076002c810281c07103900c5260b10641c000e498018280283d424003a080c1540a000a04150480401030040d00b2a070320301c2004503a9145001c10340380f5031400780241840940c04000398043c009000010a150380800036050301042981651a007614450040040740303c0c2a4101c00030340c000b50b11550200d01d000103980d03158 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305964001 1250 305962751 305962771
    0x60219060209031e06010501230301062f1006080313060315031502040617040b06060a03020d18020f01050c0c040b061209011e18020d060e0706050c060c030c03040b 72
    0xb52481c6440d040c200081104c0c0e8880359440785004101c55070340800d20b0125851507101150310086502c518000c00d210500914090040c030719000e802100184030740c1101c28030a81205c090045242e541d203a200da11050742e0794201800c000b000302d03285101000f00d58944190404000d4444c1ca05141540588105d0304003400d40d000c56100080840c01c5010354514000c0d0102006039100d04004001c1c043c0319280400d603004994003000c01001416100280390804021640742e074949408840840181c42844899922603040502007092042400d40501a4500c201c0f003122815180170300442d25406070b006080100d502c205103401d02402c0c90790084980c642c003e456503280840c80792418124000903114510346a40d90a0450b0850112803001c000c0c0341e02c03920f001d1010340720600815609405a10029120f9568141c0b108100501948501c80480c150025140e200d0380e105005840c42e04452200c40c418022000080c2d0405454400c40707100f441400724460854940340c40f82d09546800908801d05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305965251 1250 305964001 305964013
    0x506030309030a030c120504080303070e0d02120615030d050901081e07050a08060402030417030709080111040609080606150d0e030f03090c09160e0321031006021906020903 76
    0x60361000d0003e507070824082d840d5003514480c00d150501038004194031450030072500307000c00d0001c0b0b0400b00031a500004a440e00c81144021280000e0102c03500301e800941c8607044003400030148001151300d1b0310031040d125400154140c0d0400b0b064035940c5c4c44401c0000038600f04400d5080c1d40c06030341050b8205a4014540042c2c0240c0000785061450648469012850100721580c0180e405001e545c1c1c4488196400d40c00e6040903070f120710300401d05408415a0320004000103440310300c036001c200010f041c03144c000d00c01981c5111016a41e035105002e11000244848070100f1003207000221240501c801030002c0d6291503581c172500c221070300b100000101184c2c458440541d10380c8100044c011991400d075009603241404140985494070085080340601c85810800407070251284441c65403036034909140f000d01003881c0000c0d003400c03021046104441c0742825900c81081560b400755201c0c1003049100ca1109403103050a07a903950007540c0a5144c400311210b0000001e5980e000b4008003a0060101e0340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305966501 1250 305965251 305965267
    0x411040e0c091816030b160302040b04030f140703060507020f0703051c0c05010509161401020d030f060e01030609060c02060f16050909180105060103090f02100c02030f010c0215130605060303 84
    0x3004007503171341c01a14040740480501c5001c3c00c0410213081b1400480c1000c601d054900b41e050400750042d0320020b8402c6c1603022021040c8041078000451103080307041503448158a0b49040b500a000130b6561a0062152040e0382200c0000000d607a01601e030040c004010106603030750b8100a4220161083d400c0103202d0382102e000400034042c5074082d8020102034075915402108109044103c4d51000d41e08040429840100346d8002c03900101c0c450032880c007c1180071000c00b03030b140644140c1e0310081002d90403000004c00e2103d10342c09240c0c41440f0354000e20405c142d6071422a0380d88003d0b10203041c000c1c8200d022500c9461450780c03480700c0c0e00003030805a00742014480082c11040b811286001402e03804d0140016a140a200701a80a0f01c2402c0801c0704006d0341d16030550140c01404024042c00301c0514030a00d4074050054074181c90380c01000c403a8491101c030340c042d000e03007a15010741003d8803031140100303480c6203c82c908910940102d012445082043d847d03410181030080d000e29018041000602c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305967751 1250 305966501 305966533
    0xa090905120d090506060607030e040b192909100c1e08090306010b13210b0106111b061204061104060309150603050309061c050411040e0c0918 63
    0x80710a82600000f40302112030900a00b022402000c0e1403090303804200481c0082d4001e184d0415400c8151000140198248040340c1e6600c440400340d08450542c410000c0d0400b80d00100210707240700185200f105a00070403014655028141030a9407085c05c2d0082c9400c0d00380b04080c00740300240164207565804048c14510851140c0d060010340c1e080e40d0000c0ca11110707060412115004115203140c86160200c03d10111b1340c0719405d8050743c4000484150300405a000c09850f0b8034025030070062910007541d58000207072031105400c428500c0360180014141200c04c00c02c008110049000e0b10b402e18101c400002e0300c2d0071620041040f5025aa1003065600b485000400340000c1d044644000420000508048150181405200414a003803020510010b40040107503810701000381c4100341c50362580191541d00596005403030310b403a0320303140801c4140329540a160092040623542004003600c00700215485408123001190440c4035040420040300810f81d8481000c0c07211825211494583c642c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305969001 1250 305967751 305967757
    0x209060703030506180907060e010c0605090d020d030c05030103061d0f0d120902030a0609050709020a17060301090c0b03070e15030a0c02061306051306020a030501060206150a09090512 81
    0x98001956030401c01004d800d0009504043c40c10101c003800683c600480003a6540d8079070f028000c10030025002142c01a4080e0800309040c0354050320500041c90440b114581e0f03071001c03000c3c081c014807410b0030480c10203011741728505007144a60395843c0303168296241c0da00900310b00c0030b4014440480810075440c08409202d4a04c2620701d81014002c1034041030f1004100403018842c1c02c07142ca00d40402040142d03800103507014019800789000c6404940ea003011814a80654441d051460000401d080c0d50f5600c0b810030600d804400741d0319846600d40009141c202d81d898180100810b0f10b02c00c050000c04003200113503920402030702e00303604892220303c0070034103c458011200d000b0300d00101c103120282c2c03494068105960b200c1d02c0280000e15095031001c002c1d1140ca030002d01031680d11000b150114207040514808580c0000c019580c807141d18500600600007403040d07074014000d00c40800c4d58600600d803900c814541c014138540240d41460080002000009000c4541d440307584000b0100c0391540000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305970251 1250 305969001 305969003
    0x40605070c0b07030f0305090102040e06120c03061305060f07051e0418020403020301110a052d120a060609060c08090d0f0507060e0904020108070f121118030c0307051302090607 78
    0xc081041700b0340341000e8160f400c050428071080cad0041c0020701000c5d0401e00360643c0014120b441076041c00480f007405040c071600f00385080d0140602004c00140c5000c80c460364031018420011035030641d03602c0391800c104034002c0e158400001c5003040400d51070318071140e130005040300904a091901c2e9441450820101c4e00d49240d1140f5a000b14041066240c01c0c0b182c00c00d9005c03903200030351901e030300703000002e0452052124100c0400708541c02c40a00c00c0100d0b07501000710208030300c42c903900c03465004250a5034400303d40031488141400e40100303e02d8441c3c0c0810017210340d2911034200f148116600c41d030b5250440ca034801e810021038094072010400c003943d185040f9014001070540503003407070720092101a8050502d80035041c401c2c18040141d03840b810490307101a442c80c5c01d0712401c82007101104c404c0c0da40401000c4007418040f0071440780329403200401e200d81681400c41c0e030184c50b4904ec0f58448503480803095042d044400200064109000030b203540500002e001460300042000003902900202e0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305971501 1250 305970251 305970257
    0x40f0c0c0c08070506031902160602030f071403160e0d1a070e1309050a1737030509331312030b130204120b0601090308040605070c0b0703 61
    0x11903050103180808000035118000140c802c45007008085070303261001400c0700f008142c040702100303007811403a41680c1d048250b420729000303819050f0070031001035001a1000401142c1c52400b0400f1103015414852650241c01580350442e40e4a41c044021b8080100080d41403286118229600ba9108141c6c1d101e8648911031140220100c900e80c074001850091901040c049075054005060b900e865018880500c444008140c0704041c0c43d00034100700b07000c08010b10490100c2e580d2a204482040a0030040c0d52030125031400d80c00b001052251946030282c800b4240b100284c00c48803241c40703604070591041038041228103540611440041016141031240c01a1070340180e0030080300d41040d540ca0b00a603610f0174070031111083d0b407600031915114072042070034169a0101e40020762260b01c02002221101c00c0110b40b82d40e030307e0018017005201c881084850301c1c0014001003640d8040c80c1000c0c02e4941000c000c60409041c01020f1b11242d2000710142d66044640d0340010750044c80100420b10103100356 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305972751 1250 305971501 305971517
    0xb03011806061707030611070b0709050f0609090c070606080703080a09060302091309111810090c1d060702090a0b040b060901020a060908040e072303070903020f040f0c 74
    0x1c1400c408440164110420f420403040d80e4141405000a0690940e0382150340007601503000800b010840c82800c9004100d0000b500c10002e2040e00510814100c607420b0310842c1021040f0030400080380708640909510030305000210391103c206002810456101c0d9400180c1030751034401c1c1c2480c20145500c00c8030300780400201d03000309990144104000f0001410700394101080000000d51124640054001960f034511228041c003040a015800d60b803c0130b8690702011006103414800d815003200c0140034414681400102c80c0614824142c2c01000b544d16450140b00d0b41c204003581c20f100c018450743c029800d000013405a40d400164600414210500245021840b4144000d80c0c101e42d400e10300c59102800703903407140d0340c0106034175105c1340c3d00410000304c207401d910b003c40c0940a40e81240003001c00c820100400785410074811050318032541c2c1360010004149050170154401100d42d0313000100c0c800c1040005082200210703100d03030070052001c9500c50101c4040802c0307902050164000030000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305974001 1250 305972751 305972753
    0xe0c09190f1406010f03060515090a080d050f0c0109020405150405090703080f0a050403080403030c051009020a05060a02030d090c062d05070203071a0405040b10120b040b030118 78
    0xa00c41c82400c88400c000511150035010401400d401004283d030b4107101c030300c00503040c0c041d100e98440809800020b01c03e0502d0940d00288101c1074008414070380c001c80b08410041800040003038000e51204940c3d80b141d2034403100114503090f50b0403401c4600007564a8cc1803890044c0d9540c0606881030705c0c0050400021070034601080161000600000c4441c3c0080c58140701184482044a400c542241c1050340d480308500412100c2c0d00c80d0b5800503040d410701042c040101a4442c05a0b400e0600034022503180041c217400d000103c0d03e02402c02540b01c1400c032400c1007182040300103814000d0f40d90040d01d051500000c0e4002c2501d0b01e01804588034417240405120707150304201c0e0381c0003901c01e2003850500301040c0440c1c81c01043c8092200401d215010a6050031075408000b04000f510040302802c624100701101144260054007800d8851420b100510f440350414101d88010759145540710076902c009415400f00412060241940040d2140030304a580d4401340107210000a542d00e003072500b0921 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305975251 1250 305974001 305974051
    0xd14030d06031b1205060a05060f030f0303040611040b070308070c02060d0c080c0c060a0515030d050a020d030b01020c0f1908060f0903070f0b0903040e010b090a170a060e0c09 77
    0x19a00801c001d28624440540858170004500364080200c0034000740680b41d80c000105101c41003c1c1095144c89030301100760324081c010002e54007562040800b48400d116154410505009501030381c004080d042c08441e0100307200d40f0380c10307402203424181058281d804c0d8022401c00c0d0b1203500c00d0103206840350a454003045e032000352590b200641440c1241006840c8000c20384030032000c1c0010792030741c1d150004540c0e645150035070616000c900500700c60f902902540003902c0c0741c1085101c000940188103c0c619442c0c0039006071034061605030702503c0b016049800700700e00e0360444044d254210b149160340903c0c3c0f207499118103021308103040080c041c40c600b00078a07044d4628010407052540d00280201800609000340803568036920003141344496071080b60040c91801141c1c810140038034503000000380d040e4804000c1812a00c15103108071019190380d0000703561800c01d407003605141e008031307541804039400e58051000d00034040140c985054041e000586510300a4a03201181c1000c04000140d00035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305976501 1250 305975251 305975303
    0x51f02040b0c150601030b012007081501080114010509070f02010905010c0302090312190804030c1b05090a15060e0301150806010509010905090703060b1f0e010f030204050d14030d0603 81
    0x1300340b8050040c1c000d00c0d40000c14800c0f058031115034030002e525001c00c00c0b96080c00b10001510185040b6855107200c80001000b081e000c0c800c5407069468141b00702c0f900110428654103803030000c0d00d80c0960340c5540c44104d400c4010316900c0b4086541e164400360015000f8054401c030242c076179502584030403080c4201800d1014610042d00507902c00c0203880b48454500c900760f0104444c0d41070807021980e5505040da1501d07550704000703044805510307010140213131444030407003038400640b50340707401e036031407007910b404a8145030405030403018101d9003000351a103d00c200c0410500c024001041554600c44837441e007107596004500c5541110005001ca424403403885401403005a4050000e400c21702e5440d0b49074012804094016521001005055103d000c400700c40400d00c000c0c01001141142d60090541040307601207400564030703100c0c00e900ba610a0080d181034a80003418903240312025a034601c5220a85c0001080cbd0340803e10000981c40814414140214001d145524010010100900b0911 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305977751 1250 305976501 305976511
    0xf060e09010f03080a090314070f0909020a1403030403060f14091203070c020a0806040302010509010e032517030c070c0902030c120405120c03190c051f02040b0c15 72
    0x98510350041002500c0345062008807a044514141c2d148036040f400c03620410640c10243c030f8020101d1b140251040b000074483e04503802d0070003250650791500340302d2003aa44082c5019610150000d41401550541d610003500c0000040c03c6900c1e0964a5841000b036848a4a40d000c0e4159507808015003100b41d1025542c1c8400c110011704502d1049a03950550307800301404d03001c00c10510902080031500c400c10520301400f01042180d04610b41780ca0f00134040d01c400c8a5501143d404d01588003294000002501c0380d84008040300c11403112095a5138059101400007598021080d91030001c000070307590001c1d4000c66042038026074489090030040d40705203003607205c5800c203032040080141450f41c0000392140780303020640700740f810340300c9003040c900d004000c200c01c154403c130000d0b80f081c5038a0004001c08034400c02d10802811400150015200d4402254019207030f60401d030140304485030040e40103100102c0e112001801d1035100d50b031014054002c0c0d040c00d112507000c2e0303404260031080343d802030740c1c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305979001 1250 305977751 305977759
    0xe0418061503170c030d1103090705091608041e1b0509040804050d1103030a030204061b030806011b0b011520030a050706060911030103021e09042a0f060e 68
    0x201d18650720303401d1a0351424110148110b0114400484c0e0b0020f000700c0383c84909201c0d00741300c50062100340c16266401035610054901c515080043c440c02d058204510075107820004041204a41000b5110307035100400c01ca0f81d103c480b0041c2c60701000f0f50304104c01d645004481141c0304600510301025000d0341900704920840d00e0350304100c001507912003154151170080d01c12000c0080306280c52082c50807921505541400f0200d0130041c7c1913419400b420440d5202e586014401c1c101807650900000240d6025002030708980004031194002e01400c02a500d16925034280340e006600c402a03040d20030382008800c111084800d10302c07594400140c94001c00d0400090707261036840e0655564038442d400d2150148400030031241d041c01559484500102941f000c140403071907150386040120b0340240000c130711508e060302e64450146850405580481800340c134942090700d0380d44501d01030001d0080c1c00504481c0760f110280f03440b404807030880300501c0020340540e84c1600f401c0e4090b14421048a00d05d0107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305980251 1250 305979001 305979041
    0x609150306171c05120610110105040b060109050103060302150702120114040605060609091501231306020a12050912010906090201030f0b0109090203071803240218100e041806 77
    0x80d000768550030300c6d004041101c002002d4840d400d000c0e64950382941540050303528001c100014010f00000c001d101c0c4400f661410b5007280c0750b100540c105c8009020294004100c2542540c6403030100d001080135500080000328030080360030f22a401d5411861a401c850034501c4188420011076018064000c0012110281810794100100d0000d11004100e00d2110900391a440c5031640207a40710f035010001c5500400c452240b40d9103480d1650b10181400c1c0d5041845100000d000340f01290207180c0c039900038110b61002800e49812150381d0042c0c2044d0354001d00348040918074800074440c1d1304682d441004041080c2003140009411207403e401b1440503a4113015020106030b038044241025903034500740058598a41e10000c4400c82c2e0010380c2c0c100d03c8400c0c1c0c5000b1062100ca05502180340000301400f030f804a15040070201a405807040071030360950881c45c040303002c0c6403101801c00030001a1420107180d035400c0c40003405498144025a10098010582c4002c1c82800e00809402c904401e9220134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305981501 1250 305980251 305980267
    0xc0d06060302241206040f0608061807080607081506040603090b06060301060f031d060c0d0614010507030c030c150f0f090f0f06110403030801080c09010609150306171c05 75
    0x483d42c45a1351141c540c0710800e600156450303a8a6214000041d20103004201c3c03a82c80e6000180c0e5040c003541d04c0a8502052200000c0c4044001500750640c0c0b0040c02828084e100c525040d5404030000d0102e0741100c2c0340b1175411101d500c40201800003421103640c089130010300c40c101340c0b062040103401103010382ca040006000c12900458041d4610601d8500000d9140303007040309854064482759100d03558050042840741d112150405002241c03964035040001070341c0c8070f140d40b08100440340c100d404148140b10003800701e400b030400e0b0100c8900906103442c0c0c84503c0e40d00c00208142113041680e1190f5a940c824440032598814040701d5040641c003000300b03941503203602c41009500c520040000c9071900941e000c11005030040c0c90603e078102002074460b0740f64038019141d0a800d0103001c64034407840324944400d182031080c441c100c2c1d03b282c0b81c0d00001c41c20000d000c04540c03e08250b100c05e058640d00c002030041c5124500c041c01c140076401620091120f10381ca80c031001604e155600130007209000b101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305982751 1250 305981501 305981569
    0x1051c030905150d090309050909010b030a020f060c070807231818121b0a0f030f050c030408010608010b010207030317070e09161b050307080c0c0d06060302 69
    0x1d0701c004546104400c002600c0c00759031482030007114001542498409800c151f0058800010f66004a60740716240e0341300d1440908940742d20200c5a4158030006034940581007007000345410355009800da52070145598031071440c04034140d020b68440c0d40b00b501c0c1006085112081503402c00907000c0c1c000e0305480d03418002202816414100c2d03080c1c10084002c1102c452010020720080028041550042d011040782609150000b0900c00c20380c41d10340300d1100040b6008911551203d80c441ca0a0081c403440c0d407070071121941e10f00c4c4030806100042000c3c44864008002800082c4910b500100d402070400c03000a082d540c444858505552100c0e10a200290300400301159042200030102c0a50380d440034202c440b10901c0055907000701da1402803003101d07000b00c0400d014042d4241c0755200e0b2340d01031305095401d241c005240a46603401c184075030800517400b8401410425907090449500c0100e11000400b40f00c0080000c8501035943c010420850500710300c0141d040d00300681280b80701410b52002c13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305984001 1250 305982751 305982767
    0xd0506010b0a090e07080601140a1e0201060909051c0201020a0503011e0506031e070503070507110a1d09060709050604120f0c0b120615191b0b01051c03 67
    0x100a4001c0c08280c01481910907030a0304020504480b405046041c1203401624000003910f03002d0000d855902c0c0c540040102904035002c01c40b00d940d0ba80c8405016280c80d8000c040094034480c219504d8003400a408003241c001d02d0640c40c0944040d001c612140c902c84011071614003030100039640140421803140f500801580e04481c05441e402d03c81c00e1141000200701412070304019803180e408001e000d800e480345d801221a44c9980c0d04185d80d81c4d1a196025a6280022076040000800c10048030b00016105c2c40701e2003845101401c50440c9944400150301800d1180907459811110001007242c00002002a1600002941407d108985c109400b045141c812800349007000d41e2245560300400c40f0406000501d550040761003106244c803444c84030f146a000058034a203c1d4948008600685440d0030700c40380508054000b68684541201c06d9155141c6a13018101030103500000b048a10610301885130100b441030802491560400c0100711130103505000c1042c0c1d030884d0800702c00000f500078980c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305985251 1250 305984001 305984009
    0x40e01180f050304090f02070303290f030304090903080603100b010c030503180a03020c190b03040204050c041208030703320603010b040219080106111002090d020405130507050d050601 81
    0x3540034607041508042d880c40c440ca52040c03405603e06407044000000c9035020f841c04520a950a1104a540d84030718181203014020b80700500807004858101490900000c1c0306418024060704d040c9507481d14001d040350340141c81900840c040004115883c9014400c15241d4982c0401c01c00100d40c503000001d01151400030028240000000410b44807406201401d0b004851481221980b41e440d2400940300c0c0300000b41140594103e5041d00329600d14182860705a440d070b1a0030a003107030340365002c100c040c007070242906401c16010040814a40c03482c0001e25030711800707120107540e40d0800000040842c5c91f0b0075614200c241a050101c110042125024a21001ca440c112202900c4c0c5000090040c250540d43d1540540b00141c2c001c4000d038000c0c0401e002d482252141c25a6a0b44c0700350960707902000c03040403107868000e13850350701c1e030780f552507001d40404075019100c41000da803a07a01040855900f610317004d01000350724160b40c0810404014020103080c0550302d802400c2403507941c247e43c2e10f0040c09 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305986501 1250 305985251 305985263
    0xc06030e15160302090d1b06020f120d140a0204030b0105060304050a11041b02060a06050a1a0c15010306020705010509030f07170f0a08010f0504110d050711060a0b040e0118 76
    0x1070702d81e2220301c04d40640340d080d0700080600c2c1030148145400c0c1386108442c00d0020003842010f1000656500100b1403501124021001d0194a01c0d00d0300c01d0411031f80090072003129540c0d261007443d014640b95451038860000a10016511800c60a2003400098140d211510420341001048006030b408200700502652045a6641c6440070a00240180c0801841c404001461a1a020460354000743c001e0142c0c0a280d010040d10b900c0d1424032400d20401d00410491407140040d0906500c6204002d10072840c0d00e100b50303a0b00c00d68600900301502c0080e8825101c80386c01082500c00e0050070320629802c07290340741c002d520b0401c444071280010700540002401044503100710201c0c00210f1070890314172843c542c881a540d404e00300005001200280618812045640b5001c03071141010b1040c40154104030309085e00304a007074044c60020b0305006141e4010404940d02038002c02c6801c1055074020042120b0100380611401e050104482100526400c103a041013400e46445900405003803d0030381041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305987751 1250 305986501 305986531
    0x50303090d06200a020c1201050f060d1b06050910022803050408010221090708120a020f10020d0b0904021318081801090b12060f040b0d0c06030e15 65
    0xc04034920f0b0780440d0114802c2a03200280d01001c0c194040740da0510715074200ca25116070b00d1400320103401c9541c11241c0389500354101001c1800c81c50034024100c2e2a83c820042910341003901e1110441030381c85c40e400080412800b2810202a00d0401d480c44c811070020706c014141c0c1008003418400a0700c1c269030301d00c1d02e00d00c241102e10602d4419000c55000d043e40c04003c0d03581d8028003040200c0342030070355081070321340100e040403454168002c640c0604032010007008020003032000e004500c5130340c080e090304020b5100745145560050700510550004071034840005852b07203440340f003003030a444844061074801c1c2e211004010040ea10792130301940c0f410b5400ea00184440c0d2409480c100f040304500701401c001c2c0c0104440c400c03081114208403c409003a0b0b00e944c0496074418144000e03000d001065151030000c98001780e4141403140b1203c060707900044c0040360902001c0c003c0b0386020f4900b078003583c0c48850b4a0b01800a0340e050f0240d020301e040d480d8010901092681e0300540480300240101922500701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305989001 1250 305987751 305987771
    0xf030f0106060203340314120114190e07260403110106050103020c1002030a18050604020f010c0305180f04090501060905010b070201080112020105070602030114040c050c07060e030a0c06020f07050303090d06 91
    0x13101070740c88c0d1884e079284500c41561914000b251416200660360722035003068449a844030700084400301198030a0301488142d4513080d01c02c0e12100303000b945c026402c4c0158582e1101004081000c9401035009884001c4020400d0029600751840c03074000c0c038107050042013004105c41d000140048550000c050050300e030f0311a144040080d007010199100d00c0c0d9540801c00c000d0241c0480c40074041d03407007201d950500007d100c2c01580d032841c6071301010b400300340b0601c004441440b01815400780402e0003003202d000054403400241c111450300c041550f040e992803400344003485051041e24050a00c80d0411420701c1307140c0e40020b115140500600c44035003020308c40a070869020710191003403540d2101e015912582c44641024900100c810440d10860509045d640c0980c0110100c41c04d07603510b140684189810450150b0f00c03102c04601084d01845403117402d1010540c0041000042d01c02a4040c145554030154403e10b000c09035001240f103608104140300b6280d6a407469600525805400400d4100203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305990251 1250 305989001 305989037
    0x607021207080303010807090e060121020a03050d020a0303050114090403110a06060b1c05270319023d0b1c030305010611010603080403020f030f01060602033403 71
    0x40d40d002041d43d00c00480045420070002c259201a5481200c08104000103040e11305d958100a209059101d242401940d0303402d000070036500070850000e081141615565555203103070034015001c140040c0c00401d80c9104159160140740d00410501c40c40031100c9501100040d18004090002800e0002000350304003544e905010401d03a050300000208642540c0d1146400b55a004400c0c00e0b4580b80381d604550764550b0703d44511402024466034449000d010301800c07820304404502c1c4005944000d01401010301c046005c0030034035045c00d45c00742c046800200100c4080806a500400141cbc288585030004030301160790302230707010400c10408138030145141e01081803401e50b1640c5030f01d04860040e00d0424543c06410160488140f5541c100000c2a00c21085088030440c0c04000c00c4610304020400c05840d00c04280300709120300400790743d440d12040640d5400c581c000d070303ca81c015070000b158049040003900b02c9020a010010103280e000d0030340b1007280142c42903155005092000000300c107038907001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305991501 1250 305990251 305990263
    0x6030606130e090607120e15060a1a042619150c08071211030a02030408090a0312140304051e1006060c1202070b04090b0303090402030a05040201030e0c06070212 71
    0x1c010300b500e029043c03075680c0b240c0f5510101c0300c540215048019040100d10300b0711810409002050240154028a0100f14030f04500502815130003600c4100114841c45000b1248003005500503d41c0e6889142c80c0038500d4a042030f55102c0311b002c021505232054500003240140301e00030885490300c0c1c403460a14042006c2c900010311003105510b00040003102e203070070091aa001d20016119005812103038120b8034181c03080c07a11030b90140c442c2400410440e01c402d801a5402c1032103000058180916080402c21946903031303000366189080c24400070340580e00701c41130a000104d07080d1058958030302625070650710b2040313002020001c4001035100255030002c4c055076005180c1203405220850f81d602d0001e0180c3c09a40095074100d0b41008004d5001c0d000242c032200325844450b904d414140f5041c40b0000810740742401d40e4150008101c183e005942e10b100540c4640e0701c91000007010b040500004040b0740c222001312507507a0020350710100b2691000251802c20f58125030340005445006d00c0075080c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305992751 1250 305991501 305991509
    0x17130e190f0506030c0a060225120f031205010311060c0c1e01090906080d261e0a06030203031e0d0608060912030c0304030c1b0e0105031b0603060613 66
    0x5140003064892040340c2d40066000e50811411200700c3d0090404003d840c101d00d00c101000750b03004120300302801d40e248200b4001d01c00e1003851248004d90b506030203101500300e5801200c000b42e040010204041c0c01145010284481c45410400d07503065988030510210702800c07603441550040347d2540914010400501036040291404403000640c0c4040c1d210b00c2c00c00301c1c1c1c060100300c0084011900c00d24071702c145012a002c040050800104070a03041d60401298038240401c1413400540907030300c607c40c602150081000502e908a00c0e00c030b0421010780d50318060802d2002a00b401d10410142e079001050319641c07042e038921052925003268100c1d00a1160360385078219142000030000e8800000300f440b91162900383c056400d150002c3e41004400d1100702c0d0692092441880403401003407040c034610341128030070180082c03803103141c8a104490301c1c02d990101c2c40f007061410040c482c80c03d050003c1c00718507031041ca2034020101d228001a085010040a460181c5c00206128514191000c4150014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305994001 1250 305992751 305992801
    0x4020702040e010f14041e080d05090c09010902130612020c070801050f060d170f0705150402040b0d0309030f0c0b0403030503090601050a050306070804080d02130317130e 75
    0xc402e80e07007800c0c007800c0c41e1030f036626080c0e117484041074110661281052059074080070310300d00508101c06e00f0004405143c0191102071007800300700c407480b50f948a01030040659030020101003507484200425040141c006e00440c41c011700c002009282110007a6081d034821f4180b10090405240c90a8020302a03042180c84901c180040014403003410340c4201d008451034442d810850760fa017024080b28280f0b06400601c0c015a43c0d286640d03180b00c0d08064007101c1c00d00000c4070301d40000c54540714500000640c903805500e100406000440c50300c2c0c810906040360940326480306c1515502e001e0110441e503c0043d0060100f469080204080c20580c1c1c0082c1c6841c0011513107840e02c0f403d0040107504200c030260307234074030036100007044919001401c10211000100285174599500c0800c40d6000c1e030280c000c0700c480d0018800742102020a00141c55071182030f514664a5920b1401c01030071103036490000b4041118104000d07003071489200c0d070070700643d071504096001e6a1074841110070a10300c240000780e05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305995251 1250 305994001 305994011
    0x6211d0a0602040503061f06080402041d010e2a090a060515130f180207060605120309011403060d12110106090501051f02030a0c1b0609150507050a0605060402070204 73
    0x1041102da015005661064044030050fa80c2c400000d8504010b60f903500c0e480f52800700080010701e100340d0803d0f612074400340010510b410074100320400030114001110150b511080008284001003010034080c42c2000b00c0408400b0542c0300040705081c43c10302d40c2c0c2c0540035882c0084c4c0e01540c4c5400920081201600500602e5013400d40924940c02070500c0f14045141510000340307101c690ba000d0710640b01001400c817100e00c0304400707004c025402402c0c03c9030040e807614000100f0760354200c000c000100a4074007665480d042d0382c0004118403004142c40401000c1481481029102c850886c450756510a403090070300c00c0305420903a04400d071541c0b83e206a60034428017044072500d5800c110304032001680d5180d01c01d0600c01e01011183c50f41e4055500582c401e00c07040e00c031948102c07040c1050034010749000ea18010701d40b030740111400094200d40007081034403500300203102214000c3d40440c150f501e401410464207558803911042d500c0c0c00544070f283c444001c1040b80e6210381c110b4042903030007041080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305996501 1250 305995251 305995253
    0x11d120a08040b0c1924090510020901030b041b0c0f05120702180412032c06040c05031605010f050c010203040c050906100e040f0207080a080a050106211d0a 69
    0x95a0300130611900913003c0c03140c94282845e4241e40c0c0c111000c1d4045180e2041c19401c015604000000703010128050f920744030214040703201403254414044090701c025076a864800c0016040d40c0c85050b206004502d4400e0b00c3c4907101c1903452071085102c0921306041004c01034240300b003d1029403900030f0414012000d040c02c15810385402814980c0c4251800c00c0b020020b02c9a10141031011940070302513219214404221610035401003407074407580207a070203c801c01c03460980202c01400d0b600202d00d40c8507400703010074440462003600082c20118005d024450f034004d4003030a050300c10301c161414802c000960303860031400f690503a615400407000841d1a0b1825041895440c21503205550007080c150000c80c102d8200082a10006802c50322241a8200c400b006c0c0f000410000011f1030b4029420300100303001070720f100c00400005295a443c030303a142c10028048000c07508180d008600b400602001c00304201c10448800c00f201116210006024290140480402c900c41e50108468021091564 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305997751 1250 305996501 305996519
    0x2d0206120f0609010b0315010210020a030f0e011509020a0e040e0a031106061516020603130605070e010e21100603030e060313081305060310060e011d120a0804 70
    0xa118000ca06101c1e41240c60358018040f90900a00641c1992081000004c1c081c8181911440c1c07115810310448046003104070962040344c101c40122310000f0f4840e000603800c58501e000d07000d011101b0038003c1101803034107129044042814412080703503980210351b074000d42d400b031404603044c840090024440c001c1c86462041d01c0e0323130404204a01151803455030151802c0c0c00102648650000f030210445514128020100ca821603841491590500d080d4000141c564801860060454440c50341818505207085800e617440280004100034035086840f180f0381c1d010610b5241110f0949904c14010102d6507017100c10108881e09500a210b12640382800648941c03000301124000c0c3c1d03030300d0079205500042000d10301c030903200c60141d51500c19008d00481c0c543c000030b0074451186210352170496035900125640390000c032000c00101940309000c10842d030b000300c220107501e0401d10f0030441c240014070a240150019041d500c0c00b8003400300d00a001e200302002000703165600b04100a440399901d20b0340c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305999001 1250 305997751 305997787
    0x72403020712030504200a060c0606090c02060603100c090605090420090a080f151e07020106030c050102010c0801260a050a060606140706051b0c010510122d0206 71
    0x12551165200c211b6440b03007050403188502c000d0010050080e040c501001190020103030a0180d0b01c190ba03610340007448031514442c0b41c40012032500a40101d1600d441094104013003c202c2c86101810100d5101c40d485d0b00c051100b0644402d4105103031030705d2200020400410007aa01c0340c005032074a00c100320b1024a07913005401c010fa0110b031000c0107941ca030719040e1707140d940d01d11209910340d00c842c00100a200c1c404440c00c0c3d100c40e0302c1e01c002181141152121200a800350303400000350b59501420b105120000c28500090301d0701380001d21030002c4c80038000384210014851606162a00143d100300e103d601c241043c500d030721034002c86000c2c031040d0034000d45444030391070100c1d4031910705080006ca440c01010180203ca074030019150903c030142d00e50b071003d0700004001820b1040101c2c03445144452000c05010065a80703000051149401d60705c0d42400e0b8400e40000240110554000e00024034251000c00366901c008000b8442285004403000c00c07100c11500290700180200d0952406000c80c908 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306000251 1250 305999001 305999003
    0x40504020d060e090a1502090d0b160207092a050c100204090506120d030b010e09040f05010c03110405060f0403020904050a030221040303111218030609072403020712030504 76
    0xc8943e5549584030720036075401c40040002c0c032080c001c3c3d400351044039041d4050304036104050603200101106660b1085440e40c05c89002e113513958004a0300109030743c100131000c050b0a4102c0c0810049004400c51000706440c20380c401d50000718070500c5080c0724070890a6501d540c2c1d86604903540d210005455002a42160040f41080c600e481c000582a28124103410036004801e4042d040c51004000d0880180c00310b0f0313040e02c0c1030100201e0450f80071b8131108440381c4124094450012424101d1900c0fa080d6058803506c2c0c070401d401d100321084110b00e820308076011503400729601c0d59600402da0104411780581e0344069803244480e8100814014081840300009100b542500c1460320180c103207203442c10300e10940c020036590501c42440068007502d0280400d4502d8002c480100d40c01d00c4201c00140d2000c26040021490404074140c4d5003005c01100782c00441040240c1411750800d41c007401d83c1084550300495401c010251425031601030b0303040302c21068015020519040d16650040c001c0c22081e10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306001501 1250 306000251 306000269
    0x1205091e01050114011d090a48020c030f0304030309121a06040f050a0e01060f0b0a03052809030f0503040f0b0615031005010f020a1a0408040504020d06 67
    0x34158031140c4188141c81c140c03690810307140c140a1128004560503011044080040302c0410f00700449540d405810612480c440c1401107600c003803071041c411103c20303102980c1469084a0700d10101501001c1480c0c4a21600300400c1500303000005412441d05100110395900350191030510f90300d00b030010006006903806501e1b080c0345142c6c4c0e03a503c50072080200307002815850f0140e1014818640280c0107540100c4001c2010980c02c0d00301e5517042c01c82e40d0a0310655086591002e00c000030603030030b00841000f009180840300f20309280040810f40c41c41642e00007420141e070ba10008840c00b1001c0180c1d102c0464000c41944541a1075031000000c240c544029800308681079000c5055520480c2100d208580c00f00381e2652990a0340d46203098400302404480d070103240c01c5800380012201401445c490b5802c04403c1e40e6940c9480000741903e40300c1c034000c1d01190051421403010482c010051005044d800e05807a4017541c0d68103021fa403e0143d5003000ea4014000174542a1996554009009440e4129 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306002751 1250 306001501 306001543
    0x2a0a0f02070b0904020904140a060e0c090d0f0f080a05030a060b3c181c0503120403050403022d030c0f2206030b0906060103020a0c0b0601120509 64
    0x48166500c201c1d5100e08030500c0010000403503141025000f0b4602101d000c0c1020408000a402450701c4501c00c03150354280c65030740d140400c20107181c1c1d026550060400602c003890721030b00c1c001086000316260301c05484d071b00600b000300c82001319410f612040785030004a42038a0f041420300c001c107140e1096695107402c40c02e200000c244c0d213500f001162950740300c40402d00007400c0384d82458450183d1180c04c0021040040500445440c915001000038602d0030701c0d19050141a4002c101850b1003840c804040c1c0389a840a50000505c00012a0003203544403d440405545628080301c051040b030308000d4102084002c0314002c02a0f8041584802103241030b50005481d081c0c0905640301c0a444165502164082c94090f940c14144204040310714100b050040c0941c01c002242c00b500c90642c006c48240281008100507c001405581c0c0c01c01d030b09180c254a4003510a8005100031200300b00034000c01c030003070081680b582c0a1f502100c401e80c42154281b1080c030f00280907a88905020078504841c003041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306004001 1250 306002751 306002777
    0x50d120801080c060a180e071710030309030f170a050c0606100f03150306020711090c13050114090405090c012003030a020309070f08013206092a0a 65
    0x403c40b01e07105680604401c0c00d18070b901d101115042003565480c1d0240c0b0400d10003054251000392424440c811540301c0707400c032920301c0a42d5154020014880c502d039210490303051000941c13003030081040782d400210303603440e5441030301f001440c92648212103154170750001001042107070003002810940302100c1c150340f96a0380b08814030035030b00301d051040e00019078400700800205010354082c8001e20440000e2040858580c0c1e1990101da02141054070441550042c44409251102004e9404141640c009007451907088101610101c0c6d40101170501a8010400da802d005440c00d8540e0040010030502c8a41040700340c10b521381ea081e000c082c0c001034000e01c44031000030340840840341c82500700005500c3c44d629025110b000303410141c11141c25001d14040044e14140d040e101c0b10240c40d00c0800024024003950341c07034002c0c801d041d02080b00f00692070308103503041e694141c2d80c55101d141030b42c10300d103199140000a002542003001d8416011818140030b848905003001500c03d2452a07195a28002c2070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306005251 1250 306004001 306004003
    0x40f14040c050306031c14030c0d27060b0402070819030c1715031903020706080709030807020904031b1113062601091202101a0d030c02030304050d12080108 69
    0x8860985c2c06503c2666005c07401a040103003046134144038a8400020300b0380c9000610304d0fa009482d01d40314040e0203d84020244898800c0a401100191210700400d031019401c20b02c001030f0300740140400399118004285e07a142c5070115488103511041f01a078904000325198030480004408800092520a040c5601d9020380c1d00c4140e03d85403490362540c1c555851069140d204107100b070707554141c080d24260301c3c41224003820520312203209070060040c3c1401d0500003014018021320316001c10200d46c0b010404240e0f5402111111134042d1940e658503501c0c0d0030140c80d60301e5aa521104118046070004041c00500d180360000031004131481454004413103440c8098070782c540640d00007040c81440003080f441e1900c804807840d506000c00403661801d1a1151400c2c11180244030000da0010803862078900140e10071904040360300b010b14051140f186000c1049001c1c2190020240455020303100b00b5541d040065030014075000748800102e03861031800b00c140d00a442818804580600004604040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306006501 1250 306005251 306005257
    0xc02010506100c02090901020705010c05042108031602010902120304050310060506250209011d0a050c0306061804090f020a0e040f110d020904030206011e0503030a0f0203040f14040c05 81
    0x24183c2e0f03810848040c94080140022000d8001c4030a90f6081100d9800110280941c0c1c0c801052912220340355881c0000c1e508802070b4605510701c454800c00f01620002e5041c034217807a008280c094100312401e5000d5816070041c07400c4000a07500294514104003809000801401550000d0b82901c2080e01d001060506603540303070003496413241d800d01421001c08038100c85480a90352412515000680302d402045011400703800c42444502c02c280b09409035041c2100203134100003a070780c0400a80c60710050b52600740c04003502c1e0034898880022106d882060b400d108a0134810010010003003403407289001c2c0301d1030007a490102c1c080c202e040b0b800242c500d00030040611030340c2c001c904503501152955404c1d12510350400c0e02640a6500d40001c0c2c090307111031111a1113544a40c00030b03c4035506001d078648080075009046c0b4480507031030a05200d680c40201c04d83d4940c0100e400c040c050456400016403c5000396000400381007840000000c103c012207485c0b0201c04000e503410031140641e0801190144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306007751 1250 306006501 306006529
    0x703120201110306031b01121404020108010503031305101205010806100b1e31051c03093308070e0405010b2a07030506060306090114010902130b0703030c02010506 72
    0x24001034034401b03000340c0c2c4049601080070305140400252034800103000446218000b14040210350204000031940c01c03c0c4c0795405044114021410710310700110244113802180201801094023400c00b612342402180d10004004a4810070f0100c1d684901045945003800c42c0c2c1030a014841c100001020b00403a003c42e01c03402c40d10880803211100040c1140103035403201d51018001c00d081d408000101d030402e100680411014141c6180c80c514113030070030ac4428102c1140c0201c0c44000418000000e8100340c5a200303c031030800300d5445800368140c0c40141c000e070081c00340c00c43e80301102820b1410340d400400c10788900314607102c0c5a03901c00038105110440d1024040d04140380000c110103401501035904080410040c2400c0d5003007050400411802c021a035030045030f03568442c4083c04190702d010b2104940c024849002000803e40940c0c0721403040006215030f940044e1300042d403001070304080d500c04001d060310072055540c800c0c991900600900d01c0003c0800103502c0c0001040e11442c040311101440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306009001 1250 306007751 306007753
    0x60605010c030203121302040903020303040507050108010b09040e0109060926070c0501030f1b0210050a050403080f040302070503010c08010501200c040209040b0a0b0403150608030304060203130203070312020111030603 96
    0x4001d0603121704d214030501920f10f0700761804141c0803030010307071307840c054004254800e034091038490a151038454505040b41d00460306000d01840144074050048007520f1031504100c8020807100031007003c0c2030040107201b03000381c040790920200a00380f190114452080301192200080c0740c41003000da0200b14000c03020002c040070f1010000f0400c030743c841d400c4403108000a030000a08443d46080e01011021010134010140c0c00c02800800184402d104040e44002c5150341402a49081d0741c0040c0440b8000f400c00207801031540200307040c503100f004031001810028008015030640c04901802c40802445224009100300450030003c034046044041c41c400c101c002401403460380001c201c003942100c0d0141b600a40e8840d80794031682d892121800003080c504049030f6031b44c0d05600704031010707245480342e0024403402c0c110108100c0c41d0010452740d0054110000580300d45918501c024070003403480002e949441100004010b0000c0088101c01545480e0000c12071038400080d80c1603d8081200e0369030b41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306010251 1250 306009001 306009007
    0x10b09090f0304050423090106080d0c0203030703030c0c080a0c14150412031e020405042007020d020d0609151b0504050907020c030304060f0e0109051c06020405060c0307060605010c030203 83
    0xd0401c6d40003225621400f2001c044c81810352007001c000c4420458070404d82e83c0d11060300700641c0c0010710107120701401900d032600c1252000c0d004681c1e20b00c18801c0082c1016038030f60a402c5014032406d4400ea9240c0d00075012a5111503160004000450403a000d80f840e003001800317400001000200300c80b0b002c80c400f8201e142d96556869540701400e44005000905444541d840a01152030103450725042910100586490420041c4021105074a42000c410460403581e050805242c1042d01c505070b80c100c445550f000401d1020491201508100405841c1491580340c10004c8100460714003035a00d917001c00c10400b41103428144c02c00001c1412022030402c10040c03110742005540f1540c804030900440e000310324020701003441c603030055020360000780040442e4601203500942c202d02c10102460a40d00f00d6092000240e082c2103d68040c0d100b2021509134a4200701e5203406490080c2001030400703840743d46000081e901da03800300c00c085403003d207000c03000b103244d6003d00e040c0c4000c03507015030043d41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306011501 1250 306010251 306010259
    0x1406030a030c1119080607030c1d0d020913060b030d050a0503040602250c08031e1606050c0403050c030312040b041b06050403050c0306090d032309010b09090f0304 72
    0x1d41c8a82c046400d950340d8600542e000c031a9252a80c02d41ca20048504002d110245003200a83c1064800f178600c3d000c050408900c541d2007075108450f004001000d01c510f0000746608000030b02e104840d030000a401500010821400704094103200080714000c5034140580c03d10300081603224641a4420b0010403070500a580065100d4005140c2c4248100801841d060340e2291a040b200d5100701c062031644407031080f071410003040d15104401004804025420440c0400120170441e54403c1c0700c010f00c1340042035400082c8140c48180324400c1c0c0001c4104024144441c42649a41c040d00040c0d590344241000315040f41400811100b10114000e45020030792a1a501c1381d0350010094030660341051810605c40c9600c1c202d10840c802000301d525030741d60701e62540c41c048e0709014040b01ea0318480d0300450b0421405200200d0001c3c8014254540047c5e211004034981e0102c4401c02156103102540500300102000154404440e0ba9421500200f081e0361300c2d400a80d4074122403e800382290410b0100708 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306012751 1250 306011501 306011507
    0xf0c01090b090a0506070c051e183601140c030c160501060902030609090d0e01050c01020d15061b08180105070b04051e0a02061c06150c0203011406030a03 68
    0x240300c41c1c004046683c0240d0b140b000802070f42018100355002c01c082d942c100401d01d00081403640d848050303d00064980c4030000007031200e00950400e0f0784c040e4050000514880402102d080803291003043d5114407810007100c1c0345020052180b0100c256181070042406000520101840b4400c11008245155502c22580310303503030003078800819004481090800081e00c01c0c0190000751142c1840182c4a180001c10045222009000d2800715041098000446940b18001c0e011180007802d240d83d80701e021504460080c81500215260245404100707651180e100302d500e401c40c1c01680d9001d20780740c058040c4450240c1d1030000202200780402c20101d40312441580102c200005040140c00c4c07000549400ca81c4030403c0310300300c4940d008000b4414000c00d86202d0200c07403500490040c0044506507010070704070312440c1a130302100e16075000780388812800c9400c0174010781000324881243c2402c4440103080300c0c0c003a82c8102d209509000003407214081d130008043c8110b000600414800807203031019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306014001 1250 306012751 306012757
    0x311030408120f04050307060e012a0b090709090b04020415150f030609090305090307060201050112020118031e170915030601090e01080d09080f070509090f0a0809030f0c01090b 78
    0x3140d00003013840300041540d818800400100101e4550f0034002c44a0000113002c02c110805001c10000a0f06a41c1c190100d010428010740350302000e0f80700c00703840d4154401e20700110f41d030000050f141440380c084d0404c004030092078000c0d482680c061001c03207001702d615101074806010b07800c180b07510309a00c10800c074800c5070f035050009440d0500003212a103804071242500c90245003075010650008051405080c1001480c0040500384000c001c00d5040c10140c4041120165019040281c2c580030301951025018581000b190b120030540c00072200c0d81858188112012010341d1410090039400045149080c00c0b12140700004285054101581c142c61403903030409040d490400c45921000700c2c61000d5502c83c1c034060071743ca100414000c0c042c0c1400a040400340d80200c1c2d6141c010360031000120300c0008005e42960411205980aa9900720507a4545454003142c2c140c175104001030382040c801078900402c90000c0039400d40d805440b4410a003030303841e00480d1a060020f41084004c0040480300405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306015251 1250 306014001 306014017
    0x1050a030204031506050f040b0a06200607021c08040c0509041103100e0f0102090609060912010510050109080307150c020c04021207080f0c0702090403050705030a0c031103040812 79
    0xc01801c06840780c0b540180d0b48110b5000801d0700356105404d000700d1415602c0104210012101405091820804a003035044180714176414006c041d521328580321081880118000c40180031a1140e14081d00300030358072000c084541c252802c860441800451254084c03612403034000150400040c0742c8001e200140400600546420115403442c06181d40d090084031054080c415011621a6880d0117550902c07041d200300001c5a0320401181000d1f417100c80594501100c01c8035140d403038281e440040f9401c1250754103524965480d11080003d803a0b0780115100550f0300a85c0c0d4902d186480302031842d80ca101d801c3c4040e10b240141c032600c81159502e0f40080800300c00354419181741c0c0100001260503a0450810078101881c1801041426540b190b520b5900400701400f4580368204005440c44a206d140c002a02524030f01c030000e400d1502400803902502d5003c404c490f55449001c4004200310742c80b20017200054100070003829210000001c6c0c0c5d05031483c000c003074804406e2022240c1e8540c0e001c050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306016501 1250 306015251 306015257
    0x60b04080604020d0c0905040b100603020405010e04090804080d050d1409060a0e160f08060c04061d060f0c030711030c06040501030b03070f1701050c07030e0f041b02010b031e060601050a 82
    0x30001c584c2141b54060240181d10038504c0940e1070400240345580144981c115004062040c0710401c40c603a888900825211026203002600c5011410030514911076034004002d01c1c03007a036000d0b80c05903a118004040011b06942c003000b9180b0b50b8010b01400120541c1d0241440e800800820030140c40d6510003001c0780c907401c0894600b50b40b08030221480407810f0b884446400c54448081101ea0403d1003155130050703895041e030f89080e042c4040a402ca046403004400301580c1e01c04001c08c0d07501c80d0421207661810000e046500d410020700e1450342c9602030041140e666000c62081d0a0504001900300c4120000a09882c205400e1100440091138000f50090b410f12030081c0000b28000d42540b01c10181503003014044201c41d1110300b150a4801c05001071111101c20001c0d900440d6100814a5100008541a0229225a00010340070b411004414004903c1c407506000ca026015072204800c100150150f03030407541c24500010315500180c60703860311908648006801507200d54010000540141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306017751 1250 306016501 306016523
    0x6020303040c0e01030b0a15092322080a050d090c080c150d270c06021209150f071416120503030601050708130305210c1f0b031b0103060b04080604020d 67
    0x80d540010b4941510b0501040000c1340710b90031650352b844658650224a20390a01c449405a440038622107050640240c0450f0010030b207241550301c503030308840100113001410702c1000d8540c1802030300b005040c420501948100c1174031072490704041d8004080d8000310081d032424043c180c40d451003c2e00c010306042e020100402d081202c0c0b0101c0e114030101090141080c1c0521b071b424071802900d4440c2c3c0c503a04a00c490810303c0307094000c0c1e079118000c0c0b9031180c4d07248040d030b11401c42d808110264068071400809000440101410030301c4009150309034104542e0b07801e04110307910b02142e20040050580a041d54204200191007540690000c280c1241301305c042d2445c0c40c061401c0401415007640084030300e604814401d682550b41c1581403411030350764002103403403c80c00710305569070b0b940c610522008610b010706005035440103e0380a001c240c00c0160548040074034401704000358003134103c5803502203803503d040480c10160040580d030907200340d20700800715900c0350380030440005201c680c01c49a00c142c603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306019001 1250 306017751 306017759
    0xd08180c0411030a05010506030411010e010306050d0f111c080309070509091605041e110f121603180b04082b0b060306030d080612060106020303040c0e01030b0a15 72
    0x282c0300e1040300c030b008100e0700c94403401d01080e541d0903144103030f010b14400e1105009003c0811400d00d084021035900342020b1003941c040030010b80107060070750700c0380380d100841d81d00c08002d0110148061038a00e1103103010b1a075200941d800c02003025803040b0300400300001042d6520004549a0045400414502c100c1c0c80003036a0b10b0018100203001ca58445c0b240c5c2010540e00203480e0700c54180005404116000d0000c80c10444a1b038002100303208071600141e494117030908100b51980100c3d0742200b103c841d101c0d92400403141e44000c9003029100310251915a107101c199083c030a00c40c640740c81d283c09070410790644154960b100d6900d8054130035140380320b00b040803504801042c0905801f09030030341d01e108450740d83d6004460880b150040d00e0b80c0101e20803c1000515a40401e091026000f50f0811920350344814010440c8920142c0240d001803061750000704500c0d07000006140705900c00d608180245440d0310000f090b6001c06e11000300400e110a000c11110a41a000381c04180a04442e0100c1e240d5a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306020251 1250 306019001 306019009
    0x130b0c0d060605120a1a091803270f01171b0d050405010f050105061c0b0315060901080a0308070819051005040e070321021005010b0d0e0d08180c 64
    0xc1c6902580200d1800a850780c400d064049803180c0c00880f4080c2081400459409281a138a403d44000e1080d500940052041240150f000b084004030b801242d0311411003d003869240e40506603000d0b035801c0c0c01000340c145440c0c104442107500710181c0d40c0c0d1100c0c0600b47d003060881c49014140b402d90f103012140290025060300b0191015040b964004502400c050801c0e90845142c0c1c070f02554214184001401142c03108001c84183c900d41d424103840c0c0c3c9036030320480c1c002002800d08480d858090894071800041d80400030600440c0704030354007102a640c40c00f17955619080342500501042c039201c00101894003542072980c0c070800400220396034201840f1400c3c22260110340034480031213032a90030b010605103407003011003c149004c01401d03a103045480c0d805a000c0450040b0304504001c0c03140c0040f151081c8510360131800c03600790500a82d61141080c40e074a80200e25041401840d04103a1764016000180030600c1d0710064a400710f8030b031100e81c031090032528071040300303075592161070000f81490311 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306021501 1250 306020251 306020261
    0xb1c2d050a1103191203020f0c060103060b030307121407060509100506010e03060c0306040605090703020903010f0b28080d05071a09070909021819050f130b0c0d 71
    0x1100d00064800910545400d00040c1d5845150a0107503001d03114039610714501920002d0055006501030740d000b22111800c0b8060311805090790722001c2c3c0814090b0382860002419816a8070981052082c40042414141d50303009041c0081c18041355010440c80145c024088450580000c1d01500d1030036a840d00c400080c0c0d101034074101c1d910390060b01110700380c9040b44503c2d038202100740380c43e1043c441e03101c0020b81e9074000505010104440003010070101d613074a50101c2e0080802a00109452420300e0f4068000c2d0403d21082e0b009500303000c1403650b46903141c4903220340c0ca00d000782150383c01d2a25400b03030095004075032640703040312030800e5011855003c00c1241e09011401e60751041d40d41c03500ba251242d00a210b954040084222560901c5803800003c02c0003000e0750040c0200240003c2c1c940000f130302e410803403903895080b6605842480750507540a042c2640e118140e05042c001a11a2042e0ad0796000b4201c919980b6607203003165040019405041040e00070204803907050a2201501c10030045072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306022751 1250 306021501 306021503
    0x30c0c030f03070203030708060111070e09192406050603190e1903110334080a0914090402060405060a0306150507030207080c060a0c02180117010b1c2d 67
    0x290006c802c000002d9400b80703906600c15820319040103c1c1c01e1020510b41d48403036a0040303003050f0780c00034005108404100400c000c0401d8602481d0b403090321509110192000407025103081914411551f84e0222032805003408803007014000503e141e4502e001e0303039805007a80c4100c60100d6141e01034650340c90000c1013503040d100c3c41114181d012044034613014024011132040320328079070401e11408004801300803854290000007000b06002c103814802982e0f0f1800007000080c5410004620806602c0e40040d84505a030b140400b00280040048100030081004642c001d41c0004c1c100800d01547c208800a0000d00c1c546d8180420296180d404000c0f4021040e0040307000108041201390625074100300c03400092501d20080c004074015400410100d00c80d1b00d2102d02130180e280844021502e03040079020403013416240a901c0c039615555441070740028410142c0042d03007840b40c00c1c00e0520780105100b0a10010310007103552404280c1d5400412003d601681074086540d00781200c005d0420034a2401103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306024001 1250 306022751 306022753
    0x90f0c03141905030304030c020604080604030203040501031a0d120e030604082808040209060604030b07211103060409061409060a0609060501210209130212010b0906030c0c030f030702 81
    0x510300214149140940324000c1070b0301c140800451001040020040300d41154051410860713100c028000b00b1003921a0790b002c01128400c007820001490b90110151040d118240c0c0c091014241d400c207070b9229000c001c9070060b801180c0300310100008404502a49010384a407c00e0466200308400080c14440d080340c1c16900040005104100c4494062401c1542038a2211a50441c14869001013031120000c00080c0600e000d603010a0f004d80d40e981c182c800461303200a51000b2b0b80350501006250340604c00841403160340da10030006c4036450a010303002141001036000d41c01c0d592a1020440a40b681e2102502e01c0c0b0740c0c404010400e002c80c5000c05211f040f2a200414031800d20301444002c4440c9540724040003807403c003060040d607074407644e5801c0807001440400c1001c010101d4000084c41601406c2e82e000c1c0031100c0c01c2d4400d60413078014085e540d020083c65080c41ea40d0350248000e0f4499004243d0f84000b04000280b403881a04026140d1419000d003164104401030b03860788030551040d5142809 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306025251 1250 306024001 306024023
    0xc030d0905040b09040b07030b0d02041d1204061b0c030f0803180d080703020a270302031005090304060c170a12051006201f020c07140310090f0c03 65
    0x21506090140b40c103d800706440b111018541500e51061181c40a030001040580b50f100741142c2c0da50340c00400419070f400070070401c00071041400781303246010564514046030184443d040041c0c040724050700c088955940340e00211040324030b140708004114080c2168110107001000c40401e030003e9441056030312540c1500d5580c20241035a80e00d2075400400c1031a10750264845c1241c556104030907d4100342c4504001d03889070400b01c0d00369801c980200350a010105044c10002d0451001800c4034112030007a000e5514000c11f841c540c0040d55400c440000d00c0358420001040028420910601118050500c01c2c50000c010742c0e8150141d88000ca800c400100600780740100710f4014880c01d034012000d07283c0000d01902d454005000d604251910401a0301c4247c240c165001c0140700304442000c0181d150800c0c1c06001c80754000a40100c03091000e107200c0c001002c139048a41c2d1580d000d4581009006145030500700d0501130240410301000c50300d0f10501c003411000100c51035000c00c00b03035102c0c040c400c0d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306026501 1250 306025251 306025259
    0x7080c011404050604030f03050d1104090b0a03020a0303141e180f0312130509090f0c03190b0a11160b0619300602040906060804230c030d09 62
    0x585885182000300c140d204000800460b44c032081110112640300c40d01340000a10742c20103840d2030151604645615040c02d400f01124035129008100f82d5080344010404c0f60303242c9081c01210900340c000250410308041060000c02d006001c01c500141e0f43c558841e140c103841400301011650041e40c2c1c090180008948a802000032201c0d000d103481c0d09079803402c070100e00440040c4c2d56040e80450380014140000e0009403071313004000101302030440a000c010391801e18940c41550381c64a07501c0f1000178004c280d2460914980880c3c0c00c54a04482058600d022040c0e4a0341504204003900441d0119543c0e0000f02550141901a0100c82d9401000981c3c180340c82c282039a000c3c9006101e68458800c10800072000111700142806840c003514081500c100002d000c10f003003604800782c9e02d00d015034040e840c0d01041003c0e0018010f9942d4a24280f2205641d0602950800c400b620000d00441d040d41c440124141015004001045d14600300d40304150480c0c0800d050021080000000a03804c0310284 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306027751 1250 306026501 306026507
    0x804090b0f0d031b050c0a06080f010905040503070b06190e07090b09010903110301090614180102070803062713060b090705040510230715050402030c0409020d0507080c01 75
    0x250aa003007038800c50340d214155a801000c1e10444c1d02101d0310307081c039400c40c4001d1000420040000d268098110058540c8802d40540014422107100030500c84040003c1107543c2c1c1809002d00071940f0400440c2440070650f01c1c1485400d00400054208052003201c110be041601c80030001000383c106003210385d0801000040ca005219007001310f100741d0030864840306903403252200c811a0b41001e0400820303c500c2001a014140510028160340d051046040d085221101202d01444042070184030062080122909074015130f82c0c060407001c000c0c4005581424103a203081041101e51320300282101003040760061101007540c0c000e00300741c000b01001c42000004d202d6034400b1310081f14490150714021300f00403e02c2c400c0340621030252035682e21502d120360046030289440c8100b42c0c1c01c44180d00e400080303c00c00f9081643c1c20354944480b40605220000c42d8492140541d030042d001c0c00d480c54070081808050941c20500f00d81042040300014046802489980050200400a0040110904001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306029001 1250 306027751 306027769
    0x30c08091903030314100501050f0d02040f060906020d0804080318060a0c03064509030c060f0203040b060402090a03050111090916091a042c010f080307060e0a0804090b 74
    0x117051504030310b09020719104924184c3c41140d10910704580d80341d030400300501c0b403401100821864180042000718422101108250654500e583c070180c0c40c50b03070b41c00103c1c0d84100d10720301d0a002c94416030119021074546070007168401012542c03000c083c440c542c0315500c5c1010884462000595070941c14010340c1c4d00d4017030207000b04416004401440d001304444180b030802d500b4407809005040c008000002c0d041000d0951040c0710340010012a021418082d1040403100780890f426498090361000b40303010392007940d000d150480483c4200d80c3c3e9140500c0000e601c2020455404640340c040000001c100f401400103101d204491540c80702900c400780110351b64007900c01703044145181949411594050703400001c885004d42c080d4403500d000c121744036807841150000c6d04a42564602e85002d481450101c2001903000c4840e4007080c0e0340c41601c0d03120340ea40c6001e0409103800400141d0041812a00b140f840f4102c980305079448182142d030f41c121a0390240e844a058030b500c440a0b200103141c41c00074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306030251 1250 306029001 306029021
    0xa0911030313062003120a0e1507080a0e030307030b06040504110417061303030b150a02010c0e0301051501050903101508010605030d12051f0807050f030118030c080919030303 77
    0x410454203000403025164006c88420440d6810341000149400c20250007010b4080d081200391181030602080100006500702e80d008086108200480c140900c1480303000b5001400c0d901850450711803c9040700a48080d02c00c2c40d40c450030500010515560324401c0b80090010104072a035100d15017000844601c0d109038502e089604401c0070414851903940c05000b0701a071515000851400c0701c0c00094030074186404d500034a44020074803c40554055202c3c00252040d0b4868004002400f800c0609850088510714640c0c001018003810950042028010403540242500c16041201d84501c040740c0700c214480580201c00181040081030a2040c98081d141c160b0241070079460b2041c000e00800748101134000d0460783c400001e041000c0810381039054200e07000d0006101075450151594a41290250794882d0908140d0040f0901c0d0501c80e024100d10a50070051408025817002e8890324104002130b94004e000b041904607a0740ea2101d03228201c070740e140054002ca421410300600b1551060a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306031501 1250 306030251 306030287
    0x90e2215140c1c1803080c0c07030317090c03070b3412030c0503010b070609050a0501050601020f07030f11010c0606030f1514012102060d0c020c01050301030b0a091103031306 77
    0x2913544641c0d081d400240d4207825062007811921420b060600740c0c0300d100700c0300c3d10900814501104266104804441840468140c4012912805900307034030351082440c4294154040c9404002c40c004d810003130003035010600409c46da01c0001210046090b010301346c1c3c16501005009100c001c2003141c1124007400c080ea841c0c2000408039401010f00148010301558507401000b150520400519070402c500c44e60348501941d074403103403520300940600300c19a00240903028084130b88408034400618107040b203400450350303044190749860301004d2400b82c585041c104100e06030b0a6000c1480381c080c6030002c0d0b20510b0fa41941c481c240c20010344801403200c4004040d801c1c9150a0200d40c1c904003500e0544400c0200241c0c01110280e00114050005400035000000494102c100410319400306105001540a0b1403036028038000444949c403013400000c094861310004038503021001e500ca80e040c14440e242004800001e140040d2075500103010300324801c4007880c818404142c0c4550f02808948040c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306032751 1250 306031501 306031511
    0x50d05120406092a0305100902030c060d0e03030106020a051c2003160602030105030c0f210328030608030f0d1104030210090e2215140c1c 61
    0x100316a1110018001810b12602c8100310310a10200108880003802c544100e904103000400716071640d5007443c0b105031550b006801a003102e405190150303013080c0b58000e02410202e580c000800c03039250850400040703582c1d601c104a10403541c1c200000e41c0640425001421410213525180c0c1c500710303010081076442a00416902c42c100d4000c4c010f4541200b080049046507442141464914080c050302203031a816131104c90424040c150707000b98181c0e09c09030f0a5a100e0101d4130140400c000102c0e08042d0049803440041c0c0038040d108160050300305000080e02d15185a41e81018400100210281018490f07c0d0040000940610580c0000c0c0b244401640c2420280355005066000310003c0040c43c03501c0e910700c00c0001000a045801441c0c5c02404420311000f05c4200500800d0180207040050f1194008100c2c0c102003d03600380c40c04041101014080021951071005203000303004080c00381903d90280381012642610348520408240408640307030b441ba00c00445d100d0b540d110b802d90005280c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306034001 1250 306032751 306032767
    0x5070503160504051902041215061412100f0212060901080303150a0b040f030c0b19030b03190b07020d030203041e020604030501090c2607090f02071a04050d05 70
    0x101c070000044401c200c0b40010300340e40324907100803040995040c14000078400079002c24010758050300e084030280102198007041c030030000300310100c4005015909140340b40080500091404860565001144000b6038810726035544d507032401d450000d60340b00c0e00c040d008035001c01f081c98000011039200c00c1c03c0b910b00c00396514240d012030300d87c84003600340c101c0b0860b040140310154039080307800d00080c641c002c100c0340c0d038075960390340b000c00c89141d40021118000d07217240000340204bc90b01540c0b072008980c40302102d5405140f10a800600110b00581c0d003500609902e41120441070071b40204841c052010456070340b425070710083c2040005103030b44051601c180140008596410103118404403000003210941e44140001800d901495000034419828101d0392410000007101241c200e8200f00302c529038100580c0102c00d0490060000042d45030f00c060f20810904c65690401003140720b01004c01850900c41c0c0d00c0e50480c006481e05030040c1c1d0008007060104010b010080c60f415404280340c51420a666 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306035251 1250 306034001 306034033
    0x5150c07470306040b0901030501020a111f020307030609050a0b09070c081801090f0605090307050609030d0305060a15020c1905031c181401030c03020c030723060103050a05070503 79
    0x7040c1d80301c0c02070a80400090f40a0f02d4942c003002c0e0300c0000610541c0d59607075a1500e107001c0e501151320301d000120f00044038901c41070009280c030a05114500050b80500000c00204002e4000510006c205a1038000000c0c0c656032038451240510014140800e402c040a0705102c10010003404010821950b002c80601003170b4400281d40282803039060040d88010700c000100c8181c8460b40040060300240400000e000ea004801854244d509a0a0700d011030b81e03550402002c0d0042040e0030350550080700404100b0f80c0704c0c0c2e2205502840041c2a40030194889205030f04415200307000c40c0141c3d01440740b0102515119642d180c9250704003580b00101414180400d0700c410418805070031100c1c80d0044100d04a00840e1443d0452803815028250b881c0ea800090280703280d811213250200340303022201808644039000321591140b44000861800c84540e5500003000314101c207490814002e909089440c0c0350911449000318000d00c0188210205070410600700380311580414801c6d40078040382e88104030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306036501 1250 306035251 306035369
    0x70302070c0e011a070515100f0501051606020c071a090112090c030312020d020703030c1701081b12030d060501080a290609040924020f030105150c07 66
    0x1030304001c180e0b112074071854176500d010003452070700003940d920304100150341c00b60300c000700200c070341101149c0da0650ba100f005540900c03860280380e0307850711065020070100c1d28940040c140b000a03031007114091a9140200319a00408a00c001c2802d140010350b0340c003640c2e22566403420051500c41c100031104030341d81c80e503031407140922004080c820301010552034410141c6c141e9440c0c0441c0b04046d9550700c1c0d285801030040141707455a00109115690710440c415003024154140c0d00440000c0007420130001224003840b40d0341c55101c0d13100040d08003540030140d040c405000340c0310804601140d03050a050015041c8040288015411440d018520b001684901c102c0314124001040110884090340082801d61040070301c441e0f00315090000400802900181010030b800d0303110002140350b44021041001c2c0d224200f081420304405000510243c9420180d41c2d0005041c0b0016510300307003904000c0c1f801c04203550320000c0034001e0700510810401201c40f4503545000c00c00104081c00004458000c1546 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306037751 1250 306036501 306036539
    0x124050d020f06210103030f03020a090e090708010603050c04060b0a050708090607020d0f120e0906121e010c020106050901060203071709060d150f1503020c0114070302070c0e01 78
    0x2d08000705407190300e030340c02129181c0c415031180683c503e9031038003804045182071104500040940405082643c07182c4281c412105040e900c429002d45040b44508110301c002e08020880e00034a1400101d8400906c15980210700c00c00184c03122005010803c011544682d0102d0382066082080b4070900d83d114088452555211171040d85480503800400c0e82ca02030680d0081d00002220741502c00c0c070008200c10341d5007902c601507030b44202600300000c446480040c40c41980103030110700450280d150803060790004428103000c0740c03c07030341c40420641900d071460401c1103040d075524041002c920380c3c207000d040054a4103a4900825500d080750095491065120142c0880001110000c0604850048035800b00c002000142c81d40c4989880c2001001c0d001240c1c00b0045611400050142c01d0662000c01c6070002030408402207a101000c1c0c0103948461a0300c43d5555a070143e41031810341043d030103400b41085540c0143ca0300300e5403608400c44090342c1c000b40d0030036100c480104022910440c8911440b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306039001 1250 306037751 306037759
    0x30f0109050f1c2a050114070318030809030f21010f030c050105090301060806013f022101090c0306140613090311070905090601060509030c010f0e0a080124050d02 72
    0x1c034084c0403200f022055000303402800c049461542d040c072a05401c81101e00780740100800c6a515041ca0507401c0300e0240000301442c080c80400c0c00c020034058941c03564040b880d0425203103407200c1100041030a504c0280c0303003140180c0700841841c0b003d50991889006d4520040d208a119040da25036004141043c45424100400001e0103503190310290410802004084120b524650319414888140325480140c80100825103821541d01c1c011100503508420300c00c1ea6902c01d00590b6024003481c806030070307401045114020030300c0040842c244103242e030041c01429524030142c110b1030300c030081c3d0340700200410010a202091040c581e44100a511002c44813000c0014201002d140564208101140c02101800344400005400000e904503500c01c4c5010300030f94088c1d03030f2265010345990040d140300f0b82c2c26074020004035000b94094560360051342c0c3c41c4c0c10000001d4030040005241042c80342c00813001f90351291100306003e20342c240195005046185255034032400c01002c0740c0c2402e082d00002e486 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306040251 1250 306039001 306039017
    0x5090405100c02010204090c0207051008060a080303070306030b160914030f1e01151215060e041a06120c06031e010b1c0203010e0a0b0f030f0109050f1c 67
    0x40100c204507030545212220800e0000603071001002c0d000350400e204124103541841e00b010030052020842c0d00580310b004151311040252240c04485071035004100c2600401c030304d540492104801c1020f584144001c0e42e002c07074a0b41c1035144c250440800a000011010309040d62420501d4203c5425800d45040b005415201c03000075000910b00703c40e4480c5a81180a8403a030500001c0b190078001582c00da402009010006020a0284250400d4429460594140f074143c0c40007655403ca12103810056032004103000f602c4040c4508911010754040b20000c400055004c107824100c48100e5000c0c0007210080041248a0085901e400c2014a003d11034a80007001a5086401c030314403500c0d942261014115035a124540501964030000d01c1c040010040503040545100500889041e0340407003070901e049803541d0b21594060401c242c0d6282c1c0c04014046140ca003501c080003401f4442c04038030004500c545c081c0c1402818000540051003041d0414220300d650700711542040300f00b0043d985403545c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306041501 1250 306040251 306040253
    0x70f0b07050d08150a060305060f030f1c05040e012904080d140403050604151a0112090303060302130b2b0f030c08030c03093a09031a01061b050601050904 68
    0x124040745201c00517400f0030020700205400d0780c1355100038450401902c50500300c0b0008410141d403003130140148600c0b0780c00400080451074513004c005c540c50451b406c2c41414540c450b184d06000c60f100743c006d103044284090160000c020b50060b03400f0703010140000145001d040c2060b0355101c080c60903400f42480070003066424002040320441d001140c105003540c0c914105031800001c0c0d1031044a00700940d40c1803105001c051080214002c481401c141c4030010341510703140d084005441052015000e244d600c02c7c000016031142c250b01120381e03100c2003000400c400310f01c0410190031000171480e400d81c0100d140190484040c80350000260350050750540c0303a6800c81c0b804448503942000018803000012091060301c0528030040c2d80076000c040e0564015600c0382d00100d51044030841e0366a180196050820400c2d420702c2e4803021040d20619146140c2620b90f1106529080c10030301920304a52524010040e031680b144500c442c600408c41a4507030742c800c580b2007030350701d45044c00750174861009600828 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306042751 1250 306041501 306041521
    0x171c14070c0c03080406080106110610060e030f1204080d020f0a03080c0d090506070e01170106080c0f070503070201021920010c0b070806040b0f06120702011d070f0b07050d08 77
    0x2c01142e0112120b81d80d1900d900b00108400c0083c8500004a00301d030710048400003021500c188208860f2100075415071406e0b4084903503603841c3c1e40712074041c0180e001006c114401030201d81c400e44003004010f5965454400e60720f1a20101a40c02411500031040c1c028480030081900c207080c580600c0c091034180c031060140b0f0503030b210b9000c071415220715006102c2d04000011905902c10a9140c0f41d110100c0010001550b4100f07660181112041410005008d401e006020f41c94001c6000c90402c1e043c40c09806850f07038143d2012030207030f490740c0c4041090001c56078100701c0d01c000d20022442c02c00044e40c0d80d9403488600d80d00680c10810781c6c04080c5403030000340d00c641d038204040e03500005160030500742040050310400781503070071500071820103900400d05e0400a4140b0802503020306460f00c0c00450026609a150001d00400304654071070fa003503a8000c044490780f2100f581c003500a0311070a0310300511101ca90607140c0c4110024081071011802260012030700c3d02c840080d904028256607a681458 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306044001 1250 306042751 306042773
    0x606020616020f060a05060901091b0f0509040e0a151404061109130504060b01020c030c09060d0f0c090c08070c03080613060801060603060b070507061b171c14070c 72
    0x10f10b851183c0c2d42000f011168a400240c026241074581d08081e036203900c41201941c0040d00306500040411184110581c803a00035012440381030301d0904d0801311400000307015112405141c0d40d05501c141c00007010700002035080c855620107600200000d04207100c000c60f2110b401400908010f54451140c030401c80e80078210b40d5184001030440b040d41e65100701c1c00000b84009c1e03a0540c2c00525003d81c079802d139400021100300351100100100712300030903c400c2002040c401418103810110684048001032820921305450307c1c0b02c0d0f25094111410284814110340394095104200002c040a10020307a8002c64080c0d24181c05240940c4107584481c080741480e1110200030740014540800000c2203141036100c002681c203555010b2100c0d90b510304015480d40a440406015600b01c03039001c1003040d005550b110118400c3e842030030031851654540942c070541d00714030728000329800203500220b04502c0b8255410841c44003400c0000c00e40e00b01c510000110020286014041c0003100390051003414000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306045251 1250 306044001 306044023
    0x70e0c0403051501090e0d08010b0c100203040303090b0906100b030705220920040e1003120801090c05070f0303020a030e1c0e0108041e02060c030a0201050702070801060602061602 79
    0x1121519041102000d204503c24803075030703d0080c640001010591404150075001480302e039240f44659091041c4000c01e5402415808214820f282c03041c02503252600155220342c0c001d45000584c246503003069000c6d40d1008091304142e421a43c204100030740600c01040c00d8922040145449666852080e80d09104030162511a208100c4051070007210401d03d05c0191044014184028005d40c804444010aa008044240f0509200602042c0a940110fa0b4401c40205444c42042e43c0d98403411140d020040508000951040042c04151060f0140b80004841890124980320f03490b01c80c1a80c05048080040800d500001c91101c1c2500c242c02ca20a920001d03c251200b0114030000040c2c0b0304220700031080071401c008124002c44d03004180c0300740f150350440a04010a280a40c2465022410f41000c1fa400801408005036a40c0f0401c0603010386d80da5a00000b038107042c81030002e40b411a0aa000c01981d038100081070041c5c51340440d00301c4e000038400b10303020340705c0c12042000d904003010070704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306046501 1250 306045251 306045253
    0x90f030604110103060b0406050409090204090f060207020f090903030402310501091a0a060305090703210e030c0f090615070302070609050409030807050304020f09091011070203070e0c040305 84
    0x180070034005900c0c580d192214090300c00700049a0b540031290003034001ca01c034503804101c040c0810051007145800c51b03450944000ccc0005299a920b69841f400922403400507504141d020a0241c11820001140050ae5008491201c41e40c6850782e00c09070f1700d2000810007402017a0810020750408100001e5040c1e204503411030003213000c2c0c6004000001d0100340300e1044454103000000504d40301caa0305482d030b8184040d00507500a0304000060b40030301000b80c6102c2d100d2281c0c2c4070000121b00458203400081200c03424240b021000130100414080c0d0340301034907100f60007100e0800c0990b5a42d030022410640e09503499041c0d5a10640025202c0542c070203480c4a001002420340d0405901003010130170f548040d00c40000840d121010312048941d8a02c000f008105101e001c544041d000b040590380c420301c01081030b200c509504011032015103044e00c01d44882d5104049038000300441d4007412006410440800c0d00301216030700000d40e68441480342078040340794100403030302d940740d001e04540207183c02c24 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306047751 1250 306046501 306046513
    0x30209091f0e1f09090807020d11090403210b06090d060209060a020f150108100e0a050f010615110616051204030c030906030c1e020f100c1806090308090f03 69
    0xf10420a90f50180104102d802c0e05100046001503151203040d88050f040580a17003000610b90902a079034242845c241c07812040e61f51b050646940d070b032038030718400e51180e55222a540261700d8000750581080c03030040c180c2d5080c5404a4044d880b40e100381c6922a0084460800207030b020b04140c0002d2183c2070034150814030004001d401a50002800503014410200301d48074550743c06002c4034010402e02503000b154120a08080640005800035040d8044250590b03811600c0c9a4032541340842003030136180e0594443d1002c0007080c40059014038480781c6420700c407090000c0178074404e0b200c2034000d2000314036015000545510b030380f0030400e4a555041c41042c14005003031604019050703900c241d038110000707008008042482e500c0303405039842c800350f00e80381c40c000003c0843d25984162486201d4004512501503509a170702c0d001c02c41c0324238440350130b000025072207a500401800b071100f006100303400c9200a54100f218503884600001202d030080007151f164144000060040940c0d8030401c2c1c3c0c50308c605 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306049001 1250 306047751 306047761
    0x9040203130506100e0c0d0b0303130609080f0c120a0f0615060e06120613060303081623070804050d11040506090714030604020d02040e0115030209091f0e 68
    0x9003040101070140b812a61903039565030054001c61a24081c10500501311004034800049007000341081c1054103801007000022440071902c0c1d41c121180c108090701c0318020403c00310750007240a001400020014180e000060b0703091503034400e045140640159000b00c0c0030b840e600802d02c100e014041e44000360010001c00e0342014006020140c00b144e0900844c80c00000705140290320411a005000e01111f080001444106007403282c000e1005400c00f018100f00d003884650340c410750024500c0380d02c0e031034054180741840310f011203406800c3c98144044e801c00e1401c4640c25401101e0f003070646180303c9581d40c0c0340c0d01e03104406016641c0300c280c11020001901c0204860121502861002034800700050790b20881080104541529081d0100d070400805541e0054040c005550029002d48090319011a000b0f800003240d2160307218020440408006101500308030700514405101d41c07409600340820794001030414030010f0515800540d14030130220503e020620700c0c400904070f04210300030601e40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306050251 1250 306049001 306049021
    0x6030607051204141906060503070e040f061b0c1a06090f100b2b1b030207020303130602010b030f06100512010f060308030105190b090103180605010303021c0f020d030f0209040203 79
    0x44440480b01c06d424480045814100000d901044a00c41c048040d00b688071034032010300f5146006030590300035032900032503800d422000c0c1c0301d41c0309d8045907511000c2807825424801509600d121891780355008041c1884020340d100c0c0d80300398018100030392022181e220740000d00080060f56020704a56140810786401c08110380b80601c10341c40030720401171410030b06030b0428011900d0004d082d01090380c480102d001182d1180d400b80001601c0030b412a854000d000000140c4610070340d00050040c0e4480303d19100c54201444460b02d00c1e80010018405402e10503180c1259030001c0c040c050141c12181070908505000750040001c0b1081400200410340c2c40381407203601c1703070f009000e03c80c0103104601c080c181c0c0311010709513441118010002135007841311400046000d42862901c01c0e0600c000d000d94034001c10701506c03855000714400e070001c0400e03c29010201003a00e2000120005010f03e64044260b02031700456404184041032500082c41250f10000d42c0003030041c0c42e01c10b50400d00c084100302049507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306051501 1250 306050251 306050293
    0x4050a030e030f12091302040b0301081516031a041505040e03040e010509060612070f08060402190c02011e0c260d020306040f0504030302120603060705120414 70
    0x2029994a4802500c000c05160fa1070412190780d070103d600079400700c0d0340c54804801506120300c00420383c0c21008621490070080e030f003080e041500301d4000000100641041042201d203c0c24296a01010910b800015a40080d000411120900d61503032801d07030301010510000510070000600403c02c00b041c485001c100c40040d1301815020350b20708007078401016000810380f011140c1d42801c44485a08207030600132420800b5040540140050124149045545400610070103140d660010f06a1103144010480e400240800e8000c92040100015500001c406000f1500c640d0410000c00070940c0f0041b501e071114104900c003422854258440b00507403040070190402d0086058010310364800c8400402201d0041d40c240d41c0e0402000117813500492500510b511500003080081c1e203003603a0121009130351040720304500213540040c0d03450803403c1d50f850302078200c0019001032896103003282001e48184241b1803410394030712580c80000c0030040744d4681802080380500c25a45a064504422144c05c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306052751 1250 306051501 306051503
    0x1c0305060f010801080d031805150a051f03081b061042020109050a06020307080a0e1b060705010c050301050a09141308070f030503180601030503090609031504050a 72
    0x30a44548030325840d0711440701c0318140c0c2d0f80b60014044491b0a00d0081c1c0080c00740c0c08000080c8198880081c01150040c4071041216005424210041c545203100300101d8200922032003851004d100261100f91211113850181c0b40c2c01186640d03a000d400390b07078030808620006481d429104100400120440e03422a0714100d44000440e040c0715200d94604800783c00c07005082d55841c0e004072241d0a01c00350b5100d04241045403230700000441d4031050702c400b418031030000c400361421030b0008140300074607501416459222800f20303003c10008803100c1c2d0098130344009640f1107c2c8000f1040520440d50380e03600c00c48070910740c024001c00a401c0c42c400b029100d074000b449010300c240c491400020b030441c064000c0040c0f196100031200403556410312001401071002400707844d140b10900c1501c00103180c4108103000039000f40c4070719460303103851104589089002c50342d2400541014004000060000040c0d458070201150302940318080000400e19000d0003100e0354110303d00d10700c140824040d0108807030641d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306054001 1250 306052751 306052759
    0x6091a1602010606050f0702010305040c08010507031a030c0d03080a1104030501060e060307150f1412040c0801230915010612050601170f090c040204061206050a0509181c030506 78
    0xf4540c3c540781501c05015112860001a1041114600640c030a5001c42e030311501c914100d00200781c48405090840c0d20403506200400c1d40c41460040916500e00150320b81c1d90114000d0507000702c1e03080410300c0700c030035450000d040c1300c0075401261603880e49070400c1100440071190143c0713465803070802c103000c2d040610914440002c00c3d00800c02c2814007203145c1003a00c2119003104400c0c1e1070324038210b41c5102042c05490420913440200b80a0490002c02000350212083c2800111300302401d2079000c0c2d12140e0b01c00c03045680b40003803008080841e518a100c000c0d46010707884049030745103605507050101c2480c1c00542d8852240010803402d03080f8480c50900c1c0c84c2d5410400440c0c2d0b81000654081d0034101400440d240c0150025040a00040c0116440030400c01504c0c0010b00510100e002e0780c1068004c1c002003840c3d40300c9000002e20a00c1031000030001142c403000d0803454240811400100a4014121202c401c0500c6042c204104588240d5420f0150181d0303d0003c410300c001c00802040e680b003031003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306055251 1250 306054001 306054011
    0x5060a060b040803070803060402070b0a090b010b180f06070204050f0a0608010605011b0501200c06091603080c0c100302070209070201050702031801030915200c030706091a160201 79
    0x180306070800381c805840c8050001c61078884240c031496102c0d00003d0a55a019400300040d100049800e87c409005c3e07a2102c030081006103240c60045001d510580240c1c007140381c1442800c20400d01046046011801501d0a1141816003c0414028801c1d40f00213904941000107001980021142c80ba1056070100001c00c0800d85805000b82a902c01b4860503000940c8440700700c0c201107440f80109602c1d44110700018281010f20b1460b18814480c134001c02e141c12010441c240661011310200d540800440060259a080224a041c2c42c003100d0001407e580070100781611801c80400682c00301e44001400048191600e40c001030203544070348001c0b401089144085030f106801400f0b454060030b4960080c0d4200180c2d0101ca90341d00c10031183d0740b070400d61101c1d00400890780c4800300c1100c0c0000d0070408110347e940c400f4500c1c0600103900d03510460020811104c96112008816900003c6d8402c4010990710740504090100d90110b0702c00100100c0c40000340012442541140700c03551070342e17400a1103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306056501 1250 306055251 306055259
    0x20a050306031002070f030e060c010c020c10171b040305030d1a04051005060f0405041a09070206070203042601050a0902120313050d080c120a031409100c0e040905060a06 75
    0x40c0e0040e14001031040004006c0a00040c1c01a4064155050054402c904000a010700c02c2e080d550215a1072001d0b8200c000c1400960400308000e401c2d0000302c0c10304141c12166440c01000c40704e00101000d40b92003000c0280303010728403050300300c4000b144c0207400c40392561182c0030094001d01c101e0b0680c0340d032034201015808080c1418081c0034400c00244c03a019910600e05014403140703501030403240800c150100030110b00c1c0e503280d10400c00540303400701d07103200007052540503c1080000030b4041029540940c0030021110f40c0002240d090f02c40c4a440002e000c403c20031102c1c50001d14190ba0a00e950900c0100903212210364040c05c100b600131602444000c2411111980701c0c4038890100001c223079041018800c509181100392481407040051a140a003000806410094240740c0c181c031000740003c001c400c40354940a00c2d41202c0f50100040c500d400d002008594a503444001012800d45900c1d01a5505005c0c100160b000480a4030a021080c10f900c0c00c652108001c64a1080c100c0c94130324081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306057751 1250 306056501 306056533
    0x203210708073b0d060207060b0402130b0904150326270607060c080a05090309010f03050403021608070e1b04030b1003230c01020f0d0e0310020a05030603 68
    0x102102542285889031000400f14002125a00700300b801030301421080145980d02d0300502802028040c110058440f4a2481c10005440d002110103214900501c2003414047c3c001d5018411a805600d12551300d8040b00701190207420300100e80f1402d201e1040c400070070f20580b5151605244420b000b20f86002a885072040464082e004842c00f0460f80302484900c9180300d40040003105000800003030900c80e5a607501016504032440c02c90002c3d4021b0280b1a00001c64024a9007024541c2c0c00b0314140305c440b000080c1040000c42d244410503480d4004a070030b06009000034501e0010351180d0045981e20740345c82c15640c000b0b51081c0b02c400740100001440a0019900101c0e40318a1000072601d06440c45c0c9850101d0580900154480c100d4890000b000410200254003c0c07a041d810b6078490030390445c42c0301d0920425454450564003d0140178800a10200c1c0b04c1440500c01c3c2040c2625104201c080b80c0b801181e1018031000074400550400d8a5801602441c030070f0030114103c688030100320100d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306059001 1250 306057751 306057767
    0x601020d0207150c03050c070b07050715080402091503060f07090f1208070503040806190608032a03070b0c03160504030804291603021b091501020321070807 69
    0x31070f884002d540e09041168803806501020781c0c040d00d06035040c032020989860924010341e03c000040740c030005248080203401e1080000406070004514035a00803000c018010f03503c0180000d2107800c6090028008500c0c2c0c0107042440040901101c00b60b14140072440000e400c04d80e500c2001c0b0341001c00c002182002c01100e441515001040f500401d0b0841c1e5039840a40c229850440342c0c0d0100344800300f1604000c00c14144640c4000320604440c0703088103080800c0b558540c10079600c54004000f22581d00010388001c4c1000c40c05142c0900700c03902101101c40c2075018216008101c454104280319104944d60050b500031a88000d0628030031040d0b402c261031234400ca210042649a00380020860f40aa0b5160240c1002001001020407070204001d000a580b0103581c43c0c020500241580c420325904100d455400c9078149a0815200041c100207413032004010404811a03441a03a03040036039100388241c1b40780354826048001900706520303219000d82d0040303d1410004a1200014211910070b800ca = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306060251 1250 306059001 306059009
    0xe0a1112150c091203090907051219020d020d02040f171002070203070f06210204060509060c0309061306020f060c030112030e10020d1b02060f0307090905040b0601020d0207 76
    0x2451141c1d000080140c0c4001c0042a6110000040c80b01c20200c0c0c8540422001c402c1411003d50b075551070341c0c400c0015507100640703c8010806c040c4080a03103a08003283d8607402c45070a01740b00032040d025251480103071282814030607070280042000e01113154543c0280041e2454a00c03c002c03c0b6848540140d000310b8402441c2a842d800195480c0300d0440a50080200c14001343c02c9c4c5000039141c80c40000c040c3e156602240004000480711341002c0c043c051110300c0b400802070154134041c6400360003440341c0a0800d50600c54000090401c0c0d480c1d03002c2046484241024082e1501d50404c2149014140711610914025008807060030400303090106916124a425494503400e50f420052280482500044103c06100352000810704036078a0b20a00900400300341e000306040b01c04450010110005505d2651001c0c00c135089410050307440358103427410080c01040c003d42b0b03669020422594660607034031200d602882c00051005000041c1c008502c03075076082e02106d401c0b0701da2003803c03aa00d14043c85 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306061501 1250 306060251 306060253
    0xb0310030f060b06122202030c040f0b0406030f0506090d1719110301061d1f050706020408010f0b061204060506040b19030302070506070308070c030903060e0a1112 72
    0x44280009494108200507490045030009441d00803071000c02c1d101d5022080703540c00d0307610301c0080041c17520030781100300401c1c90740d19154459043c0590100b5a655000f000c41446941c8928a0550055440d070141c9501d140c020000d0001c0ba98908214020a4134200162424040c410000788100800104802403510079a0b0711481c2e682c4000004007560b001410041d42d07800d15aa070341d1441a02070141c2c04509140881055a0b03514140380a4405000740740c2a00c0a038141f208110000e540b240041c0c0b40c0700201c5030200030020140101128640f20f001c4008105910106010030500015400f160a5145001c0b0400a01080e50100b00710785c01a2414594202c0f250700018001900395004140c11083c090000710783e6400040005122001960400000300e181460400070306504005080041505490540c41e000d101d84008081e134034010180d10502469503d100304240c802c0e2041c000545c1c00c690204880a81c010f40c590b1600301d01c3c0d5054820b1105000d11160900d00070082001c4040040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306062751 1250 306061501 306061531
    0x705060c0418470301091502070507170703050601090228033207080c07030c0503091f030c030e0316060209040e03040602010c0305130b0405010912030b0a0b03 70
    0x400d03a07002512100900c211010380903071150f2241112030b500071240d40c00c107040382c00b25101d41c00751041c0c280080c8540640300383c2c107040001000c00c00480348500e4481d1204800759903100b4900b01140b0740780d0603503c000c0c0c4844003504800c20284004c1002e42c1682d2003441910226640d4400c404182c1c041c50034050089009020105a20f6441041d4585044400d050101e010080c1e410325075040e1840620328084034442b10b0010225001400c035071031380104282404032044c04c004000981c28010640001d080c0880032101d00181302c0c0c10416640e0300940206045000c0c0c0d1400d5001d4910b1000314025008207060943c4020700f02d0090056400070040d8a000750304009440e460a205c1d203040d20016910198200f00140441d2183d018561000c1c5d04800211f507160301c0c10f90300a00b140c15004c1da00041504d488184007000072012411303000c0d0782d00078404c01c5441d03c1e01e0a044c1c0c01030034100c1c0020030400400d01d1038048590140c006120706013040310384540b503035a1114a85c50611003150301d104004005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306064001 1250 306062751 306062789
    0x30f0524010f0501031a0a150809031e03040807080307030204050102060603070302090a0b1512010e011d041101110f010509070f080d0807090305030711150702030c13090501050c0705060c04 83
    0x20790f202c13400c0e01d03280300000c10f9101640000700c0c05481c0d07e030300b0904a4030080c1c014140da00e0f0304041e01b2a040304c0150003c516194024540121940c0c4641d00c0f20404400040840d051124200959282580120002e0b0307a0341440c0001030b00a6003d44907050260099500043c001d20b4003040302c7c403c507600600101131a565030744a00c0010018400c07200da00c070300a4458030030200c0c1c2d010094a03940050321030003045075044c21074014480405910607d040b4407800c22100580c0000c2020542088d4408001c0c0e0780083c3d42c00040e00d8004c00060151048e20803403102400e81441508190b00900040e819203200d43c0c1c56042c0e140002034680a80201648a07071030800b4141c0c4030b81e80d0a41c1c4040c491034041b00c9c16480b03584880c1140c0c1305503012b45401001c03801610700e80c81d00c100c644c071521401800e058540f00c55030b03011980b41c0d018219180d220307d086424507249252250020509d684d4050020412403809401445072900442d0090356240300700700010706500a52002c031000c0e01c6010346181443d07800c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306065251 1250 306064001 306064007
    0x2030306180702070e040534090906021209060103110312120411150405040605060a0219030917010204080607050405212a040e0d050702090405010204030f0524010f0501 74
    0x701510490861180e00c100060ba14842d0001c240514400c901038803000502030071144000300441c00901c2c100d5601032001f10b1211a0740d1a60088940300100801e565103941070400003802240752943c4050540e03010017581240103c3c01c94141c1c0e1040894010520324407013450340e101c1358144a071240c021b0402000c407400842180160307029105002e020108443c460119003489241c145142040c0c00124023404140741c00d00403d0040d01064a01905010080400139660708409105640b552001c4d540b4609140c410300040018055001b24110084086845a4000d6006115031010381c090080890590f904c030740c0899040f07440040c0580301c40d040b01c01d28040840781e00440540c1b0341c824aa1031b2041200c5440c070900b040a0420f417490300d450035440510080c0c40d070329485000c00b508002480010250001c05803208203405503026030480c1c1ea00e24000d030080c8110342000e4004880380003a075042040c0040c3c507246003c05c408220220401550030054548000e0003900c404004800041c85a544 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306066501 1250 306065251 306065299
    0x18050a03110f2106090d170711030423120601170a0209040c1706092107080c010507120c0c080702060d0c050c01061d01030215040306050a15050102030306 68
    0x40200002604040000040c4600403882e070400308001d08110a01e014000922101c5c0d0300c01d4440e0f02821020084020051400d5100c11440c00182c40301c3d00407604484c0300d101c0080282d502d5008984d0780300d40b21014442301800640715005e01620504d50400c00d820101104690b180c40900204140e0b420002180d5550591403201511131292000b03c01c05a0b403442507a83c01940169011400c40d4140000031508100070110a9080c0c0e2040061258401c0c001400c08951244000d242c00408104150340c0001d02c10715001400702e01001c100c6800116040d4400b07030040b801c50320f400d90b0706603862840c1d00035141810b4420012514000000700454000c40003456142d100612140ca480c0380760703111404039040c101c1c28500245010980080303040091150390301520341103030130126004200844041072141400000e0041521043c1c101d400e4245005680145611000070300c014900446014001c00454103e81889407000c0000100d550010040724001c4001920303c1b08051818451032500704 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306067751 1250 306066501 306066533
    0x160807050a0f060b010e10020c01030e0c0301060b04050f031506040b04021204061b02150613020f03160f09030812250201090501050105010806010903060504260a18050a03 75
    0x8003907120220300155000b05680d84040c400c1100140841c1c0040c00102808001051140249074010003500d486400060284044809103000f0681005401d04a42400c44006c10983c041d03086c01400310305503902c0c00c090420380c0d00c01c0c0e031440040c034039010425590300c0d8144c9048840300c0c840302c089101810305030801d005516006e0405444d00d8880300340300c4a694803c0340d058442036607540c3e00d1103c000c001410400e03c1622440248100000801c2c1445400f902400702c91007400480500704c1d140c485e0790181c480440c0107050058482c600b00406a0400e18000c10502c0025014540720403028050950b50080e00e411150380b900b0015450504400ea0034040c018290100480c0084031144208000c00711910200b030740085041d48e2145010341c00e60310181c11050501513901c0400005036401b81400086981003440880d80c0d8031982420015040c0c0c4450f1070341c3c400e00d090002514000c1c0c107801022000a00d544080c03080c600103280f0003200c1c505000341540128070782c10801c086030323007034130515011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306069001 1250 306067751 306067753
    0xa12060506010219030c05070b0301080d05090d0602030117120301150e03070b0c0705041103060105070b0705040801090f120807270810060812090906130e0604030815030316080705 79
    0x110a13a204071120b00c103030031000300d000031410100e00c400c00c0828040030b070007031035541065415541480c0c04d40fa1107140f04c1d00c00d581048000b040c81d0140c6d03601c140749403600981140342190f0f00e5071108110f8041654040c00c1608034851402c80211031b2503048103c134102d504000a00c40c409000da00d04407038810000c40c2c01c552600c9062000319070060480010420319840400600c04240380c00140000d03180043c4140d040040305004100b040d90b00034044130700e0240d00c4160410603070351b0f4417420f44480c05140c2100300d45620f04400c00e8100b02d030340e5115541941c0103a4440c1c1e031442d030324501200c0a000403034500c070006a100d1000010300c4400d000c0080400700009254003210f031030300c01c510300d08815111450700d1251201c0b01042021801d0080d0800c040038540200d01d000c10000101e0703800c1d40c0c080c006030300031401e80c282803200b85000c0e400843c06442d11300c2138071326605282c140140b245c2c200340d03410048583c40c50f030700305110302d80002103800e1031155071100c001c03148482d19801c005811058040e909 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306070251 1250 306069001 306069013
    0x1703130b07020309030d080601030f151e1203050306040b0306132402030a0209010905010c050c01210216030207060f08040807030912050318060315130608030c060f060a120605060102 80
    0x5e0f5418041141052441d43d83e503803151074a5000181a2425042d10030046861b200703504816070340d030f10540d8040d6082e0004115003030100c0340c000b4482c3d441c2d5502c10b440288911100d00100369000c0011030140c0307001c030360510858012208142e210a0191040c0b66401800300403403001903107070a0504c2d00c0c2e51a81503c42c8030704881c08600c1c0183c1e80220f0f0701d070000d1540018100000e680001020024010a04e0074100003499660340c80c0d917a000000603581401711903581842050707a808100b00707034000e00840664480409045104c40c442210720104c4c0540260540401c0c064414600743c2c0080e00c1d2a03940704881d845a4442294550110b41c05500700a02083c0125040620158a0450920030801150380f111020b0b502c09240d200b51050303c1c400d400420a1150325502641c0c0c4c010410011079641e4442d515070b1644d03800400c4030790700c0110280004034580041190102c1d4052280c160401c001c0c9841c3d51314820803241c012980182010140441221801f00714507600007580041c06004480d030b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306071501 1250 306070251 306070267
    0xd12021006030606030506010909150b06070c0b0310300f0f05030d150b030604021813020d110405220e07090603110901060203040504151703071703130b070203 70
    0x81950082e42080c1d914a8031210208100101045a2401002080740811000c40c05584600c40020341300c6da0043c02c281c4880d0304003c543d40f8401180da60560248a10340d41954505071003c0f40d80003180d0032240c00c01c0c000c0380066540b60840420303c400328101c0144008807180340c685180344840020a9494103024140b00700000e0f858428114228080c500858440590800d40c00a80d20952030500d814664020200041e80808040c0c035000071044902580314000d680717207194130b8045039800d140c2c00350807024800c81510047e4018206e411003e80c090005408116060406101d507100e19508000074070f80c3d48182901105c0c0282c5081440c4001046610400c002d20780341030303002c3d008860704603a100c0003081002901e074a040400541aa5100129850404081c0d128091841075600a030b48401e103802a4645800180d806810040300d150000b07000c04158503603a8010b08000c40d104500c25154000606500e000c0e24480c481c0d012000002429995881d24040d030007501c41403c0d40301c207000c594 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306072751 1250 306071501 306071533
    0x1302030303060409061b03020415110c0d03171801060b0405060406030207020604090204080c0f030607020a0b071103180102010b0315040807060e0a12020105060a0503071403070506071407140d1202 86
    0x11106e10f15540250f1100d06040c4000b0311250700d0002e07003007444003c07400341074010001b00304042e00860450b1581507032840b6040980d0200d0030b0154030502d100102c001c0041c400103c2140c00b0000b40717080300800019844013403282461186018490340074034103000800901e4442d4006002c054030141c495810076585c0c040b0a02a030304160401c84a90300064901d103241c0c01c281601c1603041c0c0007207000b4511810f000d40007940b1403142c0d1402a1400c0d0560000501c02c602528106110404005c1283c4d6079201116244040310510602c140c01542042e80f510514500055505200c034401012020f01e612070b5076420029600000044036420740311001d001e41c1050a001030b078070050203007a49114503ea242002400c40d00001c0c0860300c1520390308428411501c00052110545590980310074503401403000003454a0140e41c040c80e4003840004406040120104102c000483c2d004100c505140e102c803409050144c40c424819009141c1001d4280480c5c00c000e4401038058140c01903070740c4080029a64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306074001 1250 306072751 306072791
    0x11090d0611040b12060603010302091b130b0c010c0207061d0103060905010608060a050102060c0913060b0c0f010605010804030e060d09021e09090607020319020c0604090f05130203030306040906 85
    0x10b86154080407800c40450401c1246a030341c8040e01b1128a8078543c11640080c241800141000070600030240d1800c0490030044100d40d80c11103034043c2181866681d80424501e0384c4401302841c03940d406c200d0076000d20360000801c1400c3d02c205450384225049080803102e404c1d8480502d03503040684851002503540114440c01d8060071066031a90070519000c01409184865580009e045602c5001048180c00500098038106401220000840b030b0701c8107184400b40a064011000102c000540c1e1920b501001440200d0060048000c2c01440d0791400190303030194080b10007174081401800c22034060320f0284020321200f00f0041c000a03880f402c4c0d07008105010800120703070741e0701c00850041981c5440e024000caa4402c001c140240113a2800740d81c02516400b505007030036261410311004140090080c88510851305000c0c0c1626115692882e0070b07030141043c1040d141f1a07a2400020418400007000213090307580c4c002d0011861a1030b8403040c0310080c4485901903c59a58410700703650764181d80c03c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306075251 1250 306074001 306074009
    0x5030403030f050f01060f090f091109130905060a060510050a110706181a0d0b030f0607020a0201080609040521070807060e0607180501080601050c060406091511090d061104 76
    0x28a1307166041c0000a031100e6005081e030402e01c0200102045003501c4840054181e0720b03d1900498001343c4041039040500482c80301a0b4020700000d125808110581d110410a0380103504641d01915803034403600840321680190342d04100451a1411814050f01c01480030300c8052030032002d4850003c5480c0e0400500e604000005500e140c4001248501b40c0c0b9040c01510450394184052841100d40080030720644070012a4503485038041906a0b4080c8000034013502c03110f040c6e035078501d001d02c0b0003529403240d18001c0313011490b44008203040381440030515100780e078044d004001113103d10580c40d001c0300185d0212440700c902048003000150500c00504000351203600049040e1600500d580e090120052083c01041041015021031402203464902140c4013820900f215440d05401280c5038441e0702d40505031449008107002c10020960701240c04a170060308a444c440b8511203410050395007000e181c141d032803418800c07050703107242c0546c0c07040d2503500c100000280f50038001b640034801d80181d80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306076501 1250 306075251 306075271
    0x70f0f0b0103030f1b020f03070b040f0e1e18010e030c031305010c0f030c32010b0102010b100315030209040c06140a0801030813050901150e03030a0f05030403030f05 73
    0x401c201a004109240b82081c0d60624140f0400c241503103d1900b0740785c2034043e1080291140b26656030320305004000c0540386e500d020725615034940c0301d04003d502507441900300e101142c0300043d050600c1d100c1820b100c1909602007036000d40b900c110421400d6500443c0004a5585000300001e1520400081c440303035000901135901c449010166190000c8aa07202906000d1a95051000560000f282070310b95641411b0442542140c1d04003054120900c10b01c3da44049542019622031843d40344602058240c003400130300107181c04100480c03d9599004807260024039544040e01c259000e60007541641e01c150040704030543e500c0d000291080b00c15903040e0303451168240d003071000d0b5500619500060b1840d102c0e4502c1d101c0c84803002852841c05110103040031802080781e07900c1034450100e0400800f401000840b42e5610b90300400901c0101461072404104c0ea581060721600f004019520300442d03607101c0c10346036224400140d5055100905c114100f42e681d01a800c6046820300c40c072802484144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306077751 1250 306076501 306076523
    0x9080313060509150315030601050301060e071d0d03030f20091201020c010218120d14030901150303021c03060302181b0301030b070e0102061005100201110c0c01140f0f070f0f 77
    0x14043c5400d288d0186c2085000ea410004e00303010342c2940700440c0d0340150a030301d0700401100c1410403903018003441d4460154003c40d1105154245541600403101041d83c10748100b02c1484031100b80c81c42e501d002403600646400611040c070480c030344154003060444910002520305030a41701d04a003240c0c0103ca91845410014007503034010b00b0189a10075121107a44014001d03803800380005803460181078480807244030000002451038070203420111000c044400c43c40d00c000c1e282d2501940380c5051840030392701c007802030320300b00402846801508103c0750007604103d000840810135004105008041d04500c0150340c0b04410540a1080107500030b40c050480320b000342c2480ca000a0070703001c060a00504561100050007181a41700c1100811982c0c22280718004c5040008164003408202c00801c0e4550310100c0c0301068100c0c003289800d500340003680c580390b00380a40c210b202a580280c111000c0d260006100c1c00d050213503414010801140145090702ca007400c1036507400c21617500080200c808541e95 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306079001 1250 306077751 306077791
    0x1030f0f0204032607033c03050405060c090f1003021b070609151b140f03041a04030305180f0d030c02010f021930020d090803130605091503 62
    0x13060a201c2c44082c3c0c4482c0c501d0003100f034030010107441015491350600b00b01ea50300d000444500381100003403031444101d00d000e00da480d03da0240007484215001d41746800b52200180d200d171081d408441c0aa80c00600e1050b064908109021042d01600c1a510074180d081001d03910300280c01010005104c44000140842d5003031104c01000040194001d42c000094a0b00b1000300f2a0811104419824040890418011369041c4403468030700300c036941d80340c40c05a0000540c8141021006005889000d03c0444050101c40c01c1801d40b88158440a00040c6080c494a46a48040d500d021400b250007003c0b091801d1203007002074050980c0900032404500c040c890075045503003003a20080036240303d00107801d1409042091204142c0642d20003003500c1d006820f081d00340c104140380803000141d03100340c0d0b9900b040442e2002c0c1d91404400d0104021454400001481340c400004840c2800d905e41c030850040f52402170251075079044480c051b584002e424504100490300400038510070540940c64900b98103a03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306080251 1250 306079001 306079043
    0x15030f0e19060c08040f0b070e0402130f17071a090301020d05010305010506010e0a06200a06091407080705040f0b04050c130803030f0c030c070b09211801030f0f020403 74
    0x80c420f120800c0c0144a02000003149039040b141802079000082c00c40070380e0710740d07008880728070100d036085501c00d00c017055440c1c03c00c03aa890108155030070341d085107003801e441d40003c5442c0c010000004007280c0c030046090002201c020a40020189184852814003a8690009003680c200111070030101740d9442c010014800d090107090740061b401c0c20302d01c41850041c0c010405100560140400344154250300752003100d0b105441e1100541864182d03952501c0c05d10380200907111500741564030380c0928580030225940400c009044444c41c2c8000c10583e4900301c203005c045c0c000030090f05006543d0300300740b001c10740f100c2c002d041c8210214030081d0f079581c5071095840240f50968200d1541503005000300b05d4800701c1c0c103181070740003006901c10030b0b100d903904401008c007403284a0000b00100c500d0701c280b0546031030002c0c085594041283c0b4064080761300f0300380d040d51406820101250000011905600d55002c0d60029168600001002c01d011b50708044240680c0d04c10351007240c044e03807084010410081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306081501 1250 306080251 306080261
    0x7031a0a06090c09030b1b030c0403020901060f0c030e0d0204020309070e1b070b0c090d0303020d1d0606010c060609060b091201020a0203070b0a2702010f080115030f0e1906 76
    0x307201c000801206504420003007a0003a00e0100402c0c06c0307000c4004c07070105540303180c000300c5401c0344000c1c4039645d1074080d05071a0307190428401280581d40810002c5038283c06110400c9a01c2119a202e284075010340d20f084542d00c4080c410640c00c94503044040c401740c3c4581c00110300c0750100200030403055141820760b01c042000208840b103c550041d90700401c800c2d801c011115000d411141c5a4560384501d000c1d198144211562542d12000f148142400c25806030054086542134490400929400307854240c14968030b007500c0b19160304101c0024240d98041d00900c0400d42c0502c1c0009003e64803042c05d10300702c5205400000c24040041703100c04540c507025540845281c2030b00001d600705442040b010f5682c1c020004001c10300c0281e00d002519440e02588003108101c1c602075034400c0030070045a0850350f00940c0030103a000a51004480405900030388004d07048400c404088481c02e6600c900c1100203094500051038a1a00c80158038590301d0b04100c034200582090b48041c80309521850a001118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306082751 1250 306081501 306081509
    0x17090a0302150712020c0c0d0308041a010521010b100201060e061009050d030e0a03060207020f1e061602120705090f15060a121104080c010c080a030207020307031a0a06 74
    0x54070001c01030f006a100300d820703c0c0401343c130101603200e54001c6c0140b0f090540c2d600303050340c0101011845100f40b40e40454520b001b180100c480c0c01035170807010558007a1078000d000e965009251000d14400c0c031080401c0420360003094034000500110440001018130910004003001030791115003d0240d030480500081e00b0020444080683d21000c81c3d0240c400d400b54400d05205907012040312082c540110754200d091080200121030032505d900d0200000d420035038090340500e1700b50940e0405401d2060b00321280c110f1880740314100c04649000c1041a901040c409083d01130510070f2003005840b03840c00c0030b00619403103014100542c108402d00c4000c90008015000a2020805208003a407490f20522010071040e9507490341c0f00e2004600740d80d10004180002c02003458071603011003410549000c0c000340c0e0110303c1030740c0a15400c9401103502401140700a801c540301003205000e0b25000350f004200d050b01c05000d480a859980d00d40c00d988440c240000d483e8866440e0802100900174802c84001e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306084001 1250 306082751 306082783
    0x2101080106080102030f0610021207031d01051c24090902040e060106080c0706020f0c0a12020c010503010e04060905060f07120504080313050304121b050109051c020117090a0302 78
    0x40c1b0340102400501b4001a00640c0540303000072009255904c02d121104100d00366002a030350b601c1c203a140081421581c0700034a401000e54183c50165584103c088a010b82d6214440416210801d12480010240865140e08030030740d100e41d44541884c0c041110000785808070001a1540040c018441a50940714940b101074000c44018421540c2002c14603410092030200c241d110300d0b02c0d00d0220020303c50540d03404503c1c18041080c0125400c001540c0c0e10b0039105d0056109071001f5400d0030b0f070780d038514441d00b640403c60510044c08035a00c601c440b154054010140856220b0745030b19007034100f000c292a0a04010603c5040282c03458003c0724031801c000071240100304c185801d0701d034402c1e5804050181c00075465601c0a01043c803804009076806030240e000c001c01c0c1d041c4940b03030206035407900c44800b0b000e14040c0000081d856000b4806c0c8030445070040c1041e01c0c0341101c0c0114106554100b4022410700440c2c084040301d0b8110000c0c60340c070681b4024010300603200f407814042d20745200d02c0030403481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306085251 1250 306084001 306084007
    0x30203030a050f120124030e030d05130b090706080f15060702010908070b091905090106050c1f0b03160812090d12021e0c010512040201052101080106080102 69
    0x161000800c658520205140c02c40e100c1e0002c403880030661041d07201c4840c0c001222000852014805d03007403007800c0c1c1074580740030210b0a4691001c0d4140d500f2a000a030a9810030700c44004407141c250080d55100741707814000d9011115558070011400380039140c800080e4800d030010301035503405c1800560001c1403540f007507100789445d644514204c060890454010b80e404900b61045900074200c0c600946010700c141c0b2051501d4284c1e0358200d8200b012654820421440300550340c14828400100b030390303c081c1000d096a03003000b806031b030141c2c025440c1956610031400100c0110103000c1c101884441d1003000454480d41160030145030128060440d0440d04074004100440e003000524029644556407a10742c5650343d1600050460711030307001c040c101942c2c1c07880c003a0403a5800304080341d411610300e040300c1100c2d503280700d01680c550580c10750a010410821a40300e81c903d5950314641d109205150161038424a500e1410980c81c4041818500341d030340c2c00040c00126400c0c003034180903114903070003142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306086501 1250 306085251 306085253
    0x9091a03070914011a070c150219050d0c02120607030209040e0d09061416110301060608090c0618120a03080123040b030106120c080606010c03020a0b0603030405180103051603 77
    0x700e0200107204c1c0301c0a1440e020303490654580174000355621b0941110540c07002c0340d0350341d61940f00b810b02a1b00000050040350b80b0403000903010032400c00810b4000e4000c004194290106642c4000c5029060340d000321003024880c00340d20200000781c46074640d0f80c0d0250300ca00b0000140800e0f070700c0600c1d50310b803941c03c0010620501f031713070080c0440304461030341c0b40040a400240004000d03034480d6501215104103844015028484030021004c0303000c0003035008018a070755a04007110181015207443c6001d800c989030186091401c02c01524640c0c3c06011240608c4000500080347d803106403014121540200150070706041d002049039004140100d030300c58400c002d600038203090804034101a40700b15561540814039072000d6200202409421084402c414010304005a83c02000d115281e203d12031840000e125510590510800c198142c00601d19880c05030780305500f41358020074154141c80240070010321070b511900d0703551055007124000d4246504609140d4100401010303008030000c480d405c200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306087751 1250 306086501 306086531
    0xc01080702061308091e0a120b1306021303030c0303051b0d09080409020403080d060602010b06030406020903010b0616030311090102031c1806022104080412020109091a030709 77
    0x15030201d560f11030340822a8040c54100c400d0b005042c64140c010f03200d50030354101e84680c9003c003181088210b4580b44210350340d205450502c510a4402007860001d0700214407070b007030052181070009109080c05810845032008008400400342c2c41540050a411916000d240e01403145641240c02c003891001c011203038409000c0203202d96260150910380d942c1c0304900f8806501c066401411003c3d40a55440341e0b2070415050f0390300442c10b4040c41d5032800350b0001c1c4031801442803d1502402802450031551151200c4000f5000f03010120f4065480d6040035842e656090014406030207450386c0c0c4541503030203003001800c8070590010101498801c0014040c540c2e000001e480c6052139003280807010503803103c1d01030098901c1c1e00e03e89041598000043c0100030242c1c002d015070b040c04441c401042e008010a00c0c190007000d490180c44080300304018060000a003070340e49441e03401030401e0910290f40c2e0f1b0384402264024035a40c912560b0384815003072286030038840e41e4001c00041405100701d40d00e00da90742d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306089001 1250 306087751 306087763
    0x7060f0515030d0815030708011b170105030a0816060608030d0b031b041509020c03070b070e0a0506030702011103090610050604030507210219050a0b071a071b03030c020c01080702 79
    0x140341755442403205d400d034650b001c02020b8007030b0440341c0090051007580041c0c05183c0310403c80b400c01240d120240300403400c141d200040e040701e000400800c00c1c45025215080c0550048002c3d4000340c540554400c0811041c3c01840700500140006507a030b12888000b480032030700300c848124400d41001c0c008003030701d040d8034091903030140c0f0031940040c0301c030900c00800c0041e85070307684060807990010a4100d0307014070100c0038042050003203840c044142e03640302003290f203090801d6500b940b048000d6400c1c002c0307044c05000341d90f100815000028840c140c2d807034942d10faa00210743c584907962207001000000c00504a0f283c004140c140d45950a15040d6910aa202d0042d4003600100e58810b040c0500a07820350f49103800312503005003100c01325207911440b20303003504a40d000b540e000340720311000010000b807048111068607812410a102d03045029245259200c0d010340301d0410062160040410043c0c50810713445030314444d480020b101d8501c0c100280c10000f01c000c610341809128070800400396008510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306090251 1250 306089001 306089011
    0x180109230f010203091002071a03010501081b161b1d040303090f170d0e0c030d051806030c0703030e030703090e1b0a050c0106050406060e01080c07060f0515030d08 72
    0x680742080c22281c0101d03c0c40c000e00485645c812802a5102d0030340d50007080d100d043d20b0900c55201d4a43c117408601c108681f000780304003400201d28a0014185081d401c40d00343e40401d0000b4040e05d403040c007012268101e503c0c41020385104404500d08520644020415002804106a074412001c292001c02850100040c005418981c803903c2503803c02007500c0407044081d034000c080d40380444012007001196000141842491441c2c903041042481c00000e40c442c603070f10010f0061503400111602110a80c1050110010200080c1c400c05100d540c0d8002442c890700340d581c5900c1d01c9140b641001420381d120380d5291141c03900708120002c0843e0b441407081003600d80c10283c0c449542c44074000c82c4601072103040340c0c00d031850b004108980c1c4503a21400070404a05018005d01140751070310b00300001c8448074030410000c940300840004455014143e07095221200c6a101070801c911a1542420340d000322070320142503070340c84041003942440104404d03e0710f03405900034100181a640302070103c900c0030380 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306091501 1250 306090251 306090259
    0x30406051e030a050601021b06043008070302150f06060318010905070f080708101503050114060a3f050102120106170c0307080a020d0218010923 64
    0x1200500000800401940310385032034000c1e9600e1401c1d807218001000c00751140307030050091144400c41100c620500050090f402400f140c500382ca030001e0050156042c1052860b0101500f009002d258140c3c19042103690146105560f10800c80c58000e00f008100945103d203c0036207005c2c403420910f88004180d015006894183c2d0725150800703845204003079049098032a600388800e010030005e0114188044440c5041945031603501c0d4480d01d52921000e01030350b540c0b81e0107840b5900d401e0145070085e1450440304000c480455480e41c4030542943e544890320401c0700c0300d14080c02035504110344d482c0002e2400321241c2e80300b40b050180e4041c0e5105800500c45000c41c2c14904a41080e0307906e1030b100c2c1c680303906c500219030f5a034484000522403c404d1041c071000c644480008080ca601440926124080d1100740e030b4516610a101500e59540107030840d10401d600340881310006006200501080c8010002060540744007800184504140e410001c0b070210042441b201041e550002c0100703180d0222 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306092751 1250 306091501 306091507
    0xe070e0409440f0d05070e12010501081002070f020f031006030515092b120e0c030c100c0803060f0a03080c010b0901150e0307080d050417060903040605 67
    0x1041c030b441281c8501ea05418210205150506a62082c22809440312081884600030340b0055a1070001400741e0100a440d402c02009295403007941903112560082c0c007810001c40240c01c0c1004034800c8207151141e200079a56a9006001c0c1c1101003100d14541064201d0a502d00350190b41c030440c981c6601d0f44000d01440b01008504034694082c0f004a141300c2000000300324455036420500c1c1d582d4a00600355000c01c68410201d8070f0340c0c0022502c41c020354540e0100c1d440040d40480b00c2880c10344000046030400410b814010340031a007030b01460007070994507402401180d032004101420322084042c1641715007408c46030305503080d0b082140742d1541ca8000b8911b030386a40d100030206410000f134803043c5501076003079100402080714800281c1100c0e50400004c12910507d201480040d1000307009002c803540050100e944228800c0890300358103203000d010349007111b64800c1c4052801f03407581c0040012a80204050040004948180500311a40e0300209001d007010b1008540321300c224019101040000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306094001 1250 306092751 306092753
    0x27042d0b03100902090604150b0705210c010c0807080c0c07050d030c05060a020309031b0f100515010302190e0a080a0c0918030206061002012309070e070e0409 70
    0x140d01003454158090166801d00440c0e140c007500402e6641d504074402c2000401044560a140c8903814110b11518060510a0300b0f0546c0c04086030001003044640e84511594480c4507280b513100300307003000c00043d0425100e0f0b040c0030712282541c04001c40c0c0000c00c01c0190030040003030391000e2042d0b000008880303c10b51340d84d110b041c4c1c00d0810100750001c68021307a4200b5040209503203c00002c00c41e40c0a01c0560b00303030746c032011107074000c0c1e01c000e80781d500b0954400d1004100351500052203100060300070080b50b05d080b035620041c5040403124401c2e0b4130001d42d103404010014500e0352851040007000d2070110b1038a1000755480b1401c040d603060250800000341070300803041d1179101c0c41401401c0c60100b1200c26802c20b24055a08407654000e0054090801c002c424400d40040ba00c47d0005503d074020f0003036641da01041c070241c14101007440d403c540d01c1d1a480766003a2621942058001c1244541841c02d10301038584c01e25000c641c1c2d10003500350780001c3c20000210f0f400741f000c0501c04411035000c2114031312 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306095251 1250 306094001 306094091
    0x100f08040602090f0d0804080708060c04031b032a050102012a180b09030c040b01050d0c03061203020a020f0108040b070503040204021e0d0b0118060e03010906022704 73
    0x13030705480d410032084900607080c070810030050003c4440003005c0b140c04503251031180d621100c007a12503140c808010701c01840020714400100310201c0402c0284450b00f0741c3d0b52104034a0280c41035005e048501c04910200c2d001d15500300b0000580000c0c0024403000c603401c10903000b80040e241d00e9401e0002040030821030239100c2e00a44030940401d011301c0001d581c8a000707030885507200d14440e92107032250214001650800d40180480800143c5840b0300b00060207008101508010480c8000c2561303800f00415864049414072a200e07000e0f6004002514141c41406510b90540c008141440308440070040001c03140906a68030010b2845c006440752500c1c400f18020340968001c2a81c4403640c0c80c1108034880310103019140f090007201c028482130021100640d0f07150500000036105036044402441a20300a101b130034000750010340001040880740c1c803458200e070009580c048000300546080010b003000c8541c801003007001102c0400c1142c40842030741d90348030480c440520042120054441c4a194 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306096501 1250 306095251 306095269
    0x10b090709031e1a0703060f05060f03060424051305041707080712080f060d172104030c0311010b0105040e06030a0b01030b310212030f0d0b100f0804060209 69
    0x16004c142c880261310100c80d480c10680b07085420500082c078100000598041414203442115000707080140b40140041305546940c1c0010909604981c4a241c005003030700f90322071000210840300d440d004060b41414208005604184043d44d03601f0700341b1062001058621590801c9001582c0400f6515846803508201d20300032290f000e046d144402d5522821140c1010740ba40c8643c00781510b404050b034501c81040f1851400e4030014121820004030324003080c1c1c000000300084841d0305030402d10048a40b500d411601011281100015642d2203c0b404060700001c25010403207001c0300034407014a081d4002800303401144200c050a0002d0004510243c400f4000040c1154210008104942e100d003030540950f8403c1e41d0000700040c04580c250007000e0303c1c00c400c180003801c1d4050b20590030324039005c02c107517a8020b00504c100303800f04104041c03009840c00000c03d04c144003c1c802107110517100e0b00b000380501c4800c24400034024001882c0a07180d610000840d40b10f40d0062005860307142d6003012841d801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306097751 1250 306096501 306096503
    0x2102030106090509010f051027090c0f171302090c0417031608030414030d06261c020f0d020f010b010c080a12200315030c150a05130b0a02010b090709031e 68
    0x14090f10f070449c1d5007a04d0000104180c460f41340d02800003440f00842181c07440e0b03445ea201000110203002902a0314660070110390841c290411070344240c1c845400203a05140c090364010211540002e0800c00c01080050f51130041c1c484034082e509280291101d00e01010a03124000c000c0e260000004040040d00b215020400854a0840380c81d4611810031200410041c042c00c00041040c048000e00b43d035060f02181034450303039140035140b0740b5808181c204508076804021001e5024a1075035445200040104c1000041140c1c0141010221042c1e2a42111080e082403030421242a031244046120b14044843d00c90f114500000b4004100000e40e0042c081c90841000144204080005142c008000384d4010760440c0c1d44007050752410810075990f4140b118810742c2095000030850400c80e005d0028141d210654203140d80342c019000b261095040581c2c0060b1f0b1107500c049a203c0c1526424450707440c10010540c1e00c10700302d0602c0c120280c0076070001d02c4001c0c21480c0840210000400b0704075a0030110f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306099001 1250 306097751 306097787
    0x70e0c0a03060b0d0e12040b0405040902030f010504031e02030f09010c02010306090f090c0e040506010308070813030c060f080114040c0e0301022109060408030601030203072102030106090509010f0510 88
    0x40d00d0201d0400041d20218400350194400c04000c41e0110700024100c7d801c440364540e016150514010922000e0907819205a900d401041c54000c0c070325900b0b0003414465440383c0d5074071581038000107403040741ba0342c05040d0750219801801842c050f00ca510302210031040d03003400c00144613102480100e001d820941c11100303000b41460a030040b0640c0d26000510300038032400e04c103001c01c0d03214624162180801c0320701800311703845180100042031a110080034a070b402210b066103040707100400c4258641c0c0301d43c0119130751140305c1010850290b012246e28411802840e0410980d45040008062a0707c4516400d104540c0c880c21000464002c1c013210019040160081d0b458881100c00b10080341020700c8400905178415000a20360031000c0313105440b969100d0f00f00707401d58481900440003508010808406e2103c9400300002280300c000260600700c442e500050b82e40e60401c1c000800410032a80100d000382d641d0360061080b6040c14820106645003544e5403840248090030880c0c00900071480314000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306100251 1250 306099001 306099007
    0x90b0102070608040510380a09021b0d02033004020f0103061a070516030c030609022e02010f09020102070314011515035f0402030d02070e0c0a03060b 66
    0x30b007102c1e880121405400c140045288030006001c604245150171f60030b583c00b40d4800c0301441202c0c0b8640c040e0000140b15a83c07000c81c000c8c0c1e080b810b0320b0030009500741d2025900100320704101e1030402ea0702042d90a8007aa0030018114a07903215a908500038100034410180030794040320340c2e4400d90240d4020820425010201101c0b4284070340700354080c80d401d80c3e070b0303009081052614a01c0808004100c80d880045409980d19580703d20008241d05a0202d0344140141c100c605c90b42c0303c981500c250000380362800220401d04034000b07400c440c000690501900d04114041c0302507038001c0b83e0801101d400440e2020072440941c415401801240c4190725184071000c0c0c085403802d40303800c81e03400000311910108205448240901002c13120043c1c4060740c03131010381c20b80d4205020507500c50ba9120302d40c3c0a0710070840042240e0030311045484040389a000750702c1e04120646c80c4c10841403540706064000790000702c0c00d11055228652000340382c4060b040300000d000c0d070024401d500c00002042e0f07100305291 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 306101501 1250 306100251 306100271
    0x4110616061409010207030f0c030e060a031a040c050405120f1e01050c1303030c15020d0923031b12030a05010305010b040c02030405120106050616030801090b0102070608040510 78
    0x7004110360b02c2c0101d82e5940b01c0c00018400c41d01482152134070fa4040e25440082c107008081102c2849420400b2000c0041c0782c6814400c41d141c400107043c01800b29200410303120300480841e45650401d89405105900b0802240170940e0400101c0d002da0b40c094960044a60140304400c1c540039260512141030b11400500703040e001c0c0301e5445410300301d40120007441242c076401c00d00034190040498143c80d5001035207080000a024442c46829a03200d8040741c0a8624a00b842c20120b030844507000c0d003250f8540c002c4404225007071460f0003410000d040101d100380c2810403020760b2800303905c3e09615551060801d1090a041c100a01402d05004000e416070368a092256038025010a101c104d40b10742c00c000c1c8144480c45d041c090a440c849065009600349032a000800082d00e12489004415559803c8046034a4450000074030000ca070103061101c3d40706891900415180c4143d00061500c0d241049180c003581c0c1c0418910111180c500d441811a2070f9420043e062546401f0860324991405807424 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 306102751 1250 306101501 306101513
    0x2a050907030c091d16020105010e19091205031b040b12041703070e01090608040209190f051303230906030a0e0307050703060b01020c06040b0c01020f0a0206040c120b04110616 77
    0x5031003019001d1000c2c280c5c00c50028107900ba10030a001d420901130f00480081c0d070141c14640d400f89940d0601c1c0380443c0340403041e100c0780076501c62404c94400282c0008108180c45845540341b071520ba4484403028500703450001c4511042c00354005c01d9402c003071440d0206040c880d4010391001c254082030340483d52414802c0700079000581000885002c00c05003000052014082c6034840d10454014201084940d5002442c0b4246440405e46840b01ca59860001c000f108080c800d17079204281c00510022050900c1c00d020341800112036100840011001c05000d06074101d805881129006540b03071034481c0c03220340d041c1029000c1001800150321000c10403070140100014128101c0780140c204000501c451001242c98441d0001080c0e002041004100f00d4070303240600414a040c00f4600040c1001c06000710090b803584401c0c000d43c01079022034280001d11440941510003416004941d048442c00b503601c08407500380051000e492550f8201840c074454680e1b9007124a01d0342c0c0c1c45060030300110285480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 306104001 1250 306102751 306102809
    0xe0613050910030218010f12020d0b04050f0703030503100803040f14130c0c06050603060112030e2b03091e050910050a09020406080a09031b0804030c032a050907030c09 74
    0x908944101f80c0005030303007503a403954034071058000d4808080803002d5210801c0c0c041015008503205d1203441c8640040f5002445103801942c400d540c1c50b5a242845002d1b00e4903034456801440c03860b00200002c004034101410b1810850ba00b40c2d02d400340c41030041000820b11645481c0c040e02c901e040407005681c0d80d41c000030a0040b0b5115800410081d01d0b44c20516680d110240a5100900c415500b100c000c01d00807403108600c0a03000740400482110072468100315507004070309580d07071148102c0c3e060405030005201c4001e0180c405a1194a884401100030f5160140c40780e139000c0d4000c14086018442d80014407006004050600503c1594424889000394414801c8100003043e030b0000c01d200d00c02e240501e989464040d40c9440310101c0784003c0040b5522460411181c02104110000000da200170200000354021425000b60000f00c120141c03070060140c21500005024038000d2240390303110341003942c0140072880c000a8816a181060b41c291f82103410811a5804400040e51140e50507900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 306105251 1250 306104001 306104009
    0x127021905030115020d0e0114040302030307050c010f11060a2a02071a0702060304110307170c0a06021507110c190503070e0c0301030303050a09210e061305091003021801 75
    0xe00d020790100354038102e864a8506e14040d000400c0b4852a440541c42843c0d070986070143c101c00285030654942c00a031035503100703c202300d0f40c0303401c0040004819030308256840c80880a909100030215040c00880da107802e001445130740c046030345062444503070620041400102002d05090703564036920710350103543c0301030910034240d00c825504605400b8003c0e050a8036002980079018a095480d56951541c1244041410640500c03ca2a000441c01100307501e0070140e2211001500d044d260007402c2c000c1808498000d501550f201d102042c06103038103c42241d9010420b85400f0550a6040e03583c0703810101541030301603000c44555071054124001c140580d0490701e08034110350300d0030b07a906282000203104031880400704000740700400100340250440d661040c4092000120700f08150381d82d4656040810707100c0340e442c22203014030841940151510805681c00c96480e03051100c6a001c070b00f031400242c05441e0269123401701080310003d042c03140d00041c1d540207101e911400035a4488112104003441 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 306106501 1250 306105251 306105269
    0x4030b07020601030b01061b08090319060209130506060d050402011b03090905070c0c170316060c030507020c1e0f0301050c0d1803050304020f0112020a091d01270219050301 76
    0x922180100c240750060341c207066105001c4208d60710380426075040700d07420a4041c02602c601e442c50a00b8148610b074514490b80c001038407035100074113000c000b60b9280c104240040c64203080c010b5035907401b800d68a40300c0c80481702240f00d40c2c461004139014200c5010305c1c401300841200340420960000864000c1c1c840061041020b41d45095040712a55481280506458013010044c01600e01008990244030140da04481c41c0025111003549420440d100c15114030b0740d1038520030364850341800717001d400031114401844031400c0344000428400d922040c2414442d607402400c217040e141c1c055024a11980100204000c1c5051030202049034040b00d0390710400b07881c016914504110300f00c1e003181c0c0c407905607075483c2c01c642c2c071503007445400e000000609061044107003526603004490b000501542010307540d90700006242a05146c4120012130030340150170407840049c428140d0620ba6986610703140040144215410000d04000348160035105c9114892607060a1000350414011412928050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 306107751 1250 306106501 306106523
    0x9030e0d03140f04050904060218030606130c140f04050a0e07172a090103061a1603260105090a021908090316150509150105090c04030b0702060103 65
    0x401005151506034000401151400a29821200100000c1c10420f80d80c03030025031074140c503603000450300d40c4101c0e003c0b030345c090b00001c079249018245034500701080e01c2580109001c0c141003000540c2805200004240a6900e03c0c032440550720071000c9400d4619020421692110724040c80a13281c4c1c050f02403640608440040001c1104480602c140300d02401d0baa40c44055118082c01202c0280203049104198000403154002400900c40d003420342c1d8006c40821f0b990b400e100005800e68240b42e0114640c07200408110543c4d015002c2194000440d503205142d00d07550b180fa00ba074071006006404003d0300305a190b0100002d07445042203050300c0e0115011100d03550b800c1c041c80c080e8444e896020300021018006104401e0203050945d801190310010f4038100904e41403121030712403440e02c0a6440701d0410703c02c920190b04510840790001d03200c1d03001d40b9501c2e10b0b407000410300070ba043c428103004801c04400034502c0b510a038142c4000d0741d448003d804460803c030300000c1d0384410038001030764030302a26 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 306109001 1250 306107751 306107777
    0xa090203150c0d02130e0906010906080f0307020d24060f0515071412120a050106030b0a030b0c040b0c0303040b0c03060a1206110f180102010605181005130903 70
    0x500540e82c441d8820780c0125142000d00301910b800307908000f010340710030818444042000541e40329402d104014400050025601d40f019007020f50b13405a1200c00c45400161148030251400300032202c100f60151003201d030300d003007520348403020350048600c1c007048010807440d001050031560000e02c222000300b940c918500d6160000c1040b90014903d40704030244041200e45e00059495202407074003c580c20668085908135404900b280d800800b85903803460311403082203011049489001d000d4045854200091060f80d4042104105140006000c07842c42c90000f4000079094001c48000d03080f0f41c10000d841d144c040d00000d59a42007528211011041c210008035007407910000e4900c2040c00030640c44015103490100c8100810a2030181c500c2c0b40c0b90f58004d00b881c0c0854000307240440c1e0303111021341d4820503403400400f02d40c802d000302070469041c03101c02c000079555160a260003010b03e02c400f4496480380030403e0b960070340a038410ba8002000c4003c442c502189540101c1a07d40030340c0354080c0384500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 306110251 1250 306109001 306109033
    0x30308090312060d0f0b07121a031f02070f0c031115040504090305090301050106020604051006080607030b041401260102040e01030b04051006181a13020a050d02030a090203 76
    0x3804182c1c4030b9060ba050004115182c024440031880d8003c0610380d0300d2081c16120300d503001504840709408203000c44c0364415003103040c0c8aa80f50610b540302e0f4107611161284000790302e40d2038082c0d402c400080440400e1103030a0702581110645c81e40704102c0d07a84100c00d0310b011030390000903210a58030a0300d200440d01c3e1a0800d00b61801c054408004854580b42c1402c08010082041c01c038154100182400443c1c45a2407d01c5a94080c02068005250526103458214900b090320009800b03154240f20742003000190004069030080380780d04010400c0480b100101d001860b41d070480c0d0001c0350002c000080c48200d03c0708040084c0302110400300e0b185580c0c1342c1e00d500382d105500c82c10003410102001000403c04030040f240e0420711520a8454007511443c04906a409075003208040c0c000c11000440c52109601c075500820744120485041c651344100010301d005200b51301c4012450f000100c00300d08510401c115003001001c000c0c110344905040d03800301d004200d455412402071082c3c1d01c800018941d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 306111501 1250 306110251 306110257
    0xc0b21090105100911040f03050a050c100c03030504030c050102030f010602120f07021908031b0d0e010e010c0201021f0b122802040204050a0605121f09050414070b040303080903 78
    0x20505060701c14452030802164000e05807510b60764007010b170500010905031808000384005602403401070102035040d00782242054810303109644150004500540400d80040020f00c44980500340020195a00c1c201a110888102d070f00600d40d501c00000c11038034944c40c413034040c1610311590864408001030000707458240300d070310f100343c000341c0c0203100301401860081c5103102d000b1000d03441d810b00d05595080706840c64200c20410000c43c0c407400c00d4080700c1c10040020030034409035490500d25040c90f04002030520090f00c0310650402000c031004100b9079008102c00a00341e0500340061050280003012000100102c0b01114422002c0440e808131911002030784101500180da00450451648036005c0f0000c0302060040340c100d0380910000405a9514800303074014001c0780c036803950319141c440118515542c0100000e00500304250fa41030f01172031021081090710303a60100040c0640791410461088801c1401c070700c80c0c502c6682008256251804003600c1140c0c0300e80c03202d5440d41c44110a0a407240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 306112751 1250 306111501 306111511
    0x6090f060702100203060a030c0602030301061403010b030a0911100c0302070e0103031b060e0601031208061e130b032d0c1e0f030109210c08030f040c0b21090105 71
    0x41d21103801003c2d02c02d000d034000c540002c00284480e00143e5255150309101c0c241e0307800500503800200040040c140c2003514600b09000c4980102c3c034541c14030852a85034000680080405591240d0700010007417005080210464002c2640b4508800100014480034280078100e00600448030700150040ca070140090607660f03d03485544030403031b0303483e450052000c040c00f003501e01e84d482e9003401d0401881444001d020b18050302201c182c103003407030030003400f01d00700501b145010f00c0410a500300510029040081c40007400c8031030070450518600303690080c042241525034580503000d660f080e58205002072210005800e407012125402c1d81101c5a11481410b000f60342081031061100ea040a041901103500354009003406006849040031038215285204221181a9030004030002010107845031002000c803403030111150001d070380d01c40910b40009046652280c4015010804000710318001d2800340003555130300340e1200170b64194614621a41039081240794201808642d04c102e040c0a028424 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 306114001 1250 306112751 306112753
    0x1815020310091a09040302161421070302090c090603150108070906020604020f0109031a220c0b03060315090a0b0f130308090f0706091701020a09031103190506090f060702 75
    0x541000340a0000007a00103104a01f18020000741000000079584038001a159110101c194400c04005110401403500d44642000701e0b05402580d0442000845809072030341030315500350700d880b14500d40e61b030307802051941a84582c0c007008010940311a18804c0c601030340240d856044688801c0760590754040ca5014900c01a00010009409420903a0b801c080c850418500141e0031644c1e030310b0383c0b00500c108040405038258040b06000c10220941d07540340700c0c240d00c2e1140e140e1012181e0384207980903280d8424200c0b14680440003621955050185e0380140c4010103402005103040740190b40c6074190032208480455220010410a40c0c514480c61300c100d40c0c0780310748003840d002d0f52815180c03d50014400c0c02035201d6042c10803103468007070190b02e0040c860340e210480c1d810300b006000120507240d1070040f040e603841441100d603281c1d8410004000c507034028203202c4280400d80082401d0403d0300109500c8803c0210b000010404005541d1384a1000c400c262038a11b95030f10040358880805032420801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 306115107 1106 306114001 306114041
    0x31d04240b030c0a0809160806180c06090108090a05011d0f010209011e18060801150801060206071b1203090b0a020403021003181502031009 62
    0x703401a41003003415458100c0204401c2d001e000c190b042003011101c085a07603814180042d807500580b591200a2041c0ca80784041e580700c4068902980c40e25019951025020300860512607410000f002d06203050204001141c0d4000d02030860a001e00501003800005442441244c022040c2c0c084901c800c1c80c009901142400c0700000c6d085060b034010000707149540c1e44156003074a004440c00700a1840b40b20600111814100c3d20455032010440204c081401500314038054100d508681c40516081c0081c401180c0500c1c080c030a90340541d0240001c1180c0c10b004680d01d9859003d0b44101d10103c080342e40720212400000c101d00d001196407076001c0c82c184601d5503412a80894500001c0d45052b00d181d0104244c8201202d40c002010b80d80d07604e41207020800d5281c102c1c1e00b40c01602703103604242c9418504d002540191030208030070403400c500140c10191402103803c6e049281000c003078 = true := by decide +kernel

theorem cover : BRFrame.Cov 305935251 306115107 := by
  have h0 := BRFrame.cov_init 305935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305935251 ≤ n) (h2 : n < 306115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
