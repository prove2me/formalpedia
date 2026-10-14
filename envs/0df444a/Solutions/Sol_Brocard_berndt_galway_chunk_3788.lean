-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3788
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:40:47.499017+00:00
-- url     : https://prove2.me/submissions/bf67389b-a405-4d18-b4b4-c1bf3d6e756c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 681115107 ≤ n < 681294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 681116357 1250 681115107 681115121
    0x81b0a0b0406060e0105330c070f090504051f020405040606050d0f020a0f0309020303070f05030a12050f06061c0c03020d060503010903020d20100e1b10050702010909 73
    0x61205428010711007004102e0040002420004d20260340320360400e400702c1c2c140703144403000c0d007220a51042041e010201a10002075403007030301000540e90301c1e82c1446a82d5501c12034400e0f030f112100014800154040c5030300c43c640c019070740840a00100d080e036240d1080034072035140711210354035400c000001e01551244201d80080c00c55031039803134560905d5022a02224220074011813014010400091340a03480a82050201c11078100001c20100341c1c008645180900d64000340b0b840d84002801090203c0000600a040550380c0c031003542200c100c28510a1b03480580304161107a036a00045041841c01d4000f604078469104140e4400004006071901542c00400510b80860782c0091101e5600b4114003508015050a400038003c0308103c2e6402940e8002c0110500b04000e202511840c080d54003401035035104900c0401c031190b10401580301002404400c1400080d44551161100016401511070240301001094180b2040c0146030980da90350160078124104100020085403a181354030602c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 681117607 1250 681116357 681116363
    0x7050a0906060318081e0408010609050117010e1b0d0b01090e010b1e061309050906150f0d081b0a050307110910030f110603150a06090f03081b0a 64
    0x700701e140c681140a421075003100c8500311101c0a480904012400310001c80700510b14480c0c01440e05440081d003507840e40a41d820440265080110004003164543c014030b050351151a20082c0308111941c0703407422500c02c1c00c02600c007604605010040356000111690710700d14041c01c80325280c425643c82d040100c100742c100180e004d6076030996205000c0c00348141d07421101c050b80c03507450b900c0000c1c10780341103014108000f500c90900020380008400a03504c2d2440185840c5d0410311075400e10401c41529210112640b240300030b20400f90401c42e16206500e8040340e0409005010b030980541c54000303490340500c1c5840400c401040701003034040400c000c4c4104040c096805561205041c1c6002096604a604110703c40c104007828000e41d0b0095519280440c0e81c40081c05c0154812440c0100c0710046e0448002d038800400301c10000c103a00004441d580f040000c98071f1302840750300e42d44241e03040a0280100499004442414030018003940000c06a5444195000c4030b43c1004c44030813440c000c0800012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 681118857 1250 681117607 681117611
    0x1212180b091603080d0903020a0f08071b0b0304030804021c15050f10150c0204050708040b180a0f0c0803031e07020613080d1e091e0206120907050a09 66
    0x40c04180100c5050703000e0b59040701207007032940e11000d1a502031084130f503604c503a60340c954804040c000c214120740d00d41d0103141c1150414080c02c1c541c010f900440701c16a00b4070180c01da104800000c022082c2c003900c100101090a40d1500e031021a03540c00010070417600500101c2c25030f40240000c0c05008819446440101c2c0707040c06043c07103078040d5400a007155108600d010709104c150106408043d0540d004c90300d0550341c080c15000d0854824010b06c0010790003e180000744400e05922144680c843c40c000d00c0440d26644a01802d13510b242884013402d05680c100b80707101000915610302c044141da002d41003042c40c50307440304542e42c25680140ca01d80480e001d802848124000380030f80480d40b100c0e030390010703101c140307480d4440d0005460b084500404001c00018540209081d0b0760203036502e110440c17488049109034103c0b58004144000d0309403403000300d07604200030045484000014060340904454109640360042000b5010f024016080e9800b03004408140c0340c5494082400800344040c0c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 681120107 1250 681118857 681118861
    0x61801030e0601050a0501080702121b010c020d08011418090f1c02030a050c03130305160803030c070b040c08120301060807020c0a140604030606080d08010b04031212180b 75
    0x941215208080c2007810703000040100f04035a2801411000c40341c00382440b089079900c4800c100d06041824449000c01c0c040416034aa0000f104060914103120000003001200d00040003a0b90781c00e601a025400034210b00c00600010364001c8400d1080e01c005004d201c100f000d501c2880b0503540003145d0700c0e042a4406c8401001c045d0341001895401c45502524881149654000075101d100d03040e856410b014000030f603c2c0d0f000c8800c1003110b9002c110795040c140f1aa480e0b182240d02d4100001c0d00211001480c00045190b9102000300ea0140403546c00440c90036680f541c40403040f880081090318841c400c0840000d00d600140000710064580c100d1044e41c2c0d6041c403602500c01c050181c01e00c4210741c402c0c2c44c0c10646854a00d1260305844410b015408c400c03814600080c140d1240340c200070040742c18400c00052142c40043c4080720b0070840d4580c8103040e030b201c18101040d03019a1101400b04100e11003114800c1780200e48607030311a09905408600505054008405022501011a519416041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 681121357 1250 681120107 681120109
    0x301150311090c041d151009030b07030e03190e030d030608060c07020d020f150c060103151b030209031e03070308010608130b06060d0e03040906090c0c08090d020618 73
    0x2d10503601258003030210f030429060051070070003102061601041c02c60802c000c50b150241540c80c01348042e90040072a228000301c940000c2483c0d40c0351004a442d89801008280018024024100305280b071000550070096901617651110840c0c502072401c2c48204000d81c1d20f01c1d1002d101030300c4145d40c20781f0003040035441c0000d500d252580007092241c05010a001440060740d91110001c034042d01290503590740205500050000e076480540c201d903620002030190342c000070106515040f2401001c14131411940c1028003800e80745a0340340c408286200340040c28405e0b001e41e01816082c00701408581c0625494000b40501110380009946240d10202d40442050b600c905a540036003c0c030310b001810b83c2454103031850f8049595078010070944840002032055104c8005070380b0806801c045c280220140000c001d03840340c1c850701452041382d0412101156460301d900820b074005010343d544000c4210580c031074100b650006410701b54400e102807030850241e030310b14000c2c00108a8101c00103c032201040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 681122607 1250 681121357 681121369
    0x1031403030609010504050402120d12140f06090a02091302070b151c06090227070804020a060e060c01061e05040b030c060f0d0504060c0e2d0301150311 67
    0x4486a1155401081000300a841d003400c0d0b541100e100740c3c0c0118003604d40748000707108011aaa0501c0881c82902c0c0002c51080e0301204001c1000412001001400c05500d040505e00c0c40480b80311011200d14000b06006040824440c0c0d171015140400600308002c40001511011070365862140058021818200b48010395007490707000380e0340e0082c2d048151038550114004c0c2c8520f403401c0d03086614032414a82030000d581c01607084964003e110000c070814003281c40e20308803c551040480070120348005940107000e40c002c03600403a00145000691272400008840217044000c4e40d5070803100c244881000d0302c000b4000c180140c00c0c070302107034890180864400500541a6404584240d0a010100c0310b6624089207820040805544241c0d50701d501d4101d0340c82910070b102c41d003003203c0c1ca010100420300c07146a2140396020b01a0ba50110385102c048100075000c0480d056590f01c044202000c3d42005401c2e1140340c0f017201000d0300200d002c01e0a80000c0034a162668410341e10719500c0d100510861801c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 681123857 1250 681122607 681122633
    0x909050106120f1e1505090117120421022b05100b0d06020a0c1a040201030f02030c0a0f0e040e06060f01140a0e0d0c0b07020108090106140f040e0f060103 68
    0x10f4008000010310403541c1418105a03100d91381d0281d566105203404004003c843e0b0380501005482c2e800c0b556550038400000051050049800b406490b00d0204410034050071030b02250b119088020444115501150000710010300c1240e2010703282841c2c1e0f0034604800c03040f03903c5559010070a46224128280359042072a078001c181c090714500300301c5401a6840c400500c821a030040401038813040d00341000c0c1c6501e0b000c084098081c92004000c00784d40c0c0c1000303d1151080c0d100b85c2c1c003485100c105480f01d00c10703400241c3d40202680010301c050000c031449041201a1804e40c0e1501c6000c50805001160490303160a003401aa1b07048042080050b040050284054540038a41a1005407810b8440f514902030f41d034070b01c02002041050502c0c141d417031841a002d425004070032903038034650b2410850394130760040350200e000c601408001000d6502c18414103046696080c0300400380340b812030030044071480c1c042411740d100b03039205c61245c40c02a00b00030034610006418014007895055003844511034840b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 681125107 1250 681123857 681123881
    0x12030309031d03070303030905030904050c0c011803080408030601120c0201062c0c13051c11010305041707151401030b100815090a050d02010b0a0504050421090905010612 75
    0x2c0c28880c0203103840010349141120740501c1d0001e4403400501c0c0690461040d1094568020b0400050106a50000c00141082a2010020009104041c904440049003140060040394072140050045025880150b911010504d89481c84103454010302c13007203500744140360b00103079968031040c0300c40e1000c1c09007140e55910b000354082c040c180c241516003400d0002441e021039103801003080002c140703a1285a20280800070050803038007030340c59003030b900d400603d000030395041d0951214419154000c0c82500d00590b00b00200118443c024454802e041d8080c0004680e00c0804540708d12100c08a40b1582c0c84444165240740429491810907088800015001d00380d0315901c44810840c0d00c6c00082d500e2102c0c11940d4444650303507142401030b420f003e10f49201500500443c00007200032641980180b070810411205c8400464448040c44221502100c005150459010003043d0341841c410050a018079549400e80c00c451b1280b030b41c20240c503400c0c0e12450104581500170050040640100d6800c404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 681126357 1250 681125107 681125147
    0xa061805011a1804200d0b091006170d0305070e120601080706110304140f0603070207090507090e0a05060f060d0c0e18060118150e0316030302100b0402041203030903 73
    0x600e6200d40b4280c80c0c81c2200428100c600044e03210141d150046d0343c0b0040c54004084240d0380c500341d01c400d511804400308000c0c07c00d00e4144007240c0780c0800d00305c0704115803201004101d0010b41d40426401450080c00d02800d00902481ea81c00503a03551350700035000301040c40941141e52600030703201d150081e1908040180200710b02100c0f8900c2d000415a01280d00d10401c0c15030003401ea0000c01c0c0f6412082d4411604a0b03800070801100c660001f42c0041201d0700c0700b81c2007001c0e81d1030322021188a02140218580c0844010200d881403446420140c0c00900040160308811034210014030f00e54400d0b4188180c9503106c0340800303102600101c01c0201100300343c905a203492084038900c00e8801000388054140038441183c0002c507401016400080e03c10703a5581411200c081401034135909050908620034401d10195440d00c10013a0303c1030082307a606070020001b00461014190107407042150080e0001ea0a000c0081d0700c00c0d035002416400c0d40242c074001843d4005082c01082959918210031600e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 681127607 1250 681126357 681126361
    0x160c080606060d0b04110c0307020906060a021f180b010f06090302181306020c01140a02041a0a050d050c07210f0c0c1e1e05030a061805011a18 63
    0x5200c5004840000000c83c20000b11413030316a001400070300d00c01d00c41041c00758011402480c42c000000040407030a00032124483d280e40c41d0300c1041114890006d400c40160490303050f690b10100c0d15180b03002041e603004404079104041886070510703281c0088064698150402c010450007448100e03000107030646241c0128421705640200d465014240e0b07001603951440d400040d40041e400791640d14041d44558207543e601940d2803064040c1501e008131080703150b0400041103081c00c2c10701c01c9408480042d0256800d007046400160010f030800499081400340c200f02e0144004003900c92244241805a01c2940701e00c42814042201002c101d003580811411800310074036a5000310907182d03540598034000701c05c410b580c03506a000b004558403030305080381401641004444110083d00c10b40d02066130384605150f000304280c04080f010721a0641581003040440d0104410f60850342021440590a4000207065500c99003114801030304480c1c00030660a40e00d219245c001c003421700300051501504118 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 681128857 1250 681127607 681127609
    0x312081003020f040b1e04061d010e090a0b040309140d03080c031003060e0304060e011805151909060e01020312060405102105071215110d02160c080606 67
    0x603540c940000b0340b091209101e5600290f80c0c603000800d90090180182007100c0c5a2103680c04104450103000c4d104c0e1b0300744400800e503c3c1d24402a84d10200304403185400a918211aa20100c400034107074000900400d2410740124005a044a0140d84259540c030a40c074a004141e401031421003100c2841520320b01c0c40c0c0c0000c80d501c0003445421182d01c0b40940c0d96519614017020224126a01c01442c960030b000030001044c3c1c011010b48120380c46601e52481d4511a08011140300d16281201610b100c4040d07805d11581c00c0c280202c25400300250360040c90720800340460303541001640000400180f0001003440500c0d070210a03071000050a000650074050394840100d040d0100411a900850ba50300001e08a01c00e406c5d0040000c0c0350341c1d00c1c9890200184081e5030f10b143d401d4241980c00f03115080c0c0005507284511090140303140c0282e00141042c2d01c84c06d036200905200e4098028020b002d005c1000504454402000c40900030f42e5865050f840f40c0c038200d5001382c0341e0360000a454221034208699 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 681130107 1250 681128857 681128881
    0x305061609080a06020904060603020f03150414180c12150c1909031403040e041b1a04031a01051f031404060603061406010e060a0207120c031208 64
    0x114141242a10510900344222007818503940310604034801e810040c0c044c80016401484200000e840a001154079a8805c2d02603102d0700d042c0000c000410000928044600d18081c920b03c40002d0002c2068441e41801007407150082c1c5543d003221701500440a2180c0040040310b22400042e90202d80000c8940352590b1146000c940da52090f000c00300c0010a0301c4a008110b03800035010740c1035034211480200c40181100c403103020450b0b0172076040307210002034140002614111000c68503901916034517036a41b40320490114002c200d12031443d00000c2500803040c44055903813002c80c0001c0d52520300d541002c00c070810f010349980641c9000c04005100c01c1c0c503404000900ca641c01010880005403481c000c400611400d0350144504610f103040c0000c124664000c0401c51740903010620144070800403c0030030341c1e42920fa03d030208010000c1e060590074110064501142c0343e00503207040300d0b503c00441f070f14254200b604451070039140d1818010401c000001d804003c2d2149044000c1e8607250300340d418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 681131357 1250 681130107 681130111
    0x10b0d0b0d0c06030c110a0506060306010801110d0f090b090f2a01080c07050f2b170604060e0a0c090806010b04050d0c170709061d0109050a02092d0901030506 70
    0x41095211700c81105131602a0381c3c1c88401c11112012519034181c18246141c58010a41d40503100380100070001500010500400342d031882200c0182c0d02d0116010400c000414000d12540c40030b03911412070b900410003040b11a4450481030014106000b201c81009080a1228040190301c035641590034510245024100345020020b09080070a61030b40c3d000020140180d080007800d51156014500101601182e90384034042800c44451025442801809030360000c540c146001400b109090350341110074440e507a8002801900c000b50158994000c0a0910400c650340520301d900c80501d05011640260b03007400801c0e0300000390185504201400c03545210760702c945031092018a200405228448500c0c00081041c8040c141e00300440c1135096403190424810b107500305c1d1400100255507200f40c0f001c10107805104100e041d079a030804200d02c005000140003042034503424090a07606c2d8440003803120007510707080c005c4101c440c400c16620303036410b901c560311a0298843c6401000060700000f0200c0e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 681132607 1250 681131357 681131369
    0xc03101509180e072108072006040303020d0c03180f0e06090105090a09051c120509190201120609060f030b0601090e0f07020a0b0109020403140303040503070f08090405010b0d0b0d0c 80
    0x38a900010300005da04001607014054100001e540c2c41042442040e2000202d15009041c881c0720740ca0003080203e009500c0054056000b50092481d160310491106a889201e814611003050394203950803a04030a0b50081c0300d065118040500c000100341d400f4542c03000049440844960416001c6072500360050720610003d519984030204000f0240702c001d0f00403010480c13002c80c2d0480005c000304200e1400144400183c9003801003142e000001c02e44e900581070503082d442c40c0c100113900460b850300061101d010080d41c1c600011440d00b03040d000703c0e4010412141b0b650761242c19410300b40800c020103858641031041200d003c0092044e062f804607802161154107525a50b10f400050b0305046009000070701059411001103020400c42d4080d00c03d4a0007074000c079800d4a0540b00310b9580c1d2200f914060060f5000b4000000094107030388901c00d46511030040e0a007050160000f02d410b40d00c00303800c451813443e004190080c038120700307102d001400d02080346c10303400ca130009494500c41c1220390300407d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 681133857 1250 681132607 681132629
    0x821090d03260103061d1c0507140604020a0b12040f080c1f06080f0a06051b070c15020c0a0b09010306030203101b14030c03101509180e07 61
    0x800d0515000300001c0c01c8120b94000001000c1c140d59810a02c030b048240001c81e5100d02e016513414152000d040341001c0030010500170a5801c1d68256800c00299080d204202002000c20070500060b4012003c3c00010302c0e040d00418030790526104100c06200c0580103a01c502c04140300e0880c0d2410010074131500540c200e100480342512900b8200707544c0c8643c1182c88010b102e81e0510714080b5032000d080243c03490044408005481d103905241c3e849003418035410107039501c00c686040c007003400da500240c5c12000080880d0038509040c4031402894001c0d88094505010407041041000b20150b2007400c0c2010910141a2001c200c1001a0600ca102c0c007808102c00e90102d149442640603902907000766070001c0c2104c0b541e05442c00070030050f041154110100f54411481d1039a258001c031a4840c1e90144007500038250b585103510120140c000406503104001c3d200780018100e201c40136240480441a80c503116050309220f50407051400d1a4110b01000d450000e030401d9603180843c1c51000d0720030302500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 681135107 1250 681133857 681133879
    0x1060f08101a07020d0506070e04060305060114041d030a080a27050f0106091e02091507061b2606060403111302160b06030a02090604090f0c0f082109 66
    0x4002c0c2039003c0c0b502c00a41001d4004003000a01c4400100103100781459502d40c0307140303c15102440150742c440e2000902d80d03880100144880c000b402d10f032030700c203100c047c00000c0e03180282640c140034103200740155409500000794542c0c0855000d45407652000c03622000380a01000c0e108181000f54100c12a547d001040700d4580c02042818000b511440680314001e02c41c0c5900d0785000c41c02414100001441c0d1200c52a05100a0441c0c0c029901a850003c0c01c440c45003180802d80200d552003c14219003c0707954421150b00c941070800041ea1b807280d941d80e400f4031010011050002c81105030b0703401040782100010014a5a50710f02114156540040820050381c1484e01080c034a11024101891050022507204895a0f40d4594822058018822805982c03030311014140c8841444401941140580c00040c03443c0c1429040700118600c01e9924140525950f1111885400603030030503902d50345401b0342007020140c1080203901d02c040745070090802c00b15051110403184207402c5101e00440c0714240d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 681136357 1250 681135107 681135149
    0x15070812062713050327041103010b03090c04020d0b090916061805090a0c0206070903170a05071205030702070506270112020c010204090f140105010e1908010501060f0810 75
    0x1030f004001a44442101c2e00c0d519100000f0340300c050703500201c0c0f03241c1d120003025059910346401001c0b0740462102c601440d590810303010b19041c0e40010466001072141801c2c10210391031380d20041c110a210890000b0300d084020040102c03082028100c0403441c1e10046000d41c20b0390b1270102032422984241030160b980f6004405400c0d03152865404160701c6000a0100800d0050941040070000031a900741e0702c0359618400103841c0300c80340340800317840700c0c500804149050900200404c3c6c452018104a802c0158503513414000c0303e42c901d92a00020004400d00090f00c2d010010755010b448220f600504000301020b0a4050580c1e00b00e00308007141c11540000c6169001c1e51520000110340c64007903645105c0050070317502035031091040c0074501c1d1411201c04101c900e54840c014158065617013030a1280d02e060011100e16000308203e6078010311014007403518450412040c0000c3c00c40c10b0000c41c0b150b1624078084d0840703120007450800d000c1d680003004a080c0c0840402002c0d5030803190540c41e0b0800d444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 681137607 1250 681136357 681136381
    0x61e15150a0c0b01080a0203010606080903030c310e0c040506220b0309070e0604090822050622050306060d0b0705070f0b060406090e0d050306150708120627 69
    0x40c0028155003455000880e245d40b011402c0301c203640c000e074000e11a9564070001201d840c1030032189045950006d10210f0702c0f0210741002041c101c41d1241d58043c0401c0e1b02500e485101362540003003021114003200411040d4031240301035130b11003280c0b80340c1030903c2e2505020400e1480b07805a05c000c01d88060074002031400364141264040d1801c0e03c0d84503124076081c100940d40321420300503c081c00810700700290103480d050051980301d50340030302c0103402c0015007a02c1a601003884000f4084403207202d10f0125168032040e020f00364031a01d202448990052642c401a0300d540d09422450203074100404200c03880d1070304085101c000c0d41c095501c10490741e610b0b00848a60080ca04020600c03460510a4814072452101403400b911003158200300071655001848100c0303c0d088400b1009401c4000b02e160b9035070140c0007035603200d8409401e07041060a5131b01c500410f503010f50421901210003040500b41d5041981516a108406440200f0284040c01c0100040324158580700ca5080820000980c421010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 681138857 1250 681137607 681137627
    0x100203061206010e070e040c0f110c040e03041a1e0309010905010c0306051002070302030622050a03020102130b030f0a230a2f03060d0f05061e15150a 66
    0x1e00156800d550310b400d0650804001903601030002148100d240045103404d03c2440c40e0807900703031100000030707601013415105000c0710440782540307020b0740c800036005484900507504030080030702c0a103075618100030345508020050000000302c1030040c0808520710741384c00c104070501e0504840007922560b5540da0a80500072100000308103500701507200d4811364068100e101550300407181540c2c00e081c42d1008a0b520301c2c06110184d4150b1140b0040346800c20920500844000040c04604014150740c40300ca1824500280032030050394000f904081c10555250030001402e08444a23501d103040035036580c60340d05005080070000640d07640700d9100b9009032510304080c1d87c0000c03403070414500d0310340c19400040c0382d100911100502005c0a01c0704404c0000b90a58090745041c940d2815500c0300c1c820b00400c0c0c030303003c01c0844000c540f422000c0c0210f8410840f09101302e01d00c040040d01106604020904150050710a070020b40c2c410381030680c2541c4101201c13103c03044100ca59500d034070003030904555036200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 681140107 1250 681138857 681138889
    0xa14030403080f1e120c03131e0605060d0c0605031302041a04111c0e03041a0a1b0b0a0f0b18180604020d0305030703110c0d0210020c10020306 63
    0x40060111004000c034000762204d2594450784040d40c56580f03890000c070b0701c1410364144d42d00d032280d000035260750028405550041d00e104003011440ba4190b85800310b1240c080d13800302e4200b10000300701c3c00b001841d01419602110a5442921b034101542d5448031009403402088207000c4084000703a0010648010807100e9034005000340500c60110034004451001716100700c0c05141048a101d030562140c5046440d0141c1680e0008080032420f2030610040c841c000320a00a4003041000245a01000200f203445486401a0b0359907004200b40c00740c55a400003c04030310407003240c0442c1012a18008510340c2c0151640c401080041100d20858000e040303840b18a43c1c1b00380203043c031405040c0c00e41c060910481e825008604a40300d4030100c04d542b071740e04850003540a0540b40084001a105001946c0c20243e50b05002c50706065180f04215150800c00e210910707540806005413002d50b0400c010719001c640d941e8210724210103d0130890b141e926400d540c10035181c001000c0b440648035420084201c001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 681141357 1250 681140107 681140123
    0xf01170618011509020c12030c0708030c0405040504230a02060d020a140a180f0e0613020c010911011707080610020a02090a050708010e0610030b010309060504050c12010b030a14030403 81
    0x14079000f015000f504000102d4286e0702c600c0710284030440800040300d00510700300c036580b82421040d40d03a0701056400200100301481007400001465112401818012072090748044c048451024460b47da0840c0202c042196a01051009000d030b125081144e22400d210040560f4680307410000342d44018070490b404008807400125071324410b90100840b50360004d001c810a450a6031041da03881ca020050080c51480801c071008140c4502c4e1040005500007015007001d404c00307442d51001c5085814580d000e80320781411040c042c00e42c2d030348031a00d6030b68201241070480c41410300000041465400034810b500070030802ea60180c04074020400c011401c1c0e4000c10318050b0b807a0175a0001c001e01025122007021904800000c41e00200f03510605116200103091110000b02d100c400b20060301100681c0c2c1d06041c6c0d19244240071422500900b8072a5000d03400412034150707041d0504c0610231030081c94040a902d0710503401c0e020b69022400b0602c0541000401d41c10569190030b003400e6105a52000307200752 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 681142607 1250 681141357 681141359
    0x62016030818040e0727050a09020f0402030f010504110f0f0904050603070303140a110318090901200f0408070905150103060302060313170d050f011706180115 70
    0x1422401044810240d5401500100985052100740e80c3c040022100380d030001c02d020b000c41d1b440500b80005500004044088403040020b6000c21110306452172a45141c40706883c03001d600b00b0071420301c1050000d8508610318641400b50100d203590601980344603e495010708420400241c00742d030611f80040300c0c071569807004082c0c002c4c5c80b40e004900c80703030289080800144035450041000d1040b2034040d102c240d0040301c00b100300d80565021321420801d001d01e107101c0107040101000688107140c600701440503000b0302081048030a000090040e0000d80c1001e81e20301c102020719442c040210958500c964032038010755602c650328056034110b001148500880021001441d8000b00d000707006860a00e4a5040030500450656a040c0400303500600100041550f2012850070100618002c03c1c1c010703441e2400000c4104603900001c03100a10319212418400d410040688040c01802d0005044441034a030a4604da12094001c0c402400901030a440301001c2c9403e4010100601040440c2d0030b40c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 681143857 1250 681142607 681142613
    0x9040213021b0c01180603020c07090c020a20150f0c0307030c1a0c030114130f0f06080303041205071505040f05160612091b0303080f1006201603 64
    0x9a4418401c41d40b0384903044002d03000c2d500034400411000c030000c14410b2480d08002d801d902039400b4021918070f5105050001400380c4141c0700310301c80030000c1e40c090003c500180c203081e80400700300e6841c08200300d031f400742400e06682ca501c808001590600c00e1282c60349011849900980134102c258035250000044c0b05003010743c05912f11225612401c0d46a0007400c2d90a40510214011500b0068015082005100b40000d40681d00740020008280660710380b1540078200550b58204e5000d0403054a440ca00e07115242c030b50141c038016180300c1000303500b1880c2c03030386446d221040150401814014001000c2040c00055039120387c240700350000900007800d103850501c86210a009060b2051b000300c0301d582c1030b4000d0412001084131410b94980d00e4400a6004070001014030481c22508491300c08481d611580800503600010f50082e1254091480c0144a482c00389200600700c01d141a030b00038051040941203400200021070701c00650f4228045600220b2400000c4201030131441000340c000010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 681145107 1250 681143857 681143887
    0x1d040f0b09011d070c031706030c0a0803030702010b0f13021605010608031804020309060c0d0e160510081b0708040815041103010c0903080705030f0f0d05070503070e0904021302 78
    0x141030f00c80103032034003243d841c850200c81d41c0c41c91480c002c00241c55004400195842c80c00c5094101c03200a041e00c070228801000240700548503071060003580c001104002c00740b602841114080b0009440d54440d103c4600c000402d00302103004040e198a07408506610120422080318150b150b201000f002000c1e10313110500ea0300e4101c1d0007851014502c5031800310060416000341d9000380711840c0141415101d0340f200c00300d941c000203a00c03c0712954400c2e205651b60b41c1007050104480401c2d41426403282001c09021b964003224600384103005001c800d101d1b190702400b0390030f1004210b01c000682c0303c21242c50413400c20b204a500000c098820b14510000c0c01940c0816a03001d00d2144010401c070950321030500d800d941140b1001e001280e014503040020030101c00c01048400c1c402d43c1542c5c03521000c800c5942c3d56400601c1651491039001c112501c150026108071900a0601d00303100d402c44c94990401420f022180c01e1150090442c200880c0854807000020742d030b44240e000d410b43d00d4035100c00d10301704 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 681146357 1250 681145107 681145139
    0x90c030a14030c0d050403061107021f020f0d0e09100b031b070227090c0a031b0302041b030e0712020112060b031305100504030c12090b0304060e0d1d040f0b0901 71
    0x1c01d2440c00f0300b610744c9500843c003143d041d00d032f010700541855580c5d001c50104948112007510254010204505140b90050040018102194541210088582041c0300503804c000303001159180e03003500244400001c80041c3c9600000301c091022106490744d10000c2e05000390350000f900050040c16100364050100d040cac1c40c4c48010711810a5080e07440940003035450103c0000c1036042401d03c001030010402d03903d0350b0044185013042540840355a540891300715802807018500101d0911002e103915075050051211410400000f0103845041510280b0044010301c0000c1c14400c003061603082403001c0c0c2d0450700040200100985d202d03c2e00c91080000e04c1c10240084625005070741410100314081c0c89024003aa4041c1d5522040081c647e440c5280091039120324400e00095500008500144100a6101e40d204100200300c0c1c4407069211840c0c045112154001c0c040c0c85900c0c3c401e0b0301502034004403108402c99000c02d07800d03e000c103800014200c0c8a01903030132914010003c14640c1c07a00407010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 681147607 1250 681146357 681146363
    0x603050901061404091e030801031226070c061508101b0e06040b04091505031f05150306040f0b060102030a1d01030209030a1a090c030a14030c0d050403 67
    0x885a50303900c0c01018221102401507011140044603a40c3c002d040c641d011694840c481d03c02c01c0a920103150003d00c40100c2042d003100002d0b01d04005204120011401013213000140c14505003000e60360311101d54181c00d003815254405202d02c00103c005100c0d48500400c940c00560030041c03030500010344c0000d13194500131800d0a03c0b4118480e10710300070318407131a65140d4542c070503b0400d00801c84100e90060070202e000e5440007080c803020907180c4c503400062005000f6800c00140501826183c9681840d0a61206101c1c0e0402c41c081c0145800b051042c40c25a8091840003e06039500f95110701c0d424503180199405200744001c11040000580c480c030580c60058010020320303560640126900d01c5910002800988124000881c400704e20030044d4240105060240c108502400882d103419900e00c000ea03020040c0c40c40401114035020f0060344c204070b101000d809620480f50209070754400d14100200305030a01c440341c951a9405000303683e012003041054801d07042144034002c00b07680150100fa = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 681148857 1250 681147607 681147611
    0x3090807060501030b0709080319030b060c010b24031906120813320a12030c02040c09050102120c0c03120a0e01020105070c0809030a06020d020a08010e0f0121080a090603 75
    0x10801b86401880c0c00c50480308094029071500609a140b1619a0442100e031814151282421040c0359503610180285484602c00090300e000355904019262100301070324240b1000b0070349040c0c00c0c0200c50b0110707948980c001c4245074541c80608588001802c070350380a8915003145510740d008014035980205241d4946c0009100815181c007900300d2050030001044001d0302d404507c4500604244a5400401d8402481061090364a0901c03504080c103c503002c8000070f2000c0000411498148102405040c291038440e42d800d0401001035a00d00c2d600806082c00f11002c02d9405d40782d4820006402c00303040180640304000c50789100d0024035001990707004086821045040d0340d079441441064414095982c8002461120751203108040e03001c00f0809070035010b461920b0020400c2e50004003211048502c0059036031031608c3e001001008180c1008600b105401c060041c110300d10080300e0b05443c40c11461041064400d01c4240202e207426000030040079002c20794419041d085400c0034102e6000740c0701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 681150107 1250 681148857 681148861
    0x31e020f091807230712120f05040206092107080d1e1e1709070501030b03210922060e1f030b1902070c030201020c0a080606060a03090807060501030b 66
    0x445090450203e603020005500c550b911005800481c840991802e10003203020729011680c0c403000c1c17201980600c1c410104600c248200035100c26842401c0c5c107019280420001400c2a0740080e08510039031071502d01c10032140c20001600c8800e0030344480c1c850403603002c0300c0f141a96482c1d52500e40c0003030316401012503000f0201c00c44d5504416501c003a901c07250f55902e403031522a00314800c43c04100721a80c0c800c000102070005808800ca003074043c010401c150081c08458500301c0010f00303844001404071b000f608205150500014600b403805054044d41800c980c64100210104032554424a1070300850a6042e400c401d52641503800441500c005a00080d165640c0300c0c602e50714103901d12480c54880003125010408112400661a0003040080c01c80c0c804140d828004070503a084103005440b0013030510810002c40d1b8040090b520390307590130b99044407000d280210090326000004d117418019400010760701c007224071030343c0402d00e4964000242501c0744480d040101c0205002d00080301c034078500c280 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 681151357 1250 681150107 681150139
    0x6080105040b0c120a0c0c051f0c02010204050604031712190606140307030903030e120c01050f0c0403140c1806010e012a0c0b041d060607080a031e020f09 68
    0xc0300c00d104180e50030140c0c00d4035092217500051401c0b4001d0000c00410301c8420001800030701c81c5100b10046044410004080641a4802c5901c0c0180300410b581c410881000301d130f20340c0ca09680849401403002c0301c4484041107084400e04c5000354113001460440c007009800c6600445044a0b840d030380e08108440c0d600e5013000d856421141452a40000c810300014501c075100b500144080e81c868600440c0c40e06000941601c0c00c01a44089000e407080030403480b600500920605030711243d1402c020000c0d04100f154240d4510035400040e0080c0958048003c400c10204400407840070088c0079061940c2c80d80c0075400023034034262a410300050004000000e030350b12903200103041c83d02840001b91405003549182c0101c0c00300c20000c0b1030710096018005040b0400a0141c801004080201444418100c8420040c050000c042511800061004401044042044d0b031448909418009961b42e04140788014805403c201000303002d00019540e0324041d9242c1c003603c0d041d4002e640403020343c04601 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 681152607 1250 681151357 681151381
    0x70e0f1e1005120a0501020f0c1501050a0302060a0207120c050310050c19020a080c1e030705060a050c070c090f141e0403050f070f02130207051b0f030106080105040b 73
    0xd2008030a440450740140800c2c80d000e6942c40c6030100000403614203030215034845003641c201c42200c4101c0038001c43c006003040320502035103c25200c00c80040e1107941c180000505a187d460202901420012488050b4280200181c8014000c0c07000928804420b0b407404510165060003800c0c041d014240307100e800410399019443c011038141702e5050411b440d40102900c070621101600d01140305807003003100811880d40c01400300c054014040d0854000070149000c1c1da11243e0700f80380213540b003040740c2c50101c0c00108200313401262240c0081241d4070740781940441400341c020301401d44100c241002030111800e5200c03211084440b0010b10200e40d0f079107941c2c2d1a803101110140e0300034000b45034980359512080046940903200b820a075082c1140000c1100050f04500c1d402ca8000c00e031740c840709096150040c1c2c8030a000c48140015403401015546041d150680d410550b43e500000103420300041d518002c00c0683c0400140081183c1d65640107150b020740001e4909852030400c0d1400303e01408548 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 681153857 1250 681152607 681152611
    0x21b1603060c0809070b09190f050307080615010c240e12071707080f0409090b01051005180105041215050703021e070602040308040801140705040620070e0f1e 70
    0x4000a0b102e120303c6c0a101564951203060420303070180381c3c501c1c44140035020f200c458001d00b4400e002443e01a08282c1410b03e01460790308881c0140c4d2005007005000b13000c0c1d0380b01c1050490700f0701e0050260142450a68018034035000704100d01c0000b100700d00e00c070b91140d5100b000503406aa085903008402c0400f440d940e8441c40b84082c160240a100c143c401f000d00d20020700075984a00281403402c1075401040c01507801070b8011400c0c2c00e4607a40703228280447e401615000d08070403202184007000c01000584244a1142150700a04001c5640d4070280e00440a540c0242110450880794840c82e140101031002021456503603585003402090f84584644207903480281e1824414202c00c0a4096081c0036800034107003124115000c010100c0000c034044058001801e400c400410300700040c2100e0b00c10b07000018061400c118050004000481c0d00c0814210b0030444041800c40c100b0054040504000d0641c02081ca6010804240090210000c001610030354400c2581d10320303007140320000c0c1800001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 681155107 1250 681153857 681153871
    0xc100c12021308061017070608012304111e040b04030308090a05010908030f06010c0b0a09080909011e0602010c0f080a0207050d0e0a09110d021b1603060c08 69
    0x31400a00380d400e01507402012841d01010007071101c295140030036450504111041c5003c1003525108000040e1035484250054030001d010b00401400c0400c020700010051056107003060807181340307400250a0100640084e11b01803c284003080c0621907071031407940000207002102c146584400d0000d00510b0580f400e84420b22000351406d469a00c00300ca061802520190740c034091841c9103000130320244030b0b0b00940da11802d4516100e2800482031503280c14014416814042c00e614410001485500015481400310400003011141401c1c16480e80c000d0203201c1d40c00c40744440c00814010403150700d401031000800d55a480c4241c0790b41c0d080b82600c00004440020070380c207108000205001d1840743c2e40c00741540c0c2005007031030200d4886625007444100140042020f01540c0c0e601401c085d240c11016008922082c03200917401040310002d4400c080c0b00740701099011420040014400b1070503520340740442e080350f40b0354545a0008454520501c4212220b900d0501c0865109029641052103880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 681156357 1250 681155107 681155117
    0x230a1505040e0a06020c0f0607200a02011202180a08010f0c17010501140c010f0b040f0e060112020f090103140c0901030f350d0c031116080409020a050c100c 69
    0x100f40c0d900c0001c1e4000880303d40a40c0038031f152144004204000c80e5108050a0b9180c10301407128513003003118040c901c43c2182381078004658071005170360400c100b408030700030110005a48840b2100071489175010b1040c2e0540c801c2552500090b17050b01500891464640460708000c0001004010707240540c1c80c2d040c464503002e821004012660003440300781d00b1030b4007504180e4541200f0380c48442c2110028100314110b25907410b001c0445044c144541c00743c8030424102001491500304420381e4542b014450404240c5403064050110740300e01c0100030f010000038101c0d46007561030349481c41b103e0144421300b1803076101d000a01905031170681d0865040f01d4229210350f100da0021348448204064142048903041e0038075406683c000d4007030707013103100c49541007c4954403800500d01d8581a188800d415030205418008403841006013003040760880d000301c3e0091241003020f4982142e0301e00175980210042c1d44003007031103000980c10000414643d4040d50949080c034080100203011280241c1c0c1c2c00c0c000803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 681157607 1250 681156357 681156373
    0x801230a050c071703100f1a030a06090e102f0c010e060a0b1203030114060705070f0b03040b0f010e01060c0c030516060f090b0904230a1505040e 64
    0x2003181e1006402ca4003a5010310718125080d164503891000111000408290002c2006030400b00c070038030340002d404c081301e028a40034a0051900301c506240d01040940500020108440f0301c690740c4a1030007000010f1083c07001301007202c48a5200e984148200303501c103003400c02c180e82413041100005650640915050b03803160b401c050308034607504058400c01156599014030b00300e4110402c6154840c0040c50340101e400e000704800e00c020442007014101d03240d8010300041c4aaa02c04141c10700078240b080d5001601c40d80c490030240e03d4041181d2001000102d4050003041407540180118460390081400030095201c10b910004808400d200f03002e6004031a1006002c0c0a11822820786403900900c00008042d031203440e01c9052950742c0c0d520a004a0b240a0104911500003890449022007400c1c5050507601c0e02440100034480c5800c400d00c2150b8451444185054940c0640c2035130324050101050f9282501c1882e00411002405448178444180006071501e02401011950111b01015181c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 681158857 1250 681157607 681157621
    0x501172b02010f0e0c0a0503060c0306040e030d02040b09010809030a09050105160803130302010b09040308040b0a0f05160306080a0807080c0109080a030207020a0509250203130f080123 81
    0x446129641908554840c0c9500703c00345600e0107a018040001005420060300a03001c001180d68294411400780c2c02c00d60130419030f0f42a10f03050b290300501c140c9022415100240e040d41c298407410150303002d26403000c01c0224110000c0806400c9040c02030b200c04003070780c6a202e040d0341c1d43e0003203401a400046405e541030201c3c1d4400c0010700510b18500d807503494403c5550307682c01c20507003048914248080c211110841851f030b09001d40c2071010030030340e04200c0740d040a0301c005000c4500240080c1c020880000410a03251041c2d1040c40002103003c030810060401c03114142e10400d6000c0c14030002170074200c02040584021443d458070f03d44c0968243d00d44811684c4016507504504910499556a2150700000c074418a000349824000b580d03005070384620030310420240c0361858001d680a80007910400040382c03402034954844035480c0c0003c858511581c2c1c000ca1551040c10740d2020010304034000010560b035842d049900369007000703000384082e8048a02030500015070783d000c2203194480c04085000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 681160107 1250 681158857 681158923
    0x10308031b040504020d050603060a09020a1a0d02031602061609090b0f0a030b010e0f10120c0f0803040914160c0c1508060907082806030c0801050117 66
    0x100d9040c0c1d2406030034540d64800181c01c0313810004c2d000304030a80341c8040140502d41406140d50040c0d10782070800050b4059000314561b07032002e01500d90502d105400e00d00b204003184041e1542003180141c150355130303d0101c03500c1c0000c6840b02c400002522840d80403800401c01003062900c0d01805a5884202c903203480e69800141903400d2949402c00c120220000c107075100c0c42c03084006103000701c030500c0680d4580030708003c03e040004c01c031403824090202030103078107101c0c140d0307103000c441c1c41034290100d90340c2c80e003048182200a940024641c4483c542c0000384410044050811184010810822180c2203050008a641c04999194102c0d210043c00d611103405921807101c40c0780101030040017603440701c00044450300c4030b084d144081054001040110720300381c281d007903000c201d91030088250300745200304884100b000700f60b0340403556000401c4800d20226500000085030005603140b036203665000c250b40204400c4c002c0783e0b4284d030b4900001c4800700000a4040070710b8004070f2440f49500d442c40550301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 681161357 1250 681160107 681160141
    0x2103170408090108091c2a0311120c2a03100c021216030503090709020301260c0306061c0c0905090106080d0503040b0403140c0f0105010f1a1303050f150f01030803 72
    0x403c1d4115036011f19620005601a080326100e6250620b003030321006c80c0145010b108072588940102d0410501c0c0c5885004a841036682068800d10320030540211601003110f152035042c650148a05900000e60400942042c0e882e05c0854080d1a4299050304c49403d1503c11494003802c0280c0008030b5100280c451001140e06c10000d10917200c2080e2140d02c0c0109a0b0301c01e85c040406043d001205d600030400b1181040d40500c172041c0144409200d600c0840d850320b03801803440b489803400c5626126640744558200d08000c1e40a41c00741c1c490342c0c89865120040809031201c419940ca02000070420050001d269054040c0c1520f03014115652981c0d5003522000080048040281c1001e8540181000c00e01811b42c1d01c262001505c0303144400910142103560503400600101d10a41c2d040155121040c0c10780d1019036040c49150b6501c4044d0001c0d615402c030359100400d24852403500c035400303000104105010040c204880310786a2990320242c25a40020701018050301000c0000c80c40c0b86200620b20f103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 681162607 1250 681161357 681161387
    0x80a1d041b091202181e0703150506030f1f05040c0507060b0603041e02040b1e10030203060a0501050c0c0306010b0d0b010c0b0621030f0d0e0105012103170408090108091c 75
    0xc011160520001d06c4150340660f1032a02094a515455000d190342400700c1014040540d03170941586001056080c0405026000c1d195001c021582c031008c4544c04100c51018020141081c016592079540c002d200c3d500c40e0000780c403200d00c0c11b0b0400080340b4107501168052900420410f004540c481c1e2100000c7d45801002c90b401980c6d214109001e440c5c4c00b0740c028941411928480c6648146818403199042c004001ca081520400400c200766440820f0304060300d4081c41c200341c481c030028804074034040c0e0002c10541d1511030400000707039000040703006203508403020700184000c00304180152013000100c8070042046501d40006051418400e40d1100008072501c04515003402c4689203d0440e48041010720940000141120041a050040707403100d0341c0c004003c0080390700d001e041e138200301c04199030750400c0c2152419650901d031040f080a00c03440b042c50208036035401c1c5841c0290b219401b588905000c203520400107200607002107644290191056084440381414190858204200300c400b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 681163857 1250 681162607 681162631
    0xa021c09050301051312030605010206181e06090f0304050a090b5803050715020d0902090109020a09050907121407030e0a080a1d041b09120218 63
    0x546036003d0084d24091821051200800c150030305003980490741e6469010305050a18404120f6a640055115800030746100c4410b00400e15003042d03400c00d03500440b45010040c03070100900d1845004581c1601401c0398404079214120400c80598890103144074903680525000f0040240c556a0b4125020000c0b000f400c0c80b5400c2c80340d528410403442500419141c0d4618403194a02d580103010324107501c079480300000f042c00900068600c0902100c40d0000301004400311b0407200b0450520b2200c0364015080106548540714420030500800700184c0c182d00c0741501500000300d400c050700c210ba040c0c1c0301039515050580d040800744055980046e103400200010100100201803036031003240b5440500c5c2690aa0328280706000806403031402400d60703030b2500a030030194000380e101c2d4100c42e01c01d6424104081041c48521142440c51a140d440940080c102030030103004c00e82c42000300708190466200c4a0301240ca81b16502c070310300d0200038000e40111030400c1010902d08004c03d255804070400e50b04c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 681165107 1250 681163857 681163859
    0x30203100314010902040e030f1801020a050d110706110d030b030c0301090f0c050303190807030b0d0b040b010e09150603030d0e0706020c0d200a08030417120a021c09 73
    0x2c0000b144402c40140095964506100c4110700d00b9001d041c030380d590303c440258207000186104d9a0180704040304007034001441000c606c02d0717074000d008000ba01900700302502d1407007a0202e0050100140c201032403003e4080c000c0b01040c9940a8190100030080d000c0003404900c0d480f6205800501e54580440d61610444003502d806540034051b803c1054440d86c040b1100c40140e01d03081c0c201c2c48458214502c42d8105012481b41040c400440f4250060180382c81001511034003400e81c010600080b0103900010308840003070a002180502c0d0707010b284034003403030003140c1c0ea1541580c103901c90540d84055603400102a1802c0040c140303080e15005030008060340e15112940c0c0c000d0040b01c00500422400e508102000c0007526014814142c0041d030684801045155541d25160396080b80c41c1340001c04d810725410081c243c0c80e500c802c00044c2c5401400c50f07507250b03242d0301d034600e0401c8402065001803195600f0007107002052400e460f04480c55800901020803486400081c8101c406000c00401c444080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 681166357 1250 681165107 681165113
    0x61b020d090f0b1e0d020a090504020f030f0c070b040b1e010b03180f062509050d021e09091c0e031b03120a0309230a0b090102161a1003080a0302031003 67
    0x10501040c3e81d1743c0050341c1e0b5141d41d601a01c440c560703078001d5200340e205005100064906108580e845036400070120b0f4035660710001a052401017a0020780213281c81002c00c000c01c044032806500814032010741e00040304010350070340c0403120240a0003019217030610225240060302049330003080144004e0320007000e0940713911b40c500403085520b800053b81080c904d49201c440072058a0008005251012000e070800c0c5c081011748183d048000c0c004c0c0c0c1880360f01c20450b51069039650703840d107000348400003504084114503510500711141d164890854036440c4512401060301c00d40010b030103006052248035005001014103c3c1d0141950140102c1000c0c3d414400da0f04000c106131186518000b0f0403070000d09210360208090000c0c0c4440031717090003569608a900080b00039500d42c3c000a01c40310796880c409607502900403049146128042c450000081109105071000e5030700303102820f4031296403000744290000c0c040d444003820000081144554080c030a8000f140e02c522620510314406550755 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 681167607 1250 681166357 681166417
    0x127050409081e040b040501200a0c08010c0309050a0b060f060a020d02061602150903040b0c07030506091203070315030c060215010f050f0913061b020d090f0b 70
    0x4900b1603002000181d28280c886002c6070401c2c4140c498040300341464105004044244254012907052000982c903c10311801c80f02e040c031b00d00059000a607803030003482e450003d164148500600d113482d402c203407030300185910034484c0c00350498210000f06800d1415885008400ca000707000243c004c040d03515482000c1e107440009100145140d0300401c0359800d6507000070308214014010000490090b0300c0001880d5001030030901c2e0315001d8400e81c0382511642410751a504c10741c1d106400e052800300e5140079080340440c2c00d80440c0d01503410b5922503a110703c1d0840c1c80303510031405024205414004202813902ca5030004a59134450521504220785035110100c2c1c050a952180b00181e1188100485c0585091219401807900d003d020b801c081c28140010042d10348014010302030804400050741080c401c0741000d1303800e90408003c00190340020800340c501c0e0000300040303000d0310400b0307032441e001441040300f0011a020218908040c905101d0f444e12203034420f902e060b2050700100d0b0504641c01b00c3c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 681168857 1250 681167607 681167621
    0xc0518040b040612030f17060a0b0310050a1707050415120501060815010326030a0f091b050102190c050d05010f0e06011a04030b0601051e0a0306050f04050601270504 73
    0xe0348401c051003404106c014842c0c550080406100d12030401400b1441d1604080f10302551204510340740c46e44c1d10503441000c444c2640d07201560140108c0720020381a1807076211505801c5054041d2404035448509010035240e0411030120540030718030003008168680b00843d810188681c001251075666100080e281801d008124111001ca10004004001c2090420b02c04681094855070790380d905544010344c03601000308203414003502c80c1c001c0743e095901a0302420303085a1000c950103c21300800c4103001c0403810390081c1070161088500d031941c00e02c80c098411407107543c090300d80500681000b05114810000d0300048800c2d648441981c40c1c0ca8042d402800c01001d0004000e00c520340c07621030080c80d800c2c039070b40241850590400c0240045540c40072000d5004400382031040c0e450601c08002e8213500d01558403001382290210310380c0005a40740c3c000d24200c0700d0489952202c20424800c00c0200e6406a40046c041041030b0900120750008201c0e0802005a8128010485581b1000709090302c00c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 681170107 1250 681168857 681168863
    0x23a152d03030e130b0f01180305060c070302060709080304090c0c080313051b2b0803090607081b0715021308010207060c020606030a030e0a030c090509010c0518040b040612 76
    0x2044000000e40c0c01d00840c501529400800c0500000c01780c0d802141c8100d4180c0c00380750400001c591404030f8400c030b2141c0540116440f01c122121032404180c1d00e0425081100110014014400403d1003d8407451710071080d81d502402541c0740519000521700241080d6100e03004ac450400e0102c030100754030300050b611500d6040011901556145040703414205582d8030741039100d90710540d8240584503102100e2180021080905020390260381503031006d50100d90040c2039030030010800c00e40b4200030403203034011503464486805e141c88030304107000b80340180700c050340b183c0006000c3d2801041c4404080c1507102e00c0400010b1400ba041184400d1125180c1c003da00141e400042050410465114054440c2075900c00703007106091110000e0b407500e01d80003014040180c80c100480c019911141140c00a607440903040030902ea84044050103020b0440c0c5464180d481d1081c16071410b80542c0c03c0306c00180c002e800c141c8504006000f000020581075101c190415a5010013060420022080780d1650340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 681171357 1250 681170107 681170117
    0xf140708090906030619051302100504030302061e0f06010c05010f0605010206060409051e010b101d0a260304030f2f090f040501023a152d0303 63
    0x150642440b0041201428490103070380030308100b0182c0c501d0500640c1e001056442c0114098403a424080c020300248040654800010125000515084001402202c3c4a602690040e0380d4900848010744615420ba88882010310002005096041403403584004141460000e400098a5080c00c5400410038240504e80ea8041801550380400c81076500007000c540611100201e5034800740c8810b4072684030601e03140020b03203011202d00290000c0b0103020002c0c1401619151400b802022003d40b0300240300016a940d41150003410b103e40c1d400250717146401d02030301a000a00074002c0d003075900da58413800d030300081c0004000119101003030318416000d201c82456030f800d61089141110490307003010490750104501d100e26902c0d40000b25600c58152450170665541d5030801501a00c150f01c400700400c00807038000100c503000b80000070640444c607100c4900107209100c04108031103035000448041c900403a0304203c0e6400c542a80320821302c0090a035807041940c00080108660a5002100812 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 681172607 1250 681171357 681171367
    0x240d0e1f0525020a110d050715120b0a05190e1003060f0b030c010e0a0305010501030c0501030509030423040207050a0302010e0f03090109050f03121b01181203110c03070503091906020d0f140708 85
    0x12b80c04001742c40c402c82001c0b820442d0100340340c000f03a9248031510807a401540111440070801803190f0044008182480d5001c10038605a21055990f05e460301080310024584980a600b05031140728000e8942d0004d001060503c08002c01510307030b440711010b8954498000240440000c0f420b00801d40291310400031040c44504020024040c0d8000a0020100d5401072008020050020000d0030303108a01c590b02d0f549000c0260003050207440b52135070140482c41510803810825030f0561042c9001403240058504112081450366103e115946149000070300c403410a000500d00302c182e45080b071600074101c0b00e110b81058001101908014071b65290b003d02d0f0610801c000c0001e0042e0380f5401d41700170140e21540311f40c1d5580060040941c40e010105540c42d540d0110114983c0100c48440308010304403910380360140fa00c42d94982c0006e1a00b4040c140c0d000004d80d1410965420606503609900a0501c00c01d80001c21981007270802c1c030079806c22403841c07109480440e0b0080200b00c994040d81c00c1560310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 681173857 1250 681172607 681172649
    0x302070c0b070804030b0a090c0602240105060a0e130903020f070602070b12060112390e09070e040911240d0e1f0525020a110d0507 58
    0x410959000e0300019208009510000310301e041154183d9a06c13a282404503152000c600b4010301c54500e008021b14501d00700403c0d9250000b4044081104400c4414040307507032403060000380b2800380f00341c5401001c144038166129000705881e40000e9404ae003110b640a403440c4500f810380d4003c4c0070540268000f031040602124007801690044c242340d0004107491450444002e20707078810840740003a080100d00205d059684154441c030345020131400240881d10310002c40500115262140144942c81c00c410443d00710031081c000f03842c2854980b20354860001c610b081c01000740005050f9810441d406074440c01a51310b9124800030140902036024400700c1040912400c0000404500e001140005034030114040030000c5030504e2040da540414120386100101d440c240d02201c60340f88281c02c4200c24080090140e02c010320440b0502a240205491180a40200520341d0031460041c1c005806510100790f0340440e200c03103c503014060000001142c1c68a5003090802e4002d000100e100303102c1c6580da = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 681175107 1250 681173857 681173873
    0xb0906010b0c0705122a010e0a0e010501030b120a030503180327011107080109050d050a020c011b0b0718330201021201090204030218010501120504140d030207 70
    0x503000902000b440c0010b00300486035100100c0c030807140300b03a5041c20f400000482c00d11440c20b507921400703501c1c403808000b000000c110340e40c00c505460010f450f0741c0c1b5404031071810f00000400c6515201d2540343c80c1c0d0a102c01100a0040c6101c025042329181d180c41e10020030410041090301d00903a0f5060722400d0101204200c44081c640707000d407603031050008400705450442c104433503181c000c081e582e50b03940b0900140c90500e80018200200e010b200c00015001038103402c0700c1c0b90288510141c0302c0502c030005046c2e90601400ca005c10040e0f1213410070885a50017046400c4a8201030303500032503812207039a00c15441400480d041c01c00030f1550f4803568084418048183c0191542d01096034580014110701d4202000030001c0200b19001300929003a903d000394100c038445030f159000d910f040c1d80c681c00c605029600c1407004a0103004a6511030412600307803007009040c0c0b001650b8484201c1c4403443d0074405000042c20030344071204003811440002008000148910603e5140135845208505180e48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 681176357 1250 681175107 681175109
    0x3130303030606050405210f2d060705121015020c01030506030f0c01030515030d051905030601051603111e0106090209011b1707060504140a0c1215090b090601 70
    0x4188034040c170051126989520900001c1c030000b841c2548000300d0541c02c646401481c980f103c419004007007101180c440c00d841130202d440755540d980446184d416880326942d02080362150000b40e42403000f0b002c542420306200e03400883d502c0400d100f803521a03049003c880515903480d0090384c40189007900359600f41c002c150703000074100c010308220700c44800700b1900c1e510364504040c10165030781d0010360110307440030b100d00c510700018080340c084040c000c401405507405810140700d00101c0f003020304107442c4a40308880c822001a910a801d002100c0c0f02c0e07080301101c1800c00c405004048030084e82c0b2000c104203030400320405407011155031a95183c40303400c480b129040040f0316401008241400d90b0051850b8100d590252404154050203080221031403400c54414214907038001400b40c14040c1d16000320b4041d41c010b00c0cd03182c03400020340c10701d070355440c1080c0014600c0c035403007008000758035146a511101e540694580c102c040c5074442c841c01141d40c9058201d4010a8171400d210080c01d0400a0328 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 681177607 1250 681176357 681176369
    0x30f09060703091106090402040b0c0102071509030e01080c0c0124060806100e0d120807110d020736330b0f070803040b0403030c0509011e0c0203031303030306 70
    0x300b40c01443c4c440e03401c45a00007901d107000f0000010206026200ca504031401401040702d080d031512aa859028040d502801e0152a44081c02c1c0c0d541d0707540b1000d4400c1c4203000750b15440321204203080c0c50054404600041a80e0b21a03a410300c6040c26004c0c4c00e0080d20041e044281d461300000d41c03003080ca041e06000640000b01004200300c100442030300c070200318140c2c43300da5081c680144000b80001a0001002031310060540c845403c001031496007140071140100c0c42512404503254040b404c041c1d950403000126801a80324500801844000003042c0301001080c0759405229800284060004170655902040c01036075460103100c103001c1e03254008034104c060141c2030840200c4c401034070041003031805020790303d400000700a0307420340448048840d22640310b091903407685080d0074161400d1104031030903408281041140f0030f629101d1003c5a40712041615a4034448800c480c80682103034038840c1a1050151050b411800750740d00700060080100c80c1071820480900f180b800400b5100f081c0d10507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 681178857 1250 681177607 681177611
    0xc080d0c0807020a030905040b1207080105041727030f0d020f210d0e03130b0903010b01080712091b0e0403030f0501050a09020313080c070303270317040308030f09060703 75
    0x12500191b4000070341812202c0464004c5400f175400400200c001c9403415024001d40304024000a0040064014174483d40c080c03074104105030303800b070011444d0f8812480800740b18161124600384501c8040000890301c04080e04465410404c1c04696160500301111400175a000c642083c0710080c04210905c445240040308011611000c0c881c400c2e03038080c0c5018aa5081d894802c03800c00941e040040e09d0b4210100f505602685543e16009c0b0a258010007581c1d000b5400c21821640650041040e01c1c0210819550500032003030142030f403001800d00c840300b222004030710010018080c0141c01010060030700111404160300302440e0150846400c141110142c070b0611004011984d1091400000c1701e1101d140980d036951502241038134081403000040440350040380c0240011400201c5800b0f60344251a8580440e221140601101c030f050072450f502807198440034400103084055044c910410107050500342034903551030f40c4250304100c03030491102c0b142200300050000100604c9405c03034028281 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681180107 1250 681178857 681178873
    0x3120504081204140d030c05070e06180712020d0b040c081008010e030d1a090a0c02070801051510050d0906090303141e0621070303020d1115070c080d0c080702 70
    0x4035907940b104d81c00d0304901c40c484007102e0005150190500e2070540382e00405941c1c160307489080c034800410781520601c0c02074a85000041c6960b406940c020b000304015100c524140b016036181101035480b105141011070307113410507448a03480700c8c0105440c00400740c49c0e0301d0007450408403568141ca259072020340720303a040921410500324088200c40f28610460808160302d05150b06056844000040c620340044000702000300f0000707141d0000041540c00da00340d0b178a044c2c0d81c10b5564269041a9840030400000c080700c0d01d03061400c5008403030b5400140c20b005003800c08411413003048880218041d282c040d2204c06940030554180309001c8900c00c180303102c0045003081c0386403101e18032485001c1c40310002c1000c04610360303580329010303034041d8040311141400030380036000e01c940ca07001940720440261184030588108c460048041d9000a1000c400402c000e070f0325085400340c0d038a4050720503414000c1440b08400413600043c0100040e100284020406101c402c0300282100d0b40200081c04541103014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681181357 1250 681180107 681180119
    0x106181409120a12020c0a03020601030212010b01090510141612112d0a06020c011b02031c06090e03090f01110c271603060b0a140304060603120504081204 68
    0x20a80c1c3d00d0541603c0c20440601c41504404000d1044c0d0340e4400040c400c81006e8070405a00181d024142c030305c299511119124240541420b9450180303101d40850300702802485903050802801ea914074051a05400c68450f05481841036800182d00742a1000c066075400180607054590b1440e05540b8600103500180c0d402040d82c03a011625a8094640950200c0344503401c100003142003074800001c1500c8461810b864000002d50220000580650070450651030b07001031446905144042c54000d50300c1c040070b10203100d10f244c003003840404003130340da4204c04103414000d4400c00c80444103800045555035502010400303000b41c18805681001075900350903503480000714040883d004191802ea0060002c0c04044e4034440980c450050800100d030208403c400d000f108014885459031010050103443d420305240521a1540c1c10011422031070230780e01d03504100c20043d0360260148a0005109071031f9035444030380d84003504200b0000341010805008030102405110314008041860a180074a849 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681182607 1250 681181357 681181393
    0x304030c0803040c0b1b10060303020706051323040b0a180e010b1002150c0306090414010209030a080406021501030b070c05150108060103030f03140f090106181409 72
    0x2800181081c1011022604000d503890740f05014024400141e03071550101c01d503c0b0480080061604824412a4041001380b6040d101d030106994060f07010300748040c1041030a4038a0b50081c5038101e68101848400070341c1e8408080030710980095a02d44000109041c000c000a0320107401c8810301c54511420100880e070700040c8000504142d040d030101c0d028262180702401030840f84030f802d03000002c58421256056021944404128074029010859144d41d16029214081103400c5c942210107100868007148036248140140814a400136140140400220381000e10082c0111850003000c60706001300380d018000f5042580200100c0b180562460300c0c0c4030400700340500300d0f00910002951000500c04207011200c0f941c2c0f001d560a203950350391200c08580c1c50100744005e900160105200d040e00522a00840c161030489585540e2a84c075400c0300000c810f10090305d80c01ca190341e10740c3c3c00241c9613140030140d100d400140200140d00c0c1a05802d03e0f1400e00c009012010507000b080030801e008203a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681183857 1250 681182607 681182627
    0x50303190e0d0f03060905010308030406150b0a080417120709080c0102031806130803030a060b07110906120d080f09030715150b0c1c020706020717070f121205030403 73
    0x180790014400040c0f50040d40200155084401010700300000032092011580045000d1482031004108500c00d1114010340c0d0f440900960b17903168000c10882108620030304802d07402601800118425284081d50101e203a448220011800120301e001c100480360040c0600000305001e50251145120102c0001d48030701c01c42c80310000030828002900707100d484e61015102010090484070440707a8a6481c2d06940c1d400032505290311508002e004a90b4047c0b18007600d04070b6900c045030080c0303101d4100420401c100300800541d0071055107420450030715020400d01c0f0994215440d8070655080c18240000002c1d00201026440d5208101e042c00040c8501c0c0f0700000b60392201c0002440500b402d142d000c85d421603500002441ea00425103100b00301000c9000c0048070304000c05141803004a08050361143d4140c801c0d82d025030800801002040c485017060000c40000100751031070b840c2c4585e04940360740220303000b483d41116035500e140100b04800c9840c00c003000807030a00500398030b05030b94002c0140c007030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681185107 1250 681183857 681183883
    0x1050907170304090c1e0f080f090a06240f0305061b070f0605010801203a0606080106050c07051003090f11041d062e03050303190e 58
    0x48403001016501c091054501502d4404004c1c050311700440401840d840055081010140c4029907411032540190000300300200c042d10f445800780e5518400d80d00e2450010046c0030603008080c403800000c2c0e0746214004100100d2010b0881c0144a1440d0003140c0d001030300442094480352100f840891000194a603110803030b00700700140444029039400c0305001c1c80c00700601032a50703030101c14100541c0f0342210317060719654070081000f501702e1410a10038150a046036138007100104000750f80c0c0c0fa58026942e200003210659842d650302c2c5110014400e12101c4071840e802d0f60384503000d120280c0d001074800d00405080c40d10500300510f43d003040d501d0340500d1050600c01c510f80040085460701940103454500c1c1c1003110507107400319078103080700444905e00c86244510301d0403080030f01c010001d42210602e041d61030020441903a41001e18540501c1825040c121003170702103500c0384007203a48801a07018621403000741d5180d040004e001e240401c8c04502d680d00c204d081000ea00d540d4000000c1d0302d420a0b01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681186357 1250 681185107 681185129
    0x71506151b0b1806280b01090905150d0804031109160305040317090d08070908060c18030d0e1e091306020f0c0a120206010e0414030d0911090901050907 67
    0x307078801414900039400c0b95010301800395400b007000354040310001080700c4403000517207081024240d805800b140c0406141c18040344103410305001c840d44541c0440c3d400700940e8001c80da80f0a02100054103096010b00480e8000800a400d20800143d41400d144e0440150341d6102a42095104c00b84946a174000c91010183c0c1d600004003418840d64030700ca811154060045040d0a00300c0342540c0326040700451501140154020440036489444603904586c503400241134141c51742c014040f420b80c0502d0300c1030000d07a450000c1d40f189507400c2c80200c8041c54140c49404004110130117008400010525091144c44002e8200d0000e44070404003a6000f590030a080701d00d441a850300c100280248443d8400c03c040206840030100c0001411082442c02010a4514115a80740407a40c6010034040c0c84110910b00022030006100900c600327030602003410039242807038210910070f0704851607500242c45640c412904213171903061041645030010600d8000b400b4511f04042e000f41e44150600c00d0b0980c600c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681187607 1250 681186357 681186361
    0x307120b010905151308030a120e0c0a0e010305010f050606090904020112050114011709071502010204030204020d020d0b030f061602070510050a0206010e10050f0402071506151b0b 79
    0x180c422502c480190400900300841c15001c0041d002d055048021065214918550081110b40c00041526014400765903103c540026081c90a03020f070142e1080b0210511a400151515540c5c41c4a69000b400c1000c0071003405603d10700702142920402007101882ea49008180080d613200c00044640404064503801240c0d1500d100480d04210646030329400186008000700d101e80080c599180519404d90301c2401d00810031009010018003079680c00441d6008010410001c10078403002074040140740001070400343e40e40c000c00d0a980c000200c21440a50000e0040c07070940a41c881c0402a0900b80c004001d007502d6004220350700c450103429007141e5070301804614611482081000046d040203480412007405500f0042c1040d0070140ea01400750081e80e0000c070b20045030498080c41504510a001c3c0c00ba80f50005000301501d032004810742058081007901c010a09640c1d40401c003141e0034400186030752078072959155990110034101c0800c1044030351240418643c000000c070035900b00c0c582014079 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681188857 1250 681187607 681187609
    0x503040201200f011409030a030e10060602010c030608190b0a09060f021809090c01050706091e110609010503061309020d05010203070f0e21121c0c050307120b 70
    0x40c040b50b41841400b40e014025510b400d00c1c045074000300004450300a120051401c0c0c07102100d41d4088804190f41c4e4401d0000e030400c1c51098000074140c44000098924500108240d2400c0c0d5045411401c051f03034507291082403c981c544951001800060041c000400c1004480d0000e800e0300200600b90040241c0418852051a4400111503078824020821110302005410194015400c0030001c410307030341d00e09000303030402c0c1004902c2204000c0107420300d038009a005449603003025601303a41d850350b200b40010015030f10030b801c89030650340b90944107034400305490498440780d008102580501001d201201c4c80341d070050140d0341c00401c21514116103c0b072051001c40208582c0d00d01960004440e0b01800a0060650045002da000c95031195114a5403e000340c1e402c2c00c0c00080a50886800c403c0f03603050010b144402804001c0a03001d540c48445e284221500720f0300b188400906001d607080074407103107003071a115a8010f4030b0b19084c40c904525010794090710a603030b14148491a15112079150510f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681190107 1250 681188857 681188867
    0x10503030d0e0f0a030c02090708061807051603031506020f030904020d02090303030f0f01050a121506090606050d0e0d0206071b0629032109010903020a030f0b0a06060f0503040201 79
    0x401040f0508940300440581001030080c01030240030307805103600307001144405110300b4003180f1405000d000f40140040b101c100b001c6200009007401c0801c2401e0040d404902141072400b810107000b40d50119151000240040c1b020300240c1c88002590b00010031052442c0c0e001c402d441541c10100e80040e06d8500d1042c46e0340c068841d41785c91681c180400020800c03007070b00b8002580c0c01200e4071605405030baa2030308107101c0d03011020f00035070b0341390030b00702d214280004c4501601c81d1060210903400708032503598158000035111a038015402044010035021034000c80d901c18410807142e220010072204a080402948a0700d014200c841080102e0000c5580462100d450a01e061340c410001c10070700001d144800ca88a510301d13654075241079042040280d074600001e403003500001e0010070362810301452414075810350028810b1818451031810003c090307039900391050020f43c05850941d050450710310b0880d000000c014882100d04d0315000052101c181c0c82102442c81d642a41422690390700c0d40e0006884d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681191357 1250 681190107 681190123
    0x8011a0906010c02030c13021201060e0a030b07030b030115090c080f0c0a180b090406060e01080f0a0b13050a0b03070e011214010c03060f0902120613060b07060e15010503030d0e 78
    0x1410507403240c2090101143c80d8000c0501c14227490400c800c40c0d0300c5030422120450850380d030035400b00c2c180c0c03414400300740201038068010301c00e03060014403240e464010a00f51850611400500b511011080201d007609010b050941ca02c00d24040b120352070700165958210b203000e03050f800c224901280e07043c00c0a000b600c074041503da0300c0c01418030b1076540302ca10242d00d078030131500c5a0286003404c070006a814040c481248080a05031290951a554200d80444494004041d082000d46826003a902c603140c0805840501400c1c40e40401c261508031240c40503100d000b07a90f0b9020b42d00403c010042c02c00c0b2075040c4e9040d070756180301c540860f040b0350510003060103c00d6001c40203546800c2540c050960594042c0003142c4000c2003440c02c0310355a40d81c070b00c124042c41c500c41661540f20b01c00900d0b6842d014018506048a035040000c20301d40f15880c00303159030003642089611640d00c0a6130241c400d42082001c00c0070104260800f055030401002c80e4a90190034009403a05480c1c4610b000c02c00381c01e0102d07072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681192607 1250 681191357 681191359
    0x30115022805070501030507020d0305070210140a1505220204030b01060c02030106150210110c2a0f150a27031721070c02060d0608011a0906010c02030c 67
    0x40c5504040700319154800e08001011280c5101d10040024594024021039100c1d5000da0080c080c00c100108040c0c1c003410005091300d0450103204081ea00d000f00764420710141008a00e51620f89252a0f41c40d542210344801b10918000740c3e51108004640d6030b0031140488040021500c580200100c80d10006030081e504000c02d060149400400c01e264802c0700740400c280200c0090103150341e00c0f07044a0900381c45258450042e007100040c80d124a1079600114003400d6490001032504682118050405044400f41c0d0224a0880d4400500c14458080440f518a0448116030280005800648000044148200b0503240410b007a40800c1c051901200d210101c1d03204480001d4004121000c80c00090008a4281e14040350b400543d051060a54a99418000d640145120340f44001f00d00e107a00100300004225007011401d0042e200c1c01c0250154500c005070201d821410300c144c60f8290b802c00b00102260005900490006075607401c405a0400001c1c200680000c180d030021900304240d0880903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681193857 1250 681192607 681192643
    0x120f080d0902010206100e0112170a020304081b03060a0e0313060e04180b04022b030c0209060108040f060c12021305030607020610030b06041b11120f03011502 70
    0x103000111541e4020740041c034401d0f402d5900544d9540060403081d5020b000d000c211030840c200502c0202031240280340744500482880010703041100b4285120307880010b41c0c10042c2c0010908212035201088210903900700c0b6894810781b0148500480d0350791400400400155450380070546007604140100d55012400c8001c040340d0b1910b03000054607142000003030320300071480e20710000b840c81c075451011140c1686c0708030640c0c160f854540070442d09541080358000c0510a0346c0000422610b6030801582c1a0711130303190320803080842e00401c04894402003640d0305004d0030004020005480c10b42e0000b407107500c85800941a0004d0380c013141d910b54103203081d00351188001075070769441c0d039500194400c03a0f6044003110900d5803444022a00d9140549954181d40800f00d024030004492203003495005d400504002034a0305882100491404400705001c00302d01d0700080d0108609003401400081c2c20800c400368500b00b0010f07040b40b204e04c414480c4035200b44064580c0f0700194420b00014410390320160344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681195107 1250 681193857 681193867
    0xb1f1d040b0303120106090902093604053306040f06050a0e0405120f0a26010303110d020303060112090203010f020309030409050105030118020d02130c0203041806030c120f08 77
    0x10040e041d1130207004040126136148070028401d0001c1c001ca03100c2000103000e84403031030304884440c0014402082c00b00c40100342440010014000100200c2c03045019400a00030890824184803042c0180342e0100c004000f00702072280ea043e203405406801c00400d8500143c490b10b080b0840d002840c091f003040b41c0c03000960b180042c00000044109d400f0b1401001901c4004000c020f400701148a030b092007062213403052000c0d46800340240340340050301041c1014000c0c4240e001d20609600b0500360000c80c0404d918407503071704100c1403c1002c01300c0c9182c140015491424410b002038848001146100541b40d11043d80e082152001c1d0800900e0002c0140d00f55207030b00388200c480b5284d411074000c000809291100000d458038050044e40504008125840f205403520f40034040f07070b0441000180e80015100c480110081c12510034003e00590319400380da00c0f54207217080050122500b6940613440e905001c0140040741000041c2030481f4030b0343d07100c0a00010549480855600302d5030001d000c0e01800301d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681196357 1250 681195107 681195127
    0x3010905120d060f0524070f0b0f0703061404020705100c030c020f1504060e0102070b07030203070315030c140307080f0d0e090f0c180303030a0b1f1d040b0303 70
    0x8003034400410080414443c072a12200714030b01c012150f21820750700108200311148542c0c0341c26510480008001455482c2100c02d40303075100e8480e60440100d6680c42d104040100c00c0d100e4115041c1c0214040c981400046c0c980020351400703001f480706862240754002100700c00c01c0b4040006404168030140188201000e250f800303401030982030070324000360040c01040d165001c400304004008125119510907952110b840c1d010040c003101615126541d800c02221010070b01030304c3c3d85803003030256030b5002d41d5034600003400030300343d0708104280080b0b040c0000051000900003240309058980058084a5442d24130002034505001540250294010750540b550060350100e406151103030140c48441025299038107111400d41c0894041c00e550180c0008940903600a100078501f1140100d080c2d0034495007040004d0a580c41510320940746a61005458000c0c2814024a054400441140d4201d0b115a1038081c0604140c414110a504054145169259515440882c00c000050f040b0b94070b03503404403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681197607 1250 681196357 681196393
    0xc060907030302070f06020d0e0103090f0c05041107050c09070c2a140d1101020c0a0e16030b091503120f0c0c06190c020604320f090606030603010905 66
    0x40800c2d00107010f805408a2900c075a50000400c90b00d080d4020b020441d04164101e52164140000074109a200c0340d0b00008503803d03104c5172440c54014240340e400ca6140c08100700c03c951101480d4078041c0014402840400c0002c610101541d0054500c21308030f03035514000725034880100340010801c980402528640e02d840c0c01c40000b0f1900d080480300449a1a018620050071203410440d9201c01f01c0050080018140d00a140a01106004a6200b0020240000c800442d20b800680f0004201002c02220752112103001c01d54480509013081244640000320b13080010040210800e4540d100c0c6884ea42c0d20100a6020000c1c480030401361a0100c81000041030761020308410941c1c440c00c00b400825147c180200d4002004140ca02c1c000188400d00581d540d10029105a911181c18400043c06000380016140c840348061940122486160804125200603035040ca001e81901340302101e036a100e2101c250742194040368240e071a9034074200001d0261000000c01049030180c003d00d400c900c0450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681198857 1250 681197607 681197609
    0xc010608100c0905060a0f0e030f011e020f04030f0510110a11120301140a0f090b0a09090209280c0f0e0103020f030610140310060e0402030609061003020c060907 71
    0x240300d0400311000c00c540b60a0303d40030340b55025800f001080c0c03402e805841c06030020302c01c604091002e00c001000090a00c8006010100070b03075102c00004080c01c000024510441048090450512005070f00a0390300e4019800001c000303c8050b0420701c14410200a40003030b00d110a00c013403204d1000c0c180c03500c03030039046500c003200401e0345400034034840440031a2030142d04100715400c03811070303183c4004c110849200c00d0845402c2510f800300400e06540388800f03c00546004c80c801700c1c2e4084c8240510010034000e0b4017144126141c844840c005949071164030750044e07141c2c00411002414500307410000341150b41d101c14201d190000f0a210307a5080110142c413260b403610740641b0102200c005405038400c01c801814250b20030800181302e031403d0264441600b0140c81d240d40c0d00e60494008901d00d5009903641580c0c40242c9604110482d0700420b100348512060300c055046d400d050f00801c200d02d00142c42d440c40740245180c01c801c42031085e41501c4519801c0c5d41151a6030900528082d1542c00e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681200107 1250 681198857 681198883
    0x1204030f0209010e060d120c08040306020a02070b16031409130603061d0a0605040309180f0b0d05030a1211070308010306180201020d2f0c190b0f030405030c010608 72
    0xb80002071240d103000b007601d108140252091294900c95a00e42c42c030380d004501c444042c400c201c00780d000840c4152010f1b0002c1c5108040050380c0e01d100d143c02a1600a0b164008201d0007420881040c922408145158003698541402c03c030101041501d10450b010b0110388076000000c014200074a800590440c46c100d0340294402c02451a89114000c2080703a20020742d04558000685080003402e5540801d0f4464040e103000c00b04143c0b5006040155962680743e0f070388041d2200340140c001c04062250000c05102240d0408440711a80d0345c81c0c2d101c4c0500074403142070000c0100c0100d02a509a0042420000107526481d034031070080c6805070140d4020300050b42d42c149000d0101000901e0f40e410940b840c0c3c0c05800506030741c421103808442400b00f003022212107100701d994483e40c61540d00e24011220550030301400925100b8814000070b146108000860100e214030200002040c000403100101040c5a809543c3d64450426a103141704400d070000319503182600009441c64003040e0520788a02d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681201357 1250 681200107 681200119
    0x2707020c040216060609020f071115030c0c0606010c030c0308060d05011b021b09010302130207050d0c0b07090b0d0f1e2a020d05070212010c0509210a020d02031204030f02 75
    0x6100d1803074408038002c1005066aa00040049c5004100142411200e010009000310305202e09584030b4150b0350801c3e41c807107911100102c1d0030440607001340100340c1d00c481b003884c100c0c04441003074074000c0c211903440c80d01a00341b0500c0c0000c15000d07152003115600082d001030003408110059210105a4141000440300501440a02c80c1c400e11004a6003145d4410040510000e41d0841d000c2101d401c01040706a0182642005482d00080c0180440b1030a40d500342c4400924080c5400c206844010040c030700010860f00c048280000c00503c01614141c9884000005e500c8104c5803941d0010104010b007a6201c032041c0c0da5454204146401c844200d15006420340c6500110b450303d080e410040242c0f80025812104880c408140300d43c02602e10f80380002c040d42c019601c492421400c4904076410240051000640b840c202d00706124010107004100076005914001406090385800c00e210009108a42a80002d425543c2c01c0140051240740d01040b03070b0381c8560781c0c60400c40802842c01c080340070740 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681202607 1250 681201357 681201359
    0x11120c40060f0e220e0331050103021617070803040507082a0f1305040302010b0907090f05060304080f0a030f14091e1212152707020c0402160606 64
    0x10800c2e4020200104e61107031030141d11a02290020050206220031107070501c0240101f5468001d890b05201d44446280c0c0949442c00c0c00718540030150440390001c0341814010440314155500e0f01d0302c0c101e01580c00040080f00c2000094642540d03114521001e40000c40c0030045c4000e000d00403c02c14100c4d00e0f00f8046900400740c0280501081101a43d030012218903485451228280415030007218007004041691040c004800f641c2146c0060701c00340c1c0140c0d0748844030500713803e0100b51780390000124105101c5280c5400030440141205009081c0101d0010003c42c0403c80c030b41c2d05992188040351492074444c440c00c4c030700800a03e03450480303490321410300f0461031070403070b20481444c010710b59840075200305441200181d0000c04060356500041c41884440604241031202400c80e0b0400500001054103003440f92000000d6a5901240b0071041455980201c0034511110441d01c4100403150b1855550310b08140e00f40704080c1030164100c0d00008100000d4030000003c00646c501c81c1004204072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681203857 1250 681202607 681202609
    0x5160602041e0f03060506040f020d05090601060e1507051207050a050c04110409151e030b012102010c030c120f020f1b0d020604050411120c40060f0e 66
    0x1c02c0300348030b55510010740190900114105800181d802000580003040c030865100340202240c0c4410100d01090b0740d24014492030440a02c0254014096032425071030000f4100005004240281e020f0381107420002540c40c20800b080c041c08025540401140c0d031150f00030708069448503120380e402c81303544c05454103401c50351519200300c5103000d801148144c241820311900800410348000c10340360b0301d0340c0c0c80000162640c407010340810340140c220000503510b10b18a0544030060040c0c1081000e60392111206c607002300105a181800d507024608545a0381050900741ca0404280364054680341c600d550f80040e142c0c00a00d003450004050307089a03424003007030304542e440b10102201c000c100c1007002c240c4074075442c3c29940120014001015103241981c1c40002800b180c003401c501545880c00454007240da041030000e05640300441c0340c0100d00d07150f4164030388420310090f040c1e000c10460314144800600447c0390110541003810002031459180c6404002c1c0140d0159030150001800e400381c00340701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681205107 1250 681203857 681203909
    0xb0612040c0806042f0925030b060306100c0b0a140906060d030f020f1603121b150b1e1905010813080c0a120201110f0315010516060204 60
    0xf040783c000c5e0f40320f070000500c4440020b813208140d500c0c6034121040040b500142c0d032410496402010944958451130411000034009201451240000d05103031284c41601e5850ba0821070b03903c0f12080359405107803c01d840301560014030191010305900d12400410003010640d520424090040300d91030241d40d9103840704680d440404440650304031640c000d4090000340900500d0141c00d5050059441c0c620845000c2c515061600d43d01d40081e1307021000c1041800070040083c0c0c11002c143c5460780e68030042d071880005480c20003100a200c0ca040d9045a04183d031140d1188030741540040400b1040342200c08003e090000c080000c0f031107002122101c680080c024010304c0100c500603142e81c10b02c1d80e620042d804414a0603141500c002d0703800c001c4000d062009101c40c403a410f218240701054214000c0c4000e00f1114a1309505418400c1009000c000b4543c0d0b00660354800c8407204182100c4c2c045a004130780c0341c060b42c02c02e101702c865005128010001250050402c0d20751400400b09041100d0680030a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681206357 1250 681205107 681205111
    0x15020705060a020712030506060c0d0c020a05100503070f0302070803041a0a1e230405030c0706030203012103021606030209090f0c070f1106070606080d0804050319030b0612040c0806 80
    0x41780080c043e0381020301079000b055005100502c00b0f42030020143c07440b4103010384110418001000805228114542201d040001d080183c1c3c8201010010080192603840007401076401c1c85080032410000620035011190144e5209486503101d0400345401c0405c0942120300c403d061484a0010742c40c1d25041c40340080014604110001c0c00c500031950000800c01c3e43d18101c641c4c032090382c0386240c0c00d1224903c039015a2242d0011507513603d0911400d814420113410810405d4010001048228180388030510207140204002c4401d88a610302a4940511418024082c818a15000a8035605580070381880702055800c81c800d540d822030b000580000c21654218602414440c90000c00c030a0455280414811408052103140340000200e0315042804103c8106450314014060b018003485420501c5d013450502e5000780c202550358503180d004ea10b00d111608508040d1940400e84203070805000842c0150010b542c880d16840300c440c880c2d1044800f507407402c00003900001d800e400014054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681207607 1250 681206357 681206363
    0x191106041721030c1303050102030c09150c0a02010e010302190302031006050c060423070803250c0e100b040b0a08011d15010504210215071a1315020705060a0207 71
    0x5861580c1310340000c001c075001491420039440b0a01e90200001c6d00920065020301c4040c00c0c640e8440705400c0c10064042603011100450b000d0501c50000f0881001441d051900d6090030010040070090004074024081d81e0060100003c0d800c1090a60642503401103020305840300780c06c40c02c070307880310000e5905105110104030541c1c440400a008544400310040c00801080f81c1c174182c56082003203241c9095600d030414a2a504005640307a200c1c0703070100c000060300101401401c0c40406585803e50841503e00c02c666101c400500080c41960000304004050041c0c5070080d82c5464540c0c90320b900d1500052020300c0851030410012070740e080d41c441d1700c51000040032802c01042d5a40fa000541c000301c1c901c003103410300c40240400300d0003240d200c92111400d10401003404492032540108080802c131189403001121081200c24045407509444694087c050032501c01303981c50304424803400c1040b00c200906101c003540c4180510450503002061214010012165551221807160040340b01e000002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681208857 1250 681207607 681207673
    0x6030f0307031e051603121503020603040b0612010e0705040608070806070f03110f031b09010507020f0a03120207030b01060207180b04060308040801061d06031911060417 75
    0x980760100c41c507400404821042d142c6079003400c0348410782407040c0503901c0c4200e0109000712840340108680344540d080003240d5603480c8c80c0c124030b540c0220700b0a20024101030f20801d55040021710303030384460b8642480d08018900030482504401101a11081d150080d80e2250741440000201d10f6800500d603416a0041009001a078452140c02d403503111421183c0700615496401c0811907800400117000441e0014203c641e03645000b1114030701c68075400c2020b2400c0c80e0b090001901c80d9910005440d4015030503548450540710340400200140c600341e00051108000b240d40301d807244c1e40422404103e0f88034548842069881c2c4000340e07200c1c0840d0041c00307100301d13134040e142070780b66881d40000310540701c0035000040c010344a0301c42c540300c0d40c02a0800011603444260030051301c003c0361000c1c070019445081038031840c02c162000a490b1400c0d00c46118040d5280300342903062284013000e0704103c900060815580b1617640c003045550444105188006001c0c088003034074400c168000102c9210106024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681210107 1250 681208857 681208877
    0x6080a09031b05100f0507032a050c010905060718061e0c0303141021080f0703121a011e0f08070c06060e0a061211040b151206030f030703 61
    0x309220284180003c0e612803144120000d02c81c0c0151159440710b400e00c01004c00c003860030450144c1a1200c0326001c3d100b41c0c510740c0c112420080703500c0301c0c00041c00803071500e6540c80400340b007001d015000c44d40c0301070411300606042c0701c4051342010400102c2c01a19003042101d95984001351184105201d04411900d102518929001d1040413510a024428140050107654542c01c2081c00e502c201d9045034070701c00b110300a20104032034002c40c8a4409181d403100e0158022a903805841e070046000d204a90080071801c4010140582030558034003c00742f401700f140300c1900045a0780310305440d6107607000c560402c140e00d1081c10702500003511744400d0340307070001790241484c012203151100400f10b0f0100510490740d400043d00902500c4010302144185104c2801c0c072408490440d20191b2010303491840c030445000004803c040701d00c5941c00100c0700066141d0310807010070668141c3d0254011001c00c0011300c0c151801642e0303a01401150141c085a41840b402c9240983d03d205020002c0c2c0802d02c0210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681211357 1250 681210107 681210137
    0x609010f051e010909061b0806090c1c1a031605090a060311010c050c060c0708010b0a050112050c161b08030a120b0607020619082a03060f12010606080a0903 69
    0x504030103131050400145200b0480408120303508002d252000123041c4c20140401c82c83d00d101515002603a003510320345001d00036203842201805091103018141c2d168005010400e40d04054000c041101501362000e0b5070003000c4007844006c003401241e10030050800070482c00072051140030700350307135110000e5a89030310100010368414070303011002c0362588600c0c1041070450702e030100948058228080182001c0b414501a81d0030744049030304441c02100d004808000380c1c1c0c1d0104078400d0105202c580001c2d9500d074881d2a034420300c10100310840454081e0500c0f01040f10203406000c1e1514210381c0c0314002a1100040344c4c41e4418480d00e0070002d030948140c0c90007150568004e031a1508010a0300d441c11103540d0119410fa0010b80d1080d0f4410b0031a010701200729000000590301119035007181800f0317200000e4441c02f0300d200e50200a008080400050392546640044406a0313000400761401841c44050b12400303001d25000d8680000c140b40e02048480c0554001c80355066495101c0c03080400c41c0705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681212607 1250 681211357 681211361
    0x405060f160501020408160905060f190b0304080703020607210b0a030f08220506071502090301060b0a0207050a14100224060109120b0123030609010f051e0109 70
    0x411a2407140d40358545180001c0c5003440100001c1117824098241100880360807007288840c1d9101c0c014241c08e0404100099032075410130000e04004440100e0080090140304142101c3d940041c4000600041031005100710790300034142d13070361080d401c54110780e949503021512000b001f40d0740090358200c0c3c0010b40c00035207a600460f40035080070b081c1f0b808860707072501e076100810200b01c001d072403100c070001d400c6240191103050958403150014006416514100103e100e610616102514058442d2070030040401c0c10340450b600004001c000b44181516400501c0b8281d103c800724501503c03801030300294500349250350b4001c6627562103c4000c10840c0805022044c0c03a000b0b0706604500882050071000c0034414518002141c2800d00d5428510308030001505007031a98006126070100f113160040000c06010f015415507486402136034071690341c204511204002c80b890140e05001c2c01c402c0001601d070541c00541000c00c40c8005000d29141c6000c21a039460045241c841d10101c03080043c00307080d61039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681213857 1250 681212607 681212617
    0x9030a020c150918040203150103110d1a090601090605030118060f0204121a070305090606101101090302031306030605060f131205100e1626010606020607030c050405060f 75
    0x1003a0a81c030f05405440044c400400300400242c1048602c8148402c4d810100218140341d202e040c000c402550440d03c84280098030750082510503000c12170780104100e0110008000d09400400b10703621800d002c40e9050b01c40c042402500c040524241001540d460140520840c9032042d8140320440400758846901034005034840448043c0c08100006180c10310604030038803680500306a5801c172000b05e2500c5d00380e21001c0e10000406040c0010300803858404200580c210404035000c0e00707410703000001504c4917a43c403c0540c100b5480c0040c41070502d50040300900c00c4001c03140c0c0c0301486a850700d0098044810380d00840350018424410f82002243c5803006000800c0c5c40030b800301039103a40d0490b60b240b110011204555a41008240c06495141805500000404a400350165869510b207800000800d03124807003a504402d190350f110892750036924401c51210000038002d007501c2e040042d60342c1c80150b80c03400000703103448116005507114405440581d500107160600d0305a200901c00b03055086 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681215107 1250 681213857 681213889
    0x1c05030c0408070b0703020120030f04022206030201320c0102190e0306070305011a070201120e0123042f0a060906111c110a171209030a020c 62
    0x401c000c04a18040e0400104000380b00b80403500da5162868500207080d101c0308003a02c01003917075042c00450000d01650a076507000207901d41d10b103c20b54840c00000c1040814458091902c136207200e240c62030b0802508808142c83c003c0c1c999040c440c598011450341003000e22480c00e001c1441c0b031101001d9841c00c41c020840c0703070f0b0f18000150600da4000d0001620204403182e0300081081c21a00100506061041c10303440b60b50b40c1801c03c1550b24040c410780e4a2480241c0e109030400000a00c01c007160300034403400a0348440c1450401644240c841c0090090050080c824041c60a020300c0103240c100100070144615400745009094551210441e010545c8000c51032103901d41400b000300050b200c031241d90005000582d24001d90924003034000e0000021030484003403a0f089020022490a961031620000c03607540d151451403404554020f606000c80c0c803500405c1d400d94420600c81d81d45240c8090100c03500440d004108588601d203106030b4a108800b20080540c10941d88440145007102e801c95110030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681216357 1250 681215107 681215131
    0x14012018010917030d0f090c0b0d060b031003020a08120d05100518103c0b070b0411061204032304090501030c090b0108150609090c0a111c0503 63
    0x92034041c3c980a1880c80814036055900108440c103403401c450141c0c24042003101404c01107058291600b41c01d030b40041c0908505080700040220784002594040c000425111b95000c0c5c0341c0c00e160b25004501e0a076803000b44e1054402c5080456280e0300401ca144000f0000c0b03010618090000308068042d09004041c0b82c44c1003200701c0c0005168a5104c040c01101e41c030000007101c646400c00035481d8020f100d0304155040500ca001d100c0480e03840301140d40c1070f80f03900c640007090307001034035000c84005905130810400d4200205861080015222041c1d018910640a6080d610f01000910080f80509801c00302e0001d090030206000c02e02500c58503000d094040100b401e11a1180c041d220160320030740c4005141c030b550b00c00410a01c004000c0e254042d080405007444010701ca400007c144150103001820103280b0b40f100e107400eaa603103204540001c01c000d01000400e2606500302501e540040c10290301080408036008060310000c03403007002c00c00341d68004005e0500d0320182103406da00028800d1600c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681217607 1250 681216357 681216359
    0x1150b040905190f0e160b07030503130606030c091140120b160905010f0309320601030201080114011701080a051b010c0303090618140120180109 64
    0x1280c080d904c00d001803c04081503d8040d08403040c941211502c2105000003540018400b0f07200c2d0740111144907070145482ca80300e445440f002c2098600100b401043d036441c0100000c1004003040740081160b5049100300103d0750100d00a0600d44203808000c803c1c0c00450402500038008010301701ca89180ca42c01030b081d12801080316103039240c0c3c1ca07000a4005149200040100140034402c10b500000000b11100880d10100d405416143d0714092503051010401c2010354143c842c3e4400d14445820090b03080028003072480424919004500c4205100300010005180040c00548241200c1e41a56010820b03841c1010607501e030700f2103003005810450b40b40c0c11201140c1c0a201070301c0c01b030244003020704148c0e981850030340d2030407800300158064029206160b10031a030300103080024694040c1400b0803045100e160810082c203903901c0600c2020001c61304d07282030004c0d507031401c01d0008400000f081543e480700c4607030040303540102c89071039640780810000c2a280d800c01e031003000c2100181000110380b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681218857 1250 681217607 681217651
    0x504050114070204090809100c050c0904050f0109080a0e03011523090109050924011e09020d0b030f0c0d060b040e121809071b050f0a03030b0301150b040905 69
    0x288803c2c04064a02203130115421580e80741010901348c190109080a102e034490316503455403590304044e01644110442800107003817000c00d010040321914000c008206c071101c2c0e850300340300d50f0304100c5101d0b0000307040c0e2490208a0605110b0f540d061281c003894005e58520701004080700c4800e0a009450686503040c00890b503855280c4106d01030b00e00a00c0c003242a242c0038000c00d140a900001912076105150b680354602407903040041c3c1517a0b40c030011514075005903811b1030100c010583c44030041600c0010900050482e540c0861041030044054940030308595010740e603900c01c0a450941c2c4002502040e0000403401c1d0f12041003044003a0000c00e008060074a20303801e1150640c04200c081c14001804490360100c410001c0c030030507040f5070781106e6081c148002001485d24240135030140e8004900781c0e0921404016100703500807294201c0d1800745440ca03000703010b481c025045500a60810241445070008402950151401e103817030b040c00d03e80b9240c1e0200140c0700c042c00c140180f030145a009268 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681220107 1250 681218857 681218861
    0x30040605090733031103010b0702030c130506010f030608070509101a0406110a0803070c140f15090c09070f09051c11040c05030a020706060803030a09150605010504050114070204 78
    0x403505800c20080c8050804020030f01e110300d4110010826203001c031454154801071040e40d0540340e420a14a0f10341c8241e00c0820703d41105400007a510600581f140202400c030343d04560300c030b1103080e40d0722820b601c4607400030f90649441d4014044d45801024043c44103040c510b0003a0350110f4108010f103220361381c94a1003021590500104000704600150030311500ea0000e10002e403002c1000010100349541e912001c19500028000008211405c0741d248140081090500d040703181c038030150f900c403c0e802c0350a259540c030315041c4107000c110300e980001c03e50310001c03a084030400005044105141c0d1052000ca403052003400702e030014080c401c8004201511045520b002074001103442c17548811090030044805912000d4043c071850400d0300c450403455016040d2030300016451800760301e44c601480c11001400740c40c0c01c110158400441041130180c441c0d04a404a280140c03e241726450940e4218021703541d490040901081c001c20040003294800c450340140500c50700030700380c24859140c1c00941 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681221357 1250 681220107 681220139
    0x503010c0c021c03171f08030a0f0e040914010b030d030213030809061210030201110a050a140a0803090109111203092205040624230a0503060c300406050907 69
    0x104050307940c410000c1d01b8130040c0150041c0007410000e5007010150080182080e060351104030401440041c42441f070b403200d400050219501a140494a40718040480d0080c10005111486031080c40180e801c0140203100705d4080507820042c000130070b41161100021940300d4004150050400c000401c2c01e80f8440012034014002d00101035071031859400010a034114078011403006070010742d024000142c000684081c40c0d540328281038215202203480320b00f00744510602030310b0400b00008101c4441410f6221610a51180340640c0384104000140005c4502003040118154001c00c004003541c5400103d2080c0040e02c4c100114850b1104041c49068840c140e8046540e20f40311405103000c2e1101c642259804240480551062440c041200100809454403664604000907070100303261608a95803028040250480e01d488c1040c020198803a0b120301a1250700c034180f13a4003544094030104803c50001c400c42c1000f000303a2a03607100c40000b0b02014091744143c0c8103c200024980304980031443c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681222607 1250 681221357 681221371
    0x105100e100f090e0f0a05040519230a08031f090e0309010306090c2c09130b090c06030f090c0a0f0911030112030c1b0f0503010c0c021c0317 62
    0x480ea65084405000c1502c182c00440080316002d08001400c104680070751ba0140984d000415207446500340f4074109003220070b0224a0541443d05042401504500030030580140921421031420302142e003511030412410080c00044c0c1040400c40c02594081c0c0c02402550841c1d0785090aa43e82c5911802c0310907510221940fa000450440d07910b42c1c06124a000a20400006020140a654008010040c0181070014201c0051464a42c400621445420b0818090302401e100d0034144480020764040c170034211a01000c1d40001003072004041080101c04074080c1c6981c2c1107458020300e0f12200d01c401419908c1d40c1c411451a44026076818140034014801c012410944c581410b00300416140e6905040c44540d000700300400611303140044000c0403d41524200c0d01041c1e80d450042c41c1d0000c503216040d0030340781d00e050100e40061403007825400c03600200c00801c095070340c2c0d010a035103031403104001952101101018803021100da004440526100703161107815840e48a21410103510252443c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681223857 1250 681222607 681222617
    0x4140d0305090606011e182607080703030c030516151d070f0504020a180f05280902030a090203030c0a020a0602030415050901120e0619090b0105100e10 67
    0x1c4021002d0612409402840a203458030f802030b00204441c600c0b090b0030341d18a04201040400c1268030420340035000281079114566800b481d0f2141013003040d401d94600300c458501070718070f002520340000240300c400c4a5150316114050380d0a83c60503501c076040f00c40e000c40c4c00d181d12a10440000c1007000c030000c800e8a03010300080c10304074840148505540840700ca01035035001c00c03010312449c0350003c184c4c41218012600561303291403445080300d01c1440040441404e881c0000301160008441c410102507900a41d603d00c0c6910882c68440a4011004040c0082541400d000c0c0000c0c0000c0e001142d02070035203640410081030340d0340403038555400b802500d600f40d000085900d04600c0c103520000c3c01041c07144029130400341841c0d40d1907014070003114910305220f0005103600150f40030310008540090100020000305031105152900ea08040b98082010110707030000b1082e044c014820151000d42000307103420380740e081c20203000203c2c42c0c8408000a00060450313680c00c581d05c84082100d02c030071035611 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681225107 1250 681223857 681223861
    0x5040801090b01090501120507150314010806040512030c1e09030312100e1e1003120804110a1d0406090b1807090b0f010315092c07081504140d0305 65
    0x5040d00b145c034103812034a11b110798000c1213030101c4c44c00143c510988a840d8000c50b440c0c01e2151064009151018441c0c60810002d4000201a80c000c40c20920403030145094611400004405150f07a1208840305d0f041d00c42c042c000000d03451064450180c00d000d04114a07860a0540c00c0040c0c6142c1086801c5000c00c3c800078104500619480c03a214010300c60700ca2000100c0c03e10404440108000e00f4481704c3d052600000500c50315400d9012800954121f5120800003041060083c134203842110103580d0300012228802607401c10203c400300b11030b03008120a84441281032113440000e0040c0060f20b50303035207452110300442c40c002d45d40c601400c442410507400b90342407402c450824405070b00400c01c041c50a0408006901c610311030041d45c10b024070700050780d400150580482d40c0700350341040c10700901c3e2411110040c0c8840301c0399901c13100c0c0700c030400700380004484246555509500403030780a5000258031203014240303904210340252140002c103003441d007603001141c507001c5040b0b10080001d8039901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681226357 1250 681225107 681225119
    0xc170304061d0307020117040512130e07050703030c0207052202090301050a0204030b090a080301090f020c0a260309070603110415030614010e0d020603130803040b040c12050d0f05040801090b01 85
    0xb001820942c521240311f882c9140544480d901d88041c002208641d820000d034070741f10a80507130396480160200030200c119030304048500600782c1d0041b1404402003440d10100d6901c050002a540f011203600508201e0614a1144010087c403806000d40144036004c2c4180351907a582030250612400d001c2000503280c80ca1410404100d8074040c0c00084e107500013540c1c04c004506404201d90640340001e90205030303001103901d844001e01c80c41b60796462030b001e840064400c102c900d124018001004428020030001e20400e28a2944825600c0d8031580d031024104000340d5000b45c004c50242c038201d100302c42c09c180e9652040150501d1103079500b00001d645142c1400519054840c4c1d03203546400b0b107404203c503210140070031840448000080d10a820101c0040c440090880b2150300507580a50240d8583c2032518005e541e658082d0390469003080414004105000000000104550008001c0000d0b0503114426501090710b03000c0c5c0004c11008103c042007108090168020191003540044075642c9822 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681227607 1250 681226357 681226367
    0xd02100203160f1b0605180a030203010207140721020f010e09010314070905060105090f0a050612060405010e060102070311010c080712030c0315090f0b030106150806010c170304061d03070201 84
    0x1403860b25240c821135100780000303984030701500c2c8644060703144071400243c03590020388140003e90000390b05600004a000c10000c141d081c55020040351401c8035200c54031900c1c001e62880301540c07910031201c0c00d50242c1c009841c100810b44c440d0301e01810032184100c405404a4420030b003d030401c3d1b805107202095100c0405041040000074003090008001d0b03420083c000034003034400d0390f20851181d10030420a03600d980c0c4e8034100200510001f0032065441000303040e420043c020486d02d45102e030b40341400004000402018040c807414050b400782031803a042d90768140402e120100117504000b41c8251290014001f0b10040c480f10b40190030b82107107444c00c1c1000806071000d5280c15800c250405490307500c0c84841d8039800c02030303501600c008103180101e0b10050340145041550140d2642c00c0a000040321310044890f405403100359070b41c4101990754100190b807a1031500b0001000d01641144003000403411801071504103214180c0030403841c81131074100358400140500341d140c80e000044c51408640c0c0103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681228857 1250 681227607 681227633
    0x1c03080a060513020a030e060a2405010818010209090c092404170a12030c1215050603070c050703030224010b09060304231e03090d02100203160f 64
    0x24580900009080c40c0224040d6610f2201c1080020b4000c60141107481c0241c00001910003030b20100d034034614120380c951014187c4243c2009022a00f03104800705c042238901c4a01c26140b060310740c0155a00c3da40001c2c229840c3c17071800300c0c2c0c03555401d0020064a51b118003000d03008055402c9020740f520000341c00c22103000300050180840340e1840c000000b0311034200c1c064404032480b014101413619a10014103090810641000b02a20f681c11000d403210b5806511080d0b4000300d9075180c1c1048800422458100d50300c80c04010a44500c18404002c90f2400708000c5610014500d00710141c80a03d90301d0720b146c804190421400b41e0071058513003040414400504c07040394030460101405501d001c03550851407064084a5004081c0000000c05204442d00d250b61260602ca0380f22940c5c0c0700340c2200a0f100c000f0000010112002451000118040041603624001004080542c168002d508000d204211020ba02080d4002031142c5178200940308034588c0741500440016800c003000c1e00d0a03c2100c008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681230107 1250 681228857 681228871
    0xd0f050402030c01110f0a05010f15080a062012040330050c0403080d1407030908031f0512100b01111b031507030b0f0f010f0e0a051c0308 61
    0x152108210141e07400062103480c000302030030440503240521050a050856400c400c40c581d00c24034540c503040040550100c2500e60218204200c082540c0b400703056120040d11071400994070480b041d00104002d0303400301c200440c40900b401d018610180201352240c00c0b20f4090501611004100310a060300100300391191801d001180d141c000c0e0009056a000c200d0301444000035a503070000902c0c00e000c10040310b010f1504240551b0319400c820400d4005421503881140d000c10310a00868042c80c0203000d08200a6800924a411a65015500c001640d00c0c00c0d80d05c20b01d65403071040083c01303840d07250701740441d2003508001d008502103045140d01a1981c136a42d0b20304029078901408800f400109040e80780185501c102c0d000e1401590000e440c003401e00c42c0c4d0071200e054007402c0c08009a00340d071086c0262903007600c8240c00b0601c802c0412114a0380300c03000358085005d1080012449214040015580b4001051400c0c41511034000c03d00641d14505102c10300300da043d150906042d00071801341c0d0b010715 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681231357 1250 681230107 681230111
    0xc03070504110d0b040e01020f0301030c06080606041806030c0609050a0b030c30010f050108090f060105010e01030905070e220f0611090904051c02120301052407080d0f 74
    0x32907107803440d02a110f0181030300240c40e41e404101803541c1d01d50b0444100190313584002d5494038003a9401e42007030b074820311007203400e001007020004005005400036407203208005c00359400c091400d40c21380b284900b11420f80d1815a941c800101c00901c89240e010f0103003002e5034459000a01b481c0c00d01c0201100c139041008028030600801402e82d03c00011903200d800010301540e01049a02d8031201d25022400100f21341c602c560002141040040c500e45084ad082680c80703090a40f1110401c03605c858042104040c2e039045500180150b5004004a030008030042c5030000d01d000d042d44886060010ba40c0040604c3c0c080c42046c404421017568441729000502081c0c0441d469540c3e4540b84d140c3d0071034400409107500c45240c0c488221040c01905c03010f010107040d1000d0351070213140850b12070310b483c280156070780c0d80c200000c000c443c40058141035200705041140c3c03840c0d09010401c810b003800c0141c04606519068240c0707a010803040042c1c00b01c01e1003a90403d45442446000754140c0302c48456103807901d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681232607 1250 681231357 681231371
    0x1e08070219080d1127010f080601020706030b0109081605190f0303030b062502040f020403021e0d050f0f1203090604060e0f0d0c02030105061c03111e0c03070504 71
    0x3082c1504aa08810703c00d040000c0d002440b4500150500646402d510381401c001102c0440c1400c80c41d66000312402642c0e850780085100506030b80d04841070381c0d150b005074010f400a201141c025030181030001d205062483c03d0342c2c0e5401007a45007440c0340410825507550000708001030b060424402c545960905415070040d8140030f0750200150072444054100b40c4c55107141e4025441d480100c036040800320042c100903c3d800101c1e42c50008207400101d00480c5045000144181c0034400d80307003030b264014800d020758040794550120014a09031442d9002caa09854000000c070104080202ca642120280c40e05490082d03655050807401c0928400d000e00c1002000f80301240801c2c819881743e401200003a6040f2000070a03468010303031401c1c1308200c0c070a04124041c00344d00a004d042c1c885100300c0c020b00080e034650040c0000d10284000361a090011000d0840002c0c0c01000e5042c0c44018101c2207a01c40203402d1414101e02016007200300017074122200f00c3c0e00900f0103203d4000904002d41e000d000074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681233857 1250 681232607 681232613
    0x90c190b07020d03120e071d06130f090f03020604030207090513020108060316080d1b0308060d030c060257150f010e09340308032508060d0b06011e08070219 69
    0x28170310500c2d10b4407090364812024210008a338003d05600307420104020715840d992801961700c1500f81e8054025202e110030010b0031801c80d00409219203003041c0201e13030b10012940155521080a42159414018101c048419030008010000201011030082c00d01104085000c0e00d4080c00c5223061402124a00820001c02d0b041007100d904000c003030300e034100356014600741241ca239034551100070541c500000e036510040e05840022032660240420300344400c00707070035102491500b4292460070240c0d1582064440741000208030740c01d00e50540c0030358201c42c5158000410001c02141d000702007080b8180107001c10071860484c55803100308034000b00341400c1c055903041ca041c1412181c803281441f04903c6400b152a006050310025036001c00c04039200c0c10100e00b00c7d894a9841184d40d070094603040c42038203c3c02c2c03058150501680c0b000c4c0842e00105200d490f41440e603007000702113905000ea4508401c0501e1000e42441070084c545964120550808280c005d042c5244048085003282e0292a42804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681235107 1250 681233857 681233869
    0x15070804060c020f04061707060203091e150c0105040b0627060105040e151018051302091002010506100c0201050306060310050603090c190b07020d03120e071d06 71
    0xd4501d90306120031242003620000340c50b6122500104e0300141002030010b180d0200110850a20001c038050311550350322a501203969000b0642c02b158482c1c20ba51070b41c0d40c2001c0c6403401c404002c0d40a004001c94101c0065400710f5540310305580c5105a641e401003000340450034054540088040301c41c006050301d410390f5440781c3e081256282e02c4c3c001420020030301580c0034808890003890a00030034525450402d1000002c410750511340d901407018881004081031107110443d6103201c41200b201c2c8682e0030041400755910002da1103a4a05030b080040d44c049648011845080c0f11440d0f001081a280c09030a00c41d00d0003004c01c00c10180308481c00b51a0040c5c3e0403500f5a0390003c02604c42c29141c0c0e0351108031020480b40e076803095070440400000e2010703020002c00ca401c00507000391501c0003070201c0103c1244004032103100d40780480006101200040c607000c0050360203180a85000794243c0c2148940c034080380d1031400b421015900050b01003042201074036000c2e804110846c0d18a41600d80040441d034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681236357 1250 681235107 681235109
    0x2040509040311010e0f0105060913030503070c08210a11040513053414040e0612010b0301020d090b09060c071b0312110f01050702031e16080915070804 67
    0x1003071014039151144030307100035030040d20554596001c40c1d002c6d41003150028001e1000307032001d03401781c14803c0c00141c02d07103082d45043c2c040c103a0554680386140e85100b01206d030021031080842c0c1403001003002191135008801292030100400c0107180c524142404d034a4110740e400084030b40010f5087c8010001540c2c0c0d14000d069404141e00e011a00b03541300c90522110a1001e0340307100c101e100009400f084c81050b2a2140c40101e89034031002c122040701131002006000d0703807299030103800e500c0000501e1070400c3c003402c0c10612914000800d0b804841d0000178266000504a010705523a56a076441c18408002c04090300b14010001070b00d02403e12510a074280e1081200151200d00c100780c502c0c0b41103502d82c41403802540c000010b016841270444000303001c0082c42000074000d00c117041000c500305106110f414003c00345034005500d441d140030000c3c404502110342100700f140013801540401150180c1c0d00c540184290107041e5191491007c100c0c5943d2010388040900b0401d01c1307508009855031044070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681237607 1250 681236357 681236363
    0x4030302251e060b03011107291305101d07050103091112030c0109080304110102010b13150e0108010c0212070c18021c0603050d020a0b1603110f0a0f030204050904 72
    0xb410b41100c42c10280e02506509035590f803d0b602e000002800d4032100307000341410b284101c03031144484900000c07415207114213141e07429000e48401c0c0403a1a814004000c044454402c03001d981e51201e5088800c011200e4180340300c8000116810f2039503450806024031009808242030400c1004420345802100d400d510100c0e0380142510b01850503404010800da80c10201c00100034401c0f4446441d20030307129001564115601142100380a20941c01801002400321000d88204000c4043c01c0441300501507807160700c0c140200062000c01c0e800c4030412094080d201107070010404d609c1d2440002e1524621051240351200c05103c994009100c060b4079000700e0b070041c5140300c4490340c3d01440b94000c1c032138503244241000a20301440c03514446500000201c9018100703603942e0405d00d20302a0384a01784081c00a0000b020340001502c000c0115030143c2c0c42d1442841c3c001303940d00c804c0440754450703480b202305020159400303c0c10035280c5602c13503001c03080031000d840c00f942440c1c03612000c1035a0140140c801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681238857 1250 681237607 681237653
    0x250f020706140d0e15011211060f0d0506041d0c09010603060e070f0302160f0b010807060c0f0c080d02030403170a0e010f0e0916031416110c03060403030225 69
    0x941c08000c03c101e0300e400480e4042d100300c2e99581d030751f22107902071142050458903201000300c0790364689418815a50385c0c4e40180125032603c1d06089901c0d0040c000105130700e9200e95510101c06408007901c1d04e4130711825201c0010418081c010b006c00a0400059002108050404005000c403e1001c0d205c103401104030709020030350080749541900640552040c607145501201a0901404481e130000402da80c010403034642543d0329480000d13103131804ca01035038012500100305200003403040341c03241400c1d5014601e15950b161b1904082414070761541618401680701140c244140480c6a40744a20b030116041c1c050302c0c0c000d1424000c1d08070400c20800d80d061010b03955104108500504148600c02001051849585880000451415401d070301000000e484d25011007035414000040f1400f9803c0c9a40d10b180424020100700c41c0d448680540189034010040200724548041002c81d0049200303071005a141c0c1002c2c000319210344008202140901607003040d60002c04d10118441c070901c0d85000071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681240107 1250 681238857 681238871
    0x3090705060a090b160614090631050c0306070c0201020d03020c0c0406090218010201110d0519021204030e0603060a060f051c0509190b010905250f020706140d 70
    0x80c3e4680d075841d4401d0400308000245c10f45001c10300e2910080f02c51168104001802901180700c2c8040400c071200c148a0303201d078010070310844400c001790340e003621082400800da204039581c8903a04103030300d0000c84086d444026280f03805e14062110b594072035018a4641748902060700001c2da6082c07400b40305024580e00298400d0440c0382440030682c6107401a0050181a988a40000c020b60040710507210f0012240002c506540c4180658030380d01b400e2580d824200051802c02000034240034200d45180841d00e0b07048002c009450003d4280c410405040f00154507290401912000c022170344180300f16400c00402050792780e880805070071b85040703240c0000b4461880c0e009030f820b4812880c514807449095028040e01c040c45800c11449003e4010035103075641031011070070380706401e00d16004001b0b0742810014090340321907512003540100c4159401c00d89640210300c100300301141071100c0e40081c0c01700d4400c9845135010810780c0000c1810780b400c9207984a0049040030300d401560120400d554481b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681241357 1250 681240107 681240127
    0x905010e04030c0b13060513121d060f070b010906080709230a0b0a0f17030715020d0b0a0815010e060109030303151a34030f12150302150309070506 65
    0x203c0800c1441d1b00140c01c1210342070032441848107900c600780845007030740051060310a0340e01c1582c0c52208109105d0200088440c04410003d0760f4026078552804407509109003808100c400c00002d0007070441801c000394843c201000e141c20030019030081c2056504040402c211031b0070010301441c0c02c00d0b000c948110241c80f0f4840d00301c00f07448100441940034003000400b060040303824160743c0441d200a8400d1501e1030304404529140c3c02040350150044d0076492507030300003440d250001c004c115048207000034824004070001c0d904254a41112800e41d1104152440c16494004d1143c05002070700c418070344a00d2b00200080c00218240001000c058444410310f6030580008485400307800803211560080c01090750555141d005002090b0310341d001841082d0340b00280401c449004400f0305000d695404064900750340144100450104008003005500d0300b800d401d02c074201621400000704c0f0160b40c070314010000d4828040a141c40440010028000201130001c1c0c414102c0741c040d181a03446040d110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681242607 1250 681241357 681241381
    0x60c13081506041503061a01090e1b030711011d0d02070b16170d090309120302060403030e0a14061f0e0a0c02030c030301090b13090c140f0301060f0905010e04030c0b 73
    0x2620080c00507090800642844a419206000d0752a0a1741c80c141c0055036074ac1d403658001001d1380c000403074400786a10114200928002180c8c400030034200100100104884d4a007191015100c44402e014240d17004400d2900c1030240760b804004030310041911a00340106100c043c0300e45005004c00060080303074102006103101c040b01c03c254000c3d0310541c507800210080320240000c2a0300f1000a4940c4002080d24061184c08800aa416500400b5075a9540c0c0c0d041d80100704142c6e01c45410301c80e141c0090006801e000703000c0719158140001c1c1c001c40c00c0c0f41c1d44142c0b0318404200c08a801c1200001c043c0807143c0030011999000d0700c4104003081d10703a10301405a0441c41034070541c6102c0d010001c00800c034003419400c000701e542070a0350920001901510800100ca1240d0f80c000c080e00c804400805c040565003168806a11000300307602d20202d60340000908494850b80098091a103460041107560f09030702c259401485605900e1031079180a9800800745540c0001c0100308011a43c00b04074030303048003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681243857 1250 681242607 681242609
    0x203090f040c1101090c2c040f020409022e0f05120705070c08011a120d0f0509061308010c050a0f03050a0b120a020301110901021914060c130815060415 67
    0x3c54020482403a04e03013452003151034280100c10800c118010404218104201104501ea0001d0100c58040e00c035551961048100f5644c140d9001e9118031682d07025956029141c501300c598080130701d040e04500392070741c2115000401c648040c402a9420b40780c0f60790704881128054030083c4061851640c810000792114044c0c004064658109030002140701c0714151b200c684400101c0c030b03444003410307001010485590700049800d80306400a000440205000302102e82c00000c443c02c107142010120004110a50080c5040d2080c0d84000901001108020b21035007210035603c0c9070580c80c00400d141c0207440340303c034483e40004055481c4c0020325071401642c0100e1041e01c0042003540305001102d14682d59103c2c182d0141e00c2540380032901e420650f025002c0340c801e400180c001d486007459403c1d029003100c00128058034240c0d5a8100c207403002a050040380e1180618440a035240c078000601c15101042c2a042880309a002105010111204580300e69120f0011280030440c00c1180000000303c0f229 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681245107 1250 681243857 681243887
    0x90203010f230a0e0f2104350316030305060a031a19090b15010c0203070611010207140d110601080c0f03010f0905030409140624040e010f090c0203090f040c 69
    0x20803900c00c00d0f0141c04111340d80a050484280c4d182c11481b98183c00081c440e40c41b9081c0c090f07081000075400c4140010201c00ca19180c921081075214070400b0050940c3d10685004819950244104041581500ca40750300140256540c00c174503800c6503501d02d82000842c0c070482459040200103010140e80720840040b041545109010a040b540b9100f010040292218101d10102a17451009548506001049a41c000380185042c5140c490159041104c002400009540801010002c6003000801c1e80c5684a09070040110302d1480710b005228004810314036100350020b0300100214038002030840f1030400b0880d411265200c4440000e4010a0944c0c1456903441c14580c0100034400040050700c01c4468001c000d00001a1003c000c103906c0c23a0890b07481d603200520000742a52101130180c80341c68001445540c52401d6256074601c841c0310001da1040c101c80c044a54140210004c900038083c42d503000b0b000035410070a080d0001142c03007600d803544a02a540d2248010600352140020301c0c0c002072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681246357 1250 681245107 681245113
    0x3161b0602090d12090f050d0c0303050903011116060c110604021e13050f060114030c0d060308070506190b180604060b1303021c050a0b28090203010f230a0e 69
    0x11380303510040c02040162140801204251200080ca802e0130120720a03402e511100048001d070841e903081d22960400383c2d40a030075642e1070580c082e031280c28900804212080800c000662070366440c250059034000280e06040211144201020302000a16190010303030485c0e01c0140808400300100d818040300d03000c2d982c0300c040c0c0c1c84840041105640018040c0ca1000825201c0c0d50310704005442042c010045c414201808100050869403410046e003460415444041203241d5644c8512445802441d000d03070380e9400100910aa0302c0203004001e14111002d2000c0c03014401401c001422281646244115070340300f1800242150303642d034009806000d20300f00160316200041c4450302c1194403030000302d00600c40360100400b0a5182505518500e521400400e0b600d0403540e18100c807000d000c2c10f074556400700b40701212030b5000c020503040a84105000c000402111900426080d10304d07015404448918050340b401107804a40e03800107400d03101300c86407401034450856000040455103800306141c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681247607 1250 681246357 681246383
    0x20d06050f04030e030d0f03110d021308010b0904120e03101803020708060f16090302030703110112050601080c0c1501030b1b040501050d0b0f03100203161b0602090d 73
    0x6209402190300450103039556055900444c01415070b2813080700d4044010036000402c00020902c6508461641c0c03c440e44040c1c104800d4a0403441070ba007095030345802a0180701c0c420b0099142c24460310211060840d28500c0701e00707203034440ca40e03140c10041c0b80c0390801640b50b246802a0728200880b020303080f6441d8003041452103881485501c00c03100d6104038010b00501a00040002001401034001e810f071600380941619080c00101075001400645000e02900400010140c9e41c00d0008000a6005039980c3e00403240141c00101022810401940518a0002400300c2030340d001602662200c928003006a880f40d800100a142c000001c00c0840e94084190010080158101020340124020b14101b046941b549004078050300031401440d000131005e000803240b080440c2c00034502103402800782d40103c0401320119040c001246064070705940c001013444403508c1c24003240069820b0b01e18080300e03c1ca005c030864501c4030350220340281410390082102c0c0c5450341c41c101c0340300b1644c2d444082c0000c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681248857 1250 681247607 681247621
    0x10c02090f01080d05090f1002160f170307030e210601140f060c060f0403030e0f0c030c011103041701060e01080a0606050108071b050f0a1115160f020d0605 69
    0x10040074010440540030b080c002c1403032503004000f1b84d0b1007010024156048810040f0500440749924403070340d0114481c08404580c082d01c82c1c4d512902800c0e4420700d030401e890400900c181030600703c1c050f5005551042010b02c011a5020000101c80082260b02c0400031002c0344a5884e6100c86440c5000503010701c4000084031510400b0412241038150303480320480c4400410480d0b180140320034000035400000029480300c2d288188158060711900f00000c06154180201d0300c0c2034800000c00d0040d51103107408180c10f2804000d00229040b00b480c0c400d80569030301e100640c0340d01440c03103400500b409442c0348280003034003074004102030032211448003125a591104140c2d281c68502d0181c41591900c0b1020605511488050f07100f0080d50f160301c000036003400e042400c0440b404409a611340202c41c401800088180003810000c1d0046480b40d048030b884108000710900706810003407070250104036000d1105400703208840d11581008841c45a044c00e0f0010542080200f50f0007058186800100006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681250107 1250 681248857 681248881
    0x13150b0a030209090609040b15011e1701050307140607060902030a0b040c1d01030b090f070602030409050a05070c170412030c0b061002060613180506041406010311040b010c0209 78
    0x10f90581190003031582c0c0c0380c140074000c000c00180c501410000305400017031404100c0142000b03c40c103040c0341c012010450170014015400d000340d10032000440d0076000d0400444c18004040c00350400b140541401444d051958614414600c4214000d044c045500c2d401c4c005141e229044c1d440c0c002e4243d80800d000c500d89010b00301c0301140e08a44000781c0c154081041c5085454550f0654260094551580d082da20b6180c400c8070000c005900520452000081102c0284010380c014440c1c1d030021a221400d00022406443e00100344c010784500c1c0a0400001c06d40c002e001f0100140c008681044400342c40c821070409106507000300d00f40201c8818604d04240d44a00b003894182d006400c4d0425540b41e2034200301d0071a4240071400011b0b4080340c003003107480c034214504107400102c00c0c100003103401740700e62514a84445030000f030710f203500940b082000b4040c200350b030400c4c5503c440c03018003076940c150b90761241c460324001701d000e008680e40c4540b0b0010303900a2804102c0503030010320600035403800c400074980d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681251357 1250 681250107 681250117
    0x3062818020402031608010b0405032e0f0e0c010806030a0f0807120e040c0e0a180608070b1315050f0f0909042f0d020f0402120708010e06010e13150b0a0302 69
    0x1000400d1a80001a10412003045e2707400d4031f01c014080c0c5100600346242c412000e06038400110f41040081244403407403200d00c29030001d4080c0d6000482c850000b584101d0034038040840e0076042c880c1c2001040043d550229484000c250306c0b02034031000c07140a0909482c58054000000c007103103445401003003c280c00c66aa164404be08840038004004140030448002d8020300246401c062140380c20f106100d03006c0f0801c00755045410000861543e940151450004554042c1c0d0f4405400201c424081c10310388203c00c0640400301c03545410101c1e0200c000c2c554440c103181ea0856401c081500e0400c0c603a141c0440c1d12407140205030101d00c0c2050300b00380c3e02c607100784070400d400d0480302118288141c22000e560b41010a0007012418010500d07000d000049280261169026608001c000e210640c47d614050081040da650740c1919030500c0d00603c1d6615002e40541c1c180920000c124040f507607040b85180ba0265031500204058181142c840191380054001d00300c0000042218000703c0d5040e07001e0301c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681252607 1250 681251357 681251401
    0x110324010c05060a1e02070c03150b01021228020f0723060c0f01180b0606070b130c0b0c2505030c06031e0c0304020306281802040203 59
    0x9084091001580c0489900500500c25082540000c43c030342865440100c0c03145a80c1d2806000511891030541260701180080b035901c40080340c148140700c0e01c885950803440d43d05408010b20802c4500107907641c0507400034540d6002001a0048010100948500844000031551190a0002c9001075102d0001495070149071052100000d0071580740101a000c2544003600549551900002c1c0911680b100e071078000603100c2c60403861809282440764a01d13002c912a00342d405c0440c185880c03038803003501620041c4a00c3c0240700b50030102d40802c01094000d900360122522089051901c52810f1245a0207440a80404148086020700100761350041c150350000b101a840320740d0b1840341442c0e0450040a81580c0100d900c03071241e0a0080003943c011094120700c40c0d100860a100481e0a2002c48003215181e002101b8041182810445290040000462620030000c25500702164034048200445103e45620402641c0b44a5501c030040d0385402620035962864201504151054128444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681253857 1250 681252607 681252661
    0xf190203070309110901240201110307020607110f1515040e010c18150f0513030809090a05040f02210a2d2004021b060f06041509020c011103 62
    0x2200782403608090407410b030b030090b8807e13084460703220010070150010a1041c0c4159903940711614200301a1001031845203000e5401420b00e1305e0400d900500442d940f00140c11709a121107050b2643c60b0011600600000809104a119980b00c0b24191084807103031120503005071929854002444064004581c1001c1c2c540b66900b0f10a912050341800c5000d40c42003d0306840950200c021041c0701d048101c0300066185000360611800e2072018202c2d01e01544100e070406d50020707484030582480859a9804101c01100700b24618050315010201d24804134024171400e4900d51801d2481d601c404c075070b0440001d580440d80c0243c4507241030000030400361042008200c903003040b850f5400075640404540c0740d0041028003c1407000701408040b00000300481d40c89a024092005801b1010800a0580c403070000182141e08100d2540307521b2500281045010710b090090300115000d41516803411651004801aa62006025120f0040120107003140c4407420020500549482c5004084c1e1521950407a03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681255107 1250 681253857 681253883
    0x90314030403170606090f0f0105070b0c04150807050702010f1809090501050112021f030605090712050603121803190f050705031606230c010c0206011403060f190203070309 76
    0x41003214042e9080f01da6001e007d48000c1519400c1c101d032145003221041c1006402e205059071256584041184c150060810100d402c2107113800c65059000301c6c0c041820590403e0604500007401d510500c10701a050080b0112942e140f070b48640040f02e56404429031804c083e030b03164203c1001138104428244c800790308140010417601c00071500d513180c00d64000c1410700700c58010b00310344d040d09407900c0c8208289662458000f031070b80c56642419104141d940e0b45c00301e80106400750042211400340c00c85000340c1c002c05110500c403140800701c072a0700d0000600f040407800240c00283c9084d684104600107881000364040c00c1000c01c68003040d900c1e1084081d40d02c0103490f2030901d03517500c83c0c400780710110710000c0ca01001307814010000c82c0702004211700c40c030007100c02c24020700f01280d06c862000c85080c1c0d59210144100c41d07040c80201d000d003030000d00c444812000d030f8001039030700e0301c010380460700500d50400400d5101955404200b441092440c0940d140e00d410000134004014030704042d503110b010500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681256357 1250 681255107 681255109
    0x1c021f0605010e0909070306020f0703080a090c0b0706021306090305060a051005040b0301020c0f0c01091e030b100807180b040203100b09131415030609030a030903140304031706 78
    0x1400c0a84a0603510500120b800a082005680c0c0140025009001c2e00c54044040f5400e0300041c03c006500d801e40e19540c05a0b07240003045d01000030f05d24080180740405440c00600000034100464818006c082c0d100c0c5454209070f4020310400040b50100a0112800121903030070000e000e046a0081041d6442942c2c0c44400409955080b180b00f041c190b21880c0602c03283c42c05074005003019002600040c1010b1850a18500e0302441038000c5440d40c0c499442c090390356074803ea056029125003e042c0b00c50310b1082c091a6400d44850000401e500070244c0024a403004040c0c55100900c03040d411540b619650344100f907a07600d2240c203500308040c205080145c0030704150007140d00a8441d0002c09d44140e02c0c212180400342c0008101c940d0001c1d031a988491034000c2c42c013075002c0e800180003482a00381000da00041d003200000c4c80c1b0b140290451810001c4520380030040e00c009044908001c50308401ca031408851484101141040303203603010040c0014558080141540d001040a1030b601a40b0703084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681257607 1250 681256357 681256361
    0x60f0402120303090a0f0f05010203070804020a05030d12052d090d261b0d020912010b060417071701050906060411070f080403050f0d08070c020a05010509031c021f 72
    0x8904c40c0003540902c032100b000a4010440e0500613016a0052002c49550303950182641e2099900100107800c9409000542c5000010344004003400c400600c0250714803c00a801c030391401d0040204260ba4000003440201c03100254030155126141e4480c10080021409502c03800546244485125091810020f5801200203450034250580e600d114509000e02c820305815000b0804c00c40036250b0500c42a410182c88050920f107001c80c14003680310346442d0140600802c1d004a800d0f041e07810540201240e440c0c030b90480e41560702c0b0f042c882055815559070685007044a030b11000106003c02482c0007110310640c8902c3c007452080055490136100e0104010503542c803100e0801403084108414000601c0b00c4030081c1c402d610607085582030a070781c0e8458134101520100300047e660465906195a168800d1403568001101d0030417680520890f008503800207030502416060107000a040a0346640400002080c2070881010500d4481d000c0c00007903c60082c03100b1101c40030031440ea00d070034905040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681258857 1250 681257607 681257611
    0x90b01151701051503040c0506030c09040b0406050105093d030b032a0f13090318080706080a18110a05011103250c120c090c0c03080a0e060f0402120303 67
    0x10f21001c0c2c19142d04200e13000701ea0025004440b0000110720018680d00c2d003801039482640300b24a940c2e102c41c002c40512050301c0c2115080c42c03040d032900304144003aa0f001015506810000d07101c0c002203442c0082ea0f880c0b01103900c4000740d540c900524080c01102001407641c41c04e03000640e0103200e01400b84061542d51b25551000c03410001403112100c000b0f040524403413668840040c008010b403140034000c1035101083d0181400c0581d01c8600810a00d5003011a149c0c03000007103100d4001503494618025200c404501402c020003643d034000c13030f2429110385c0003580c0b100880b100201b06c0d848a860141500c8903490020303402101030070750000f01e80d13001d4640ca020f102c4000000c0c52030001d52440e0245880100c40d010010041141c05010208050f09007a8024040c4030013005440c000302c1c141030241e40b440d540290354084c00c02c5818110b00343c2c41040380c104554907081428050311440481c0015003030360b450710b60441c42480d00b01301c0c1e01d00030b02ca070343e40c0138a00984208581d881d10980064070b038402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681260107 1250 681258857 681258859
    0xb12150114011b1e140a05060112030c110a031a01060206090a0b04020d2a05040b0406321302030105041a0907051c02030a0c020c0301230604090b0115170105 69
    0x1205510007040c205951112106a242c41200c155025603440303811440f038603403428540da88406040c2d42001808c1000c0e5016203a060104203102c0d50b6035600500c500b8585900805440504403015000d44604100501031a07000b1043d00e8080202d0840c5041c08030244210030040c81840701040e41a600410540b1600d504089420360603a11602070003000c01d09260125008400c1d01020280310b03104455040280030701442c9441558501003c1105454000807450f100b185010802c20003421040c2045074801e20f040b4910b9050020f020b0344401103085101c803260041c01d402401000d200040d07000b035069a2003107408011001107140b40d120141070714600e040d040034009021901c0c850080d0064440f520890321105c0003100e41084010980c0c0080e1400349070a911445402855501070000082e80d40f4150001c0064194a1083c10403041c1c0000b18419861049400b180390303030312540c03c0f41e002e06411480700d0b0480d5035a00d250818845a0036a801d002072440c940040c052036406204134100d401c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681261357 1250 681260107 681260147
    0x90c030b090c160507151115250e041505180606040b1b0109060501030201022a0402090303091503180a080304030509031c201f0b1215011401 62
    0x560b5007100f655190000055030188246000080c0c1c401c0d950a9442d200307070702d03036503141c8000040b1210301e450421076484920660a00030200040c0708080102c43c030903c014111514019580008180c80343d00302020801c0e081410203c40002600c100000c1800b1504251160901d589110038000342c02e1a054500944c03040d0200020480c410202d80903088110842e64101004101050000d0850751741c010120f0b40507031142c00400c1990b80500600e40d0415000d03683c014000c41c0701c43e0181a00c20b00034a000d106580c0460040c043e0313282007041d501d80d5500030700785400840760110700e45100d0300200c0c0e136900f1400e40b107007003038100b00c00108484003030a500130510750654603076580036585c1780c100c440915010b00c25018401e51052450054010800341912030b07004802807502c40c1503100c107a841000314039a1040c03191036002c030029582c1018180340c0940015261001030001001d407100e142c201c40103031007030710300d4014400c16001c4083d040f503243c05003c218010410005641d01e00885401e000c00007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681262607 1250 681261357 681261367
    0x60705160c41060f040e0103050105061302030f0a1d070f0509090307030c0213020c0a0c15030e07050f150406090f090501050d030309080405030a06020c150603030304030513050406090c030b090c 85
    0x30810f0300141101544141c1c0c03440c14240c603840614015102613006030b40c940e440704180000360503c10310b150300c20303c030b02001540340d850141c100e91054100541017400c202d560b50b50b030704911600000c01c00030f510001300a880031180e44030310300b5290030100c2c010584120350000100711900d40000880b1440c540c107440351040110341e44c0800489c540000310003082c40781c0800c00001c1388030017402030081c0130348941ea00003089810203510100e508500071a02041c5442d02841c400b640200183c40c0c0c0848404a81c0310260341401c1003c1127083c01c1055040040440114001c100150030240100584030300d140344801051307690080e034003034460030300c905a0480000a10350300880d100340c110204803401030f00342518050355100880d05e0024040720954903250301040030031050f0301c00e10003440190b5007443e03c0405803d000f800640c99102c05003000b4107110000a03c91031610801a201c00104001401002602c4e83c0b410403801600d141600d49000034a4001c0c04106c03450f14a42c2270380200c01d1118014102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681263857 1250 681262607 681262609
    0x20a05150903040f15030f02030123031002131a040f1509150c0c090c0206012d0b0706240902070206090402070c080f0a05060705160c41 60
    0x40d0018004169a0004000102c0c45440c000000c000514851144d2841443e4100700101110001c1001c984800d00400c0108036101d0682c80c11403091f0340d000450310f003100f1658002440d190b1101e0111440ca4000718881070002904602801218484070300e9030034444420742d062038680300d6802a215544101c890a0003181020043c082518582d03041c907410a0b515488910f405d040b00d80e40c6200002c000c1104242002a420303101401441e030b03400103000c1d10100348400b07515842c05008500b800c06504070b070400456043d00417815040d106050b80781d8101d803a400d00c5041a0b20450060301e44509084a41c021001121170041c3c031a14104d01d2010031a080000450207035000039009c2c4c0e80400c05011241c2e01c6d0b82c1e544020610390f48682544080589400d103445d00300dc0d0040181171642c1c10840d80342000c5400452030562183c55480d01681d60002180e95070450038914501420781c400702c00300495200d40102c018054a011199441c44c0c0c85c5a500c000000440e0030002c00c2060850101c1088071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681265107 1250 681263857 681263893
    0x30215030601020709092d02030f0c120102090a0b03060114030405010c030b0118030311150a0914030301122402070b06010315050a12050c030303040302010209010306090b3109050f0d020a05 83
    0x1102074442149042c2c7c002507000246051003100c08042c0d140c010144480ca00d00e0581d1204d10308a043c08000d5041c00c0038000040c606c4041e6103c3e040085c000000001c48507881840001d200c0ca01c62a9190780b070f41810705006000b450340c10024000b00b460707c4807280c000d60090011003100b0300000f244920580c1950382c103c5010305c07100e001740f903540b01d8075446031900f05910134214414102410009144055400d02c0307901c108541d12612680e800410050040d92414001760282581011019006255881008a00500308002c43c0407103031001c21140104941d50482070302500d000d90302030000c0c1c01c1c1d0101d030600502d010321031280d02090328031040180700a00c0c0c99104480303015409441c800308566001ca0304543c400c030b0301100180d50026054189603050b1050f1300260000300020070050740d1940c0441c64540070440409540c8513070104507042c1100b40c220035150160106401c1c05480c256203040b90b6111060400c6026500450403880e00d65803000551861264110f402400340d18000c10407004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681266357 1250 681265107 681265163
    0x10311070209060121020406080916030305030a091b03050307150501060219050109120c0b24012003131d04170c070312080103060c0c030f0e0a03021503060102070909 73
    0x1900008985d584060400b032000c2c1000b4105504c0e00392107898840045810100c2c02d204e00c0c4a122803060043c00426800000e80f50300051401000641001c0d50a000342c0c01080f0055006040350201008810000080050f0580b203204400500e00d83c007111502c802500d00134052800140d105a0b5030464035003480c1d21180c9a58041d800005064000d0346414440e000307040b5414020501c0b41a5032010018018050359000c00c848900104c0c0303408401d440140c401d550201d00b81004515481081b800d082052031410084505007160355441c2080b4a14040e200b1910500501071449583e003142500c4800025205660101d507030803015400c21201003981d040f080b20701030207200e2000c000c8000f45446064803000c071010380f00d10403d585541b40c078605403003454061381c042040300e00381040001d4002d0071132060402c003070a10004011148002c075142500952002c1c0d848500740a0302c1c84080c48100007140030f064280d0030b4429040e20785022000352280711f01c0040040990048040e030206415170104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681267607 1250 681266357 681266387
    0x1902010f140c0a110d05030708090a1709130e0106140901030b042a060e27040605180a0c06020d0c1a0a020d020c07080c270903190e0103110702090601 66
    0x12000241e1413802d1800813031811000120302e00000313005c202c2c4c0d004402a81c2c010740001c010a00c00500750b580084e460554104500c5d00c400c0440c1500c042c1c0e43d801a80301e00080b4000341001601040c840c3c2c1806031003e0301c100391000007800d0b2110b08600b0003069060503613070000107400c440e03107541d55204840c80440c0010306000c2002401c0303050150151446030000c09042d514544d00785a01804c00140c0c841d0501c410070b546c4c0a82d82042c000044c3c1c145002d50068020000207166658140800b03100707240000300c10840e000d071100c034074200310301e0384c20039010f640040c2c0c21103c4603034003c1010f0328540100b11001d000c00d034803000011401aa50250346900031103000b80941004580c1c4031002c283c2c1c01040481c1c0d41904401800d1211510802c50000150700440380c40840114013241006041303802c10740c001389056428000380c040101001107900c1c014400445460703014268100818200340300c1c610900203420880300d11091500881a0f039001c40c0c0003404282d00d901c0d400015500d4200b001018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681268857 1250 681267607 681267617
    0x70201091b0302010e060c060402010c06180507030c06020d05040b090a0e0403032016110f0612010602151b070c0e090a020406050612040f080705031902010f140c0a 72
    0x600003400e41d64071003070071210615400162421440050074100315412841e006035001d00000004d044009101e5420580a0801e40524042403d00d200503004001c10102c403050303940c000108005d00014528112030048202c0c0a2880c0c8808080340c5130b2250f0003144002410520090003d0a4810001e00c484000241748009483d500e100f1003900300000c480540100e03a40d0708107118070b0703a0b6440c400080d0501000e00707189070400d80095403150030184580601844002c84001002c1d85850501a41e402001010607886846c090014040030301c090041400500540519441355403400c2903660007101070140481621104500d40005604207007410b94070514059030000b901800000d10700e000b24442c0c00a0568002c043c010b2000b07032803035640403d004410800207071172600c000202054205501894500072608141001000e0340920b44003c1c041e8080000c4100e143c1d00300c984103c00e5502c02e60001e201c446a00e50f0386400304c89186050040c4200c019001446c0c03c145100242050174860800d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681270107 1250 681268857 681268871
    0x21509010e0d05090120030301060e03100f1508012304030e0d080414090c04090504051e03190e10050d1104080a0209060a030c05011d090f01030c0f1d070201 69
    0x2400746001c07075540382c650108100141d080072651b80010707481d40b900d5150448000129a8a4456690f07100c148101c41c20440c119018011980e000d200740300c183e103100041404605412440400241040b0a0070000040f40100004103200c060240d10740d2210140051650401400381c1440b11240041c0104c4c104006880800360aa90f14502c040110740240b8289440c2c40c18201c1c0c4000c1c50803240070251080303140d0020021a1809503003102e0964040381004503443d00c0d036281c0b0500d01550442c58000443c90b5046a039140403002011305480440081c8261158010320b2003903410b42c00d241e5525400c008019491403145002d00c00802c1c0314100c54a001840c110707050740c0c0c1b00030341d045a0000a4035400442c000c134203601d00007003c0c0b07400c4a41250012891803031541c50350301e810a144100c506000d1601c481040714001034400c440440340181c1a010b051600785d20004450801340011076403048444800b2462466808019042e51020070895a402854098000c1002c400030400c50841d903c0d02c0d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681271357 1250 681270107 681270131
    0xf140f160e1807231303120201020f0f030906070c08070209041e030203190e01021b0a030209190c020c01051e0d2a0201090c0e1f060504081005010602150901 69
    0x81014481d202c0c03542d80340141e4074540b0384103030030303412552a48004c20780900120400d215011004001c81e5880708850078030b0300303170600c050740a4001c45151984488021560221080e058001184900e0345a01514000e80d24104107584010104001404070441400150010708065000e071b50824010422141c1a10750b000100d0a22914000c0450060308089108200104c2c106045440c0d1003d5041200310028504d00003503551045800c00c030140d0a406c0240440ba465000e9000085e40d0007620a8001d0700c2c00310140603108035450303c90b0018928001c920f0040364404586850b030480165036003032410400c0201c003c40b1b101d401c42010488081080440150034a41c421365a503499114510012264000d20200c603400c11710b6820020b590400d00e80f1000030310503c07d0042a0b441c1100c04c03411030340351081011080b2a070684094101084039001040064115020700b0888a8040c101d42c040d14941440c28140da9007031140340701590004645601a0044d001820f07407220b8050f0000881e012844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681272607 1250 681271357 681271399
    0x60902040204260a030509210a0f11010801050a050402091203070c03020907090b0307050d1d0c030d0521071103040f061e021f0b040f140f160e 63
    0x603101d6007000f224621a076191103800103850950404000c0500716540094802411921035282c10314400c504100f0002141140e507984015041d02c046c040710000c040d03510b000c03203110000d04029a07016404480c028141c8d0720030b1ba1460306840303005e40300303030703212860035040c00003a41180c0b0394242d001114400c006e83c1480c0404c09030510601035941d000515196005104c000d0394054000d8003045601c035024003030303010f500c021a0b4110410b40741032680c55a8103404800241f00034144015a070b00780070061000c1041c0061680c0703100100b00c040d02c128544074041500d540c1315008840203030320b180c2140c08098840103d032499020509051580d1640c202035581e50441c0d02640200701507411804092100350741c02640e1003010001da15207a0b0041e1070180000c2c0d80c900c42c1c400261618280105075620040c65a001040f2115000e441409488203a568200c080c04074000d6151149003030b840000c52a4010031085801840022030038206845c20039421200011001a0503805c85050a1198401c0002d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681273857 1250 681272607 681272609
    0xd030e04180b010f1a2a100501061812020f0d08030901020a02010f050606070b0403090b0409050612151b070230030a0e12011d0a15050403050313060902040204 70
    0x41e501c9500c0543c100448050307a04c201c1d40200ea580284401e00c070300c2040741d681c00c40300d412002c1d405e0301515000074102e0200804407a805071045d4082c40c0b40040070300296400c254140c030b00b81d896003103a460398100f0701d80b42051588140d001281c00509420003500b00240003401c0000003400e242c1c200702c0c1a445501203544140c03003005131a0340c002060700034180e0a22600b03600b404220024040303030a104e0001285030141c0e80010b0403c000500106013058000c0c0070f07400062140106041c0c8441c0e5410050008000407075940340180d40320f2910b10405080490a20511012000030349000d1f262180703178070000707940c280c07807444c0d18001003203e1809070340ca9811100728191100d00c41d2440316905645010044c2c10550f00d21200ea0041c8240308a0503044480180e00c1d4400fa9826942030b405201030b18050169090308501224a03403240c201c0c0940c0204040b07403442e000d96840c12042d801c12613094111001241d016001480030704c0410a0f100341d400320090424040c010126002282d45c000504070b03849 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681275107 1250 681273857 681273863
    0xe2d01060504020c0d08150f061809090a03032004031b03080d050109200904020901020a0b09010b1005070305041823060f03030c0c040506031e0d120b0d030e0418 71
    0x101d22214646c401c0005a10240490407120401c141c00007169070380c41d000c00303000d04c1080301080c0b412540000610030760300050000c08250340340c1041a803442d201d00c101202074001909003000c184a41c11003041c42d40008400c003c2c01440d241c41c44c0c441140740c0c00c83c11002d10040348008400400700d541240603107003a560720b03030002a01d545062452030440301c086a10001c85085218100f00c0c2d0400c1c5400d545108001390b401580d120203450040b41405a464801804801d0400034011800015842442c04410a13161148ad007c03560b01c0503105400307100707001400a5000c10050180d0020807002c0d000b6652048004100c0d9403102d10b5214100b03441c0d441450a0450000070807116140814401f070300410290003135498003200c52213840c1c035211906401d900ae00d0b00c95010079900c2e00e08002d1100c61400c06031003460000c41c00f4070702c10b444401c43d0f07a081c0c000480c03800e90007448108a214a03801040010f101c800396031840d541c1980e01081d1601050b0384280d40310f6800708041c085041f0300180c544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681276357 1250 681275107 681275113
    0x8160804290106030e0f0a06021c1b0f0c05060103111f1e170609040305160809150903061602010608070f03051002030603060a2d0b040e2d01060504020c 67
    0x1c1840c100074221144c0d141c0000171580700c0104825800b00c0452200c18458100402507555401c4a1212801c0b80c1c0400602170302c940f134030520001d00303410803040d83c62516042d9a4051041c0d19404100c039807010400c07020f0403030b4001c0401040098a018442c1d01200d002074900302d403079002109420621888105c099000c0303103996850310103982002005811200c1c890814050380381c01581120300702100104061300407110840400c00381070040c01034036101c0d80709040188544101c0c0c6002145908841a010b00514039841b8180000da4070760181c035003413000074008010940e1030450a05513420590660700640d5a01c10003c6000701d0107020141c041c289105038450750a140d0710f0010702d00300d04041040451481881485101e540208800303130002412030001c1075001d08400e001d410511140d180320005c003e2503222461a11558004841c61802181d0810000e403810384801e48481c0006000e810410501041c2d00c00030044107600035800740284000195291102c012070126070264891400302c0d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681277607 1250 681276357 681276359
    0x3071a0c0114070c0b061c030806040f0606090e0609011215090204050702070f080106030305120403260411031b1005040f260705010813031707180501081608042901 72
    0x2c00d91511032500f02101fa11240c00e03c0c8921102640703050011a00241040f03892400b00d038007995182c111189034550b081e030420496039950006400c0f4240742c4240c580390300710742d0b00103481071402602c124102d031509000c80070303104078643c3c664441507012032101c2c0c6600d9031038400c20050380301c45c40b99511816042d00145081e0b130030450f581c2402c00b0a5800000c140e1305291091000071340c0b01c0143d51448005070b04440094030350307113410360f928130402c0340d070b416010480c424407030b20703118070204103401035001c3d0030801002d18030720040c9512924894116521408505905001c03424042082c050b005194604a41440e45917089103005001c19404500030301d24484024900140304407041102c0300f080710041680920780400a4520400201000f4140c03040c040f40c0c3d018075000d906910504028180000490315000c0f401508154401942e41c0c44200304500200b05540561030640c0907441d50080304450303d01c0c0764030441c2e00d02002002296148042180d5000445918075410311b2132441c0c0070503801c65 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681278857 1250 681277607 681277613
    0x15032a051608090a091503020d0237080d021203060409060f02031f0e15150d1d011413230c03010b090402060703030509010b06040803130503071a0c0114070c 69
    0x42c813050f03044911210b103060f11548064591180040c02c0740d034180c1d40440c4d06500c40c0002040d040b4a400e400510030b208454298540d141d08600f2400010f22810b8129401c0e00d5144955450306108a5100903030300088040c030380c5800346c40240d94010001000420200ba403941d0300810f80e41244480c103030098000c41401611098580d090b40c100410700140540d007072400c1c110800815016109a180d0401d03c0001a80b5440c1c0581c01242c0c43e078086011030760760100c404a84014048100390042c49a0500c911000440060080ac044403400c894920150f894185000895564903542110040c10782c03050302004a00c54080103403800d920001074441c0c1d4200009142c00d41b51520385aa108841ca01d04000c01a510102039030b45084e014070340040d803942c1d010041e40c018001c018120380e0080010a0010b11188000020700340700d060309500248032a0b030780e4189690750300301380604010003102c1c40034200c8608098014140c1d183e01d403000420060b0120012184107032081e070b03228002411540c030800138 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681280107 1250 681278857 681278869
    0x70f0209060108090a110d1a19022d1908070305061c060510030501051302011409030303011a0d0906020c0c10270503031315032a05160809 61
    0x10240e02030a0011103440c0c076408880e01d61174144001040e14500704000100c0d03840d03644500420aa01803046041e03a000420800480e071021900204107c8103c6200f0004407021300a55030030300704061849100121105c0e040081528255160642c45800e00500480f000c5071014a00440902d03100c886113070034100340060503140c0080201c0d000340410a0789825410100d440329580c00d82140001600d6280e001d90620362044a80c005015903007081c00f4010310000e6901c8840010303100340c9480d044c800c0c0d07030000361080303004000b4030740d034140c1082c0f00410440e411000781104e040b903201e0508bc034181010030074008440403e10180c800c44c3e400300342e500b8228000c111030008400100c4124400582ca0340006200e28503c0c4981d048404130b4200f02001c40220b0300680d40500001020340784c9a03648010050b040807030520a1100e1590291030808035240288240315040c441c1490b60040c0080103110100c100600d03014039800c004040154240201c241c1d00c064018510412425a8503246e0008000b8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 681281357 1250 681280107 681280111
    0xa0c06080708090f031903024e070c0206041a0712050702220b030102280f02030f1c0507020a29160e0909010204050406271a06070f0209 60
    0xc3c2d154000f821641c2c80160005c160b6440340076400f00070401886c600021800f07809000415120381c080030208003c2004503043c090700181042240c1c5146a41c1d0010b2400d092501c50071001003081c444021800d840d1103900303d43c96290001d080b161901d640c4012044522208089080ca55040829007004020105580c480090b011b03150040c209140764000a9250b00101140719445100300e1135518850f08a030072020303410340300500031500c07685590305104041ca4403e040c03c044403800c549024020340070300c080d840380341402d40c001d40c2088043c011a000070b9005400e0002005011720b400400400e039400f4007407003040d5aa001c2c044410152410042058496400000d9109043c900c40200d4504042050344040c00380913860142610308000d580500c500c1d2505900490100704011030301a05400410444030251001c1024a9a40c0740a80e0f064100240750b00c0220b00d00c2d1a41941c06c4486c0c0c0048498400c2c0c0032145200802800025101d03a2005200300c80014480c2c1c200c00c03d500d080b0042039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 681282607 1250 681281357 681281371
    0x7080412110607080346050603010203070c06020a051e0c1216080d02090a030305070516030b16140a1220042d09060311010e030607110a0c06080708 65
    0x10f00b020001d6a4031034550100410b60090304d00300d100c103014088207201e500080b0740d501d002e480d50101b8490b6120300000c8551428205043c0c1040c010402904051003101d00c20301031030360b60410703998169803190060340c80b1070700090170088107011001900782c0100c941000b0120030010240d4580100c4c241509050101c07122020b001d501344151205000300303911320090359a0100e0740b00c0c1e42d40704210803040280100a175803500005440c20200070150000c0080102070b0040e401c40c0c070901d5248020b00010303601800003c104d81d014402181260301c0e1018428000b40040c20045039100044002c43c0141d013292202400094000b40e60003144000d5101d904c103a014040b20990400c104600070000038461031007a010300c003080410b0544a0488040360640070f12000e00002041d6a44200f590003501450005507210032208080c44419802511103184c0340101130050081076075071400c00e444d030402d8000020050f01940f22000005401d10350124060721040d00d820545080be10f07002051164010440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 681283857 1250 681282607 681282619
    0x10c09030506011a0d14180a0201020c09041103011103060f040912050a090810020406090801020a080a0e0709020706020d060501020f1b011209051f140f0406020708041211 75
    0x1840894008110641035804d412111a9444c0c0403012609031482070840340c0d481a46040e10030364940002050407070050102200c2000c1c450020b03000c0e5522001107100084c050ba0210202c54030a01380201c0c0180c6c040e02413500000c0201a640c082130030b40d810643d140c90005c000100f08003103447d260705211800102501d042117644002d54076001840401041e40c01845008200c18074194400e41c075000243c003408055440c407550052a402c040d41090043d9000b06d10b500380d020842c03a0b0144240d94405040c0c0c1d0b40c4100d00c2c3c403090040d0000700a810b13850b400e58010004081480042da000038000a0312031000181c3c3c0e5440400b80a04650441d08024115007025098801c0600c0018004512200707542007100139082d030000585c0c80143c080d00b41c1d05c0982c14105101d0a0080101d1000c24004141201400312130150303081900711111594990801d120ba4004500c40300f00301c03030026610621490006150498544a100690f003040e40504040c0b030012051004101414401010b05401503d070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 681285107 1250 681283857 681283859
    0x111011404021203482d011401140a060f0e010314010617010611120f0f040f090f180209060a17030c07050604030305030f180706050c010c09 62
    0x480c180410300500064030402040c246145103010900845411414148041907404003000400800019070303603c1d5800b107100134495100385000220b0300c9080310f2811001e800a500700c042c20404c0c1109005050401900085400c1d2000c00b09100300780181032184401c400541c9445014030800c890005001d00403605e0f840100301082e006420291848030504214055044201c0102d00400c001341c0a403c202c409900001281c0360040304451209003040c08040e6184e890b09020f4440700d00d044c6415003650310010703000108010300800703403a442e403c1900c0f0a180000743c0c2413170203498000da0006400442c00d03d60400400300301e03101d0b00303501c19080c04080c060f02c491b03441c00006c21900803c002e0700500c2c0d9000011415030f1282c0c0c00038040c2017001545003d5034038007c0016640d80000c0c03505d0480b481502d0000c1b901d8030740324080e601141c0d0726a0315285555520005071031005c8000d404542d0340d0a00c5d43d0044410780f400e01c034031005050f4958403913403108001e4060074290b603148200002440202e0038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 681286357 1250 681285107 681285131
    0x30b040f1b11010e0a14100b0a06200102030a15081605040c02150c130b0415050c210306010813020a05040c11010f050103030f14090f0a2102011101 65
    0x40a0896031528140b040840c01007034001400340c10b038408441d440d8060303028441d0812003c0e9080740311000c420400c035580039440341030303100c1210761080605501081380f2034200a02c0d4409c440002003070039807952032035840034040c07410b80c02e907041a41e01c82e1241e074480c04120041d040350300410700144200c40040c542003a0130000303031171104407900549001d540c94020306822580204508a0101c8600e6030f04465460031520101d119004605032085041003e1070010b041044403051b1019510001015401703001c0c3d2080c00d40f43e40d48526a8401c0303601036124010b0035802040440500d8200010f003040c5e1302e250150005003407210041c818407000c65001084005612543c5501c016100195400070b481503043c8400d80310324011000c401850b40c20003100311807100450700b040d1304072442900c880b0000300482c1020b460980704002c0041c0145018401941d86141c10780c84d2040c0740502a08c001c0086031160390a00c0104030304621a00c2e010412141d4000710f5911000380c40540c0f1a0400810075079a8000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 681287607 1250 681286357 681286391
    0x1b030e030a0c122f010e0d20210705010b09090d030e162603120411060403150203240105040e061305040f05060a090b0c070c15030b040f 60
    0x104042c0401c0c0b880c2680644040c044c4504d0303518a92a07034201040300e04441c0000344011030f1407401011550034454030040b556000241d0203402c018030f48913282040031039841001800c03044110a4828403400198415100200c140125214010750003255200c01504041e42561400c4884500a00502007082452a0302103805035081d6060f15002c5204010052034920700840c180480701d019918a07800203020180c0000000d8104907048034040341e80e9201101900c900070030f80c424411310500b000080004c0c0001c25108c0712800d004240c9424152607888000b8061500e80c00e92054550000601126440d2000c250500c014103060b40d0544111000000b090340c0260710075400b1811011300480c100303070744610035102c603801c9001c820417403132030a41882c0180d1058607030217a41a004d0600402c100081d80c0c010500c0c01604185000259120b802e0440030a900640003078801c1074681402040c4107281d44501405c0307844580d404500030f0b440600b000101d40440703800740c07255482c168046803103216070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 681288857 1250 681287607 681287627
    0x50609151b0d091220130902011209170f04030b0703062103021209030307050d020607200a020d030e0904030905180f010614070807150f150b0901020703061b030e030a 73
    0x4000d1030000d0a400209201c45542ca4920711703079101c042c030356480ca846100c0d903200d08a280c1c002d90365510041c07081d0006000f1244111005003070608007030320313021040c03140d0230040114444d41103086141a030380703440c0c2c0e6410060a840d90350000b40c944004206100075034265917081802c0380110601c0301c56665020750307a1160340004c617000071400305d0b8166040d5414415216526081404c1d10900101004001d440b680704072000707030201310102045101040340072102e110031100035004019070041a020400118103020046042182410201141ea00c9640349180294840d0312030307a560301d0504081203a00c0c00e4424101c030026040c0820000711401c2410881d04581081c03d1568034191007081c046072034452381d400a444090005903100400c110104c0070b042d0810400e004000d1403051502c190250f800c00400594850700d8040144007003280d58006005401c014012121019902d40e560801e03a042010744075003841031002030340145905401502400054034015610b001e1070008060407019034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 681290107 1250 681288857 681288863
    0x10050f031b011b020603040804080607081306050c27011e0504030605040305130b030106091202031b040b03070e011d01080a0b04062306030124050609151b0d0912 71
    0x8003035146403495018080f1815a0054880c07583ca00e042c1c102196203034890b203d1205103200320000901400d20542505000301030022040060010b00d8481d01d02525010f082080045410018240340d1000c0800400c42034a0a108801025103220000b6003262000700c00741403451f0390300d0040170080b81c2c41402c440c250380d8025400103040c1c40d503040440d0b2a0040c0d03400380514019444001c203608402c400614101e03102650743c0c10700c00c1c0d2103204004443c0d401d00d4000790113910100c40e001c0c42680111030300c42e0403000034100180018142e4000f910708541d50340b00d40b05000c0342400500011076032802c09002500c0103a401050765140100d4a9a100803504002c0c109000c641c001c2000c00065400c0030384410781103420302031603074110103080b00400015248644a03620303001030b444101c801044440f16107055102c800c070707505151809010305a8814001203078415908d21841c400c02d05204040c190b0000d00c440300d01240060440041d1814107000340080c1441034003031041018864070070340380480d90380c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 681291357 1250 681290107 681290117
    0x140106052a0c15030907080706120b0f030d03090201140306090609040602070807030809060f01060e010c05070906030f1412090112090203071701200313020a090510050f031b01 77
    0x210846854200000b003107050b680701e00c0350000b4500444522000d54000c091007020b032002c041d55143c0840c0d48160030b01c244404121301d000e64440b0070302541d00c40d480c2d80c4406800792007042e109000090034129812015000b1980d25098a000e40d40d0000c0c010304580085581c0341c0c40c0d41002c0c3d0001c0c0c02d030320380105041e1150308140005810004c00780c040c0c8410369403102d0055260300c00c61501518584044501d200345106400c0003814210700303200d40c84e040341c0c044d0300e400098444400045400862030b00095500344600000080d00683c507210f040015800350080b0030101d682031816031079105420103c00c1069112481903000e0204150495030307228001d00741810b000f60150031010242c100c10001075454001e0b28030015811507011501c0d03a030424480001c11600410405507042c000354403130016103d801c20300002c3d160f400380c000c0046045000818010101c0c0d520f4601d44141e0300308490340583c800c5203100c01c0009040c07001301d07513113009000c601500088052290b00020b150480d034040e41086 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 681292607 1250 681291357 681291427
    0x106020f061506160f050102070b060316060e01020a0c0b0915041508060a030602070308160f080115020f031303020a060c0209060d06020904060306050609010e07090315060f0914010605 81
    0x90700f829032203d5181e809217640c49002d559040c07250003900b1140c0c0c15100ba0f190140022a08e01d40400d0103607400d0401550b040f1000e00345201255052861240141507106103a03982c401314801132a0b80b001000310400c0c03c2d43d00c1c981003050081745210043e5880d00103030144070034040b40404260001c2c1c00c441324941301290b6540c907000a0304114290703101602907840002d8010a142e0b0108403144646401500c501c0070050805048614402a414950010b00f0324130051061100000316860319185c3d03441155500c1103540f03080380c156485070580440c08007130407070f00b00114102960f000c0000d020a00709032501c2400784c0c0204050601c000c8c1349034400c82856000748200000e40e4140e43d40054050810002c1c6c030b45070301e801e000030f0400b40c3c1c1aa00c0b55200700700000781844c078000b01610034000750350f070102d030702d0700c0c55980c1c03c0700c60302e00510710308a561181404034049182340480c8000345188840852403142d401002007100e441a006081000f40402603103d8020b801181340b100040341642c2d0303401c0d071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 681293857 1250 681292607 681292627
    0x60b090901360f0b06030907120609021c050d0203030115030209030f03030106030c09050d03050a11030720282601020403060b1009140103051f0305060106020f061506 73
    0x10540d20300425400c400002c0c08140d0a00003507000050f20100c55404000e003810b0f1108008140c0422150f64985510035002800240d2051508160440c031070400828511030b50350004484002003460407070303580701194040050003070410910120040a0003e145103504140c101c51544241c00a000285600010000032a403801c004c201c00c100466000d980d00c1c1c0d61900c40040113804298246070006e0340c0a000031403207203417050380c10070640d0b41a15194074010700c1010640b59141070070400c0003a4041030100c1d1012503c1010450f40f41c4800940044001344020200862070b2080301260f03580b1800b0125100d1080c0c245110a030a0ba01041e000380c5c0c100030102c04040d07100440482c903408a500100303001040080c545c00400781203c0444007040750f4554030008403150040e61140c0c5031511342c25454011031394003a84c0036a03040024000c40701c030502d030000e115244041460b4800c44056000070010071949038117125801011a00c0d0014000a0800030f18401ca20b52401040302d201c0e10000071860b0b90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 681294964 1107 681293857 681293909
    0x708180312070e18010306020d0c0309020d170408030f0310150203090103050a1803110f010b0d0204020310050d200603040201050717092101060b090901 67
    0x80c01d0365044402c6948000000e00745400c03110404c4030061041c851150a80078500070b081c00340c1e4440c1004c01503c1103d01a0307050004262600072040010380c1d4000c81c0c9102c40e504802030b48400c110324011003029110341e5010b031100b4803001a0710110740a100340514860231000032040090350751015420400d11070106041c0068008014451007903000c0c1c0e02013038000700345400c001070015400b00100c0007614020825404035108042c0908407480070009415600c0f03407240280504140340d408510340c011140d40081c4121703004400202180c0781d0b112017600030640241006c1204606042554100c03441d201c0d0240d40360021152080c0e14140101142d00456041c1e40d024500051034484008007512010170707050750355040003404d04540c0e54114010504101e8041c1e29211030402d4456401c580c3c1da0b038032079042c9100030300c4441c1c0c41e5610401c2c0c0904441410500d0802e10b031000c20540301e = true := by decide +kernel

theorem cover : BRFrame.Cov 681115107 681294964 := by
  have h0 := BRFrame.cov_init 681115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 681115107 ≤ n) (h2 : n < 681294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
