-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:05:11.151894+00:00
-- url     : https://prove2.me/submissions/2fdba771-9cd7-4b31-9a52-51831980c8ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 768525179 ≤ n < 768705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 768526429 1250 768525179 768525181
    0x180f0305151b09041506021c02030c030a0302090a2103031404030509061c05090a0605010b0a0c0807080903060708040203010b03070e070e0301090f08040f090e0601050607050f0d09061403040b 84
    0x204005440d800b21480c3c2d1383c0141d80c4c0550721a0002015076007030141c50590002c010b070030b0708042040c0c070701945001a102194801c000340141c4841c04010307903511042d41d08000da1600440d01c005864111150021021242c1d0001001c002501d200608503515005e5103080141824011004a42241c1141c0145c04a08108040074072410040000c02803902c8132a1095500300300c10302a0000c0d20386c21760302003166900c0840617030280000c910603d4010076200403450710b0080040c05c05000e00305903007005481c2c2880440d94000b40000c9008a41e040c2500805407005490000c402070117042e01610240c0c025840c041c0503d5042c140000d222094542c0011400700750742d5042800c03a40c20200f908801e03015500c5000e8507001034044203800c0103036840303408540d880e1410507041c482d4199541d803000000320f06012150f08000d6010407900c3c103440d01960303501e0352851141080740c80c0100c1d45000040300e228000c186106680c0c8100d00c80c040d54455075452500c107025182a03202808142c80103040c0c142c40f02c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 768527679 1250 768526429 768526471
    0x3010908090a120b06060d02070b010e070f0302120c0c160605041701020306010e100c0203030d0606080702060106050f0a210911031b0d030e09151009080a03080403180f030515 77
    0x14047c0425600c3c0200161410000ea41c4a41c4d480c3c00a0344181702c05003990341030114003a000b030401252030340b9a260460500e0244800d00000d80c0000c0e0500f105d402001a880c02000c3e41441691120713000c03285500c1c05242d807410000c000c2d41c024801c050301d0403507188594012042c1802140e0040300141d4400000400a50401c400351500c904040180203218039080e00503141032014020407000e510740010180d1900c000581500e40092245007150044001070144035003200c10307210249500b002e40e90303c5611124040d070324450440424018440e40800a000c4c03055140c121010f201e00c04d0500b09c1c1e94200780c400340361781c1d01c4030351040d140015019044c44500381010541556124000d141c0f03000764000358408600c034004107841c0d00126559a500040c100d080042988641c480c4070f00e80400d010b0b02c0c042d00281c45600c1041c4c001c007040f01e140301090030705105528124401e4803603c0407032816170b5140c089110220322440102c038036020382401400c403500c185001511076912404003154010b000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 768528929 1250 768527679 768527689
    0x906180b060d0f0203040b0a0915020f090d260a1d040624022506080703060504020a090801060e06150d090f0b090f0a120c1103010908090a120b06 64
    0x103500a6401200612460350610101d014003000503e010b03600690300e060504100221400040003417602c541401002c1d00090390b50a082a003a0100c4d0314016160030300c0055a400d140300b0484050360000c1c1840410b8140100303488880007160350480100b0000c0b291520b032003c18003800e010140410303807400c1d03441034988581c0181f4584106c010b00015155443d4005000c100036240203860421428200a03d41d05804020750413071480482a41c01c081c02400c002640c4461103805040100007034000406c5039580250031041c094040184203640790880b0f060010300078680c9101d10509903007130902c0024040c110003455401207001800200f0300d111502c4081200d83d000e80358412025951750444000f0986011140181500c500310205650502051140c40c00c0200c0504079516080103074104006092008103407450b503281d040c10158100d290810030340044aa6000c1501075007800c01407010020b1000040c0200403048802c46400ca444800352190321040410080090030f00d040854024642 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 768530179 1250 768528929 768528941
    0x904020a020c06161b08030304080c0c0d050616080402030d05031b0708071211150601090810060e0709060e1c0f05070302040b062118070f05030106090618 68
    0x40d00403150042d01c980c001c100f9541c0024480461400400d80341c50401c82d54010a40a840100c032504078124140f4a0590b10b80c44098402851000300140b44194400148814503107d00700400b445000f004900305140c40d48400c503000118070340e03d05038001009000f04600c0e4025a0003500130010b0440304c841c02d0301d03954009000125490107118200882102c0c5200900d4000c0c030440c0f101e6165041407038040700480103c04010144442c0b01c44610a000000421040f960780020f501d54042e1140c20040c2c58107180c503006540940134038001c1c081f0030b200d81d400c01401c070b821400145c6d2080e41c46d40800c80350b000d20741c0560400145107080d80f09540c901307001d2402c1800d10440d481c0d122562140d8a441e5034203591b01c422641604910f008000398034041c13084604a410940b03103140381064a01003c512000c640154011021400c0003181c841624501407554808001007124149d51301c600c07a070b92081c0c82034072680e8070035801c1c070b200403071160007034007409c2c00f01c4000f0000601c40031203107100f070005006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 768531429 1250 768530179 768530197
    0x30e0309060d0b0d03020a05060601080408032a07030203030117060c190302041205060f180a0303050a090204050907290904020a0e28080604080304120210150513050c090402 76
    0xf84914107010541d4070300c1100f550b018441d0b00108480500c500d003882c200040100f0381414000120200404542e07683c003141d5002e140e0003000030001081d1b443c19400259503011108600340082107034000c25800000850685400c05858114000440c07200313559504120340c80c0491003001d00a9120701c0041325001c4681e090300b03041c05030501e0b86400410f252007a50580640d0503500020078000e0781c40b21100107941050032152107510309010a019030740e5031403c1100080400d603580d00010303016040c2d07901100f8000d50040c018030907810304c80c5c001c42ea1810180a210181400c50011440707011030350365180420f20707900704010b082c0f6680b401004001e400904040003070084503030045001d540c600c004051600401c02803411004101c130042c120501c040d0300042055030208003444082503205080c0c0e5400f640c01150040945503040040707080c00506070b12812414180501d80421030035214082042d21f00c00c2d192822031808036801c00d0181c070810b48000002990401909034035003013030780042020364 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 768532679 1250 768531429 768531431
    0x2130e1003031b21120e010515102c01080703020702030613020612041401061d0604050c0f030a02040e060d03080c0d0e15061503040317041406090c03060106030e0309060d 75
    0x10015040000d406000c3c0070000f0416100742c05002020710507090300506c100000c11941c030341861082c041c4000400701034802c008081040c6c210380d21a8150580d0030340c03d80c050009000c0c1100c42000c242c4c1d001c0c8501030125100d0400244013070302c03070700c241c9000c1c036001801030415456042240f1a90421204160b801c00001c00075040b0f04201c558034240182d00c10340d400e825642d00800d80a003119070603040124081d9180381e5402050300b010f81d640f904403404803030004560302c5040e0070803c284100101007002030004801c11428a1040d40074200700c0f0165402c2a2259458408220307901c102801d0041c0818010303030104018920304409008074181c01c8800258141151441070728200c0c1281d01d560180f01d04401f08011818138103071154125103050035144c11801c06035000341000c411754144038050001100010107210300030f4240040c00c086801918407a04000c040562946140103107075001e4404d4100009000f4840c1c42040c0680d5401e01c00b441c284054542004039a5122403e034031a05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 768533929 1250 768532679 768532703
    0x19090c05030105041511040e1b040503100c020c040e1c030b030f06160c03080c09060409090317010806010f0b030624031008060112080c1002130e1003031b 68
    0x3680707003445034901444c041e24140f41480382408014090300e49040c0c010f082800107002c02c201d070000c0045201d40045a1048c180802c01c0760f002881e0250003183d002070fa141c494003600813444011980301d061070181030f90036100540002c1007844250b403009400d4800541c004030480c050300980040060015080d450041003002510000900e404450a0a04015001482844500c44104004280b60041c0d414a01038106803901c0141c01404001d00c4c0c1001c00e000001d80c07008a0341d500e030454000e00340e8803604000c0d540c0c41d82401041a0341f2241d810032002c11000000c2014200001c049049921071102d682840d410700030201c50541016240a40103050b60f50003050040c2d42110384110001354102c000d441e0300e460012401e614401e03500114035078008100500400c0e4481083d10900b0f42c000e80305640c3e50110203020b601d440c808040b9007000c54404100c110a10350307a00d628204a541040403181d40c0d0b00c03140605d4200e421180320040200315001d410024101205034035a02c100d0103111001c0c44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 768535179 1250 768533929 768533939
    0x4060e0d020f12010c170f13170403030f081509010b09010507020405181e060c0a120510050109050105040b0a0c1401020301030b040c091529040f06030c050319090c 72
    0x9400081400020640d440c0c5c81c1038010168000b544e02055401c0148410a074140301007030b00f8aa40029126503140b10b4403001c07060600043d0261960400c403030411466549650b400c00070a40300325080488005038a100100380d0200c0c040c407040450340c07030003804860981d1910654203560360100d442e00781403000c2488000d001d2703a528415203110b54000c024400300003401407805d81c01c10340d4550900451011031b0b10300b581d40b0640041c91541c808440c0154030340d81d02d000d072420390b02450b0502c03c4210340c0d403c02c02004030170f602d00c1c00f041003102c42c01c0c1c0361203800c01d88880055689000b507010b07010742d85409200780c1007000d2007542100082401000c600d442840781c641700c10709a0740240c00503034030a80b03400300784020007244044000c010201c5940c20862100c0140e21000c9200c0c91340f040482c042d504080d040302e110126510403600f10b0340340d0071059680d079480c40b01559501c054400c2c0300c0030030701d004c0d132110016000302c08581c85643e000b6441c500b2450035040c42c40091000440540b401d660b40400858 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 768536429 1250 768535179 768535189
    0x60a140118080601060207050915091302130c1b030e04090c0f030506010e130203191e0b04020909030a05070327090509161d04050f030a110607030204060e0d020f 71
    0x702822264002d05504d60400703002070700d0030846074400c40c010b506100070451582c00704800a4003508084410482c9512910304003040c0b1510780c28007945c00786503c091000c841d03c969112419640c072548409403a50508101000480b40a113005401702d60080b030142c4562070140d1115800e80d02c0366000420868594002800c404002e0308201c1eaa07a00a200503c103490303d03940c00c03d030710509508400480c0c654a50100ba00c48805668103820390041d40b80420801071400c840030741c040e8081c070342480c00b05800d0170194042c50b000e54059025442c0f031401324032a002c001c02140c103120002d8072581d00c0e03e0441da03012581c05054000100901e41440b6260b945000000301c4c80001740088030740441d0f60700707140e59600c1c20410142859400e040364040c04109014800d40603503041d4100c0103c0c091142d03101d05009040c0381d4200d5030448240400100071600c10b41040d83c10140c41461030484000d5680c050b4254220f12032801583c002c00d50410b0544d10303518147e41107517080351000d010b1050054609000c90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 768537679 1250 768536429 768536477
    0x501050106090812181908010e0a29061201090b0c0702010f020f19080c032b0504020a050907180603231b071e0b1b03060a1401 56
    0x301c001100100700700300042041002c401040108401185843c51606804030a410b07000001d07405401140c18030716080e100007007140028820347c0c0003802120309203030900307440c0c18a0060440d08200c081400300f84481e01c2100e4a14a40c007640211092916500c00304000030500019102666481d58041c00000b5070f0b0160090240c441801000d4480003107200141000000041600465000480c001d20041c0b00081e02a0300e40103503c40004004400c0c1070800061181002c03140051000203070004c002c039020b080300c0840d81103090040507a00c0c0c89004e5070701900d0b403c0e140a03500010b0300c1d2080c4400d21f04050481c0d0800042d080015002d050416551000c2e003090b84004c000c2503039946060b00700354064000c0c4074060031002552100d4030700715032003000605061900314006070f40801c0c40410400c88034501c0f213a402ca80e41540d020a01c4074982045198822609559100500340341d8024485282007500c0c050348008002d050003504040044910b0400d224025040181034210382c0101045010a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 768538929 1250 768537679 768537689
    0x40303142203022d060306010504050306162006070e0a12051c180b0702150d020304020a050904031e09051c14030a0507060b03070306050901020304030e01020c011d060705010501 78
    0x140e00c45165004010b412050014241c1801d1800b26019485140c0781c8400004c9410132902d9035126180c3c540100e075140695000680c0500c01c0c1d400744103800c5140300010075034a0159550307043e44803800c2c14089403241141c2501005900140128a4003405007405c0d402c0108094507407001107644d20f0360740c01e0400c00004161026040030200f10342004454002410039441ea0910000071402c000c1c400840c402a4851140c1641001c038803201195101c05482900e1995407100c01d0304c588050140070000d42c801da50407441981e04440001d402c1c149080190300c902c1d09512a00660305007410004e401d85650f4980304100b181c021000f281d02e5803814001ea1001400202d401c2d15040185000340502000c210310ac84968800d016550000c2c0c2d0060481d0036459100a01007031017030400001c04d21b804540e40009114600b000c00300554030170705502942c800e900030740d110f0701510006030041e45c442d80c0d1726503000c1c00150b801c103004ea10400482e5205001c83c4019081034907002c915140c079421941c080e040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768540179 1250 768538929 768538987
    0x209060712170a090b150f12010905060108061005040b010807110a15020c012004060f021c03020c060604050f1506040e040f0c14030304090c120c1e0801050604030314 73
    0x4148140417040301590b0f4000f407464001c505507039900001a00c00c0209000183c411754101c420300d182c501c82908124900750f4084100c0ea1296110002251100412a2120040020304030002602d03e024002c0d4000740c40180c4a004040e20f80c0242255a10805104280c1d00e20503d4520000a60b00055014030004000e00c010707101c0e4481d0342a1400e4442c0c0413804201c0c1540e081080e507980c1c1800d401c440840344141884445103068800503410440540c0309605900821a80c1d541401c2c0c0540003084401210000e403990b035900c101c1000110b440685280001301c2e8041e0000d40100040301d80700380c07803c100508a41c101030781d40140c914002400c82d000c1781c1e01c5104820000812401003a180302078184a4182c40c1c0c606904000302c1d550b030246114424601d5250b031020032045016944a0801309103052081c4400e41044402400b04849940307000461511841204022482545540d06031440100310368580380c65a10110f440c00d280c1610206180002c00440c9201c06602c050300750340d8052819 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768541429 1250 768540179 768540191
    0x906040b091006090b0702060409020a090305070f0303030501080d081b0408011d28030c020117070315090c120905150a09150203060607030c03050f0a0801180209060712170a 76
    0x14010139520442e80143c64480062104d080145e80d140251016100031003001625014088021910104c0c06d91020341540181c0501080503041c0b50724803c1500c1c082d480c140080e07640d410b0700039510740c4203801040026201c54041081460344c0c04011018000440c0c0c042d041c00d4403031046600b114080346000010400c403024030349404c00c00344a900d40c0b42e81100150000d02080350740a43d054100010000c04000040c1e01744030440e801001c205000b17030b40d0140080000e280444016000780350300b41e0391340030844603824001000003042c01204032244c01a82d40c0c5200340c0d1407088140160000303010807a4103004510381040c490b100780c00110301c1003d426070045110030144c20b040600001c520030ba50480c5004100300700d03807a2104011a40119810304d040c1e095292141405c40c0c45001c1c14080400341e400004400302c503940c0c0700469906032110055040c0301102070351000c604a2051000c0c080d00041c0600c131800c04602d030603518000d5a032580c01c1c40c041d51034051420f2840b80310700f115082c03112070340c0300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768542679 1250 768541429 768541439
    0x915030f0f0307021e0102030a110115140a090e0706050304060b0d0c0f06030504081b01060b03070f1409030a081606060909060b0a0308041203020c060a09320906040b0910 75
    0x403141c07007244407401c0034510003403051317000039120311500224000740710a603032071454510720943c82151551004404090300e6512011002c200101c0b02c4062846120003040110310354059100d91505400c12a00404d2400e140c810142d0702a00014000c1e250251345802c40103550303c40c83c111605441c41940141c41e800d00f469405954041030343c1140e0101881d140030840040d600104030356034554076450891401c02034406560241000360006448114040148248a5041141c800c4e0441c031a44400340c0d00d000301c1e0844000e501800d04443e41c550700c10304440740850108401000090203a481248000d0300f1038581c1001c1d05d1b005d50003108427582d991484000c1c041c2c5807081079012401114800d828500d5501d40c80c0d0340d4000c0b4054887c0602452403141e041600030000006130000261105072290740e958800303050810b003840364001010281100e102c07a115015003400d0b510350f41100b441d14101c8114180102440c0040204c0c2c1c00c16039602c40600d455030780e003202c248202c2c0034403803a0007828100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768543929 1250 768542679 768542689
    0x11040e090304050102071406190525151d06090d1b020a0506180d14070602062202061b0705040c0513031b05090a0504030e0109050915030f0f030702 65
    0xc10103010340d00280018810b6a9010400e8012030301c840300a0780c02001d07071000150880c4204c03001441c00c0c034031003e582040250080c1c040c12400042501c10a5102606c80003222400c41658000b000700740b100d076200e020003100f54401c00240907920811a49180901201861310406544034200f90344601e44020350103078031815501c441606614850702600c090340c0400c403181540c1c00303121b10413803012440f5040300740000700010708940014aa9021071900c2d050600641041001203842c40c000c00402054803800090b0160040b045640e41900074034007a0002a20710910039000c90f03029004000100c00c0401c46d40d07007034803244c07680300281c201c5a261408000403581c2d044a0102805018405400b00d07842c1c10000804a81d000305030300d6003c981000c001e0b0907001841d048507521003000310502031f148482c0c2d4856441544a80c940001019020006440b01492403003519030005450001a44410100081c442481e001070111042a8460800e0301d00745010011110407907070012851100790b01e01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768545179 1250 768543929 768543931
    0x3020a0b0601110c041109040f02040911031b07080405040c03020c01050609060607200d03020a0611030c0927070c03080c120c0708040807090504061a010203190507020411040e 77
    0x1c2400c081d201001c0100d45240c45060100d062440307540d0f10000d02080d1400d18088400303105000340200b00c3c0442c4120b501000390454010f22204a1502e002e5824031800c00044034090304241044c5076401c814402e481140d079001d41801c594504043c800003c09403200e018621036080b0907207000d6110031907140e49900b1a0002070409114400c0b001c180003060300d841c005c9404180e000304451030003100c0c0c075400c62030441484180580144010404a060540c08108200494850301d42441504506621025a0b0105a62103001d0420422000210703140a0180441e01080303580c0140500e4988c6a01410300001180e818000c5400511000c04040d44199445c1c0d200000c0003074903041507501d4840612640000780310358090704000407800e040c007800806442c01800340c0c1c01100d124a86072a014070150405940c1150300c2410491805081a010070040b4a110010b034000e5060504810345154054051407082c828801c0c01c208480243c0c403036010b2a1000081303a40b0a540d00c62030b2041d14124008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768546429 1250 768545179 768545191
    0xa1b03050d0f140c01060e0726090c220603060e011410030b0c1b1c1d060904090507090c140a02071401111902041a01020601170708030703020a0b 64
    0x310050316102058102080c1c40c03015441d00f0f2a0743d110034070303440040c3c0101025040030496580040400204550000c014480304e1001039245a04a15104102c0080c40c400d813401d4042d60040303500d8241e1402c102001d01c40182054072a04e003001c4051480004480c81a042594400d803140c4c42c0300042c1c071090003a441000054420880546060b031042c00c1802401d0000074803600d03140d00032070000344046081d501c1681d03070b40504c0b00d0a00703040305520355201805000c8022906176040104c0002d400b4184107070604602d1000105200e4030901008a0f0341c0c0400c000320f07406981c480c60100806c404229140290480c0395000504c0480b5000183c404049407030302000b014020440d6810495002c00c0e50340841d070300480310752404e0b500340005131121074440003c48842c0c440c112030900c540342e010010451103402501c007007043c0e9600301344072141c14400e460901d016a001000411203145160200f00f00d070030309070003074a6259403203100660640d400464141e00603407042c01c07000d00340940c400069401203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768547679 1250 768546429 768546437
    0x30f07111c1e0308010504020304050309090c04060e0a06020a0303150f09020d05100f0e06040b0612061216060c060605061912150608060d052d010e1e0a1b03050d 71
    0x42e50350000c10060050103214010703900440414100103040064401d50000180881c0207450400c00c5c008441c0c21030300c40d82c0000f46140d01c000d082420b00030740000c1a00c000e80d028101040b603a442c181d001d801e070703291410020031842000040451040503140c01401c12070278050b03a20542800e807282a203202502d4840c40051640040085060542c004402c45400c4011035006607a6880098020410700b2192a0040070000302c0183c401c007441c1905101d460101c995252072504107581e16540c91a803804203188030f42c0c481d014050300e40154a2400481d2007040f01066050b156004141c950708415a580f1200040c00487e480060f000095020b4414a120f0304000561940d40581c241c0c440520580b4140248400413130b03140d4441e41904520b460700700c012145c4081d40925241410484852a0340d016948e4280c0e072420700006003e000c00c05031044008212000b41c200c1011310074442c2000b881050701c104d0f84804001001c1c0080f03024250031b074501e042e05007440c5007046800c100344200210100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768548929 1250 768547679 768547733
    0x70c12030e161413060902120103140f0624030a05160803070c03111207180b06070b0402091305100903110307120503060402040e041506080708030f07111c 68
    0x4046046420f4080004494940e1010070390340426008101640004810b00d00000714007240541200754a412207200d0000003020590a901481c3c40d00d021616442031608650041010201410301c070000c2202089052542280700c1d00010b49042071400d401c5409803c05e10000c1500400f50700540000c00c8004050362505805a41d10b40060350a40401072110b40540c17510a41ca480e050703120400910008112080f1076180c00b841c5480141d0175000007006810f000e0081d010b800c0110a94000e00d47c006111030b05a01c03540e00304101504000e041c04144e4030030343d00e400f001c81c10400144504140c50080028400001c0c01c1c000c05654a005100384035034410400c0000240240382130301d140d4449494031540301e4881c0320004003e03208a0380300c03150081180003403105001030104001061000c118040180f15905e440260f1900d00510817451315400a00590f0303464038802d001850350354810b580600c032190481001420a0000b080c240206218100044040184503e40c4000d25000c3d6103c074030340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768550179 1250 768548929 768548939
    0x12a050f0607090b1e210c07051f1b0c0507120503031f05030d0203180406062a060c1107060813030e030709091a0f0705070b070c12030e16 61
    0x112076a1085a101c0c0200003200c0100702c5181500521031510071000c59a1001100394540386c1c1d2414080100c9100480c1c0c0c041500c031600c090480350359682c40809481110f82100401300251f03408075110700b110782c8a4040000391030003404d00e00e80703054964954091100060070700d1890200d49400c011925040d03441c0400114400009681e4000041140c02042c8210000500341d07400265000b0b54142c4140305e50340000907004009800590045411012000300400802041d6003a511604001c24131103400c4142203d0688850260121042d044405417001681d401007107903d624180000540f170001d0343c0141c841c042c004400102201e240481050601466030183c501c0c41480040500841015450b0b242c0c0b014030105000b403214817010400310b0400d0500308240d030f00d0316a0000150304203000103801c0303440607100d42c0e0250003165501c40c2000c840d070340c46105003030015100f4002d000980c8030b4000054240e980042ca82c8216030703808611418003040740ca1808a010034150208000d2240600c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768551429 1250 768550179 768550187
    0xc0d030c08150a03081809160903021507080301030606230a121703180d02070305070b07020301021b101401051305041b060203041403031215012a050f0607 68
    0x28002d49002104140320458000054560803168002401e4001c00b00d80c860407100016030b01031110201303a5010805545400da01a09044200650740209021501c2440035003420040d40c84820314041c10545080300c0d580310f880300d542007688201c0318180c48190034814540c801080c940c0b1882c45c21280c60003150603d000450750903240c0914080c6049180502c024841c8510303401e00207044807244140e50b0705200760002c0880e40c0202c0140c80340d02c03803440740000061000904d14120f940100240409908200c80e02e01c866104403004d0b41c0c10b6400740410040c208003d405141000620001808046030745800a42030b1001601c4a20a42c400400100466103507419012107110a01d1000181550346d89000803411450814403280f02030014008607903a40c0000003082520948140f502886154008041d80c078407031500c04080d00f800c80d00c04540d040003815907040d0740f502d050400e01542c4100c000b4103800382101c0c40710080b004c41144541c400b441418041400c3c2452070f01c003c1c0c103080c038103c440a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768552679 1250 768551429 768551431
    0xf05030f01090b1c050109030e0a0f0b18060313031407080904020d0e0601080304030201080a0506010f030b0121050a0e1c0c021f030e1015121a0c0c0d030c08 69
    0x318054541c0c0a0310015610318020000c04c00d81d4031a4426000c01905100740200600002140800c100c603a0742000e52400c4682e41044840302c1d4001c40c44542020b0403d14260002c142c1a11014000c0c45080d00700c2d6545400355119a01c51880300384130986030301300241210054000e01c2500c181c00c002901c00f28a0007022900b01d00020b0b200542d0716a42512504003c101c410804580d60013400004207100c200840148110ba0013680d901815440b01c86001003107a1040d00d9440c0400c400016400040e80a600503003681c00c4141415206800745c106a6044c8010751458000c83d250b80c1c5082203004510341c424031007144684d0b401070003060081c000d03400b007948403040d918081c042d096080760115603916422143d254118100320500b040f81c0240030700030784186c130789083c90b900401d4029641c04c00c2d18401c8501e01c10707031500c1c6800024541050280c00c00700302241641c10b0340c3c8070381550410950030403815002c0c000c2995140d42e100b290301110360a10388502e0300320007050b0401403c000d40c03580c88a109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768553929 1250 768552679 768552689
    0x11150d15182f0a18051002100510050109060c06200a09080706020d11070918050c09040b0604090318060903020913020603010e06010c02040c11160e04030f2c010f05030f01 75
    0x9038065404130b821500007025034046540700303900382c10382c2e9401d541c04683c0661103040c2100c1030101d40c9414230134080741d170550301a06000640d449001c0101c0f902c00c10410321882d00a00000400d5880e60302507a140791040007100e00c17108000034000c2c414540c0218000b000b054040040c0042a041c000002d440d0902c443c120800c0010380a0103138080002403007030300000d0140b03140c1044a64a400940c4036040007106050f56036002e103880ca100f10f0704065503000e2050750b008110f0380710750341d0b4281040300078050302d11306504111420b92020401d01441c00e26a000d40b5003074981e500d00a1540c4100700d94168020b02800a4030030b01c808480050300c41c00c0503a415611805401c1d2041d43d915070040318103515896019611a08002da84030500f40c0003c2d0380c040034940c0354199000e00c0200c440c02c2da07910744548980b95481201400141c04681714040c28140700d01c40c1d01e08080800c580520130070714140514502c00c0b405800d00044139580da081402e040b50142141403403415860420f45500c2c0c1c4100520030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768555179 1250 768553929 768553937
    0xd03111911060406060612021c0c1b050a02030706020f031c0b1309021c080904020c12041806050d050c09040204111611150d15182f0a 59
    0x1402000502800566814071000012038509280c1401c00ea80584024420880031504d840741000603080c1034002c9501d503068803042100d6000e85100c4820003462030681241c00c01100038400c060300503502000f2814640181c0060407003105500405050007040c1e171110007503501032084900c01d0300021090342d40700d45041300d0001020070540400300140003090f09503035002c001012030f5422840181d1049200d00d000755200380c1d00100d800e842c400404101503010b0520002030086414901d0300340c00516103054040706843d10749114090116154000390880e00170401c01a0a400354035101c0d118a10041a04540c0d2003203080c0036803580d175201d0010911241c001c4600724001070964a840d0030140c0d450b401c00c4040c0751f841c1104900740e000002640c030300300c4000c4c0d943e488074031840ca80402c0d89100c0c05020201c0905d06222024180700410381610b82d0000c102d0311500003c0c7c0b00c205003484500c164025000850042d210b03200c600b811041d400002928010dc9418851108a0003019503483e4011420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768556429 1250 768555179 768555217
    0x30108012a1101061d180d020703060207150204082b080106030f2904181106030907090906050403080601090f1703070501020f0a08071b06050c0c06180d0311 69
    0x1c5a01d01604c1039800407100300c0d0400d8010300b05690740e41c0d80180b02c2d800c4000d48034646c07100103580caa2940e54907840e14005034072920050000c6400c80c1c4c010802030703200c0e1180c1076405901100307110503600184e00440c1c60781c11150026a0407020000b02e48240c5e80100a00c4102c0c061650000d010800180501ba00b0140c2d640d0005520a84991001c8020583c2052080c1000d41c21002e22456200d0141e280e405035042060368400d684503e85504071146d488601c503050080043c003071060a400040020002d031007501c00014013581e480c850009068016031011600f8541824068049a80901014100850504200716a42e80ea051010036203070440c55014019501550030382c80c6000d014400f8005501c0011844844101900107121482a40e107501141d07130345034a0166220000e801441c07603400031400d03409001503802d9002580c00b561803030645040100103400c0d249080001c4682080d290552400f011030034900f0049094102400e1405000c100d6001c4420311240c09556000c2000c922141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768557679 1250 768556429 768556457
    0xb07021302070516030c0f08030f03010308340605070e010f183c0b040e060a09090c05031b0102100903050f121b0703022e090305030108012a 62
    0x800716030044c5007160078244020341c0b40c1c00c000840b48071078410f01030400c007200300c001400354000c4185c4010711504a4094190781c61a16056038a41c00412178003550386418201c1980600c401035980c01c65840d050307003000e0041d20f510744103080f15009050941071000f20a401015aa4032444840560b026890940c255012078070b00c08100c40c101d9046048403a80141412001d18512554611802c84840c40101414481401107a40c103005001d081030b00042013106000580d940c002082c0c00c594040c1c035a0305180d650f0400340c3e081702c00140d03003110300000c102001c2005160400449840700281c144420b100000d010010f5076440400020800f0700740c0303c504040a1501490a80b0000140058910350780c203100030a0700002c01c81120084001070155042504995000041e1841c440c3d040c2c0091000c904507800520140c0074594071510746407841d00c1403181c1400c0501620600c07134440d881d0703561654100340700c0c5400e50b802081801c0110040000070f01ca0721005580382070b4501042c0c2401c1007159015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768558929 1250 768557679 768557683
    0x1303180b0a0806130b0612100e070e03010e010506011b1a090a0501060b36040204090923070315110a2d020d12141f0b070213020705 58
    0x56100c4040c40d04081444070050350805800c6101c3c1c41e080360300901405403404240112503404a1031500310f042880414550700001d071010380c2021000c0c0b00042c81c9943ca40303118450100c1107400f4030020382d00300c2100c40223080034040d00d204250040e00034003551401900081c0b1030070880d00081c02000914160b503040c0640d4106204499000f41c1868400b4078059403000d0340c0b49600c00701125658a0010300040281181003681c82e002c440342850041c150030440c00e440031410440f08004500b002c00a007206658840c030003403004104480700410280c205050105041c4d481d0300300c0300030003c04110307120740716100401c904041c0c0754028240b40131200ba03244c038000104043e48903101d1342000003031400c3d42c00750030074100c400c1081d00303200d502c0c403107081c18811611241d01c1c0b010f100d015a01c854104d4104500400d030b18110060b4907040041d1000590403400580c10040e601c00300d05851400e82058620692880d240142070100c0d14189000310960105054588551103002419808140301e000c010007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768560179 1250 768558929 768558977
    0x1e060607060905150610030603030c0b182a0409171c09080702120109020a050114070614060109080d050a1803060e1b030705031b040207210e04051303 66
    0x484200c84c0c0ca400d2800204050a0042e01c0345171043c0860340c4007400081c0300740560410317a40c0c965680305415071640e5501e4000ca20241a00004019407403c20380400401c06c040c0440a030285915040c59000c0f00c8007806104012003030601031401d16080b40080b5030741d4501c130942508800b000980c1c50859440b1041c4c00b00340032807012041802c0c402c031401070098220150084d5402146c000c40f68802070200300742200d41c1034000a402c441c40e8002080703998050fa200c415010816211140307024000d6480f80e089030410716040c0001d00e86002400b000d568041a10009000003000601c0c04221040c2d000d440ca000700b0f0301c10700812584101b10004c01003031842d220005d507841101480050300c0c008401e5200c10b80107080c20591642002841200d2170001810003c8500117409005a0401d070403503170743c3e1045c5c1c0320240c0b90080d030200b05400c0001e1990015010700d40c1031105900b0744810400009040681d03917141248140e0402c000e0024458030442c213142115410f0401499103100d006160a84c2c041d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768561429 1250 768560179 768560183
    0xe0c0a110607031a04180f050f0a030504140a0605040b090316090f0f0203100e040228030b0603070f09052503060e090111040b070c08071206051e0606070609 69
    0xa200107100b1940c1d0950808040100b0b81004501069044000d010445486e003100488211040c034044c070200d4900c807031a982080c01182078540115902000c00d01d0900707002e2088002420014041180b038907101d0400c800f02c00c00700d9200070a5498614014002d00840c022508105800690450290350412880b0842050340c4203050301d0320355850803c1d00920318107828010f000c1c104440455154260300c2141c0c400d489400d02418018104102d0440392000200100d0300000420f040503c089560031181c480942142001301300a419031400c807020850142005009610a81040c00700c141c685090030107840500d400000d096031038801803800340c00c00403440306490030380c607038212a440d81c16041081900d003840400c00003a11254081400c0315110051301d255000280000d02c0000f0740300300200007080c003509001e8203803606c070300342c1c0303420f009140c0c1c820510708070102048410000c02c0d000d035a50107001181c4c107c1426078040c418090710440209128810180000c2d482e0401c00e8603440b03503008039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768562679 1250 768561429 768561433
    0xd061a0d11090906060c150a0203011403060c18010201090f061e0207081603020309040903050d0e1903030203130c080c09060103020702091915090e011413060213051305070e01090e0c0a11 82
    0x818a1841239009500a024132040d060140c82501c404d8140000e0f801c2c0a00241048140341200e0b00c010020a8200c0ca181c031811035486141d0000032455200c1d0002c58140200400240d50a10071100341c0e00d01d440041c450302150041c48034401107a881340c145c903181003150400c12010629407a0403400d5104038103e01e64070600e000100018148d005015001c0603210b1402000901d115266282c1d80e0085480100300614858010300c0c0002c1c400e4002d10380040100380e6440d00704032030b039580e4000a10a5000749856903c001a00200ca213805100540c100c402801c04600d8400703142c02140f000240203003800d4910a84032151b17010310200e503004a000c1c44840f001c04110507102c25003503003d80054100800ea41d03080c44401c1010560b1151840e0060303640784080000042c5503920300010f900f00130844010641d07240ca0000701c64540280e10009070400d500700044601e00800e0181a40080582d61410001030103028041c00c80360b0903d098020702d580101603281d003811041107500440c8544030907918 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768563929 1250 768562679 768562681
    0x9050d020a090212010504060b0c06150136060e090f07140c1b0105270607020405040620030c120408090a080303040b0a0c0f050d061a0d11090906060c15 67
    0x500711395845281a94400c07035041c48400c2e40c4003c03c80840c01a620014802d400c84400b050304003580400100d0845410305007608004004801c4060010b20128450908986040103000ca0034940c0000405010241001781b510003080c400b2a09001000b044440c1c02081c2401180600c0d02426280300c220501079030542d983c400f030b038103007540341e070080c40950715501414881950700350b0195054032404201d400900e03030452140c07039403960b01440050903203130032420410a170005601c650080e94403c030300448005c100392100007040102c4010003d070700750724000d05200380000c0311390210407156540d2040d203110300300d81c0b44ca041100f080d209600725154494185100050030210100c061442070340503070300350711199a407002c0700300540707481030040350001d00c840880007091406080034080054044000084403510703030ba907119042c4000441400390940110f41d000e40c284650103a0f940310705410100d03904104801300480c440c0c000190a00d0b00c2100041103110b01c825040004900d602c0c4640844603403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768565179 1250 768563929 768563947
    0x80304020114040b090102010e031206150706020d1a0307050a1202010e0604030c031203050403020d0809100f0b041a0d2904030c0309080a050a170d0203181c09050d020a0902 76
    0x70751740c40034400714050750800c104940381034000300a561020724414000391195841d0010042005d03402559224102030900841f004101148040c0a42c450060030002c0c2d140300354030001c0503d070301e0550f80300d229a0100310305002c10b0300ea00400d0000c40d0380149242051a29034801680c001101d0034500e50442d070085000014030010461000450b8000c14440f400f0078010907044003614000ca0300a800350f0300c8040700402d6030b40300d0303a1010350025030f00341034412584c04409141c1c1500c051260400442e0b483d4440781c1c0907031402e8880c1c0981140280c420281506004020036091088200d0180070306615018914a481c2001a00503040036401c10070032180c503140c0f90141070303410040b00950000340540700110b14224009501070f0102d0f00140140581540f07031341c0d10ba0007920200f035281c003400e109006040040c0d078240080c1d0f0003254641c180d810100e10840c003841c5001d1903034400808040f000c1074403189036604012194152030050300d0059140b2624001301c0d89689035a404040d20303034400a000c0742 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768566429 1250 768565179 768565199
    0x280c030f0912060603033209010e0301052503060305070e060a0305060a060311151603020115121a070f0c021903030e040e0f030a080a11070c030b0a0c0c08030402011404 74
    0x4c1aa4840c1d280c8001c0c0e003000203440007040074a203885c1c0d05104849801ca8580106000280c01d20100516210100300310b00c5022a00390350050301c40a840515240f22040c100c441c0b19555041e03200c080c41d0800405165440380e035510080d51052403041141c10003c1456500c50032400e902070368100b412201c1c0303418503810090040035248015603042040b81e050305160301c0c0161100c050b8a512540e00d0341442d05000182c144181c8080045043d59a103030b002783c0000003525500c0c2c0042c0f89403e040d03c41e0b850304d400c0854140741c10748000b149610346130003002a555085500c18501181c0340c58007001ea814584003142010082d039240281c00280c4000000c00c1583c001d4508000c3e007421b55050108500110602c1d42c0c07074401c0a1982044d40050000710416803050800e540d10a40408004c600c1c1107881682444503400000180c0703680b180600c0600c00d01040d48070302500900984410400c034440c030311005004503100c0c42c008000c2180003003ca029a0711a1105031010f81040703030240c0d07403659501d41c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768567679 1250 768566429 768566441
    0xc04080f0318010c03080c090f040f09051912081803040f1502120405010c051006080c0a08150408030703020c1c030b010518061b01020f280c030f091206 67
    0x34400511100c0194003d5102c0c8401c51074950b859103913204282c451618070072254100c00c850742d40103c40395404800542d01c0d401104500500510b00003040b10342410000c2c10008000b1010980002190030900080c4450030000300c40000e51800c0130317031502c50700c48011101c24413102c016803502c408a0089400d503400b00c000c004688018140900f81c0d0004001640c0b103d030342800604a01030f0600003040194042c000d40b10a152195055a0020303244c2c1c0015011200d45401902d0140e009214005240c24205019006000c11100a01c4400d02d80c00115140d0724004000a180c160048041001c55000b43c060f6160a4010700541d50040115078016514100e04101c09000a09000344038007a5401141115160124807078040d10301590241404810340c08441d0b503000320503104d406031240344003c1c0701034034414980380200b135580d84030344002e68070501e0a00b0751031408154944403204e403141c03c10541c00c280c60389800e2852070380b0700c1c007031341900c81c04110b45c001070280c680c0034905000c002d01c0c6d9000d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768568929 1250 768567679 768567697
    0x40809011b030e011e020c040209030c031b04050c0c060112021305090607020601141315081f0c031b0c11030d020a0b07030c0c0803090a02151801050c0709050c04080f03 74
    0x1e58100402c5c0e0280403509812007807900258004c00c03655245802c1c1030b0028096414050212410151020046441c0603034141d40a042504801c102c00307118a490b00550b46c101e030305c2141c024180142d9807001a291801071181101c075042c002c0c02e9000719150010008a16042d0750010442c52408090b8903884440850700c0c040103000f604c0012901000c0c80902d024180c00181c01e0640605007407603070b90000e00440305100d9101485c2e2800107403444003000040d6581d2520009118500c2e0065006d0003680e481d0070302041803604110702000c64601e898145a8070f008a46814000d8220030b0400140a05d04070300ba280d0540101e08041c0c003400d03000900d0401e418031451000e503050b51000c108804444a1000c440e00044400c1d40c40004a941080a182c101c680c0105842c460041030740022003050600d440c108c04520041804d001c00d5040c0c0e040460781c00d4080c28441d103064869000c03140c1300e4605010341c940c80f680e1030f4049038a248080007030764044c1007010700703c820075038480c00c025039031360414420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768570179 1250 768568929 768568937
    0xb040b0c1602060912010216061103040b13020a0b04120b0f070915050f0a0e28180f020c07300b0903190f0e0f0306040809011b030e01 59
    0xc2403152002104441c090103400181c24001109503080050f40d90011060f6a80241a00f0300000182402e20080071400480700032926810091f15100b070035210000604001d08206008110114544c0c1ca1100d03400032200183d031039081614070009014001d250018107070000080f40204800c1c1c1e1031609169001d0058042c05c0550f80c54500c40340c0e0401e002c03240300d0005800350004002910f280b180c03807506807013103050036401c03e00b8403a040301d401d4200880c0100043c0d446107030344001e410001c010303ca4400a003440c0d103015080304448000070700f48c584078a031500310402820b400c8400f030b181e021000e0b80300f044000707554400c0c00c58449540c078030281c01885100e1550f07000c1110111020028400e00c807000d89110440100aa00d4007540311800800b058035a010030480e40c000303132006114600101040f5140d0001c06080940000c141ea00c800407014000e0702d040c80000c003107a8002a50ba944143d2290115070360340000c00c0104c0d9001d50a84020f50b801841c039810381c00709a00441500c411000030390b9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768571429 1250 768570179 768570181
    0xa09083606090303071403040806100608070809070324110304060b010c120c060e0d180609030c050d02041103090f0c0f09060904030e1302090a08070f06080703090f0b040b 75
    0x801c00640d071041c00e003220383c582d1003040004001003081c1c481c02e13058140034041d070342041d03600c107525400d10720304481505c00a031201c5400c3c0b00c070f55000314200e60800e249203010401d91500c00b00041d569202804050315100807c480801200302c4c0760104503a8074200c6c0e00c18880c41020000f03030911500141c50845000707040041401080d40305215031040c1640010340341810340003281081e80c29903002d0100703070380c1c8548800d40c00c1d03c2c01904106810421800b980c40201c1c18184050401085045400075800c00084000c10400700713160381482c2084d41c1c400c8510500c030540d9840010010001201600d040440110801072404004111b100500c221901501c047d00010001c00003180c86c00401c1c180d108018030082841030611641c19640716100e41000c00c29241054009120340c5c0a50802c541c0f450b07000105101c50b828091003030320080c11000d000f401c20b0b5080c0701403107640d50034502400301000700b4040010703420307403103500007908507600200d441c903d1802d0703070030003203036000e0215010b64038840782c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768572679 1250 768571429 768571537
    0xc0d0e0a0905090d0e0a030c060806031605030d11010b0a0b0705070501020313180b040f02070302010e0a0b0103080c0307080d0207030e0a50180408030a0908 69
    0x8042c0921586020700130b41124194804141c0e40c00303030100c44d9140c20141200c00400050044012000a41000e4458416914040c3c0405242107149a0041419400048108501c1e00c0000b9000038446030b5081500280a4510310075004150680b08a0703400303d0010400650808030324018074415004006a4051035112401681d482c410300c02e000313503031514011040081040150440f4483d4071083c0c03011690f0ba1900000400b50ba406441c0e4900c10b940c000381120800d6024410403600004e00400341c081d040c0c0948455200d9141407101a143d000001181d9100310014000c40d01480e62041c60f00d501c2c1e11811b04e8100094201c0702041307010510303001454a05140a10000040b41c0100307075070361000900c049210f110140680a8404826a070143d42d25038100e62380148260000f40c0c00540d030754a80c54004114a4143c9104100c1171006d41e9024032011031001e2046942c803280c0d44401007520364141c0341840c00c507ca040790100090314020b080d000803d031441e081043c80360f00c000b01c01041c18444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768573929 1250 768572679 768572681
    0xa0c060926090a05040e03070f0b09011503050c010c0507030c0f06030e030c1f0b06030901150b03040c0504090c0905091501060207050a0e06010e12010e0d050901080f06060c0d0e0a09 80
    0x754190b40d4030040c000c104120130f01d4160041518120070809803410074000d50b80d1081c1c28034903c2c004a80c5502d5020412200c408240300c1c2c8040500701c10390203603980b40785899840d180d079002e442880c10081c11403084010701c00c00304041c80c01182d02100351546259076410014006200c0d0290a0000741420860341c03401c9000400e0310601160a07003c0c00c024160310034031402045296409036452516149904215501c81024520401040700045800300d030b55a02940d4850454004001d8607005009000c0070429103001762003918000d4800280401c194249800c03841225402140c06c0790402d01085440d45001c50038071001c111070382c407010040e40c031000c05a8659405010b041c0c1c001e00c2c840001c00140139000c4c1c000d5003000060400b00d40003400c0001149007a82220001c0c03000b0380d121040040c0c14401089011b45002c810f10b0418100840040001c280000203403142c10070a1803400410700941e00c000882c0c0c504403c2c3c0c0304a0383e10050b14200035140c4908605414440d64405078001688801c2d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768575179 1250 768573929 768573937
    0xc06050a0501060e040f0b1e040b061e0313080708070c14030d1b0c060c0b01061707111e1513030806010804031202070b0f1018020a0c060926 62
    0x40c030b80f07460581d0844d0406000c000d22900d562000c0b50380d1124200351041c2c07607a50030301603c5607883c080115101c8402d01804182c0310424015402050100010040070064003141c1a14100032400075690307031982d04129213072840300385000e000340800040d40c900f001042c800400c0d81c64400c105034000b003035440c00c1900010345500710203501a0052102004410b10070301d1641c80b03c07000c08600e04112081d68548405407c0a40c004070b0216014240d404203201400f00704c1401010989460a00a100c0d003000d031188010107010300007402410544031190420502100c101c1d0300c0a140180e01d11840d0506195451143d00e5a0310340c1c1140c90130118180c140c1020041a0440c1c140d110301889848080044540b428024070980402c80f807078804500404880c001040050b0040300407894030f04100300c503001e01d0a40a8545030118120080810801081038040c480d02e44030f40b0f50060b128212240103507124804c160008040e14070b428485010007114a10301c80501e035000704088005042d8072084006407007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768576429 1250 768575179 768575189
    0x1050106021c09080a05010c20210904140105041d07050f0604090603080301061b0c15210507030e16031509050114041502040b040b1b0d0c06050a0501 66
    0x10628030b04010b5218901d012000c0818980014010350710310f5251308069100a04035210794680010018280c2d12058150066040329140544e805010320f2499030380f0845c03a1403520016041d0a02c401e000d820001343da05292010b0010b0051205000744605008401d001c7c03e882640380042c10400510020401201c002c0c2140040035106d00380800c00000318009030103207500c801c0c10000461104030500078400103520440d9241d440c0d50510342c020b8450300140710100503001c510612a00071a0302d600e8020101d4400c1254038071100318030501251040c007801d0700728644010b445032080036500d003a0f02c00e5119007416981042000340040d0844c1c1c6400c11040382c00340c200c0b000700b000d0000c03402c011084a040ca0740f8080c00200e4099599500d801c0d0b5a8180d1310808038400c2d00108002c1c0401d021000b01074802c0c100045140505202d50079440340503034001c03c1690a004280280d4403503180100c40604007211048031894030b103008000345000e00d1070004844203420040420403940c010301460f07040e14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768577679 1250 768576429 768576433
    0x40e04020915030a0c050102070e07050318100207050606041401050310020313060905160b03090718060306020408061b121801090605070e030f030c07030f030e030607090e090105010602 81
    0x24445030200540600007412894150901c401d01c0091035408003d103852445c419007003800401e00d80350019003840740075800303081c1250104e010420100d6110003100d5200b45800301c400f10341001c034294146440151a0545425071001443d0b4050040020380b2500c02c0408a0b8240805c0383c0101240c200800f00b8401c4c2074060744001c0041092000c160003841d804414001024240030b2180c99580c15140c2400040c0e5094101c0b00304454a000800110b030041c19421010b24914200480c80a540f59200d100c2d440450740480c8148042c45000e802003c01540c0100080d9200d9894840c22505c2d04001d4400c400d50945101203100854111000d0729a1140d0150146455507120b0318084000070f20302c00e001c006556074031624000507549102e002e000740c03515078865a00c64900414185001503c403055490399000f4015050b06ca40b0001d88017054071344c401c01c00d4000c940e040c60251410b41003440030aa00d80124030070001e11551203150301e4100c2d1880c004140316a216003415900b214000c2c01820016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768578929 1250 768577679 768577681
    0xa03020d0c110a090606030b0312090118050631080c100c0c080606120601081c0c06050916090209010903060b0f0637020703122015010803040e 63
    0x1450007903580880290003080a00c0c09401004000b441050301038000942c110303500c10090144a915124200a001042c0d00801da9084050182c3d0054040d008c04941000f014482e1501340c0070030000d81c032006040103005551500079912040880541c9010412450410f00d034440c80707070401c040c402a00b210401409400c040c0d89420522126440712001c000c1845845904113001401660141d8020107002000d03041d01d04010f001c001c64605251107031241c90380604018040e41c140803944041580000d007049040e0b00080409440c1701110301009803c035840c00e0104075107200003140024003494114442100305460311004412401006c403070a00040d090340051000078402d83c030130350030980c00030b00200c1845004000580705034045940301304400102c11004814068202850110700f2015150441000110030000c1d80c0e40030700e1002904241459000c0c6940324050212596000443e0582c41c184514802c020f81d99030f03520320503405030140c200000240d1040080159016114808004401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768580179 1250 768578929 768578953
    0x8030106080c1614300d0b030303130203070b070506060f130c0c02040509010902180c090a060e01020d09050a03020d112106160c02120c1504090e0a0302 67
    0x100000040c910402d101d81040300f00780b5403054001e00000e42d8842c403d00340e85a104070310b00508000c0b1107001e14140f0b0102840c0e168120840c03031031445107034920000351078803036510880c3c0e0005420500c0760a501400000b09024122151520380c0e41224005d0341100d00881c2e545070501151720030b0f444050919003000c4081681d84c98103100d40b08016000070009800b8034240c666131811100031016120100d1400c40c0d8140450816015a991200d0010b00070860034481d600450206003007502080c04030402d01002801174a54841554002c0a014000060107519030030f001d400b407040821024050321400780340c10075503442584502d041e07035030203000600e20344e1541d8280400b0000400f411030320542041c0329003005840b051140c8003841030240e44200303401c51180701903040c54809062602480348521010346080d8120581001c100d0b8150380b4282241c00f95003100382007801c8041002d901010301c6d00400324000c10900a0001d9070f40c0188100260500d10703400555480a045004002d48c04c60365407151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768581429 1250 768580179 768580187
    0x41230050a0c050f011a0906180c070303060803030403050703030b040b1507050304090c021c03020702150d202a0d052a011d0129040b190302011b08030106 68
    0x82d140f00720304a4152003200840e02c0d0a49031182c01c0340c210320700008010300e001c2c5029400c003074109034165602820340c109501c2040d02d90701c0042c006c0043c05000141903080501c40c0c1c0c0000300800481042c0c0e6128205480c0040080d4480030b01940003e0030050300c1c92113441c0600c07512801c0da00003000040c1110a039030301c81280b504400e0080d1094001031200003084080307030003543c4081e610b59016081000103034041e0744092650800400805106222141c0180c480c0d07400c0c417900ea1409103a460302d5003100d8401c2c1001c1c00035504801200d00101c200110902c5030307407001d012200940102c0030343c0d40b00e0401d00210084e50428000200798484a8000913950082000b0040d848051120401e401c1503c13143c2200d0b554090201c1c00c403690f4586800c0b043c0040e5101003102e0068840091005d00061003280c02c00b242c880005101141c3d444509184c03550f1143d0100d050004003070241602c01660b000b40c1da00003503051100360b012400e881d50803888110581000310b08182c0c42100182543d00b0064129 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768582679 1250 768581429 768581447
    0x9100e180118050609060c030c0f1b0a14010c051b031306080a06090e0d0e01050d2c06090604060507020106030c290307050702010c02030102041230050a 67
    0x4460060326241041a0203010784815241c14042c800c10652031443d129191000080005c8025044402400001c8003820102c0f90810790206603642c48a400784251a0b062040c03103828030041003490100700c414103022603040407981c01560300d00d0b1800030906889007a1035007403865200141e006c0020f070417401d02c1941c400301e24404840440b4148609402c03d030100800d01d400030008241c1007020010001410b02880000d0981304130180240400404e80d242d44a42c441140010702c201c0c0c007614401644a04103a4408003040c603002e010721a000c00d1007410514147c80001c180d9200d1900c03041c0100000240305008000383c2c0010155556151038580003010094203582c11035403200d00000100c0c00e94001c0502800c1c2002110424424140300a4628000b2040c9404412000d10410150075042015155030640a00344555218198030004c0d00a10480c1c01620510110f02490014005182075076245d4207d212032110000300040888078400c2c4a1507405000110704001c0b0500f910700c02c42401e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768583929 1250 768582679 768582691
    0x803040608100e090601080d0905090609061207060302070512090901060503091c030e1903230d1d0706030b24090d031e08090a0314190201050105010e09100e 69
    0x540c081c1c64403008022801d00059402d0300d44c42d0b00580040c0181365040c011079455844c60305141082c41e2401000c034854501c000c011500c105007500c00500380b91101c0c0c1c03121090100340746c1511000c03900c0350005030081d04204c1098969101d60412440b0b00741e51402180d241e8440101458007581c6010412652580014200c500c2402022811486481403840f848600407080c1c801250501004008625203031074403690908560319040c43e800480c0c1c028070503241d40c88440300c5c071012004444100440e50f00c01c00e1100c10125142a1100b03014541081010300504600c2c03096440c417036504c42e0100c0a50b1440404203034052301c040c5040e011525261202207000783c0c02400306082c51a84000100820340104003035003c180c03c801c1ca07400010180c0800804030b2218102150581441e00740c01c0c1e40c81d400c0000c01018419920706c10b020044c00d0703400b1b03142103002e60540c646074a0b0040c0750080c00391070b0a00c00e031400300c1c00c05181d00d40d00d8989003507018843c0881e1016200c0680c5802080900010043c142c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768585179 1250 768583929 768583951
    0x2b171513020a0e011409010e0f03070314061008030a080105060d09050109030c12090303081f0e07050c01060b0a0c020d060209040f020715050403090320130c0201050106090803040608 80
    0xc100303408030450001e445500340b42e07228003080c0c1046400140042c02101c9078000300314810041c40415a1304903802c01603529043d10130404d40d02c01480403915002c883e400241c4801d404103120302d60408001b41061090724821b4028404a90318040a5a240a11644080460280d42c01405607044c00000741a5440550b00c000c2860062a00e4950031280c440d04160300041004199005000c07850b040200c0844140ca001001649181c4001b0048103010f064490446241100200c41a40200c6800060400303207600082e24246100050a55802520880e00c40e50804100065040d2210203480710f032201d50f1140000c20405908011094100c0711040351402da0070b01201c04a510b40d4440d1700f80c0e2012076500141c0c0d03600541444c0501c520100f9000b50030a082c5000c2200080e44031003620300b200d90248042c10783c040314407400f03030010042031501038022070f0f80344614031400300c2d41d0400184500709030000c02050b603c81c00c00300c4a1240e180a0550160700401c020440944541c3c280b59000c1c02c3c2c001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768586429 1250 768585179 768585199
    0x40f050a060e0609070b0301121b0f061206050a12030807021005070c0b0f0126030d050403090626070e0d05010c032405130218032b1715 60
    0x15594040340c142c01000c181d654042820458501d00401014000e4061102040d045601d05096180b04c0480d4050081c61742e4400c08550010503200c11401e0050800021400000d0ba21a030000b04141030049105550740d06100340042c11342030260710f00c0240d504080c900c9814860700d0300c1c103551600e4060103203030461166481c082030304019845410300610550b65003100c904100c1c2001c00c0e06070b10240500c02c0701302d4960010042c1c2a50040004d8a0704800c804010b0030307025003c0304a045010b030074480d8900720f040204020816078410500030540d456600d889503040c1000308502e80c50134112030800e01225800b000700f0203003800381203281d0b150500140801108415a50b13082e0940d1108008100400c0d00c9180110251740403100d0401d00c4500092a0780c80c1501d020002150101c450f41c9580b64a070b0300281c45140c9420020317011425400103001c88524854802c9a50094000701415000d00d40d01e9808100b0b60520130b503c1c2035103102000c000301606403503a5580c2c941541e4032040c9298052901c035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768587679 1250 768586429 768586433
    0x602070b1b060c0d1113060f050c010f02040e091c030209120304030807140303190504230a060606020f0705040e0a170d0c0c080712030204090e03070615030b040f050a 73
    0x491072144100e4080ca50700c1e140e40340021026500194104180b0711000e000c4c5100c0110380b1b01030981202c40501c2d108500300e0307140e40e0a9030303240b068200d0f01956500348a400814800c0c1d980040c400c0750a011500251a0755901c078040c0c4510b203281c5800700b18803241080d001c81074880d402034003031088010908030000a00c9681b207480c540c80740d401100d4010000c5661400d21034803c041c11224090000a9450741c0f03000032a0041200c01440d407049041d0b40c0e6008a0288022030107840c0440a804071130044d01490540d180e9034400751040100c03207641c2040c2c40031504500c081580c0d11401c0c40351000f0541e55050004010240250520014051203414070150200e0300b143c030850034110062407226a42c3c6d17050305200040d5041040c070a01030028280605001810303002c100c40c0d08681201c42012064800f0208070f000c1e204542c0030940c1c2c9410b00f490035510400c048010300985114001c104044090102400c90103501c0b44000780614400b1f034009030100d0b150702c4003441c03098421404d480c0d0700714043d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768588929 1250 768587679 768587683
    0x150714010b0402180a092a020c0603010303171005012a020d030807020105090a170d0e0d0e01030b150a0804030507061a01020607080f0a11040f140114040602070b1b 72
    0x41d02c44041036030b04510902c02e07130804141c0e00001c6c05040905005801c80d60710001410100016601803100d0202c480c00b00140c800d00c00101c210900804903956540c4d00c1c200101405a8601503d41104100020421264510440508075007068403811482080300f04003400c0c98860002e046241c00702405040300513521f1145181000d4800c0d19007040b9070503d80002400c4840051014005901a140120100d024032511155860034001e00a941d00c1c0001d81c407002401c940300c2403442910034400c240e160160807a518944016007a80e0400014402c030023004115101104600701c001d008200b6480c245201d25407207a446030180c01c1031442d08885584401c111454901c8154070420b00b51072140056905021250300840c4514080a15041c465035011403140054050010310341d460704040450010001641d00070054824080d24080d95030803601d60758451005d0703150001c0e00b80c0c05033380c1121400b01c00b41e40030b842603940102402810001c0340b20840c1c1c009d40c0081c0709540101e81c44880c01c081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768590179 1250 768588929 768588937
    0xa20071a0106260601021b0d0c080609010b090c0414060f0408010501030614040b0a0506010c02031204150504060c02010318020d060606030b0a080a1707081314150714010b0402 77
    0x100c2c3e0720784808100d0f894441c444010400c1d007180c814903060303007401040d0380d0011305107801c2e5030701665141d44071291310300046880c60424001031071411b0141c8001045100410b40c00e20038a0284000c0c0100c42c000410049800011229000c010a051005225a080700a1100300e01c0348040c002c2441e10b4400c1480301181c2d0856840008a6034481d4018020400640118072814000b0b40e0814881d007004e6881d4240420004d00103100d2680d504005a110380c4941070700340096802805139070a104802016071904c1c0e002c0d00400f456510f06001c0129040d100b84210340071a27a00faa1010510035041d030044000e0524141500400d459016590015030b03200e0701c8800440d803040e000015118903000000d8260307002401402e00c5584101e0040025031400300b42204980d07403204001440c003461a1000d03525001c0c2c440050710180b0b010841c04100c0d0000c000c458152400d10080c04000b41500c0d01f00480b0a6082c500c4403101340060000000080c0c0c002c00a41c1051b2011002048101c5518041030403600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768591429 1250 768590179 768590189
    0xf1b0b130f0e06060d200a0203040905010b0304031e030b12010207060c08060312031b03010312112a0f03060a0b1804051f02131404050a20071a01 64
    0x6880300811076122100e0706900244007000041c4940e141010014003540650301c4080d01c0702c1d48030541d91720004040070b421101c040e0b66034660303070302d424150300025030300d030843c3c010705503454501800418001c4100061701e2040d5816640e554100c0400011880304e0034224201c4014103480b1090b418903541d0f141c1c448905819076800040e11541e690421500341e9490440300010b1004c04c0083c0a0319441c00306907000103d0940706500d82d00e4a13038480c4c40b00714500c20a00c03401d00350710110021040140300c40c134000302609199a06112410326490b002c8d11421842580d03295006004440c229540500c0c10048404800a107120007541364500460b040040456014540c076903944000355007440c0c5405960003000d5000d414071014070342a61003907692100c1482c8641c2107070030140035102c0f0013881d80407200c205010000c0401c00c01e603114403c404203c004458284240d040c45d0001e88029000d01c01c1c1e152800b501d0074058440c59050050301c2d420781c000d500503100006880e036288030900c5401a9a40241 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768592679 1250 768591429 768591457
    0x120905070b0a0e040c1209020102120403050c090a050f0402040e10050a02040801060603142205070303020606040e0a02030a0b06120f0703050f0d020c0103050a020403051e06130f1b0b 80
    0x10300310b8000145452801e0040e9031041e845c01505c10780d5181c1c000359071800602c4d0018000303000d100500041c0e00e08407407196840130080700000c0110030000c021525003287c910950b4600d0316515061001d60646070100c4541e00450410710002c1c016152030740000040039403500589071203038032100406058910840d42c2000e16500024100801c03a400d100306002406940307010041d08400034841105540040d2180020382c26581c410460700703102d200543c1c50305501404031005070f1742d07900e0041c2d1100710407101540705a28000c406403070500e002c9421401c981d03000300075006c03449040c0d0716510603030006440305400080e0711030302641d03440042190107000c80400c40182906840c5252542c075021941e214014240c01074410702582540004610103d000c09080109540e5100e03000c10000340500d40c0058880d2148810f00404100e004081c3c48003070b040d210980380c040d0b580510242c00d80c10343c01e0740104880d8940c3d03004070101d105007102c0c04601000032210384001d80e5074000801d00d07411000349407042c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768593929 1250 768592679 768592687
    0x307110109060b10090b07140118212d1209051f140708042609090115121d01142e051306030c06120b041407120905070b 53
    0x1407034640700341320018403149890034003d400c224002840c0d000f101402007038911041040b544800083d001009203040b003085c0c070032030a02141010361152024100408200b250f0032a2000c02c0c1d486503d108020f40001c00c0d800c003072150b46612094030f42418024136070410030301040c0d82c80750271035500801c8060b901540060080010004001d03442e0380782c4a117240301c0b0718903100b0110b000190b1107a00da907010189081511450b40c030360500f499040d000c0700d090340c4d0443c42d40025000c84c00d0180d01602507142e098a81c152644c1e240c405500800c038029220310045200044a24001300450b0090184402105251a0b1844602c0490741c04c0d5031148121780f03404500c2508015072040c4030000a040216111300a003841020704440c002c2c0036806000300760240341c035010300c404070070707101d802a400a5a112154000d203c1d0f8919004007a0b0444407072100016041800d6401145424013441000ca10354a880b002283c440840990f08003440691035403100e03071580051004104103000450091810800591b61 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768595179 1250 768593929 768593951
    0x61409040c1e140f010804030c0302150406050a0b0a0f0b131805040302060a1802010e040e120903010b0121020c1509030a090e090a03180f03110a05030316020402030711010906 77
    0x43c0101c0d01c9145802591a8000744031030340c1c3c5c0325035000c0e0001c0d0541048011300d1020f04080381490341781040b0400c5640c2d030340b09110410078554001132240c0380401d801c02c80340b40c0d99000c128492500d403085250543c003459082c89612001c5000f8401403a41a81e103141d80c0d0307982c0b01c45e260078116801c1d00f41c510681c0e4a04000c141501481869402180036004200c4000c1c04862101018155100030741005003451184405403516070009441c85a088202c804104100c811000542d02c000d616500035400e08029010650142c4c81d420011040d07103186250720349511454000035040121400340d84e1240c900300c90694808450b145004c2c0c0602c9000c0d5988244501001d0500e524540c8941804001241000755445020400302c26182d410301d03041e00c0290300b02d5500f01e4a86a15082f40100c20031a401c0002040410381040c5040700303080ea08124455900d4040680720f024181450b215500022191401413909600031a48130040e070030080080c0e800320410b1401c4800c003004c1200c0055940b00ca220f4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768596429 1250 768595179 768595199
    0x406080102040303180b04181e09021003090302060a0b041407022a0d0210200f010f0e0718150303081021080915070302030304030909061409040c1e 65
    0x940f11701d112071841c2c886850000e9540d40e40c450340c858401c480100358540041d03140190400c154014280c0f090058140050310110028101078804074030421003d566070041030f009000e4111401d23010f40103030130b155035860800c001620803010050b51042d07807441340c4210110360210f0b86000d1110741d40284104418070342002c1e00c4403207400c182520010080d05840080c0d4420040b0140294155040c514ac415041025520041e8404002c0a140b0220503a0010710300d0004960802c0001d5000910549400103200c40c2128901234040d6120341000d6014030002d401080302801d401c406030300c006110648004003402d404130940045000403091020b0080c5c41d1090f0120b100900b107000c05040702042c0c5041f550750100581500104074400100c3d2001c1c4568464815889030084030200360760701e110742c3c54000c0d1650710450701100403800801000c1799504481c41110b0959140c08481c03000c140d1800e08011050390000d2044802030038803440440c1c5032001c0c0c02c420200782c4e40707260250101424440450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768597679 1250 768596429 768596447
    0x11042607080f0607181401111c020114010f050607050f01051603230a180c030b2203082707060e040c020303040c17101a040506010215010b030c090406080102040303 72
    0x4010040442144658040e034103200380b085540b106d0740c1581d5001c1000041eaa1a00c80c104441100e000308000c42807504525000100c00300d4203a4000c01c40604145a001c040384000c1c0180d5510078041d182c14043c606248004000190080d011602d60f44e09103030250b429650b045904030a000103210085070b5850701030080c5003044402d4800c00480003104801c54840f48002440c403039505071a210f0b42008081c817240019074883d00106440905070700c030305021003c20070a40d5020b10b12428000001c4210140346640e03480c4a500d41e450a50680722100111308041040382a1520000c440c1031600c0a0181005110024901350300c840c9649088581044110307100d1032440d00c15504100100400512001440e4060781c8680e11604801010410814038181c040384030380384041d2800c800120306260421100100701d004407014080c0766507032401282c6036440e815005410700a181c0c0140850145070016545c040314401100b82042030f4230000405903619944440352a0f5030000d028010f02d68480044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768598929 1250 768597679 768597691
    0x60216030f03091104020a09050604081b0a1505030612060907030c09060503100908041a030a06060f0804022e050c0105060a0518070315090b01080a11042607080f06 72
    0x10407002d03005440d46204142d0340c130a0340e440780768005480d0030750034054034281025000240000b600c0d5600c0d9006036030343d0a0902c42004030703021000b0400f8000d18141016006540607156852100c1c1d24000b407e9402e0741015000c5d0b60b00404500c1013144007501006101e1250142d00c0c020440780d8914181404124080c0d002a80b8040c104001405181c8000440b640084100301c4005104402410501c40902850304901008a822962030351607000010203036000300ea020608010244c0d4174081079503600b1080240102158510002401500d841d003501c2042420101201c0c40080030342029401284205070b105011520105142500002c240300d40c542c8a04141c0d0b80b00300f02030804d4001110106400104000d003500400000c8400344a40c01c500c80520000350307016052602c6043c81405000149000e07400100c116001458a417102d004400c400036004010038500750400b060210b040c00d80c00a01030102d024041c2c02168080200508401048031300064003806a8901c981424901c0c05448 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768600179 1250 768598929 768598931
    0x90b0f09040803060f01320f04080a050706090e061201150b0a02061501021509030415031a040507140901050f071101080c070317090f100b01030f06030825060216030f03 74
    0x45001941d542501030580005212124001c42d207c1d14800d803140840c02c0c1c62040d001b0a001408580c0042c5006507940f00380709407002a40c80d04401c035101e0079944615030f000d201c00000f040d05824070400311411110748000101d00250088161180802d5980c000d50040d40006820701500b68140415038001900070000e282103402c210000f581c56410300c1c0c805c0501c40d5030001041142e00304100b11401003045041400c080c480701c21f009002400740d00501c00f01400c1985c030b2504580f1b0148905407203484c96495881e0f814040013100c1105130043c7c0221414008100003040301c08084138054618030b0f100d0954945a5158800018080320000d41305141c100800d000c54000a074010185c0780031120300780303a0a4120303030350020b025241c0300c1d0458031840075000c0e03a10307054046682c0e40c000c0c3d48941c50a807010701c00b20545043c0441103031094400a041000d00b402001c0c10343c81d4190744152141042451045210b042c0d40700c003000c0382c0c011014140350302c00c24106001019000001007454040b6820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768601429 1250 768600179 768600197
    0x50d090e010510030b010219050c01030507050328090804030b2a09040c0e060706050108010506010c03090b090103111204050106140d120504150203090301150609090b0f09040803060f01 81
    0x40814290240107500f441850b4403090100c4113a41300300481a801c000c40e40b1666510740e46401c050346c45500795070032240000d0a100008100c01d00840450b40904080364109044480110f8220741c11507410740138422864071061560003144149002e0070103507020700005400b174103120401818103000c1620052542000e00c0c20305130250384500c15185005010f0f00d0108030610555030441c0c29454144a5070392084020942005015495214a040c1c03005480204950707110440151042c180b20840280003075003040e0b00b803041ea8804c0001d4400880181000710b4070360301041a00d036641d000306d1011002480d50104000c1840000d00a00008200f0742c00711101103141e10307001c41c216002d000c0e0042d107003100c0c000040321007034441c00485005005000c903e0880054100c0000c1d107030b50110448902c03c3d801c00090001d4640c2003100d040803905140c480221003882c08807040003602413a01c03050303402242c084c8009002c0d15041c2d0402d10444c81b4048044d40e034035004017040310b8140113a6120b410412110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768602679 1250 768601429 768601439
    0xe06010308040306020304170406051b2d0c09040807050606040c0c080c0a1b090e070503070312121d010f06030b190e0d08070912050c0904050309040504050d090e01 72
    0x202c806403a0003032000350f0380b907071542000794000c116002c009400c01000100050740a0b4407101030039045442c06c4000150450181d240341d6240e07591034864078024071442c646801c101c0c010070102e09003051002580c0b21241160001082800e0494003516502e000056940820609000440e84414201c5081180c5606e005004109264001740186000c1c000140c81952401c200000c8000950101201c0c3e0000c0c004003940c03903604c0880c401c0e20616414030210414141e4081248400d68101400402c20703580b640d2034214800d03a8070800c150500ca0181c00c40346200c0380d04d0098020f11018044a040700d9030307880c0182821a00051b400a030500e2074031030140002212008115003100507560341d071940300c0c101c0740840000d042c514a401c0031031041ca000b02cdc0d0459044503005100340c0030ba480d40140b140d03032042c00301018103002c10004c00c60307041010804003616041540315041340c020401c9a00388100031010404484041c0c0c0c050324940d118111200e00746500560030405030501e01d007403580c80d501d41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768603929 1250 768602679 768602693
    0x42a0f08060d0203101104080c01090b122a1207051806090a0e041b060f020604020904171c1b021c0c050706030f1b080610030615020c040e060103 64
    0x107021a8490081441c0000655030100411100115450020486980050b20036885540640b059005a00030312400d0441580030b280d4240440306440380c410f00d080d452302031910400c00d004002c1c45103400342504008880d1411001c030350108000080c800d64400540c03404441a500042220b03081110400184201c00f000400b08243c2c00400e41d4800d44030142840041c1c2100e40030380000038855003034020001844144140118144010220700c005562a594202d0366118018054000350740203c3c045030060822081d110340c010b0048100a086061115100300e403503001c0d88095241d10b00e9079088074071000b0780c0c1c403a0b03807061a04d502d90000350034442c5001a4503010200040c1450605030850010b005015690301007041c0c0d132001c00c0c0d4103480d403200d4024000348420464a0421442d01000804201044038050050440c588610049540301010007040f0600c1340a503030b04060310707160001078040c16071071117441980c42074001c2c164007411402440200c076122008500f503a440100104003003911 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768605179 1250 768603929 768603931
    0x6080309150d0e07051212030411040209061b0105011e061101020d02041d010b0f07060e10020a030606020606034201060504061706010509040b010e042a0f08 69
    0xc10744525080c07102940e600040c501030b07502c0481455050100101007000040394503420b036031007181d143c01d01c002919011540c4220800d070035070303500301e0800224000c110005820540c2200080c030141c074103822074010501581241c400c0c6441c221030001e030f4016070300f0203014a90140c00010344407444810110174800c00c40420384920020303c0611400b00c1b807a004290120340012514410555850365203420b0300a02c00300300581159088003003400416030001c06400c681880c42000301c1203040007160b48501c2e00915041383c500c9a203110304115605200e941d0300240c8251080c03901e00103001803900002070f05103c0000e041c544640c024800407400d11820540503514042c400c0d00000310b410250001080070b481c0c203182d241004030044000a03400341c2c0b1200030401e48640b555219000b140382403d410000f0720a48600e400f1620a000c1c940703c0342005c0d0b1080044074814580888003a45c49008501103c8115a0054401c80d40d03041c0015085000070b2601071030243e618048035840e044880003489a18 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768606429 1250 768605179 768605197
    0x70215250206180a0b071406010608090c2701080309030c0103020c10050907030c180f02090f150d06080d030b090403140702042409110909060f030a0f060c0909060803 73
    0x40241a054042d104c000ba104064588951a07555071131480c1800403d076140580703070703181c58032070070002081c200d00ca000d11a000c0c804400091250350300f10400c0000444a0354207c00114080d1052038596105084c0c0c060300034540d48000d181e0359400312003410b0030070307106440b2241407500420260b4080940011030303030303030514a04000285944907002d1450a009494ac03024245010805000c600058034814100000300c82c0e08003000b91050bd41d001c68141e0003041d80e02030344641d0070180b0244c64180448407140c0b400550941c5490000d0740b80b00042100c5050b0420345003a0300002e5030340d561a40501c914041c56204850070061807805582c0284000d0010030400405180482c03000708540f62078010061940003503201080184600600190910302486005070b01418072592442251ba04011140004805450300781c60750703121030501146440f010701039501071040642c510045039034400760000d80d5104110100d000080040c000b04082016007040e40514504031007003000510000888100361 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768607679 1250 768606429 768606457
    0x314071401151d0c1b0102090a0e010b031611010609090b100b0403031b0803010306150f0f06081e070203030708090106060e0904030c050706110709020c1f02070215250206 75
    0x60f032540389a4500c0c1c000d040a00c4111014054171742491001900900501c00007a15890f02069581c982001c00007030a110380307180c1410400121b6075070404041c5101c00c103006410400c003028200c007500313821500c90343d1080c4041940d81c40351004122404101c40e403c0309124001c880031604182c13513114548900c0c070008043c40050b100c00103002d00c5051084103000e801591241c0c0b030b0b6a40e400c2603005043c0b07040280b0020001c07100e010680a82842c810402e85880151a89480303060240c1500c166501510b803480d01064400c0650391107888245d40c0c0c2c03048100c0d902a50310b034100014068034172030000c1c020140590401c00b062103100c0c1c0c0a44141029441190701c6c0301c21b40c60714101034410300c3c2d0680005e400c5d8003d03840c0109543d038215690041600030b5408a40c1c002d9541d0204070104e015011045407150460002002c2d8214000c07480104442d00840040c035028850740050703a544982034800000ca40040303203c1a11017a605489110b0280e8040c40030004c81a81d0300041d810b10520004005203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768608929 1250 768607679 768607681
    0x307081b0106050607060605120f0c041107080d0b090115020a0b130b0403360b0c100f05040201090603150603020f13080a1e0f0f0314071401151d 64
    0x10900c25084140200809081540c0d181071600b010b402a1003d1301601d4040c036002c12044030483c2c80011400f2004403a44098080700ca51401040080c0c022450b880814500c28842000452a6040140b900b0701c00300200145d40380d01e650500084030416800480ea08804540d0202d0040e00420b01c0d9072120340c00920132003c3c2c5d0f60301c21942d41030000100003808414403101001308268101e8140030350443c50310002801041c1d00c1800da01e80ca2a803205040c0070040c0000100310145c00b481c042d112110006007610440c418845c1c4140841c0e03d0081c0702c0a03401d41710000d02096503003101c0040064242d51909201c1c6c00510110304d0380c00a80c5115142c10540d00150f4408140020010f466403841c20b417200000b505d60300ea49440c0d540c003030f2980585402220003025602c2c1c0c2c0180214500c02540102010503e14580d1a41e001c160f11003041a004d001e9074458251a250000d030007040824072402c0d8a440e80c40e4001109400c4a880398406203240c480c0340300c14000e002e05040c0000b82c2d0000d0f90700380c0c01a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768610179 1250 768608929 768608977
    0x512030a0207080a0806150c070302100309140607230319020c0a06200a09090507020c30010204050d060209040f11030411010504030308040305070c0b0a0c060b03030708 74
    0xd102c1e0010140140c0000b26441c2d144036448000303507005040441c1c1007507444e0680b450030310544c13143c048000840d5105100400050624503004044050f0758100052841e2085e11464100e500c910f000b104160040c0c0c0800c10703100d400c0b06035402040c41540080003d0101d180300c0e00c02d141b202401c101c0707601d2440300000e4038241d404d4040302c840680300c005070340600c0703102d20300780300078107010301c0b070341960282d02070b0185d41104a104c00d443c074254155503901a200d1400c000b00000f080c02404400c1107014074102a0200d86503041c549110308000314588080100d003100f100c124070340c1c4040480c900e0340100400c000c81d41e41c00140a20040d00705000603500d0190b0ba0001d0000d04e52840c2c001445401c01c440c2210120a010245100b9801744443c0fa07091400d0400460b014815404000c0c0801c03c100045008a03210b80007500c8800d215503c1c07010442d4607414990381c141c2040c414000000d286054542c20082c0d039004880401d10113900650401c085580c540c00c1c40d011300341d00c10b402d0b4500680e82c489 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768611429 1250 768610179 768610181
    0x50a12060e0c092e090b0f060f090d08160f0b130506071103130b030115020102030415020c1e0c040606090e1602030f03070302040e01080a0f060c171f060503040512030a 74
    0x4648141c146984ca82559541c240c90050014456103501c07496030340e011404642002d5044403c0190045000351030405008100480c1a0291a00b540c81e1542480603810b036080c82c8461310a018040c81c8500c482c0e20040c070382000481c4006040d11070010540e68540b00060001801507040144d6081c9044c1c00d00a1004181c614007031000c9010360b84a03403840c00070b10511030000450680e6900c00c0841d01d000e0110780c090f4207030321064034010450b1200c41800d0802202c00c0d40640b4103420104155446001d40701841d4031445455100c0380e0150f008420254458a0309200701c00040c40c1074201140007610f440d0030241c103240c00818103540300480c1b0031074258581c030900481d50301c480d0071342c0420307100d040c0240010004c0d0080e014000e990400b4130004a1142c40008040ba003096104009460788100c40e0303079a0300640320700c402c0001800216504140b5209000441c140b09407181035092060840ea01c41803194040c2070361000c418803e0800a002c00b203900031605490070b840503103003203580b61141e9036510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768612679 1250 768611429 768611491
    0x5090915030a021801080c0109030b0f1305010219080a0b09360f060c161104023a05070c031b170d0b0a140d0507050a12060e0c09 57
    0x3940002c89010003e9422440344c640c5040e5100d8104444034400001e0040d40c2e161101d0002600c500100c01c0092028603054040704d5100890b140b4002041503540d4515003a41c1040c10750544000d050100c0d0000aa401010f2503401044100140400e10b014404501c3c0c2a001034441c07aa808007209861010500e940d210340502c00c00d48500ba044030030341682503074551101070070761682343c0a00310108200e4000170090f500846000c0800c2000411980d07501403103401c3c00390340b90350010340910510355000340c0c1c1c99803180b03085902e0f2400c1d034420f000900881503c000003090900390314508014407907881d911042401c0103a5050070b0601c02800201d0341e003030780d402c00014000d14110810034030f400b00100000103012426140482400741100780000c00c08040c9947c050b4529104004443e00503034a042d0041c0c0c00070074010002d4644007610346020842011194100f0031481d0a140c600b0340801151384600040c0d000c940016062111851740012010a005001011000214408030745644000341c2e87c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768613929 1250 768612679 768612683
    0x30305090606041e052d2508060d170c0706140301031a0a062106150b03060d03030f110403120e090a0f0e010e0607030b010c08030a051f030602130605090915030a 71
    0x3000d0320b20b07000c0404107482c03041103c1f4000d030521b401543e40d01e56800075110541551f81900d480e0115510002400700c019101842504d501c038103240d6041c007007500b1000800500b485800907155160402501400200b0702e84c0c55180c50341402c00041012500020220046240034042600300740c8425109501a24060b0230904903200700020300e00800c42140005200701d8030414003400908408003412401c1103030f6118611200000300005892882c01140460700c580c86070030001542410030114030201d401d00d000700e040b9000e00041c24402d021100302600c12445491400500c48000b02d80441e80290001d01144034882d250400c1154040c070903008000c040c84844000c014080d0300b076807419a9034400b0340700080071a2920000e00d0f4a54400d00d84e2651158010485910759210b052010340209002461303d03204440c1c800740c816440050354402001140143e00c09612181456401240e1a90f66800358081c400100490140340d00c1d00400707181d1180c05c0d640078601c180f642402090404000c4200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768615179 1250 768613929 768613981
    0x15030106020a020103060815041e1e02090123061308160513021611032d010b040b010c0f0510110d050c0720011407030305090606041e05 60
    0x8550140e000440420301e6000345c1e0305115540e65440c13800c0c0c03140424110081030308002d100050110b02c442c00403100079004a10b825000d00181e45500f10784d0303071b80413401d000c50300da444800c1000c3d40360075100307a4090800c44d16a1038909890341940c4007401c00c040c10040c002d00c00483c000c6a445240c10280c4020080042a6176400b00c0303c0700300ba24082050300038944254075078180e01078959850300c280e131400c03401d5010bc8040c000664980c25a495152900f059040c807501c9078000d0035071804034cc002112603900300d0100d2250030417201c3ca801e540310381c4070041c05686450300c0a2030076a80036880c4031b50b140c2c205030746030015640d0f41001c90504004480c400030445c1032050f4100031820400040202c48003d4504000b83d13145c0309000708081c458003101501211808881d06d520034600c400003641c40c00d050601c1444440240d09580d181c1d00030280c2500401c0e40e410410007000360a000c41a030065044404008103d400c1309402c05021a1088201201d030355600084c2c600310060100c4081d03195044c036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768616429 1250 768615179 768615181
    0x9031c0902040f2711031e06070819050403030f05130201120b09010b0d0204080a0c090509070503031804270203100506130c1206061e0203030c0906091503 68
    0x148001030110310034228015031905040f5900944580f0800309880010040c501c02404010310500d001200488166143c054a01490030300d40d90403c00e07212541100c0f41e1540c012110482c0041c01d20500a200d60107000c002810804008a100300400340044000341c0021035403070340d0808400606d905408203504501c4c0c1b9007030019080e403d04100304854400da0b52666520400701140d403d075810301203c0c603008908100180a00204480a2f10141a103100010708040d07446c0211850042082e105541480c0c101c041809250303928082c242c1d02000e218020300c03000c0d1030003001c281e81c2e12600c0d41e810300300d101400844409580ba034000b80408240b1110380d21000c41c00401c244107036281030104a00c00d1150030701c00c00c01000103000717152140000820300000809440ca000b0050300b0001c04c08005c110030743c2d201c1c507070110b21440341601a0050350307100701040c83c1140d81c0121142400403036400303561060040001c21005030085a801a80c2526240d0702d4040c90808903040c82d855822103500c0900100c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768617679 1250 768616429 768616477
    0x9010b0f1c0c0f0f0f0e01051c0b04030c020a0504021801030507030608030f03250504031217090f0f0313050f150c030a031b080619050607150f0e150903 67
    0x201c600f019241040c1850100d6541c48140d0020f080b1544140e03e0030700a804010019171034002da004040b280c00c00000030a45405070740304a40580212400c901054003060080d096007412201400038110580d070441c17402607110621044025846911410151601c0008046601c00d4000f200108a5041102e1b20350010702400511034208403120300c3c4011140b50640424644680340b410303c90b825495103450b003415511202a42c0105801d24824848031220f6030034200c48040702513210f8440030303001d03040e91980032804508003500e00c5513549140c0e00074000101c00075500c5a51004403841100c0d03041b210120040030521126210030282c1c20010003041c9000803010110003401d2141079940c0400160964003000640980c400c00c0400000b02420005032550900306090008007614960702c12605075107000050140c1d00000049644151844000c82c42400da4028100036043e0340d04207100780080c5c8070b0b06c19928101d0314880040c101c2500080ba81c601800d104480c01e03040300e24142d2400c05100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768618929 1250 768617679 768617699
    0xa15060305061207150c05150a1d0718020c0a05150108060f1e06010207090e0a0506010911030621100603050c01020708030a030b060d0e06060909010b0f1c0c 69
    0x200d030b11a00507a0801c0c0d0b40c00c505207020030140c0c00d031003030300041c141c0710030f000325080740c01154064085030a48990100c2c0074405408081d254030501c8144000304150390f0ba500f001000078120304035902d0031ba110110078800c810040d071100365007036101c0300c0043e01c40188000042c500741c4000740142c02c0b07000703448170221461821070065058170b20030000c0b42e800391102d144c022041003084540010704c070b41a81c1e035070f00d07100031311a016a08581c051048607985a124607111045428504526280303600c8041000200030301441014010000382038200584044000e60b44202e1000400d221b00c20855401d501101c445465a20445a0010001c40380210040c04106000707140320702042d1072500c5480d003030070000d601c00246041075070541e10281d0b04010038220300ba009042e4004450360700810074001d50040740034500c40e0300d0b140004903004011904196048c0a5040d002500782041c0c0e03410400070507600d4030742c0c000341c0080c0f00c41079402150340c1910200307041c0c10015025009003800700e6140009008048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768620179 1250 768618929 768618931
    0x60f030c030c0e04030219062d15050f0409020d080c030301090e010c0e0108090f1f11120112030509091e06180f041a071e0c03050706050a15060305 65
    0x80b40a003940d2954403400d446007141021580200144d111009021700c4803503800d003441181c0d100e4030001c42c1642404801c24001c00701c010012810700b245440304d04032002d540c0912680301c200c1c1003410480c05c3c2032402140800000d4000140a01d4032521600d01b15101d42c40b08917001904950740c20344a40049002c0c41e180c0d8028824580300038207005007400d00300c00611070f414008009407501c0c540e40071103400541d54031100030f0521034a4010074a04180c0718605002c614540209425003110fa100e43c202640200c69645502c1071210405000781180102c25000050550344d180c3e00380300d00d0b20607519045840d440b51101042d00101d80710140324050b9100480b810350881d00d030301c1e803445540d5104180710480b89190b90285104810002091000151006403074100d402000c9403494a010b034921102c1c40c03281561290002050840d00c03045804412132802c014004515010200d4281601d000b01640204c5002810255841c4089000c1c1c4071070781e000c036860080308203548804035500d00703018006140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768621429 1250 768620179 768620183
    0x6020d0f05120402190909080306190503100b030316050a02041103090309040908070c1d0717180c041a0a0e04020102120a090807030b180c100c0303060f030c03 70
    0x88011500c56008500352104000c002c030000400380d070780e6000c1240050750540662210030783da8102103145001d80c0240424203009000b1a40c1c1e0b410b0030000d00c888240405121042029115824003da5a0104071100e070441590710108613603801c403000905600c02d03140712401c17502c0b842d203a0300e041181c0842e14824590003114100509411074010a02c50300c0112003242c4503230800c01c40c90f0788528059001d02c00d001e006400c0c10b4113000c420380c7c801010f112190015079110581183c0c10994507042e0b0b81069020b455843d0510385104607a00420820340042c094070703d04003014110391000a01080a06001e5500070030a21000c050310404200018070030240302c0c004d1951050105080e00a503c07141d0180e035040c3d000300780035030300c002c0054030a070004c20110003005501100001d2400c020442c5802440c000c0c148240e841c18000c0c250402c0b401200410000381c2c010701401189039468200c01d1103844d24a00303000844011600e803c80051950790081e03203031007008074400301c280042d0901c042d003030364 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768622679 1250 768621429 768621437
    0x1603063303090503040b0f0d0f1d010902010507030806130504080c0c0d0c03030f140a09300b091014070f0207180902121e0c010e0108181606020d 64
    0x10034401801c905442000c8400781071503204000c00c12110070088010680020007460950a0241070885e000640d056081e00d13896a5885a200c4044401480140c40051804030000c000c00748060340042d0943c040c0341d80c0503042c4640b00300040c0d00b0b40c0301d401d22002c5c03810b00364408022314a024681225241c02000784d4103641c0c400d0800030a628281301c0407490090b90001c80b0358281900e035990448105098a9200c010000c40e070f000403008945003405021743c03405980702e0f660000d041102ca4070803901e50b1603002003016000125050050000840f4508480d00696100c0c0b40d5a1000300d501e01d000b442d1485014440d2420303001c030f00c0b450014919a409081582d031500c1c50f0b1180040120394481c1a13000c0e850f0210b4141c7e00c1320000000ea0303030005a540b880a00001c0600b03140009036402d081c03050409104000d40581d40340d802d18070510440c0e620100900b0310413107c1c40c040d0300081c48110014821030001c0e40006140e411088204882d0340065034000032101c01a4441000a40395100140244045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768623929 1250 768622679 768622769
    0x40309031b05061c090203030705150a1a01030b03030912010b0a06031103070f090b040803031e270c090c070c0617040f15050c0909150306160306 64
    0x2078180c20700354001c41d0002096203007414030314000e01141001445445000d241c0e9041070f000141c9080c4007910b161409000507151460f112006500b00820050480059628142c0040c07800045281084485102880c000a6000c00310000c6842e5110b000c80032540f00071062461024100150880443d02400f0741d440c2482c00d540709015025204108200e2880c568144002019144a65500e8203800321900d480440070fa55594214116407282d00045081d800010802c0151700e00000c841c10001c4080d40301d2003452a02c4065114809064409407074030005011503500110400c0202044480f0001c140000134104180c403002250301000c8211450990000e0014000307014410b004042c3c889a22840c40c0e958440e6101081d00015001c02c66101e10000c1b0300b00c0c2c0300c3d5034511a41d44180d00d403a054954560040302007041c9a14000e00d45150f24420001c00f0180b520080b55194214084c2124011245000c850560291200380c0010036010342040c40414848040320100c071400000c10210064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768625179 1250 768623929 768623963
    0x5090a09030e0f03061f1d1f06090b09061b01020418060e0411030a1205041e0503101509020c010b0a140109180e1902030f4204030903 59
    0x1520340c8101a8160480b00024440b00070780d1034900501c0e101b0403e01b828594840035161041100f0020780000d08840c02c042240b46928441c9081d00c9481a24a41d41c00c1860840000c10250a0740105c009096000c104a0480c1c4c490070252240e044202c4000c03013018490411aa000390040c0c031a039070106a103144400304094041c8900401c0d100c010000480c90303555511824141d49000c034460360188150340f269008a01400303081c2c4103001040d616a41d49078079012501c1662127030980e500e010810a000308100d565030003c0c5130351200d1000000803c80780d070215400d90034118650701c40d018482c00000e081d03200210660008074801400c440c901c480d0707500da0266005c80580f803218107010450b9680b051004500c3c0c0b0a00442d000441240801c05002075801c43e4123182e501c0f810400003280c021348500862a0501811504019100c000c011a01c6102e54494408071400351a11540c14060740316660036401904441002910400b084098149468000c3c800d00c6148410b0781c111090a0003660 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768626429 1250 768625179 768625189
    0x10e06011a030417091206010509161b0302070506031009060f0803090108090102090d030c062a050a020a02100804050105060303180111071d07030e1c03090c05090a09030e 75
    0x1959884074203100d4116640c80d0386403030480c2d10182058200000510018811381d49000504003460344a401034001540741000340007505401514200302c2402000100502540c4003d0701e142001541d0201c400c003216600f026804c10b43e058210710b8000d440041003040d034094502a40c0101c40d0400c4041100c6940da0311030070441d900a00900d04990003c0080b44140d6102e4514141c102e80403800040c5484506c10003d511000036103002c40110b40c0200c000414082c503071140158090341441e0440e549042220728103a10700f1002140024014040b0301100294820460401c004d43d010381000d100d0912240f02800c19041180d04a1300c0c0d41c2840d0018151b0304020064442040700010030701d441000c020010b54244218203d02021031288000000e200300c207204444540704140d0801c0e084a0030720a0000302a20100131040c402070740050440ba04030790720000c405440d10801c0c6000641096286029120800e0030340c0010f03800042441440310068141d8484003825120f616540000400d66040c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768627679 1250 768626429 768626459
    0x61d030a1715030105041a24060a111f0b060a0f1b080f0403020f0d0827031014010602010908041701020d0f060f0515041502120d0f060b0c1b060c010608010e0601 71
    0x30460001a0301d00003920709100c005042c1501c010308000036844030894642c0e14200c0c0c01344403142e440c1c0c001c00708541520501c0c37040c0d202c408000c2e20228a0100503a070b010f021450b0042c801c40c1084403061203107000030074544070300e04200d900c0403c2030750341c05841c094401c1d1a003081c00264400c4400b20418171051070042032982c02950301050302c0303041004941101407000306888140c81401c40340d00020002d40d60600412404840ca41000510403010307030411500e10b41d050b0000c02c1560703d02041200072a850030103507001c0340d403030340204031960310049601c50180c06814941e00d1642d0070301c8220703c0c0c29001c941240065481c1c420a100707840ba600c1c41000850904480f101131018400c200a0000c50420300d8111034645240c0102e980c0c840b0b9840d203220480c5e10034244071200b9566141d103007000c00380e5401040b008100c0c034550315007480c180d040d00e40c2c6c4512154245a01800450183d4a8a41c4484040daa002080a0300030000da5944004040c040c00e021131801003d801500008124615042034407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768628929 1250 768627679 768627721
    0xe04150c02070506091c0b01090b120a02060f041211040c02120304060c020f0a0b06030c0406060e0d030e030a06140c03160315090504061d030a1715030105041a 70
    0x20b01c916032911007440794642c407044180d13411007801c42d60001c0c1d00c3d9050a40382074142c07250503031020340d42c5000355403130460349050701441c880c40404038174034154070000980420084e01112529501d20115065800c507206170703800401c02c1c00c15100e0140502c0208810201358440c1520306000c00701940c04100d80701e041f803c150941441081c00440d011903035a92120191303004500403510f0150041d580d561515207803000440d581018203082210a0500748100085440161014003102e4100313507020300f080301c9400c2d00c14040c000c1c0142030402c1c940304080e0246d2201000d400c2d126903c11a0134500050000301c98030401c45d408038408500c24529200c1100d21070540740d1780d5028003010141c0c048000c1c0151440071448410a20300100ba840445c0c481e050066104540004071041031821440e1840841c0d0312440071908240f000c292000d800c1030b003119884c401114100b400b55201c0c1c442580d1680102d030703844d8140d07183c802013000b00410241c01c4c002069818050700c1403581c89258020380070071280b9003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768630179 1250 768628929 768628933
    0xc0d02070f0314101d01060608010b180a0b0406020c09061032040b12100f052e111510062a0305180f09010b030c130e04150c02 56
    0x81022403031864045a00071400c80581c0c0310309243c8015801038450812040545401c40c24a84a45c20000d1054a004140a00300980c81d585042c0c01e001050080d18425540e14080c20310100d00381c0d480d580300c00c3c05040b80000380d40e2101d4813800000d660b060704400c4c00e4011408a004207240c3e14001d1600b2860803c1a0713150741c0030b1307000420f0765001c034180c40004c0ba56428003810007400303c4c0220400b0300f014000c2458078036140c0b599015100b00448002c0e005000380c445c40718040c001d0706200900e0405488056510400b081000700403024100c80c4103031561405074000c1e240c0301c4c41952241c070b00c068030008036086610401b021065941c0c110002c1d65689218200041d04000071401060842641c9424940c0814440131030107502c010301c01d1000c4201c0002d04000359484440222900800a5040550700c0c09031a51350704000c981c1e03010060080c100701c1e90010001800c00da488074100d800c1400360400d542d00003607807070610b0031082c04180c40c2245c04c4019080180405c2000f0302c2031031030071006a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768631429 1250 768630179 768630209
    0x1202090609010c0c08331b090d0203010204032612060405220c0303031d0a0602030408070819030501090543081009181b03060903050c0d0207 62
    0x10055030b40100d42101104c0c164110f00001404000a010002c88002c161020844905006051500c0d0300e01c000d6190020181b0502800120800d06048280d110450140145d6468040000510207510038000030f5066000140c04001c0108403103403044140c4440319140500d280031004081180038031050300148d0300302800001c1992502d0f801c0660007040454004d1208820710800d440310034802031058030f54a411480030000c040d41445003001c5058070403504a2081d284100858886c4007076100540300540110104090040703801c03c58049075401a503260380c0300c04c0001c1c045290090420172300d000ca07140c98000038103015240251171250072500c4481d00d0143e56590311000e14140a4124a00582d01407414400c1d98020909a01100ba40b501c03500e01500d040b4404464801d403617007289c05428206503181660105210402400c6640601d0344410040342c91011100b0590765230003d060303213042050740424550004004c00840d60510240c1d03010440c4548241d0b035440052250b1880c00000d16 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768632679 1250 768631429 768631447
    0x6150807050f0405040906090b071103040618050901030326040803040f052109030105090a0203030f0d0906020a08061c0b06041107020a081f23070302190f12020906 72
    0x40002c040840b190445242000d841e1400b1030300300c84480300c0844101b9500c4100c081401050002c0950100715850030b000c0604d04001c1e00d58a034000e91041606200e144220113031062681410b60026003400f5280180c07946e52428010800c1c038241d24503000317148070391301c0c60310a04c414002c1452180d604440964619111507862944c40f45000c031050343d01e0300840060a0041d151610416017441654413510380710320b402c0e000c1508680000c1c1060150f5072203004d42c240161004400d403107400b0030f1480041d4a03040e00b2824200030304104400205003920009a999541381c00c0b050706401141c0680d90440d080001e00500d0354490b0403501c0c00342c1500140360002d1217601e010f070041a144d01005900900303020041c1d0200b5074402c0745420240180d081045010600909030318405021501880d0074403000c0d401c0c030003082002250101400c45010300b100040d02d175a000341c0403284103039a101c00080141c1501900241820f49468040c000a10001503001c2c2054007402958901800180000d26203c254 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768633929 1250 768632679 768632687
    0x10314060112112d03100621050f0307030f0f0e0312030907030b0f0105012c04180b0f152205100f0f140a030f0b0403030e030c0102090406150807 64
    0x40c08981c040c0800c62130380c1810841d400c515134184900121100402c0f12031041500701700d0000c03410650b05261150402640d001250380100c10440d0901040102800303003499030070070b004140328441e81d100000e040c408041c1c0c0000d0303150404000395038201c803408100b002144c4c0e206a18001e160305034030a001407814298504019600000d80108554281e035503681d85602c1113a04852038006022114010082560400048803130820301b6847d0700046043d980d40c107a580441d140c00c840c022555201070b09101c0e0340010001c04440d80203989840030b03240140540101050841d4020b40d14032204003008880d0404d00c81c0700109410702d421010301c1061001100006010017044821030a500d01e000040002006041d4405009001010391209092004007200d01461006860003105415800c03c0410940c1000a034036591240150b003407503e8900f03044018203010443d034335960000223070800609005500820310b40c5400e8405201c41c5603140c0c58050350b180501c1c05000412903d00004000d030b84a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768635179 1250 768633929 768633953
    0x4020112020d0c090e0109020a0504170a14010c03060503030a140d02070206131d0c0d050717090a03020601150e15070b2805070504120204090b0f010314060112 70
    0x1540d0050410044900314015290301c40c407a080402c6644106000014085404a024141d05201545485281d040080c0390340700314810354104d691140c0c55120141000d200c4401c5d4203401c40125401007116504050083c44040307a0710700801c3c5002000549800c0c003100390303209104d86403140e2281d50300c0005855510b0340109424441c081d0700708a4070005950700006856510841c0b04200d88035030a1407200102c00700910b4a4414400c9130744104648055100d0858200d4207100304040b4094851260984901440a0381d60035880f50740c40070022801000120140124043c0e800c50700240da80e80d041140c40424110860002007401d00349004e00c0c21324181c0494003e495001480c5005255110b03440c071070400761600c81d18010401c0c4a111484030030800e100314810a034204010360308050b04040c01502c120f10030341c643d100c0d13441044400c2d5555a071003403590780d4015003101540d00d001c400d5410101001d00080381c0012400c0b80800024200060f420f059074420300d1601c8a00f170182e00c2746409951 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768636429 1250 768635179 768635207
    0x71e03020a17070c0b1003080405151b06192f1201030b0109050c090306041707020a0b0702011121031009181e0c1a0f0301061d010f08040201 62
    0x7545010310300354844400750503403043d07115036965941140d10746484548408041c02d040480c141e65201440030030004400c07127049400456410f1032000c0302d0202141f0f40d0050100d5032100021404010b0211400420880d124080d85485821414120500c0304121120f000030346030750f07011306000d6120300f12200600b20791100c03005004605040f1002002c0000c6542600116480c83c4c112004121845440c000c507500001514112428aa52800400e17a104030080015144412010b21000e454200c141116001600a00036103001e030385400f07603c03529510040c0c08a0000d2800300a5002500020030712002079415a40791031212600c0e0010001c5981000d4405c3c105508400f070009007000c85403088000b2100300b210721140d0307480c060901505000c4120f0342c9003100c844540074080001c1c1c2d0102e001c03043d601d594110251070889460500d0081c000c400050441d8407001001180302c603003050904041907440b13441e0032201d00325640111740141c00c8802860218200002003001580038081d4021149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768637679 1250 768636429 768636437
    0x120f0e0d080702060f180604051807050405030114041106040f060c050c120a02031608120c01091221090b061018150201110306010c14010e030a1205071e03020a 70
    0x1410b550002982980071100300c0d00000740014900f082c860b0f10342112100c041007190903604142c50900800d4070840701403036000d03421180c04000f500c3c1a00030000d6401500c4080d00802940005014003000c007181a0380985a0b01449480342c066403401004407010740d05d00e0f07024048814900b205c00e40711002c01440844241c02544000c500680b1118100d4000d02c00d141c00501c084245c6005140c00c004903180c60280300150b00000b0320184c840014400d00f6602c107015400d981d2001d03200c1190040c8416100104122216511508000c0d0700044000c04140d0640110b84400310701201c103000c895482c01c0042c018030a4000050752840e040d00d90f081109580d040c80d084104a0002200d01d0903800e0b006145030100c01001154640d40c2445410b08000b032400b000707499410800b001030060b8030815002030200200c00f0404518403400e40000040c0a16102100d440340182c101c05400034190804c180c5006152800040109101c0d040d051ba880c00d650b1042e031501190002c04a0187d0301c0000c4007003c3c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768638929 1250 768637679 768637687
    0x1b1509150d15051e1f020a02270106020c0306070f030902040c050d0b030a2a031403180105032a040308160c0501090614180301050a0603120f0e0d08 65
    0xa0303100341c010540300c02500080d01c0e0380241494100300741c880d1841e41110314010b11411300c20f2142c8940c1c0055400168031716104a680521050492424070098030080d00482a48000a401d04210089000c07210300b140900e0350f0380e0b88405040fa5110081e940040c0d05a200c0808a40e106014948004824485260204000c401a004070742a00d85c0000c8880c0000c05c00541074805a20034415003510303840450180060510310740b43c3c00300148000e00c0c0d480d10010803809580014901155140013103621070050704951280424082d12504000698075143d4228948201c2561168080703a00c00d81404449244c59252008410039200780d884048503004810803001c00821541030180c507445842d079200c2d10380790003030745072015190045603c464184420310205110454110b00041d00e07446803207154945070300356480c0ca59408454205041c3d0503510b8401400282e25194000d041940d008001100b038042c843c0404803007034629400d0071000603108101c5443d02c0d252030002d1605242c05811040d0034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768640179 1250 768638929 768638947
    0x16080f09060712020d17010504240f050112020f0a08040c08100605042301061803120225050a0302010309061b05030405060c040608150a03080c1b150915 67
    0x8103501c010020360720f0161441019041e250b0401c101c1d28140070390f2a1405c1e103044941d0b0088035110060143c2e900c201e841c1c0d407420b031a21003000c60806003440c4005040c28001d0b5a00c07075117848000c45011b03c50020706100c2921032400c00ea80212004a6001030865150417201c03082101c9100f000340c000c0300c0081c005c680c0047c08040c1040154200001103000140f0342d072400d01040111681061b10120b9001d80d00c1450103c1301100f48101c1c1180d00504201201c071004060145400c0700700d07000140f00c0080c080c0020120340d40040d058050001d081c0c4000611452070f591070700c414520707208a5500c0843c071901800154440e4201e1011310744180780216088040269121030122041c040000143d03002c001c20041c04010403001c1d4202010704100361905041c810000d24500000745500c1c0c0350880d034804102d16880c0d0807004401550080040ac3d21207004450140c1c5580806243c0c0351b03003458800c40c04480e86480c44c5100500341c0d111103e203107031143d40c0d000e020b19600b070400c013041d000300140300c141d81c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 768641429 1250 768640179 768640189
    0x1101030b0d02060c07061e140a030b03010c080702160f05011220070515101a0d0603050c0a0e061c0512040f0603050708040b01030b0606070f12020c0616080f09 70
    0x1c0020303c0d0034064085c21b4240b1200510b01104210820f428030200285890500e800000c5020224600000030f903441c0900d1000780c020303100080071a9050340c68014003030380c1d03542d00c001028082d001070f600343d5510203031a6001101e00c00c02406000401102010100403d40c015080002640711071480450071140f480d111281c001301c02120b0707001d8014001001020070030144120401102400e460300c01500b0285545c900468041c01003880030016021040c0d520390920080d55500440700000f03020366522480d2154843c07450f40c43c00c600905c144440403c044603800743c0c1e0f0344245009403021710031548004900360124014817068070103020300e168121107150380e01e00030070203003100c010012005460501c2c01000c82d90700800003002c218415041c00b0004910b81681411290051407403089038a600000512078490104018030290200100c20f007005030000390101c544600d6000d46103e110018244101c501c030f994201e015003122108014000368004003d03150507609a50000c1c10f00100d100420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 768642679 1250 768641429 768641437
    0xf0a0908030a0501290a080402010c08180427080f130609080d2c03010b03100f0b06030106270e0106030e0c010207150c1e150b0d1101030b0d0206 64
    0x142c0300d0307103c1006110309401c0c41039103140c41c030441c01d414224150f036900001c00c40c0696048041001492001b140943e0311a904501081d85c20030310140d524200d1200744500365040d2038440340101d00b00300c15021456030f10b040e11a0050a41030156400c8a241c0da51081e0580c09141010740c521000c0c0300c2781900910070a90700010b0500c42c0c540c0301d501030a1071900d514009a440005c8100120810030340c414003400030625015039500c2840d1641d103041c903c000ba024046446400c1e0301131044d80b01018641003140c06c203940080326101300700b10212000c4148041480240070703800204404a912100310000a194010644248145c0c0c00410b5100c50203a15201c07400e907c1680082d88a0141c20409034061090405100090009064242ca0070110720031650002d44104207110310800e84006100d41440c502c14030f411000401a070340f111070301d044115a841120490b56151074a04038500a00300303000340300c58882d00001c21212820300c00c00114090002c21a0817a00074213039503008001a1212400343c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 768643929 1250 768642679 768642691
    0x90c040f030b0406141006052a03040314070302150c01150e06010219020f010f11010c05120c070b0103170d0c050a110c0d260a050301030201090512060f0a090803 71
    0x40b06450520341040301c140e80000c561750309124000421320500420a5920004441950609035103a883e8207040c41c03803025840411541880d48954100701c0100c0c040001c10550384911040340701807404900c8250b40791040c1c0402134219100300c900c40e540e06a01405000d155001c0c40001c1144042521100ba0030000741d441813040c80c00e22010700019680602c02007840c03075884c000e087e050500c2d94001406a041c0d0b82a0141070286010940c0c000e00d104d0b921107214a64654000d1025500d42c0200030055072018090a0020181c08080748503841020102e810490b08a000d000190b425510b500c0b00b80d0580802c1c000c400e040c100102c4034950103500030310310407004a0300c510342c99140001e0301130010a001c151305001074002c0c074400403043c0c2c0d40301d41001c030040e00080c0c4858240030510b274801e071804006070015482c03140030500142e810350060046042c0c0b403007070f03036421541c60f620002d0241103a841600e9200c00d8120b813001500400403a8074141e44071500102c0880d800180391a034000765801540c40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 768645179 1250 768643929 768643943
    0x216050d0503010905060603040b04060e0a05010e030d05090f03030402060f04051008100501030605010c1b0e0f043f02120c011d06090703120519020115060e0609090c040f03 76
    0x1007184d0701261044940c4001c05507200d07450b51400740e840b065156002000148225035034168041c5d121000c1000401c560741c02030003040542d00b01301007203580750800b03c01c150b44030303041c5800901841404070700c40501012130401181151125800c000d03c039008104103080020090000003066503441d0111000c1038040e8517004528200719945156a0126800035410f0504100c810001031740d00c514210740b00b07a00035191a412a850403248410804568400b6548200803018072080c9140104e031540618070444410b50200b4440f186a4407980300003045242607014250805518401026403000c560401d205403000c00c258034419110781d800c001150100d90703540700e0140b900e01c10004102230207001c60700018103851800c0c2050301d90760782c85030200500c1c2507000000b58038141d000320103076600480346505900c1c2a9126100c024002c0015801c40b5141e281c0c0c80900040701c40c0620901d4a00c050080d00c41072410a403102402480c883c00341c06000340304410080000d1403004091100080c41c85200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 768646429 1250 768645179 768645181
    0xf03340602120403021b10050c0a0f23010501060c080310051207050f04060b19050f0d2702060315010e0a0605030417131406070b010e16020715030216050d0503 70
    0x1802840d00465108140c11806101d810301b490365280a226648050039281c42070346d81f00380c1c0d442c15041c4600c401c4002d2451000340160400c10090300180110700d004030928030b416007070706030f0064240c40d002e2087c140403070000310035840895070000045511002544c40c0e044006e6032030002c141c03031406114440c004d54015880c00d000300e18202d424101d040300100d0f41881080c1c2003007a007141c1c03841755404038a582c40e00301044405042c054010b60701d400001c07501060b102c0300d2840781400030381100d2904407011865410100031131105511407203003c580140400d401c681da07441200d11803022816001e814071100c3d2841c0700c80d035940e002d9100058041c40d510141c032400c161812a45150318000b0000d040e00b024841c468681c00c14902450445030b00360780040c02041d07980d0100e0454400c010016201c02e004c02d00101d090505d0044041c044c2d1058901d8242d140c000550481e00c03000c10340218440a02010b40c4281c026100750060070501c24108a400c001da036440c0d50340c51822101e00d01e44400f1401c080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 768647679 1250 768646429 768646433
    0x703020c0a11150909070f0207080a06091707030e09150a150e060c12030c070602030901090b010b28110709050a050a090503030a111c0e0f033406021204 67
    0x1580b032190030400e0b03001484c1411100c20004142c048003d2619082000c030007010203105208101c507000030070104040d103d1000250a00e40041c20050206031a000080b407051021001e00c00e00f180d00303d642655511420150031000c002007880054842e240042340d840e035000305681e82c0080c1d40010102c0140040c04c84005100c00f510f62894a9180c6200300014400380380c1d1100045200c040900d50726141582d42da40c2d2960032b100c580180d00f4003030403142c404001c00c40d050005500a0b4012400342e02051466031b0ba42c40d1203a614443e00b03024074594a507190b1081d503180c400300980880300c2064144840003640d80340625140c50308640c08074408039104c40178455608010b00c43c441d008a02c0d424103004000e0036484850b624400a040703044007554503486409480701030300a403248141c1c002d00b030016201a004480010f02800000d00c0540c0c050b540b40000b00b4203002044a20030040700700c1c1c5092065944040130011140c84440c07652001d44da803290720001d95144020319a030411a80c40c05168207082c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 768648929 1250 768647679 768647689
    0x39060c010c051308150c0a050d1b08010801020306010c0b09010e06040b07080709050a0b09030a170d06090e19170a080106120e0303191803032003010506040605030703020c0a11 77
    0x20344c0302244a4001c983d803040b41c0c50901901d6036100c2d810407500c5a807841607840c00c4525124202d0301949032460003184826100c681d0520841d04680da41c2c1c0c4600c11391b00c5509a03800c074802079034024081006504810005845c0c8c2100f15400581440000b8214070141020b605000c1304403000c9550307a8a603070400400940100320942c106600780b5020250301d0030480131502d40c401034050521035010110306401d090358100300740c80900381e02035500581500d04a201da030311900448981180c4904015000c00c1185140c403c01c0c01c0744026900600241038542c810504c141d96030901925903645440380c5040707445002d401000000f335165241d518079132400f0780081010300e00c881c0c072540351801c0c00c3c182c60404070000b040d660040601c8101880410200241d02c00901b0040036999100121203440750a1580540c807400380308041a41410040c482e1200401a80c803090207480d40c4100c05003c2400b2152080014550080c09800c006180c0708048108915054403018115594504040d064200c0d00345 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 768650179 1250 768648929 768648967
    0x702040c05041a030f070507021f02060108100209030d0e0a030c081509060f01170a0f05070e0106090f0303030c170411030f07060206152403040539060c010c05 70
    0x3c10700032642107040202c40703a41403800103041c0908100b808980d6800790766403029030142101c08280074880b82103907058065203c6009115a4202d0300800708a11982d600c140200c0c1c0c8c024000401401c05000418010391380d5000b400440c82e007103141c0714008400140b010b0b5000d8080c6c0702100060444034401841c04c0b1045000070413101d55a006641884803241c03e2107510790545411140c0c6001401c0f4a80c815482c244840001420440c0b200d80b003073307090182c0451018166501d803009518280c0c0c03140c1c03068940b07000a11035501c2e61079200c442000468400d81c401006041240340040c8049140d403403c041445059070240c2c1c5812002030004203078070701048900d0000310040042c0000714540440a900e510b00180140b4241e588120654003a2741c030901c3c0500c2c001c00441c0052040c0094045103d429001220115410300c03a48242c044001034501940c1040521032911206504034040300c0501400903421403600030109019800d0180420301030b804020000c6d954103501c80c00504511145050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 768651429 1250 768650179 768650219
    0x30201020d060f1d0402030309210f0a03020d1116060e030706140405090c0c15010f0e040c050d14030d020a2d1103040504110418050f1305030702040c0504 68
    0xf201d00810014501496070300e035000900702212000aa8560004c2030862160840c2941e1040034030341d00d04180c02d40348541182a500410032150f1840040840c0c550307a506d82e100280150b80400201c0c0d51180c49540b50003030140030700c429111105404801944042d11580244011070310b418a011a107003400c10200d00280900d1800d60940d489602d407410592083c1e0003000d0144801000050550851030121403c40640900f01ca40b05812080c0e100440d01c1c1c28000c506002c403540900040003643c071118070740030b15000300282020b1440c00003000302010304184201ca010103100707101004080203001070b2118184048000da5280035480004003440780c6c01e41205160300fa0701e4000880c281407403030340d00303060f88007410320301c071002e00c44103c5601e1070103a0390000358081d050542e00204c0300c00c200040e00813208510140d002c4250001e00d090195002151140f00080c6c024001565244a409020007128011000d0342d1600d507040c0c0120f030544c1d06560345a00030540c005010485940d416280301002d007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 768652679 1250 768651429 768651449
    0x3020315090109080a032711280b0a020f0d17130b041101030608010207050607030915061d132027090706020304060801140a09180506060d050601260a030201020d06 72
    0x807c80d40d1b883e01c2c0980d8210260b4040c8036041f01f10012180300d40100d98203030f1400024500801c2e500e001302105503001c031a901006014040c10380c1d52400340003503032880b02070007a10781a080f040022651000f4100003000f01c864219418640004200e41c1800c00d8051405500300c543d00c155030400241c02d0301c0c410b43c01400706e603104003c0e82000c10004609181c0002e283e1030080f5041ea80c504080c00300840b0901a00c2505280100005503c1945d052024007901100360032041560b40c4500e8507111080c20344007900750303c2400e014843d40341b0100304075541c5110061a8400800510166006003465084000c580e1528401407010304035080080000030301a510096184c94103048000b0440e61041c4240c02c181c0e00c442e80c04440540e00c280300100a0405e030403081080351a5003400907070402e0b08800c02d440b64041c40000c07510608048002c4d00c07141e6001802490564607055200e0240b40c8080010040c0d0a040780d2800d131150300c00d03c9200d0445009074000350300c0740103540a00d42101c000d544892051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 768653929 1250 768652679 768652751
    0x6180709020906041706040303050609040f020d1e0b0f090715030519090b1f060f18050d0305031b16060e101509050a050103020315090109080a03 64
    0x1010002011010340d440c80a0140e11070b181e100101c1d8040c041d6410400512130b00c017055180b981c10010341c1da4400d6020343d90501076034032641d05003c1448420f440103400c0344461741e04480581050320250030501d2250341c021075404440d021900341034009070822540540440288054014044e541e075400032481e0740500fa4807031428000e0000090503454003402d0644450010f4080c04442444050040750f4603018842d10000349450703c203007003085031029205515010300d0060214405034040c01c1e10380b292a42c010080701d140c41650f03007103d000801c201d00744e88980c020819441e1441782080a6119031500c039268102800b801d0380e0051242035051801c48184101e00d000542c1055606070b0b10b0704100006100300814510500f416001030744000d88030f0030440c1d03a12403c0d400301604022141d00d11001c1080781c45000c0d81e4410b859084c4406036041c5d100c0c981500d107100e2103140941e01705062800002d281c0c03100f55110380c0d40d5001500d0417008079580702d144d007070075090340c0b4203a030070800b456400c805030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 768655179 1250 768653929 768653971
    0x200a0b06180708180703030e01120e0721050307051f0209090105090c120106050301090f02040305030703030e1e01020d0b01212018181302090c04030218040506 70
    0x1024100802d150b04024988010640c2c20429070b00301042c02c1c0f030302000d4451880e141d0030080d01401d5810a60750026280160b1040b00c00d006200b040240408200a802400d01d020310b07242c4002042044c050101d0b0f40d05084800203182040105201d03480360b07015003940724a04202103000303010010044a294010000600c240da19158400c0c10350b8070494048116458803905000113000d0381504458550f00c1340000b1620a420a010303504070388154030113128064815440c10103a0040340700042480e4006c1c061342c00040c1c001d8015544440d0140b0803910303040c404200c2c007605242e5400501c01280d500051909002d0703494041c11260b42020300340280f2091584c0148a1107410014000d90100e5030b40200010b0300e0703a103211658024100e10311042c0c5929601900750044508244c40380d00c1101c1c82c10700c2d202c10540d40360036548519a02c500281c070800080d000e008940d1030003800150016010880417006a80304860000c502505030760501c05854645072172840d000016201070010802c4088641c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 768656429 1250 768655179 768655219
    0x8010f03080307111b030705031b0d110904030906170601021507051e03060907141c0204030b0f040209060105040b0f070615080a050601051903060c200a0b06 69
    0x81201c0c0d00c150055500c3d95030950813524000c03e22042071040c0200781074111101549290101d5054044085e588619036920405590b1200081c1c40860102000c0c81852035150075151024aa8042c2c140b84004140d01000104480c1c0101d8044000c80d0300032405010320b550040302140d458041d2046040b00e4200b01c00080d5444001d0340c030503412640d000c000510303000c1c491003d480c0117800c14040001200c034400804201ca420442d40315002d64400000903071914420981a2006028a00501d14003004d03070040d40e00025608449035980c5400b08030005c0002c600c0b13401c0d01e2194a102201c04840c0c10305204108044402a20050402409120510140c4924001c6540d484581c8031100d44c4e5950718030382030000d05020b1680d880d84400d0010300003810107000c503001d00807900c80c0b0180c4c0c43c56a01c450401441d4204014501c2c0300c01406841400020402d40c0003445030601c0d414003481c00840c8656042d140528045c40c075607035800c00209002007081002210781c00105c111018421454002c26001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 768657679 1250 768656429 768656459
    0x450f0f010509162102060d020717041a03040c2102271311060c0a0c36020c0a080406020709050f1308071203020909060d03080406020a021609050907060801 68
    0x14401066100c8030703111503800c0c1c00c030f00c602c1c1366010348a40e48404c080d0b25403030000e4001d07404c299500405402c04880712002e0b0402c031001d4a941455204a80c600d4030b80e461116000104116030b41060b660000c2128010428402c0c189203064070105208aa640305115500c44140040d001031803a10b5040522070510103100c0754809501c610480e020f292a0410010380044200030580050000501c134250380f0f0049500c00c521401011168500d44e0323102048420004c03010750b6000410000581c0c43c0300c1148013410308805141c41c50000d0304100ca10101e007414080c1c011800c50b01220001703400c0081035014010900102200075042003d85081e01c05203120440040043c4803100038404a10304205c0c1400c01d481c8071942000703000781030090320070001d07000398030140c00a40b0640110000401c28540f03904803110581d45907450001d251160b98401000e034011134802019402081031107254070034645038030b0740240803100b4041042d040c000c42c000e043c02c01c9604144100164080140419602c0400752 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 768658929 1250 768657679 768657689
    0x130f091e03080a0b0f060c0c0108010b0309070510030608060709061101140a090303060f3201020d030b03011b050d050601090f1208090d0501050f450f0f01050916 71
    0xc84c40c03108807000981d0041d180718003581e100314045440607003208000781e120b20404003a2204012662a1085c98507140000c440180c2d00b6440803400b0b11550414030000f807003280c4281004a001511560000e007845000c0384d0180000f440190100b1803260301491000c8400a41c0000f0001d55072031164400485100601d02c241094035580808101807084d848000240100f041032407500d51520b8480091280d43c2c400d1108084001900030404407a02d90306164418058000380204001d2807015005461804000381c0e00d550f0b90f4500710035030400c4101501c45100180d0700c40740d6414a040c9140d0840720064007641c1004111803040c85004103060350394041c0e03405080340c1d802c80d080b035203028001c5220780713406036410441020722503007003250540015004203034007140d0300300a6907400121014242c0c015014440c1d1100c000c503c1240441840316280042080e2540c81c1c0e40d0600ca40300c040ca0689601c454800c194020015818019400e214403030700902c000003e40313500c900e000192099032640c1e02031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 768660179 1250 768658929 768658931
    0xb0f010c08130b19090603020a080622020a030e0118030c171c0b0f0103090209060607030201020405092a07031205090124060905010903020d03030b130f091e03080a 72
    0x160b415460a907038074401c014000c144045a8034082e024402504180005091001c20b10301c44010440c5806802520502e070300c01e64681d107903607441030300b0002c40c4004505c4ae80480310440f400306403056440d00080281450303a8801260359440e4607811421101036514000d000c2100c58000000280d100c2002014540c01c001e00c494050214020f01000341302d51a0300b4014458651402485011150042110b00300708031809500101048015030554804a400940c88602c81000803810702d0010003810762140030744001805e02d604c0d00302207a03c1000595580c049100e08040e1a01a00e848098040400045500d903500b400e60a40e40680952440c9001004454a90300007480300e0b00c0944c814101003850101c101c00002c4d070f02141c0800407080307005030703c0001c19028021503954021006003040b42c1d800303001c41040030080d0b1411002001d1070041e60744d120301c0340c03005621001024052041c0540c8001c03400034094029292540881000d101740003809000300d2481e80200c0d400041c29030b403062405c01c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 768661429 1250 768660179 768660187
    0x60105040209060c0a03020c131503034a0a080309040504031b0b040b070e01170c073c1110050415080f070c020913020105070b070507060b0f010c08 65
    0x40c1c3c907000302101c0051360310400000d58245640000c5c0c20b080200291071103005443c2d62302c00030303042d1002036003200071100d8800340c01c0000a10a031410341640c3c0244881c81e000038031040100e0101c60a841140b001d4105c6034401c400c004800c03d602007100c030402c442d283c02892424601e940c50707000e003070702e00b0380f02350340d184002014035005240c1310b81110306103880348508120b01d15004c98000e005132025038a288203c4009242c160007142070a21100050310b4106903003090105203c50743c071000b08071813106902400310781c0004281c50311500c034145000003000c41600090703181040c002001030300001003401c021804000b05030344040740082c0000c10b0310350358541e041d0420280c03041c2c41664060744204034880a52010303542d000c408240603a010001184c46511105812100c584803450040d501405030380101c1c0029411086464101c0e1060500a0801030701e078850b800c603420b0403505c01003ca0400a54841000b00903c41c9442071070048440783c3d00c2c40c56400008050300c00c4254001c0c00150006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 768662679 1250 768661429 768661447
    0x30709030305070f21030c020708250e090d030b04050f04080c01060b160303140f01170129210d050c01021c090b0f0c0901050307031b020313050f030601050402 70
    0x1564403200e84e1700030302c421820001042c030342d41d40380f50021501c2d40002d140c401d0b403034242880032603050201c1d0200c50041411b440720340c00f00031020035291035000e00003089410001c0d020800600345403047e178020340905541200384802500b661680c0d0325180c030551408040000d5002080c1180c0d401c15005060b8544860400080c180100400c3d04480c1c0721080204030061141d000c800f005519501c241d8080c04400b042c1c0b045500121800d039050003c09605d8070060140324400b080030150700d1303610340010621101c0266010a032851401540a110600e404085a6401c200c10107198010071080792103038103085801e4240d180c0d80034203020020040c000502c0044c0f81403d4045e202c240b141d0690101c042030075030140b2001828400302c101d90324000400081d00e0306814000761840b1f501485510380c42c0a00c80c10044030030b40e100070500b400380b41c1d07901114804019511041ca494105c15001144e8440d5462207102c04115640c0c001442481c441d05004000c0d00c0204849044030790a41c0d0158070340d00c1c19 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 768663929 1250 768662679 768662693
    0x6020c06070f1505040b010914130303050714040806011a311a09010201050705120105040519020d0b120a0203100f02221404020c0c220212040c050603070903030507 72
    0x510f000c1a880c0c2440140010b00049910413412504031820400203240c414090183e601002c0f1055480c0302910070480011901941259070703c125240b401845800c4207001000b401e80050b0054a203030341c040340042c0f040007040116031702468042c2d1101400d0510850f060180701c480c9003080f2841841c00070503110800980d01d50a8080c101c2e0481c42580c00f2441591a043c982240800d58010340c03e000210707140c0f40c010f00072510010210500c05200f6828407080c80041d1034094004000402c9080180d12074020900c09801041d1a01e2000320b520b00c0d0000402c84605421000006a6081680f000740141d0f400119861602103078074010074589070492895000f80902c916281d406c24102040320790310241320304d003c41640c45400f00d9038040c165140900040340181c200418899000c2445182135140590715420040c1088044c114080f0310510070030140c0c0c100000540e01800108240010002c64141181c064003003980c2003411441c065000420001c1144000f406000000030203000344060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 768665179 1250 768663929 768663953
    0x705120327031e121c050403170c0a0e030706120b1c05061b070c09090f2102061f0b0f0f0f0304020906040606230d06060f020706020c06070f 62
    0x300034261400c580a804400c685414091032030480c3e400351001e0005407078010400d0790b141c0312810701d0790303448101101900700060201903c103074203001c10904c1d107183c00c00c0340c220401e204644010900d07860351040b40c0007810b8025880c040c5482904003081c2400101d60020001080c516010300109001d1030741d10200c1e0304842c107070b5180811441080d1100d810f102c000540700340034001c83c5540344a01e840c040c141010300d000f6504010315041e4006002c001100c0e50342c00825a00c2d001e4002502c1191182d540c0004048404032684400301404964010301c1c1e80610031980c2c4000000400c10040640004800700000503001d82c0200e00b1000c515510407401c00415190503601c0b0680310b999881c0c6405910005400850b0100d05c0f0741e0010f00001e03d141040c0c09410704880c1c464503a285a1740e60305209142c1c1031756068a8044088043c00352503440364490280308020b06054031403140c0000f90040082c01c0c14080c1d0480c00546d404480b414001f9140c0078200d681c15038106082000100c55454120580030b9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 768666429 1250 768665179 768665257
    0x1030e030f190206071b060f1415011d09040f05060411130b0a0303121e0615080f0c0a11030a1e0c0201080a0b18041407051203 56
    0x400031804115403503800c03005280c00000b21811507007211103500201d80e110002c030380e11000143c40940720b50030441a15841c490f1a8801c00021400e01802e030780d0030b0201d0f003000e50510442d4440d002808110041d540340c01a20722030a2a102c0a44230080d12541440035410b0485402500c203480000c0500c14031850040f0f506920030159003007400c060034002d420100c00103600340704001c800f5541d00031101c144540750311100c0190001010500c0e40d103003a16421006103c2e070000c0381c1c462040700c142648045410360080841f42d000074402d4146804010034001e00340c80482481000c9042c0141c81c505045c0c50380e40205401442940e039922034804030758480e5500f00410300c1e8400854002140c03504007101804280c401e841c1e0000d0103450240848001c600300802038040741b0908041081c1d6990758001080388540685540d610280742007512180c00012603098503031480380c0c1c07500d42c1c03483d078240030300c1d03005103002c88051590312901e0074095240c3c0300302d0310b4101040c2e600790ba50100d86074407500c0f0100c10344 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 768667679 1250 768666429 768666433
    0xf080a03020c19050c0f01020d030506040626070f050d080a121b02120a14130f06120e0c060301090b01121b140307020c0d0606030b01260a05030a03020901030e 70
    0x85220a03d0503160031840201d8181c090f50428201718104140d03114003202d4140e0040544103a488800c1c0c3c01084003601194000761503c4021076800c6815045682400101100c01404518480e0382801c040c9950003008049000440030480c0d03a0314900d000d55140e03080142540d5030002d4400507548a0071f036100c4d80300c0f07860800300240b112010028091503030302001d80965500c80b540c0d00c2800270522852801d800400c42c9082e007024040c0084014020100103c10302e0355030941c030390006507074105280e481880080c0044d08090400590fa0007000340002d581d80041100038116000075015010501400c0740c803a6803030300880d816a20030301c7c0a00600b0604c0004000c0300036001d505240750304072069000042004107010700e44000c00001164442e00d01c0394041c12090840c00c0c00c0082c405920001035902c6510f415000c00801c8490305135900070000c104240340c2020410160401101c0da251f00b0340c0071904400002c00110f032001c4220b031031070b544074517005a0b0744031800016801403e075401102024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 768668929 1250 768667679 768667693
    0x91905010b0405120f10150b070501020a020717070e0411041122210302070906080a06060b0a080601050c21030a140408040306050a020409181203090f080a03020c 71
    0x71040c1000100241d84081e10500002c0c40d0042d105542d403030400b00340708590b0340f001002d900a041107900c112031030041040c0e100c00c01ca03035031461128180c02142c019502c076580003580f03011954041055000a20520351070681303040b003c00d403c5844c4c0c2c0d01d601c1518600c0500c50300160410144600c41d80fa41c01c0b0040c410030405003100503a141e03c0d000046003545201a407201c04018270b1a580c05041202e100c441c0c000329461016940803032080301c07500114150700c980034000c41c60000c5809007101414100009082c000c0700c508202c000d48030f065101401095040140351006580311501e540e001200303003841c40c1c1e038100442d0010f142034858591941044002d145480d204107440000358000c41c0084420b000c101c400b010f0003440c800c3c00752002003440034208030402c006001504410b6005159090050500780d4414001090358072940c8819071b03c0540110702020010901003d0541c00c1803807808014000045e5a21040c150401c0c001501c0c4100c0170800600c035034801e8045814100050342680d805c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 768670179 1250 768668929 768668939
    0x807090510090614070b150102010e07080604110901080c040e07080d0801030b0c0f031b09040e24090709020d110a0504030c1d0403030c110f100b040c0e09190501 71
    0x14500b035010300700c00500030350802d19010000b403080d5a61550031401017040ea4440260511f0414090341400b4150354a60208084d10b80707051240c10300034074005d0040c1286140c0b07032502203039900d0000513861181c00508018844000e0000b03e80d585804252000a450000310110614155941d4080703d01441040c900c2d204041c4e0002846040b24842c001608140d1034010a6083c6406aa170f015884148188005502c00320381001c00f54920600d18102450042c900012800340c0b421120044d009600c558194248495907420b4a0082c42c1c411814001c41e017840184951941c50502c94010040e40106000c40002d6160303200030103000343c200f0125030780e4070040740161a6400a120642c4c0d607840e60080010384d1003410300501103403030180c1720b00d40b100e07582c95a040e002000d030b1402d00c0c410442081c4110f41401e10403c2894204c40381034008003148043e0401082c141d0310301c407405034099420300fa00310700080e400030000c041d0a18201c5248900380d0756443d91410074030640e0884083d00342031800002e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 768671429 1250 768670179 768670187
    0x52d1e010611061e160306030c0605030402010f02010615230c16170c01080405030903010e031c0b060a08070212032d190507050c060a050a0b0901060f0807090510 71
    0xd5100748401d50f40d81e90742d200c507a82c503000401a01d800030703110200009800c52482015010045e065403c00203517035074980d02c801011f10071301d400590105500005000a43d0380042c0240003555a91000340f1030036082010303001e8030381440460642881380c100043c00100001c8200304400d02c0e065800d1342d8a4600030603210b40c0c0c034a2441c00340c4038610303003454000c214128581c0c0f0440503160210010540018018011100303070500030815602400180007200460f6028010b504009103c04020b47e290000818048402d6030302041041d01c241c40c111500c4566151a8251110080c2d24102a5541d075602c10069040250040703408001010000801495095035540040e0420001004120030344405c443c0d854650000c4d103144441c12075608541001034910b40210747c0c844101d2070081d0a001d43c10310094907085044d00c100382155100c20401140d100c052189502581080b61b444200f0b5241501c06081603100240e607904100c0101c0008100314007404d41100200b03c0900300d000000038035a0010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 768672679 1250 768671429 768671447
    0xa0e07030b06031f1407020d0e0603040305070b0f01090b0a1206090206090909030c071d0a0906020c071202130209013c020f0105090106060e0f0f19060201052d1e0106 73
    0x5c0035064140e40071030356117840015090300c4403480d03071a1208650a90020024503802c01481281041070410560303000843c041200350240c0c84824802c91594104009a000c1c0c0340f0145c1d6050041101000c1088158480c007540d01c02c1e55009600000c03007807514004601284152802c0c1c5410291080a03c460b803d8008000c041e0300c0c0c10351042d270b45415110300700c04115410034542c1f001c905203804003081150400d68018a81140701d61001441c2c0000b20030000d0400341c1e260302404026000002c000c0560500407800740745c3c000151001c6142100800010f0004400c007403860810101c8042040c0101920803041441503005d18000069a8101d050003541c80a60282042c00c1c0d500300000700300000c0050199805860940e26400b8080d4400781c14040200003c405a0783d0000580b008032801e5160b041c41c815044103285c2e44200c01c60704207030029003035480c003500b007501400c078003003544c00ca041d07400088602c200048101ca2900362520242e460301941c060b950840304a04500000800301e401140007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 768673929 1250 768672679 768672701
    0x30309090b01051801202d0106060503040b2d22020109091109042f1204023d020c06040825030501060b070204050a0e07030b06031f 58
    0x60044442401c011900c2e40600e0b4401d4140211119034000e4a60241050304208842c41140003540080c60041502d01000d40341c00354090650343c0941c0c61400e2000500c0003044100300c0007449850310b0050b004126200007007010344915081c1000c1803800080d140760b212000030000209410313a509084644003980c041e03c0085d4038440c5a04500000e01c02107000b0074a0703a03016103500000c94900110303c0041d1000c458082e1148800300500c81c0b0340d070343d28420348a807048020aa41c11540024205800034010030659038005030040c480030440340300c10800c081d8040c3c0e066403040d10040400c0410655482540380c00844144500760a040d404c000719004040d00169900f03c407042036414080c01146d00c03640c01000702d03541043c0c1c141f46d0b800e0b40c12280d81592000c009075000e08107a40790ad60030308592131070f001907040e5180011042c007545002d0081540003402c0100410a150031080000d668012074400100940020000a45160b800b84004210007512000b442036074603007149408018030f001c03040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 768675179 1250 768673929 768673931
    0x109030504060e040507021f020d05010b22381809061c0807050c03060a050405070e240325090e060606031f0504060605190311041206020706020403030909 68
    0x1030001d251416001749401030115070054401e07141403001c0301010040f0001c03403400c5260200500701d000e60f90340c80b4280c000c040030b40240362640201440b00d8000f031080e09944003a000b402c6401c0c0300b49034008111400780700190540340d19050107242d03004001107907001c002c40c0b41980031500c400b42112003000a00c0b03004c002c44103800d07a5507510f07040040d42e425070303e006030044007680c1a08e00061003013001019903074050b40840e000c0d0f1019a0000b454454112200301c0030a868000784010404100801800340c420000140141e01d0b0100e504090f03903840140c0c924900c42c82c01070715031003070324180480e0b6111450f10481c01c1610100444003147c04420b44207100d078543c07511000010200c0c003c1000d034002e0000400741407668590340003c003600740c400507004181d80d00315080018035586511424000b0580d07500c030309407224504944811134411000648040c0740c00c207a5041920342a080880e01030b2000500569007842c41410005d0007802900002410300c0e200240120505800162420448030712a40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 768676429 1250 768675179 768675197
    0x20c07060201060b0d051b07030f090e0705031f05040f09021c020a0e04152a020715030c0c061d070902040b041403010209040f0e0c03070b03010605130305010903050406 74
    0x10102d080320400d10919241000c2030001d410f0440042e00f096422010015218003256089800c41980307900680702180810151107004820170340040460740208094111a40a032034000809000352100801c1c6011022040f9034800c886a800780783e1501400b4046c00070403048007224024070003440e50403000d038482d0b00c850090111880c0358640340c031607599015040030107907407801403844803580c070250080700c0741c2d80301d1061101d000716548100c0e80d04000424a800708400400200785805c0c1c0309492980454008800610900c0064503817049246118600000c1d84102843c00b101c002000c958000c002030309013203404080c038010904076651000034405485c603044d5640d680104a108030301ca02480380c0c20901080120303038148033640e80c07004c1000c0c1c00940762202100004044034501c3c1c40100035680e80d00c2030008079880822510a0005007640100091b0f4184141c20071103010500c40c1400300100000d00b144c9500500c440c2e200115808802800011060314000e440ca4005000f41c0000403079030b41e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 768677679 1250 768676429 768676439
    0x50c16080c03150c0708090d0803040b040c0e06010e09070c0b090a050c030601120b070c0204090c030b0a27020d080c0d0f03090b04060b0103022205030f01050402150922020c07 77
    0x4100540901385055402d0710f4000240e80d0a07000d500b01ca03003080e40c0800d02003103d10210300150300652042d4801c0b280821589841d19251200b1240c3d900282d40051110003004200d91b00090b41d2410100308036098407a6903a00c11080328500140000101681c3c042c0d818041d00407400610f0140390f81c031550503104c102121400b403640e1004244164800d2030901c450100c003003601d8003007050304080d0500e0040c4884039990045021707214281400c0700c500011400c10401c1c00b040224043e00110ba11409000e0750620302070034080044914181a8461100c0720f142c0210340e0b500d1980300d8070a40c420f40640d1070b0703000400003588807210500070031302080030840c2c4100c415121740b150110703555001c016000d0315141d80d11424010036550000f01d0625608010001ea04040546140010b501c0645400c2640c1d0401040c5414045200c00b482466030610040c80700680e6086a02a00c82e800e02c0000c5445013012070010f0800301500021521240380fa802c84041150107400402c00703840d2450440340c00b241d4071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 768678929 1250 768677679 768677713
    0x130e0c0d030203070303050408390601050a0e130f0f1704030209040813030519020a0e01050f09150901030f120c050715020304050307060504050901121101050c16080c03 74
    0xc41000300160070401c03980e0000b81c020fa02c10b42e041800f40184a007400c6105403940b140801c91b607140c0d2040d02410720342e091144c1c0d0aa00590f0340c020304501411841d40f41c80301045a0f250280951a09010280005040b25007841c401d200559081280e8081c03100c0c09080125030075040c41025904003200c829541c03c0307801d02c03000b1102103039805400d40c801540c031500d603400a17401401410324011841400040070070f5040080e2861403c0300c0c88031003010751141c8104010050703154082223001341868010060b60b0368a40c1d0f81e0446000c20b440c015055640e00c1c0e04c1c1d03c480f0343e0124420780e0018440d0300100510003528051a166403003046502d1f442074909806503614910150024480e9001d100180034440064a42c01c40c4141d45004a03418541c41e100082c4c02e0500540007030000680100d010009494200c0306540144103504502004a070f070303501c0312000e5411030484c1c1d50621400080382004100700f0001000e584501144c80240c2c29240e5201d0398490b011034601d01c3c032030b1088401900251980e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 768680179 1250 768678929 768678949
    0x4140102070203030318211c05060d08090d0b01080a030f0509090a15120b060f1504121401090b0601020f1513030302070b0a020c07140d03110c130e0c 66
    0x40003103085541d03081a4800300e812a0b86c2c0d41c00f40b40079140504048a0213500c0511070301c69542c032603e880b50884002102000d17071103060340f810745041200f4410301d61079413078200d40c0d00c507000800203559500e10b5012501c0301454400007407007000480000214420003007486404944030795141658803083c0c85040b074560042c10f110301d84c0003c102c00420002d01d03d42d0f07c40d80c0060032000190082c143d0301d1010390b1035002da942082e601242100d040102c00c1c40c005941c200042c0c0100c41c0e40e1310036181c00c413903042540200d02807804070459020840e014130013508044460041c010340244581e00e400e20705100c65000590f9554090312480744002c90030800455210703454607401142008903595544041c0004901c0841582855800c00c0002c000c600342c1d0102511030310100401582d207000400e4003c2c9040d140d0307841580801c99005942c1c1aa82c3e550303203a00c055603054585005001100712201e030800d8001508554000b09000310386030192883d03041001440e54000590b104414008280f10103120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 768681429 1250 768680179 768680183
    0x20a03110304020603241c0606150c0803060a12050d031a1c060e162c193b0d0c0201110f01050117060702011104290f030414010207 58
    0x8020b000195011b600c1010301500070b0f04800081b00108003503000300b0ba0304a81c801c401c1104081c01900c40f028810307140110340080c50f4006500142c02c02010f4003d000e2583c040008010200000c007007459543c17140b05540c068102412401c6102e4103e140030741d960754821100c4004207091801030380a2480800044000e0100640340400c2081c0000343d001301c80d10100400c44000b80d0301d0514209905003084a2404e82102c003000c0005076091840442d980800510143d10516442c01000340b401c40c60914a5004180d4880e600400c0c4240c3c40303880c0c041c00a81e20490840010045000c082040640301c84480141c00b031070300410803814594664031000424003c502050f50b812000340154403508031810005070842c25951512840310b0440e09448080c0c1c840d032103008035102c2a8010000a0146a0704581d50f40000c2041c260b805d02c09441c039010310300c113000407030342020140403115126240d40003d01e2441c0c03107441d5652000450320080d5810a4a0640b41e92805d2441e9040c030003014400c50701c4140d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 768682679 1250 768681429 768681439
    0xa12140115060309051603050304050108010806040507060309140d03050106111b0621071e180608061201050a1b02070308090f0a03050f06190c050f0d110d020a0311030402 75
    0x5080a01c00d601031310034420100c0f90f074401c0410040a115202c1d08503409148180003865803546000b0005001e0001038212402c59000281031100040001560350216000c5050209941c0528100341f420114060035542443c00340c0c80101201680c903520080c107070350140e100d040b40001d680c1300382c81e591401e22400c20303c04070307e405080c02c0f20f14000c3c002d09590301140c14041e2000b007104100d0081c60070255200c4012440310200700764031114541409480300d40c0c0345411002003814220b03440c0c0042c0c0c2c82c80780d10305100342840410901e440d0801d0900000003884020b00ca1400e044404000400605561013040114000c441070700b144003069841c21250480310083c20440040208804140401015544030030108000000281d00340280b0a502202d41d01900302c516140c6003104440c0c01d20302c59001c07014a0106031203600c03600701c01500c3d14200d40d0f416140e1a0320264070001e008241e203050040c5510004101c0580c510481c0c1c000748075001250390180102c1d00c00f1f000f1380000e0302058400039800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 768683929 1250 768682679 768682721
    0x3030f030411180723131a070203160302030601060e13111303050a12050a05040608062d0f1507080c03090a0308130b1c0b0a0b031302030616080f04060b0a121401 71
    0x1c7c0c00303142c1888007190541d030801440c080080d17001a2a001d10500d074040b48001c8000d040042d8601409500e004045509041182140d0300c0009007001c607030200300d080a180e43c0c81c1071494802c4850143c40034a0454010321110948a082643c1d5580300b901d81200c164504416100d9801d01c21401c1e034101e80c8168032504d081ca030074144c054a415a00504458201004000d1827903484050351018990020040032001c3c00000c0700148040d201a0451f494003444182c3c452004581d1800100e40540d9040381c0341c980c40300340c414031150070f5100e040e48456002c2078241e030210a100c552070050021900200004103080d60300c207101c0c000d07405444503a1044c0851001924070100443e04880b4039500001c2c5100c10027916461900790301d40060300c030a4080382040002c6070440c2010480143c20100d070001074024a0a8000003d085210080c04250030703c0280020504004050700181001d4900520494120b030301c9507564095801c00b80010b490080d82080c554100180c1840b44440384042c0705c00070790391 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 768685179 1250 768683929 768683939
    0x20a140d030c17120f10050a06050a090803070308090f0106050102060c071412031801051006050f070f0b041211120f0c0f010204050f03030f03041118072313 69
    0x1000014002c02d0310005101c0007a5010700440300d000300040200725000e01c405050042c02c00d49800c0c2c00900c12400ca95900130705024031f5852404500c1191030601d4401e03610a03140300c00701c2d01c042250340045014480402c0c5c80c810143c00c115014862503000b02114025211644802e0036200c07540704403405130700107001280c0c40f0ba03100001840158040c4101c9541c240441115524081e00d6071800741d001c20010003844a2a0300d89003a0007880c0300006c00070700003824003d96075440c141151092106210f0005010320000c40450f0035034803490303000f0000d00700d02411400c0480200304c00302c50841da0f90040c0200610034a009400c10850140d501c0b00414011604200c0681c9941c8410240a8190381c14041c80c51401400c1240c490800340030000507888a2416061240c1101c1e0418a24820741003070041c0140a01d80d8016650b10035008842d607141071403540c01180003014840d00e00c01460b4080d13003c0183c404d0b084408032a1000090130340e5542c455a14045030f025010703042104030100960380003004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 768686429 1250 768685179 768685187
    0x8130f0209070c1a0411041a0405041704092a080612190f0b0711030a030b04140103030e090702030a020309060310330807120c0201061a0403020a140d03 67
    0x15118882d400d0141040210383c480e852044e2420b034a0140c101d00c0c0300d0411007041028410600812000c0d5018040e025089000450061030600300340d025036900c5000500740440300d00204244920250840e03030361600e4800c40400b41140141c91100203160000c9500450ba07803000d0b01013000c10f2551000c2c11900c401b002c03c0018513849440001c0392042c1e04010800a800420190140b403103068160380402c034074074040b44184c0c0010b120805201c4201200d550003032003c000c0310410070641c540001e86220b03d02c00500240b00158001c1600c50014001101301600030300c0840e0b0704e0134121012820341d85e8040080380d49108603e0f401005170000d0100350024200003002d180c02c44101c1080c115019281c040d40c1c0001d110200c4800112105400f007504a480707119021103808a240c501f13020340b0303e403d0801134950741034040e10b10082d9603141001e50601c0d100b94016006040d400205284c03c01418985105a4000307000c260310070113080e880041c820482c2c21506125100141607500d440c03c031514166 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 768687679 1250 768686429 768686431
    0x513050120010203010909031b02010207170307060f050a0b1e0f240a08100608070c060b0d0606140303160f1707030302030a0e032109030c07080a0308130f0209 70
    0x1c00c203105002071120103000d0070300240d4007a01c9003001c0000c81c4070440c04c006009901c0c54006604400440501c0009030342e001c0345880a07544ac5080d50300b810b1a203030040074a9881030740780c0a0a81441c100001d540f0f1003039900701e60700800f04200144032184482d410804d4001c0509861a140c0182004020f541c0c103190242c1c3c411000300414210741d8914800e0b40c18100c9040c1c03503c040884400007400850141c11042c4150803035007120581c043c1904001c00600790344e00203000c120034882c1014140f82006015041010003107800f510301480390440d031400c10302502250040c01d445440c0c0040c003468505002054403d400c1110300012400c4589403140e1580c0f00901c1740c00e0b600414268007020481d07103a60f004003d0a8440e0754011780e2880c1481c03501c81201c0aa0500181ca60810091051600c1c402d41a100030706805081d82c251644590305268554401c0900003e8140104c0f000018000400700300505a940030b62260760076548d426447c0140190807080080420b4000e8407100d0140c1402d410302 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 768688929 1250 768687679 768687707
    0x1e01030b0a120f060518032a0a0309092403020607030207080a0803040c0504062d1e030c05060903120c03040e0f0a0608010e0a0215071b0603050705130501 68
    0x1c100c4607150301820307014505028094a50041070105042040028413429030703c000c03074041c030301c0f4620100c2c0f600c1c0c0d880f8400c840744040051840e103101801002c00e500000d00c0c0b0302c010022608485a82d28010344100d0301442000300071403508642ca060740e0f500c1c002c0c00800c5400f641c16200c8103402d6a0030058030341c000d0b0300141c5c110310800c900822007490400400c0c2080d07004600e02600d0380b8042ca000003040c1c0c000c1d000030380a07900707001d41081820100419200c600c490400d00a480011801c015051070700c0740d500000121601c0f070550000ba1080c035803450140e034042d00d110301c40140c40d002031214602c1101002a0154414414008540040d0300a400b90702e400000f030701e14042d6910f0224203c040c0c1034440e036101c542e4040c180002060701e4811200144621301c001d200e20600d29001c0741d10745002e0400079028a61991042414000d11400c550b0301d5039000c410052269202014031420040a00071300c8c0109280002142e0503500960503120489000342e281c3c2c54290501e001101c100120b080c1d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 768690179 1250 768688929 768688939
    0x21010204090507092408060d021201020f0c0606090103230309060406030608150705031f05030d080f070801080d05091f02010519020408070e06012601141e01030b 71
    0x110781000980100b5004600513581c41010700d0030041c0c554280d80c0b070341a0314030b0721040a21680700841c2d04001e2950348520100c0b54484404c1640c0045186200c0019845449500c0050310302048058440a01900b0142a00700c4645984000c00e20117148002c0c00040c0c000d141800038907030440518104030080c2c00ca46020782e030400d13041c0008510150000d40016001ca42c599205206c0da400c20884104983d80c5a890440c803410701c0c100240c8544409051a42941e40b1504020308851407400c00c07400408001d001c89000840c1648000c000e03c905840c00c1ca44842050045091244100c41090580c0d44680207090038111012066070154000c8d80d18941003550303042400803c030713070614184d246100c5640000c40d540c908a55170150030614284182903080c03050000307021014000a1800940b408816444901e845140050302d980320001d040080d84c42298003410000303414031203014121030304004070000200c01d0034204070314030b00c0203c03100140001040c140c0003d03600c03982001482e1800944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 768691429 1250 768690179 768690187
    0x709090e1c11010e060403030c0203131a090604091a0102060c12130506041a01061107031202010213120201030501090506010c030c0804350111040e0406060b0a1d010e210102 76
    0x142c05003503d43c104e400307040b2604400d04003c00c1c0f503098010100000868030103940b515034182c03c10a46290940600b01008107130380030559000c8940011142c4860b80140040d03121903846042001070b05081d001c4038041c20350070901070720313030b5000082ea0f038020030700320521a08001340444c002200450003004201141a428160000303e2401d01030700c0d0041d03001d044520420300c148440d5040c009070603481034080201400e0641207407c0301265100c2983d45c4020a080703e4804514100c0c00380c022101a40915a11084000b60800d111041001614400c3e01d06125982c0c0e541a041d044031011562240801c0c00e4960340000a0300c14500c800b1a14401c0c099107050a8503000d0442000c07015000c403110500441e082501003010300c000c0a409002904024020000c070f01ca800d082900a600c2121002d03001c40011800700205a080100a00840150692a010141c400614020176203601400d000c13002594030000b544288103601d81c07a04084c09645600802041402d49144917807801720361554280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 768692679 1250 768691429 768691457
    0x91802070602041508010f050d0b04050c1c05161206020721091a0f0417120f0a08180601210206040609050a1203020c0909240709090e1c 60
    0x11010f0b00107400200b4082d0740640508401802600f03040c0c01c8800000e0800b0340c10002942c03007644003410581d21a0400a1a881d5032925500e40400402103030350000d5102c4410240e112007540400e00d0900650407180340c54144004260144d40d940075000b55200100384c100045481600100304052183d01e40c40510301d100081040301d840d0b40400580007680c4680c003046100411011081000034610b8000d18080c81000100726a1041d8400c0d13502d003801001c185c1e81c80f99000d2016410424807460305998414001c000745815502005e2100040341044000c90303128029401700c2100b0080380741c001c001c1c0764201044801c0030301150b0021203841da600d2041c0401600d841000d080201030644640740c0c4c00d03050504201c20070b0340642000700b001580c5120a0b0110b6800900095065010ba80344502d03a201e40c0d0500341800c00b541d241e08075607183c0e000c42912303608036074007514410705036542c40300c02141d1162030440070b9680083c0030f010300307a00c1954100c11650300d0018242281e545810050710520b800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 768693929 1250 768692679 768692681
    0xf0a1407200d03051602010614040c110f0d0f0503060f0103050a270b010e070c0b04020d0602180f15030a15030203160501021c081503210720010918020706 68
    0x720b0498000907201d509101541d007090088281421540c0001d00507070f03080c144a00c00322240c1510701d6100d96284c0715003481c1075000300340304c04403070f0714102c1500d060f0000440358656403101298403400240f51500d084000c1880b030350a6a020b2240104003088840134200110060030f4081c025000c40740d40c461404220034102c4c44810780d103890419002004120501708034415801c16070100c41e51640c5002045001d5a01c0241d410302c080e400001116030b51102e00100b0311050480800030101840020101d80005400c81515204001114a20300741c50480d000d00c14040041c00c1c0c580800001800421b02c08821a00f18800c40d8440701c411905103596500000d02c0d101c00c0c1230014a0070000c07034070240029603041c00381411150000040403610032110400a020700f200400907240e00a0b1044800803d41e018840d81c4154590ba040d0f5a038403032003030b6001d180035074041c900454001c2096400b074001c684e015402402e08010503190102101d141038a1040e00302c801e8140090039035402c0103540300103015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 768695179 1250 768693929 768693943
    0x105010f0c05010b100e09060102012304060605040504050c0405070513030320010c170c03040c060f0e06180108090a0b1303020109080a092903130501060e07080f0a140720 75
    0x20702e90f19141d211307100344103125407598023404141c11a418a100d10314410303a40714801c0c003800034042c44041e2595036030905000030701a0340c01c0f8070380c42400c00e020b1209104000900650002c0121010400c40d20340e40d4040e1a14803615103151040864140100080380c080c20354030310903152540b00001042d151506c0302c3d0854030010030210100c1d4514100c001d18910541e640b9030310850300c0714110f140d420710b81c40d10607107817003548a1501040803201c1042d41580c032a8803904040ba2010306416180da80004070b460600c10803411503400100ca16000946210300002d10424464120000928079140d145400200079060401502503640b5088000005004040100103000351607440c0c80361103003000a82400058096107400c0190450f01c40e0000ca18510400c60703030004044440303055820014988540036011540c4100744104c0c0b580c0800101c207070040c0050303224541502c40c1004950320b4a0200003110040d101c00c3c01801021000030741c145004031140c81c2c862080350b9014071114070084201e0b2400b03a07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 768696429 1250 768695179 768695209
    0x90a090c03022107060219112107051201050f04020d0813030305030a06140a050603060103200307200a03050a0306181b030905060a0f150b0307090e0105010f0c05010b 73
    0x300c41d80c10110811004d210202c050310303092001c0c169200103c2e004208845840b0400350805290300e080c2c0c407a6a81e00c1e01c850744c0103070481902c00c98030320b41802c0c0543c462000f485094050022100098003025040c8203061045240b21075092084c0c941c0e409010303120f4880b0070201d40403c1c00304451214100400d041000941c86a80c50641d01c0c60158102c1c02a10300700d40c00b403124003000e85005940390795084092019108141d4040c8d03140c0c0e0f540c400480c0030b080030004a4840032007084590304502c0c4110000e40c4101040d0300d074900641d610415000075401a128030b2003090700120980340002e88280010400f004182c540454195280d104040c029001682c0d82d0b6049a6102d1900320038440c0d690020040d00c069003410031440703040391203090303c605005292041c299510f0956a044c0e00041d80840b800f504404160107003980c642c04400416403080d240440400c3c4000400210020f50032001810381e0010f0f0340fa80489074110b00c055a104114480481d4555211034002403140c44203003091000031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 768697679 1250 768696429 768696469
    0xc0b0106031e110c3702060724020d090506010f08070b0d23061f1b0203011b0c0309050901050a030206070201020a171c0e06012304090602090306060a05090a090c0302 73
    0x2800c0e41003030300d86840001d00c44205c01d0396404c01e4000540d8848007502c02c40c80d0050b00500c4150b610b070840401440c245801300c03119138804030394020b10000c0d590010701d240d40b240d0301300d80c003507600d4900303450998880c1e1003001101e5028640512800c1c40e050044d01720300c1099030012802000344060b10104003903c3d840a4130185c8068108180c1e850803050b200c203400139051200c414117542d120020104420020003100e20f9100445590441d1000d600c03c580d8001d040290f00046e0b038402c2d400520f400390310f641c25800540b16a00200c2d2a20b800c0e51940d0494100424881c42a0700c0e540c2400125040510309a040d800784412500105800501c00c41c60303214801c070742a94070403d90106646000c80c00201c3c0003020300c4d26504090b14100012194103407600708400d03079242c2d0342491203464074080d40e01600b5001424500c2c0a030400c040c580103800724941c12010b0711020b40da01c01c140b00d400441c0c0e115066218108a001c00c403512200c2e80000d04a5000381c2d0100c6440c0d440380c0110b08088071003000c0d20403407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 768698929 1250 768697679 768697723
    0x111509060d0b030c100f1b0b090c1314040f03051e1c050103050604020616050f01020307030614010c02191d040203061b0406051308010c0c0b0106031e110c 68
    0x2d407600b4061402601c0c000c882c01d00007200c0074100286201c2900307a91806115030741c8984407100040d61b049a00d0158450805541c9141688030035407907400329a251030040c00c03881e17411481c5038000c1c0144243c0c24160040046a81e98688806402881c41c12060f41032010811111006038032510300400d294140400442d921100c0d9000c2000540300b032100f04120394508801407000070008038006e60095011103006032100741442035800c1a94014030010700c21320607804071040410040d000342d031045000303440800c0b54664604039112984000b40d8018000b507003000440005150045800e001d4944085400e014036480705003403c00b060300c03c02e1200181000500300000c600c0d081111603400314140340039450860414905043c107000303030b01442c1d061240104040701401203400c07404c00108404002400340c0c03081450301a000c600382c4502502c0b41840c81c000072408034040d001e180740c080e00c1c02d00c1542c121840c0808260003845000805803103032008020760100b10100304200040c1e401801c005081d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 768700179 1250 768698929 768698951
    0x310030203160806060d0804120809060c070620030a21060f0f1505040612020702090c0306101409040906140c1b0607050a0c0c03120f020c030604111509060d 69
    0x25154004204910031a034203c0e403040024040b0090b80e04075030182030030275041211460711759400d00800c188a9007210340499101d40c08030340080e900084820740d4440010420443d8420f0310700d000b0902403403a44e03510070010416198032400004140d8610390311883d450b4810011080d069074a50741c85040c0301ca020780710510011740d01c2c0300100c0090800c0b100900d42208181c40c05480360046114a205020402416030172102140d0101c03980c00e1341c020403109161814280246c1c0540041c1c0e003c9000350005c24880d8809800307038001c1600c10f11550b070702906141a40c42081301a1444800455440c5e86860301c118a11305e49003640c500403140e811406445800c0c50350742c081d01c9160200034290a0b0b00c0102413001030340d0044102e401c1e24245c3d01c0d15001c41c40305403c00262800760b0380c0c4001c08140c4003260440405a0000914039401c01c02ea09840c05000d1001c1096503c0109840140a40c0600403aa010503c1c0c00380351500c00403011040c941c20320b20071000081c0150068080b10804946034008614 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 768701429 1250 768700179 768700183
    0x6020709050603160e130c091b08060114070f06151a09010516021212090301140405100903180b0a030f090b0a020901031e0617030304031403100302031608 68
    0x41e12030b80c1035006101c0e0220b00041c5880762103007442030150b0110703010041416800151041c0f00295040000c0b03064a80da50b184220080800c0a020a02841305d9681e256520742318080641c080d15050703442143c10200261108485d6100c01c00c2191281408103040c0c001a000d4003132421800d0010020385c44a84c6468420320b44622000e2040c40040010403494509a8001e02954105098103020003031645891001c00d8100303600952155185c8a00898410442c210030000c00b40050300750b000f03102e401c0ca00065001c2400d0107a45c010059007000c203030b403407460840313902c178408441c0030740381101508070040d8021344c0c03c4010350004003481c8400100c90500ca90980220100340c40c61900401080301c0a8450300149130020304100e490540018950420740c0c8a60400d1207101c440c207292410300240b02409200400091141c0c0355440845d0801640248000c01035a100355050b444900724403a0041107130560f5840101460f5600c3c081d21004005a14108403407600c00c50720726031400090381860b83d054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 768702679 1250 768701429 768701431
    0xc040e010b0a0b0304260412060c1214060d030201091b0801150806130c0506040b070c0b04120f030201060e09160503070b071b03020603040b150105090609010c03020f070602070905 79
    0x11501c210401c01d21001411003844800544285400480440b0b0a500f04001b248500d130300c0b20394146a040d81d86d8003442102d5100304030120903620b600c5003400d1306c00c2c4e40c8010b503082040240b80324500e080029100c2c0c1401a45940200c1c031900c00010200803035521000c031101c0c3e031106041f00c074822100c00d11001e0001d10034401449011809407005030700d4640d0076644c420004081c8101c14040700a60740030800c1c140804c1000e0300006140c80c0d1141e88a024000c00d5030421101036400310229140000d44106044c122800da45e09146250584407031031b180c150f051091904201c00b150f40e501c500158020518412074014184032029005142c0088449a010760064004510a0308842010000c0403401e43c00c03101710aa211040004400c40007030207049003000383c3e00c06500a1800810401042580001c042c031810062910b0b8a03112100001104e42c0c1c05089249a00813004000d030b003035950300440e801719045120344100d40d10304500402c02420050706900040242e4460001440000094081c1c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 768703929 1250 768702679 768702689
    0xc020303041101051b0601060c1502040b0304022b06020c0c030c0f040c020708060c0703021513061838190e0307200a090e0c120c040e010b0a 62
    0x114114102034880b072582400ca0301c16181404400648400400b4042c4401c903012801001500c1a44da91402d01900c4034808c41000c80c0d40344882d07070300e86221458a1007620103480207580c4440c11079886a09210340301040780180581c404c445440303000d451007003041207050b581c801c0b000582c50703864602c89a4174102c0100f615030303c07980000c1c007900d1045d2614038240f2a0f00d00c040310080b40b441c00c402000d0341403000c603400c1001180180010000300112120040110b18480d9085948100058120170000041602c1411240304c0d0000300754080395482d0446110911001d1111065040d0340d0398290341c07868040100c0c2411081007030f100c04c00700c005915084600246401c9204240343c10f260224000024850034061160360760780050321003104000b81d8505030750001c020ba41640e92410401003904014900d00e00ca517101a1010500c204107004030002c1c1011540109140b00074030007000759804141c0308480c1148144414504241e842c0d0240920350b80c600e81c00025590040e6041c041040515000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 768705035 1106 768703929 768703933
    0x90305010509030915040812090126060306160206040206032a0d06090204140909011503080414010e0102061302030316120324030f02040b0406180c02 66
    0x204803420044880305d54040704503550382264411400346c03503101d41000c0c00180302e11641a002d06090801410010403007480082c00741e48012640e24a01560b000c0081880540c1c141403090503004031003081c01d8024401e00800103983c3e0600900028018500000001c2c056040411290a00707d5603003550800020344140250560b000107403040111490070320005036401d0f40c3d1084404881c0c02044104071011294200b004806004002e44070355502c4440c0000392081401424020794450307580f0f6501c0310300b0103840c0300201c0c04050742c16040c40001a404a00c517030300010642d40c0445641100c0021404500c04039081d402420000725105942c88806400c01c0300d03100c603040741107046950400010085400c1e41c841c44402d48040643c40c490440f003030012445607403041d610640050720104a80190174013040071070380f4560014254000503001040c04a50901500403072025901c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 768525179 768705035 := by
  have h0 := BRFrame.cov_init 768525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 768525179 ≤ n) (h2 : n < 768705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
