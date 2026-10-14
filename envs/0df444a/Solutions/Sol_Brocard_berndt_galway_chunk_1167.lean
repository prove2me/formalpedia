-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:33:35.43798+00:00
-- url     : https://prove2.me/submissions/86fe4e91-2ea2-4474-ac27-d242886c2360

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 209712230 ≤ n < 209892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 209713480 1250 209712230 209712271
    0x50301050f0609060d03020a0f1202070605070b01170a33020c030912030415020303040308073006030507030609051905060402010e04060506070b01030b01120809040b06070f050606010215 82
    0x241283c04a0b61190048d20b541c0081c94407101801480414180c41e402c000c1801e02081c02e07418010b40c0040c22440c100701e400c02c9039a498542500005009005000f4050700b502e03c2c140380e00700140452503611030080d003070a00c010800c00032400c51002100000e40c0312483e050800c0b000d54002c0d40c001d16400c0c00218184091841081040e00f00c801e1501d00d0341c00b0401c00440c80c0f20300042250804140da030029540d906240c68010718a56009040004000c24810b95403001907604508041303007911041002c41c0260040c11134001401d95900007015031041900000c1000020380000c4034040c011030035110f280c600c1903440c01c001003401d8002441504000300050044d80160b050007280107002d00001916038640002c181950721001c0d064454284080c010800c21070f191031480c0c0505040b4440c1428083c9039a115902c074015132105a100d1501ca2069481c240c44e0303903090740d200f5600184e022109110604001d629500d003524401c0c0140240c0940d43d9010980f081c0c894000d202c005c401c00001ca050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 209714730 1250 209713480 209713489
    0x30c0c09070302040e040501050402010e04050f06010c05010f06091a0a0f0b0c0a0c03030e040614060405060d180c090b0a030201090b09031230072109020a0f050301050f060906 77
    0x100348005041c0d007031001089104c45c0c500031900c03880c8601d00005a9003002e00015103a4940c40c0304a501c1141070808110500344031010041d0018001e086c006200106440d0043c050480704000b0300c4003901e8010300240c4141990482240d038903c400c40015100800018130144120320700821544440030101000701d00e0320f84000703286080058003550001c0c1c0c3d5541d61078000504a41c41540000c5012094480c50b241510483c0c0003480c1d110400c01c0d5880e18078011a103180158400c0511824022910f1201140180c000903448a0700c00440074000041e0b1402c0c2c01e001081d400307181c035194036050300c282c05410b00d1607180041da42c058484403211450301c04108600d0344855560b54060103425201c144007089076003d071501040d040d55a0303045440d4000c01c456408228681081000540d10038404116040b044802d035a004800303080b0000d01e041e80390840038102d10403000790442064a00001d0390441000800d00b660b40840c024806503c400d120b50b100c1d040300380e40c641d611414480105030217140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 209715980 1250 209714730 209714749
    0x1a090903090d0809100f080906090d0e0112050106260c0d0c110604150e01050402060306240c0a20011d0a030606030501090309080307080717070210030e01060602030c0c 74
    0x4103e032000c2ca000903c1c000701d100c2211910310320b130114540e01c0f86103041d0750704021002d5008401c0001052140741c2040340341d554500807500503080c8a40c45141401c00d9200d03060490403020702540031300c21941d45801c02000140c2c0b9031200b003d0700010400c640c0c0e6104903218030f54006c0b8003400440d801c101003295070400800d0303141d00040900c540c1c0c41c51300002d0402404840c2c80f035401000440341030f040082c0070314152003c0c0307504105643d161000b0400183c0d286000d990f00301c403007607402c010304054550840c28182c510000c8558070003404504030315140303c00220107052920840d4480b42a12501100308502d60702541102c2c04900202000180403414505c003a100c2d00e00103013449074181e503d495070001c807000345d042558140d446940c502c0a05810010a80c0100300c3c40000354901192921003561038002c00400030120b55600011400b0b221164094070038154000f80036100c81482030300003030000c00300080740416650030402d002a5650020040d18100e0b50004007400581460908000d43d001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 209717230 1250 209715980 209715983
    0x3030912160b070305010305161a070204020c03041202040c0f080f040305090a06020a02100203070206160c090f02030a110c10020903010207050d17060f060a030c0309060507031a090903090d 83
    0x551014006010882c0d008200d03010716503e460000d00355040d418a01c2c02c246108216504242c0c6031401004030f90700300d10301e031080e0300300d1169960b860384803d2002074064420513031441c0d140c2c8804200861401902820318411a00c200c40400ca0343d00c042c941900c404c00c2c50348c4100007148840300007800c404d450310050355100d4828a401440c4c00d042c1310004990390aa5008035006a100c0103440046007000c0d84802c42c15a101d000441c2001210f60001c0d0580c420b03130043c0105104810301407001c20005100c650f02500034400706200d10070003e01014000e42007100c009450a0402070030350400580f41c2c0c1242d2040304081c010781445202c408400003c0d41c400407003540c140d9420440c5501041d4144103c2e6003500007642c1d504c240c04003510020340e178004041e141e40e12804000740c0da400c1c03e6903940304030f0f08640450300b0003060441d0080b2003a00146210b81010b030026007840104100140c1c56400340c4008042410700541c805e10319003d0281d07240044681110310780c01008070035024504a0703903072050b09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 209718480 1250 209717230 209717257
    0x7030807030f0c02032508060c040312020c03100203061905130b0319050f071401120b03031b06090f0a0b010504150306140601090605090d0213140f0603060903030912 73
    0xf82003680403921740b540021100c0060041034110300c19811155403d4401090b03a00010400c43c1482e90590031310384a80d1000901031000014043e50060092021074280e10b40101610b898564103e4400c005e54801ca501902c24040120400e50b46e5404a805d0419254081c2c01d41242c20701101c2500018084c0c0a42640e1601c500da8683c02140920b03000c2a003158882c04c050500714030754410321843d02246030480703a108010200b01032031a981c8105c0d4412101d01c07200340845c015103914080703404d502ca15615118588990717000c1e245c0302c120000b0b000c0c0c01103518104a0341241920740e0b200d606c4000c20500180315174101c6004001516054100c02c103032403149070f40700c03240c00e07641d548010407035414014081000c55a5800c00401e9078111110200500390350802c1807034078101c8000219a0070903860000d101c0c0d451045148014102940705e52030610300e00da40070446080c40420381d400701d14101c0d0300c6032181c8903410021301418804030589024400c21401451600c04810340c040d103540120020340000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209719730 1250 209718480 209718497
    0xf0305150f0310020301090f05010e04030e010f03110a1e05090919060b0a12060e0108030d0f1d060103060c03060308030f15041a0901060305010b090f0d0b010e01061107030807030f 79
    0x8941c3c64070066009100b19130000030246214080c820645405900130350358000e46c8000c10021039044980d40c200c800b07092a20074190b00b01280d06a000340f0842d040720091500c08030701c441c00325400000800c408500120422000305902c507040b20648107404090342c1207211100405c0400b11000006203c54441d030784003158958a424500e180c030b42002d9040c1d80080d82c3c1c0081454080300510441001d0300c10440482001d60402e9031503a901d21070100102c0318207035102d03c88c0900b1415030340300e020034601310030030a001205c00c0d2005540d01c55013070001351202d40c13800c0a60b0011500a21803e000c0381e601811312801c5030f0300d10300301c00c64580006000d445c0001800540c41d115aa41d489650405007201c1c855103450b0050b00140404940d05030041818586444014040d0018100076100c00040c01c131000c010a0040708040b4106801054000300000c130054004281c0b056002d240e0780c10703150250388141403100d103184c0003a0b40b40c15a100190a00b001080b101c6d010030b10070165040104024105900c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209720980 1250 209719730 209719753
    0x504090e070e0720191104090804090c02010e030a1e030209060d0903080603011a100e030d0e1c0807020607020d0b04050c010f1805010813050d02030a0f0305150f03 72
    0x82e0300d0b048a80e43c0000d480300008680100a18400c120510281001844d801c6031464803005101c030082c1e0050981030b00140c401c1b0b1142d81d603400c01d020103980541e140c0c0e01c41d556002d9900143c02d80403800c80155080560a000c2042c000040e01e2611409031349110b403d8089200d030408800d00e8103980000c064080020300b01d507480b5200100400341e0710070800100070003103050041504034040c0c040c62203641820308140401000103120418104116403107140111b41030000e030f50828555140c242c02d4080c141280c420700d0f420903c00800c4082c03e40701c0340301003044842c030908011310302c40005200900c00c0c0701d20009070400c2000341030b03d244040c4ca2419072a90317945a080c12804112800c403200d5020403601c007441d5a00c14410812131030181800043d040320058003880e41072f82405580c2c104890703030380003c00c4841c114205800690b0460700f562402d9001000c000e40301d030b01c030800f001c0c00300d4419108008403c1c441d10503148200c2902c2851185003054804011021409509480d4180710301c0d281000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209722230 1250 209720980 209720999
    0x50403090806100302011409130b0d02091009240e220b06011206050f060f0906070c06090501080712091b0608040b0603010209090708061f080702010501080106060504090e07 76
    0x1809818100c07501c1c083c0c5481d600c0014042e041340c1e801d209012105010301080c2c2d403148010b5022408406c2c00105100010f000840d8204030036a4010758400f03100000c2c0302c0c2c4119001c1801040d2122032000b445603400c82000c070b40340c001a8441e01031380a032410340100403c40d15403400a0300b2110b5030031154840000f001032a0700300030300341c0421f5520340d0100e02400395642c0c2106080040391171882c4240401842e203c0011600a01c001c00305000d01c10004071003407109079000486000305001015262181c14a0030003001008550180902061200700b0100790b41d8080d001049c49696107550b08481c0c100c001c002c0c0c1d001b8201c0d0318421221642c0c0d10b460041c501d101e0401050182241d641c40e0384041c0707481e080c1040f070900050030040c003036441000441400e0b21a0310031150b1003c41800c0181c051784500011a14180700c0101101c1041c810200c64140c180d400f00c0c2c101c3c0a03415943c000c0c0b06130390701c0348001c1307080340c115214000108504000800102450b90416040000404180c805041d40c82c80c054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209723480 1250 209722230 209722243
    0x20a180305011407020106180b0a0902160605010501030902100c020f1215130503030105011d03070b0d0c11280b0a0e0f0a051009230d090503060405100504030908 71
    0x407150742e511a890741000398a100ca2299101c1c0d00c910085c450b03146171031800308072000c0c0201704098094942038040c68a0711001c1101008044640085654101800c405d07121644102800c5451606280001a4540c800d000e5210b820340c000305641504008000300f91400020118100d0300641c100c51000c83c0c0e0340d02c91141c150002c0a0a02070101d01092612040c515600205600310305408501a8404203a00100b501c1c1034035002e091100b010f014181e00c0400d9039130310112040d85480340313003004280c0c1100c41c00640014400001d090020324078906058070401e456049030038103684440047c0c401e03200d5100001c540040000020400815681c0382c0700d0003000708940891485485216901030804200001004103004c0c4028003d00074460741e8054079541d108054100c519100d84140040c0410700b00003130703803800742c2e0308800c4a01c51840444035180c0030703c1144040819003486000aa9040c0400c1d13042c412603000e000703802144401c10b04640109406802a801c10610f6200030401c448104100e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209724730 1250 209723480 209723483
    0xf03220602090a0b030408040332011a010c12050f090a03060518030f040608100815010f05060c0a0803090c12071814190b06040603060312170a020a1803 67
    0x26903942d000809014250780c0561107010914401c0082001240d100703410360782500d034400e0301c1078000500027921144070746110215003082400c240107980c4d60401548464070b1a03032400b900802c1458000010b46a1000d00180a88105543c145071003066100e07000400034101c415200c1400c18500c2f4010801d100314540086904940d520240070741c000b260344110304107140200c01140703000b41c015540c1405001e40c0c800c5a0900040ca4041a980941003030158003412114044621030030114a01a8288000713204900b1140d210417800301d940d0074144100d030406e510400041c036000380f40756104081c590005080911500449071461901c1d581c44481024120145006114003410f251521702075901e412a503081781c81c9862000364914200712511a484072149500b1140c4045d10840c501c00380110700d8610758803490011300814603581561001081e00d00440300c2d040d03001014602600c0ca4880301080e00d084062060000342440e0080d002001040c10600d4180003803100002c0764042051180c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209725980 1250 209724730 209724743
    0xc0d050a2004030b01150f030c05120c1801030b0a03111302130e060102010501030c0302090403111f0f0209030a0b0421030e0609070e07120209030d0c0c06050702060f0322 75
    0x1410002d02003600320407405400d50300d031400301141e055034001e804102c00400a805042c3c80302827441602c1e01030301c1074036120401003003506420318104440001c90380c4040800188054803007206202944a441910b01140380a800141614295158030050142808869601001c2c01c0040c5400070064009405041c1301ca4519100d118281074600c125800003d20300741c1103a14200040011921054020b001c40b41c040d541d600a41c0c0762400c0803a400d29410040088a2040001c840310701e40503005a06880c00007030204110a90070740e0060410fa200b03c1d415294140d004584010200d220101015002403261850564508000c0c01e503801c248804101200841d55407142280d04040074802281d011043c440500210350510010a02c1180054900800c018001031204421402581181d605100040071514000d00c65003000f00ba035180f41104444000f03412400103807181c040d0054030b0710300390f004010f141041039000714503150740c100418a4078016038428414204c40d141904108005000301c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209727230 1250 209725980 209725987
    0x10603050d0c080f0901022407120908030c1b19061b09061209020a14010f0503070905061c090605090106050a030314160203100906060e0c0d050a20 65
    0x2015030a100c0508100703070910024880490009030b688084500e180d80c0c40414a880300d0b0400c004034070349450080c40c2403400e601482220403d24036800501c1c86004207560701d03030903007030b5100145040e5a040c482c002d07c408410300204001054400161500036400c000011001d041000c150b890f1400c1c6040c403d18816210131440305101312400790085c15503100c101007010700003c1c0c100801c10003884c45128200014024444641241a0000d000c05a001041068102e840f0105020802d8400c0b04c024003090b10150b400400d540210300381c034429011501c0340c03000140b41c0810b0100640c01070714801f034110300520072700040702c0e0b01c0d20400000314000e800000c6d0760710308058410b0031114550407007803145000590410009500c041800c440b0161403a0301c0345c44007082d40410300740d0462500002d501d0701407000da6400e11200340c0e2241e40c1480c0508400d1040e50350750078034040180401e8405c24400c0b2010003000302c05502c5a08400d400002101c40001c1d550f00b02040100c00304400d01c2c01542014000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209728480 1250 209727230 209727233
    0xb04030e0a0f060807030207120804081e0c1626160602010b030c010801050d150b0402070f05070f050a12140106090204030308011d040f030e090c07021002150c0c01060306020c010603 80
    0x140136035910904600781140b50508584aa05240758200300020030040060001001c03c4510001d550700349010b2040f2049803400d600b4a941250042005004248542c02c8c01d00c3c110142c2c030460300c0c12030301403d51000503440c01521000750f80c0d484c0780e2000c500380300307202100b0700f00c1c0b01141e002e4008182903400002d40c0b000c8041098105074803c140e45041189200040c81141c1d103c03004920180c1d03004065a03480403c844110000d010301c0c00c14590301500c0850404240b04c0602c181d001c82c1c9225005403045240c5038407840700d40c12154001d403034100d54900001d0043c0f0308400d48043d17019004444c808007192090101c9800d5560780c0e041907800030f802242c10010950010041070150007034903c001c00c542a110480b0306e44035402400507000420055031035041c98050785081000d04000b421402c05844d1054107a0040d0b4843d8500f2400741c90190424811140301060902d240914031650070859100c1e01c00400c41a00107401c102c0481d5a50308000000482d51b1004000d228805030001c03461a155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209729730 1250 209728480 209728487
    0x151107030e030f2d070302030a0302060f010806010e0402040f0b3003030906160c05062406090d0201030b0a0509090d020705060309070905040f150b0901080c0105070b04030e0a0f06 79
    0x3d081441980e03010a8803061101c400712480919904031180c8a5060200b100c4001d140503d16072002c0d4050054800d02ca060640c042002803242503850244140707640d903510025038490302486601d2102d03c00380c0103c2c1c0145800e4026181c1c0244080001c5600c0d00c003000001c846200b0640d40340700c924891080382e202092003100a145d05e82e440806141107143c002143e075151800108004441d602c2840041030142c015419040d100f0303001800c8070328500e00b130040b18010698800d084221200300100140080c9130041c12156141009011743c3c125080360f60064002d0941c40b0040b50b800491903001007001e4446804107803203441000c0043c0103d81850b0740190030101c0726000305005103030420410800000c0003c02030119507031a080050a6507071414410094020490028042c040b00340b0841e407110384a401c24000444115200106641d90f20011951003a03100c1d69540416010b00425000c1071a00308041d60050080c18480c0c02e00c0f00c10800280e008005821003030710451120801d101d4140d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209730980 1250 209729730 209729743
    0x6040302120a05280b0405031c0203010503190210080a020f0d050f06040b0108131a01090f0c0824030c061201080d020705010923060a0203180d0f151107030e03 70
    0xc840c0c8030f07441c55550321344540d00e00c400d1119020b8a4400c1c1032000c41e0170042c04100321046a00c00c1e542c007805000703012106d18042c0d4030a1280900ca88108a01100300700c4d41c904c4031480d500c2e4002c0000125040b020740c180ca0595008013080f00c0d0960130301100b008503c1500c0146021581201c000034039107000000141883c01c0904035500076071a04500c0883d50340c104c84255003007032503a800c0507640d450a10b07141300c2508050001c01180005070b0000a680381d80c513001403040c800084001d12000c4000f00044500000c2195595078941110762021a042140e1420304180e41c23024081d5400601040e000c114644c0c000340c8140c5c071810908004000a00080c41400349180707080c130143c81c03450300d801c00080152200b4007e07210803d40b5030787c04140307507084158070081407000685043c0d00c6c3c40311120080d48a030803100c6550500e5000c02c02c000c0303031480c10f441e540b00c03071940c000c01d090b1020f202034640d42c80084003188203400c082e60781c12203000c40e13030090030180010314404e1341c4d8950401c1c40300083c91304048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209732230 1250 209730980 209731003
    0x160801020301061b080412030906080f0709142404051809330a0c030605120a080a0c08030103050304061412011502030702060c010c0e0d080d050606040302120a05 71
    0xd10520042c03219580c0208890000445403c2881d01d0f0788a60a01061034459648401480302500c3c0d882010103801c10800d0f011606540c0341d6503181d031b4030b030001d80a8845d4100c0c1c0800008804a106106848450450010540026226041d0035800b1440f414402580070002009040d0104007040540740020010100e039240051062060400e41d0240e940c448054007040d1034001d01c001c901103c103190105003841b041c214210002141418621702c0c00511000d0140030009040440c040344a090031100000d010740380100622a80d000740e25000031a8002c036a01c0010804560a440c02069414020b58061030040307001c2c0d603944e4600ba8016243d0705502202c500c0b00e4006206110003003159140d020b04481d01c0f10040380207103007228002c03400c1d44105940254444408900e030a0844c005511020120002c0d41382d020003220f650040004890032701c100102130601c1006403034107144a40c0c02c13450700080060724460500e40c480d40010900314050a00801c0c0e40c0c88000002e050002c10050004102c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209733480 1250 209732230 209732233
    0x905030f0c0c0a06080a051504180c05010929090901030804080105062b03050d090506060a06050f0703050d0204090609091a150d300e031612020102070807081608 71
    0x740d240c804d003c1d01c110002000d46610075920380006080c910381810352189400000c00804c03840300c120f116201070106820094030350710f42a50001c2015401a0042426a4421740305034a001c545840103218103100390000c0315811030b0520003101c00d074983c07008903800780d48a40341d8943ca0f10b080400903400c440c2e004001603c1041030210400a004254051340c580840e06a4160b0b210403050505071514480d6421068140346055100014050081500c03805880110341081002c0e079a040d0450320350280052111401808006003c0040d010b41c001b82804841c0040142c100350740e4182e90001c96115030701003802180c8502c0c0701403c00c0781c8000820007003818400c03000c0f050300300b56642c2041e079525510401c0c065080d0000d440306010000c80301c0c0c551007103403613a11100340c5140d400032078405009a600d01c010490040442c002840d010400400f286041441c442d9400d1501190790f00510010209070b0542c00384480c08184030b101408400d02500301701c030040c20b21400408106884040651050009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209734730 1250 209733480 209733499
    0xa0b0f0a0516050903070f180b04060302010e01050c0a02060a0507062405041808070c0609080c090403081510031b090f0e100816051003090f12030905030f0c0c 70
    0x7591516030400520700030345049030711141e504000c01d241c403116421480c501c90382d950000a402c8c1d02c0f2080000810002c02041c411075111400780010b0768890301009010030102c2d52014850b501c9100031b0042c4074554012500c020b01ca0303801042582c0e110805c1e01e4005500020403000f403000034020303818441800c0044000b0031040500c92000070100b4000c091080b44c6034903e035038400316442244104160080304076079071511075140148845200d03205500220710005000245035101094042c01c000002e004190250ba40d81d500311a0010000d0042c000a50007141407100c0d62168651402c407000030380c60021342c82030305c844450001001c0f41d01400412584039014800301d0880f03882003003218040708100310a0b403510312014100903aa600209294413a040c031003600e81c00c042005104807801070b1070441c224003c121044050300c00c6858003600c0301c1200e2a8400000700e404c00302c00e03540d0305030f031500081030580356036404c1c00c560003103400001400010a0b08211150140b100c002d800380211102c022 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209735980 1250 209734730 209734741
    0x2030403090806060906010809010609050a0f0506010f051206041e050f09162105190303050f011203210e070e060306010312080405030706090302060411030d0509090c0403050a0b0f0a05 81
    0x8178444024880d0f41001055404260131361025042600903003841c06041c4250f14051200c08003c0c00210075120b82c0c117080c6000300303c11354094005559244000c0c1e03500c2e072804074122980c1c1413000000e010250010303612a80300e45100305103001d00302011500d01c0d000c5082d0130301014038a0502000341051030150030a0b0303088002c01c102c1a515004980904074034a00c42d9190441c40e03c0d42d022407501c09050307800341307011409040c05040b039145a80c0d03201751003c20554a03401c201c03203100003003402038030021401e54440401290281c0014040c628440141411681c4880c5240007134455814800c03415500c0320340244142003442c11410350010342a00141059071464440c5c000340207110a8090500c030100c5c0c04103040c490300b030088070714541d0005814420b4501038500250740d20340c2110155076815180e0840d8a0501d404620b208021800b5500c1c0c3c0c0c10150035000304003001c00c0c007070003003481d102c42000b001001810a010501381c66014095020191411500d40307940030000501c1c0c140d8803444c2204002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209737230 1250 209735980 209735989
    0x3170936010b0a18030206030c030a05090604020f19050411070c05040504020307230a06050c0f0c010e010e01030e060c04060f0e031b0112050a020307030f02070210030513080703030203040309080606 87
    0x30056002498005a901c0346131312a20403500c00350700f0207074101d00000200960b100d80c45000f980602c4490300c04201c0c40da100c40e10240c40710016200250311244e04221007500380b40003aa5140707440e03080301c0d560350b040742d035030303000504481411183c0c001039080417a0003018045100c00320f0004004c113413000d11283c940bc0e80000d8a5020034084d2a0309122001c01482407900400a1078410002c003400036841c0e80e8807094040e14680001240080e070303104030400040e99a20101c0d1000b2541010b840701c40d000c105800c01514119030720340146040540e9140d10100d448801c0213014050b40040314120356031818104020240d500404040c4180300030102400303055103000810948040d6280d000306403c0ca100d9004a9440009403520700110f030409051055181c01c03030b4011806205a030310104454240c00038400141c1c042e100010758070803030010f901441c02d402a000b40c1d13404800c5c18504044025103036580402d5410940040d00006d501004100070550059403100140050200401d01ca182000004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209738480 1250 209737230 209737237
    0x109031220031f03140105040c080a23240603010c21051504051006080a0c020c12070b03070206060109050f09040f020103320106031503170936010b 65
    0x41e06003050f041950040031072604580b0180d54000d1600c1000c2d0b44003004a400b804d8103031380c15500c10050400000c1c5404000601d1088203070b00005e230400201c103052202c6800950400e2604450040038a0040e8580b00742811030a0300d10203505e260b03101c0c00c050090500312502c48910304107000d0707440d400e03c00000603206c00032441000b480011649607902d910308000701d1080f020b580d801905103001c0c8501407100c0040ca00917100140c1e250300c207540e40c0241078003e8480d080010070161300552048811070800c2050318a560083c0e104032081c2d40d941c0d070303010001680110b407000010b80208041c040c0f2981d02141800c020102121103070b40c040340c0d42002409000010348028001c110000941c4216406134001c4c40c03102c4440222541c0da5445801d0f0340342e42441074180f183e0407080e03010020800500034443c054100720188000101c00d429076807610482d0750056400310003854203115000443d96015100c845900100c8904c0240300540107a14008440d6101c12010039060440148200c2803182c055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209739730 1250 209738480 209738491
    0x50403050606010804231002031302102a0f0b010303090f050a0e0c1612030c0e0414041506031709130c1407080d020705060f1303020705090a020c010903122003 70
    0x411806801a003591404003107640d1a01c0550011003002155000d107845002c1840c000d96824441c50700c00f0f072302101c10f1580010182c40c020340c0940210b030043749070913200d00b2082c0701d030f50071070740003015602c505d9801a400da1003107000540c00d400030f008039029500d200c2c00605050307560b040240d007010040c1c18204402018104448008241a4500b2003c1d1864803540e90b0000000040b5001e9a00d00802a2400501c110040391919000036000d04092140500654460010703c00946403540d80d501039500c80008404060348601e00800031030802d07010100902003c1c00b00c4c0d81c0c0c0d009202d0501130310640c000c4803944020300c1c0040d209201c83d0401070718201c004c51940c007070b0b5944605103440c00c060701500c801c0546080c8045442c4040000015480b40140b01c1040042000c0d610448040d006400031f11004006800c075000411860500403051074100341c104d00c000d82001c1c55400801c1c2101c00031002a0000b0340d410b00b035020760740c0c201d1003018480c15140c0304440050040380021840b5200c05442c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209740980 1250 209739730 209739773
    0xf0305030717090d0c06022103040809010c0503030708071106150609060f030f04020a05030a03021f0e0d0f1101060509040809010302091c12050c06040609050c030706050403050606010804 82
    0x2d4489204440b20100c5000a00080c6844060055410b1086001c0d40300e000700409482900781d017505c083d1104020744250034400422524650343c0d03030fa404086410070300d0001d042c003048002220003d20144003540c45882295180036203840d103601c000b00442e5203405e05540c143c200100707201d04140820b500c900781072810f44426a462020314017068103440b03951840660380c1004424008a521548140f40c00349008443da0520307180c5070000c05032a40e40748507008000d07a00c607044a0711501e126402e14032840101c1c42000840032542c10101e802c2440071540940040d03246c1b8410b40c54150004625581c1031240c034000c00400c1d0604000c00c40c0c03400c0140002d40202030104a60403030340c2c465012100e68049c0034214405c2046c4115410100c030f1200074084030340c020a0040da0300078502c600151428140c09900506086d116600e440e801800c8000c0280c0c2e56014548803095251000c000602c01410300c2d40c1c90f00d949901c0e5003010350a00b80e001e00380d24104111901030201040890342c5118250383c5031003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209742230 1250 209740980 209741003
    0x501080402032d011a0301061d0f070c12030203060102061015050f0717180616060f0b1011100603020a0b0f0d060b041d040309090e07030212030301030c0f03050307 72
    0x4140008102c8081003103d000d609040c01802404502400d04001c900300707600901030180c880034072000e141d4504940c2c003481147c9100007942c41848030403c070b80020007420140b54070440e50b2a42c54070001410030f05000300382c002080c4442540d04000580e4824128800e2f640c140342004698441150949003c408200011494110801c0d581c0100c412503a4050b044008001c04491140840e0f00411480740c00c0084809003144c05040c03140803111390801141c203403000c1241c0e40d5507002c010084118540301140d81e9000d003500948620903120b04800040d01c581144020080c0d000f0728002200c822500b0050030482c08000580b81c2c60494001e43e401404a281c403a0a141c2d0110054040c0c0643d10884a040c1000002e0956801d4001c006442d80120800030241820820322401d14040d24014001103442008201004081c1d02c04e0303800e0346040f4151803040e0f0780c0e900001d0518400c4814205a41c000000402c1080900300940008007203a1242e241e81501d1521000c0d105d01411700d015000a4480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209743480 1250 209742230 209742283
    0x3030406030c0509030303281a090901140702010609060906050d0602032208070b0a1404030e0102010207052a0915060307030e19120504081c030605090a02070507050108040203 77
    0xf4001e84a40710000303000c5a07141c0c030300700d0884441d80e208200303a1000c9010740b01d5124141c2c1c1c0c090041031038000035400100c840012503c184501c0000082014200c0d540e1500d8200c1c40900d03d0f90428003031411940041052414280207500710382280e8461807100e46813100402050b204c841000031040d8203d64016141d580f6481094005110003d250014480301e0390608100300c0c170503000c0c0000740d0151100c10341c20382e190f07000ca20449043c80c003031103048120b1703400150000e031103030242140c818810302c009030601d05180e903030341d20784200040407203254074480751494554100703400301c0c5c881da040c100c032407505904005204150030011084803602801c0000005400940a60000c082c0c3e007080e201194080403804012104131721825008480c2c52005130340e465400e620400c20b840517180201c003c0d007600300300c0e02c89802e014504100200b00741341d11000c001569544036003146208800071500940e6071002864040c0c1400d11a8020505119007141400056180014203031840324034610f030b00c250b45460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209744730 1250 209743480 209743487
    0xf07030f03050712020a1217040b0a1e0609110403020a0b090d0b01030f120201201804090c061211030a0207050709020f12090a051c0e04060e060f0d0203030406030c 72
    0x1c003c1c0180c80b00c1d98400010208550024100c80c02c280070b04029080c04901c1d00303040340c280c180c00710500f90721a035040200d40402d10306048103070000d58a0900045080e14006400020005052601252503a40400b08281140d5002d4040d007a15010f035004c2c502420341d80040d081c2c82c0280981090800c021501000710745a42d101669001d030810441041903941e8030b407294503000b11190840b484402c018404541c2401405001044851001d0f5004d2501035180e81c018560049036881c07152414404c40b071140ca48440c842e0b000c0d000d014000d405152400e02a020b000d140c00c48a90440b40c0b483c01c480001c4031200301d810750790000c11402000d80d84070300d9414083c3c60040c003500000d400c2440041c800c504581d10600910424680d82c48010480d40c85100f41900c545d2412400380c10b6030022820003103440d5070030701d000c60380141c18140b003900340d0440d9020a040340d0080d0042d582c20a004000e029082c40c0003010400d1042d0129800402e459483d0b021944a0003039120310f005040e142e81000c1e420500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209745980 1250 209744730 209744737
    0x20f060f040e04150f02071112070501050a02161d090d120e011b030213090219031812030207060e010b010c0b1902030408030106080c12060f01050408060a050f06030f07030f0305 78
    0x4c00710381400f000556074100c2000f5881007004650702d409100d01000d01d81040207100da80c10f42080054203620745894010340d0b0542c8040008011400b0300200031401300c0d440c040d840040d015080c0f0410480c1c1003404030000e0441c0241c010030300c2e60310200500c5103580d0302c00d152440c200d0400c0030201c0e08110114019016082c4c08245007500905000355a4140707a06a02a2040b40880090942c034542d43e20b81500803486000101e0300080701285041031200d000b070b0001c440020b401c00340703540c00351051b1311039171080c103c0c095034480001c5c0c0010310441849070b0750160394000316003030000300410480f020018140b01201c98004060403282d1000490410705500282c85201a20800f596a4a01031030080060351090142c0d1000c01c0c0c020300030594800301c58050321280720b42113070011060744400307040100f0444505403140c100102008003003a0f601c0d09102007805a4000e1401103042d0408008000100000903c070a0180c6c0c000c0545103070110b070019030303003080300d0b0408030741800c00c1c10500f800c986510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209747230 1250 209745980 209746013
    0x312020c060916050409020f04090c0e07050307120e03030708180a031101050a0207020a09021312050a03030b120a0318170601060311030c09091f090603020f060f040e04 74
    0x5000300700300c4004804140001038901281c904000b02c2c0c4c980080004584003200f02030b41200b1240360305022410a64480d00c60785000fa204000c1d180d41d44c20241d001481b04450317400008101009010790a0780190440c0d150a4942c20244000014070380455034030700004014004112200c070229032020b0540e58843c50420001042c2d80c1c0c0440c150802034030981a03480e90401c1580781c040054080109403080e200020b5009042d01001072520130010069000220f004002c100f402c0300018000444064120a43c1e00c030700d0245c0000c08581c00c010b4215402400c60364010141030000c10401e0b0f1011406894a82e41810030f40d4050715184845855050260408200340d0140c00b81c00c8144040000d403281220303e155801d01075800404280c40d020f00042d900c000c00c0d03960501540d4003600c1e12150007035018002101c480244444103c0c01503604440d648240f624075640d040620035810314004181d403801c019035034540b038840e508001003502e2049204002516110384040f8040103000140d860100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209748480 1250 209747230 209747233
    0x603070513210b090d1b110307170d03050415090501060e0c130807030305040308180a180f090503030a09170c030a0e01020c03060610050f180301050702190312020c 72
    0x442c0e201100d0315844205010781d0424500c03000101300f0000014422038090080d81c4070b0020360307407100b1900111040307040b04440d00c1c135121703a40c0c0c0d406480030003241000340102000110080840103549003071854800c84801007505140422012a00010000308007801e4071100040760307000c0f4180b07640142400d80040c42c01d0708c00d540c14420400500c0010f0b010f0310034a8904545595038a105a035501d0079948002004101f00f0f110800101c1c0c0e00c8006041d40d00c90001030302c0c1c8005001d0000a00411054124180358010b00c1854510f03c443d602c255031112020101c00c000e40d08043d02c5841e42c03400020400f407440c07921009540c0401003c040c40c0442010001200e07a1500f910307002441c0c90b5040504501c00196041c462005650310004107014918405006408551030f8901404028024003070403a050100c1009100c000c22014001408200044420b41c505510301c10101425101d02038040001c650048a01c103400c0148545a108680d43c1410a1b901e59102424400081e00136504005450b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209749730 1250 209748480 209748509
    0x30503131703070207050108070903022b14070803090a0b1803060a05040203061524041703041d190e0c100c050c090c040605090609041b0813020603070513 68
    0x580456601550040750380c1d80170b071040103481e0030046407580d03000c64211000542c035000800140c20201c081c1000d10407403107140c100a00d001c1e1401441910500001c6034100d2898500b4078107040d003880010007810b0042c001d5407a003521400064410a11801000c3e00e010000495031720011402800d1503070306502505440d01440d0424284c40140030840b4141d010f4081c0c030000488040d018003d80c507038000c00420b5890141d61041c8500c80100448200382c009040401c40070844039101d922a00300e106008008660340d80c205582c2c200342c901d0340000316040391610400e011010800c004900141c29103414005000c2141400362443c284c1c682081c2508191003c0d074100505510964424801e070140d411150750b04025000c0c041d40c14401c0b5501000d08600380401d10840740300342d000b44000c0d84018419414440f00c200024121b1b81081040540721310760f202001506900300142c582c1c032070030880010341801044d4001c1802ca101c0205110100b00c0c0000701807250112150072030700a03108a0710305400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209750980 1250 209749730 209749763
    0xf04030609032307080f0a020703080c070306180302120d0212010e07030b0909030d1104090c030608121e0a030227040b040e0715140d06050a170a03050313 68
    0x1010340303221141c0c07420072011460790b403140150088419040d4008042807401c008000e00c6d031001d42110103174104500402a001022601480180031001210009041c542d46146848000c2320703e154904810002d450740b40c500420340104541c1d400c1c04210500d82e80d40d961200c81c04000b4450b07076882c0a400322082e00045417500038400d4140c032400c000d4900b0011000040c041180040303007101c114042d0740c41080712610180464204003e2039183d03002c581d04080c0c4840c0344405407043c21580c0b200183c1c1ea4801002203000c204842c010800f03510201070b01c1c0c1680b40001826400c2850b0030001c010f200001c076401c14912135411940c03014106c100d110022003c1001104111035407203005c0d84640c0c20890245594034180c441d600280781120010300700546800c070148200007008103a02c041c0802940e84801d1009404010030b5006480c81c40012800c0c100420050300010581100d454940848040208001c0000f1000000c1342c050030415200e60707648194050382a40d0040c02041958049401031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209752230 1250 209750980 209750987
    0x105210103060b1e0d12020f010504050f060112080304060b31050606090612070c0819080c0a05030f15060a030902120606150a1205090604020307090e030f0f0403060903 74
    0x1009100f00c80b4588108501e05813814804088130700c26511125010341c00c00028a80d10103104400301c5401a070380c103100783e10003a500710340e0221416100b07900a40c1c0e03c024807810a2168902428505915152041e000d0311541081d0000610052046555000c00c00380742d0748900464062a03a03407000c1c50440140c0070503e800d01d0081c550104080c81c1040003069403840e00c40e0a50b0740951018040f6414005026880d50f40c800001e091383c8180b1041003a0361000c41e4505000306203180c228210080002c818240003064000000c03c048000e0310b00f8013001c6403142e40001180d030010014500303c41103071100e00400c3c445d01051080250710200015000c501d654154024200081c000c0750406501841c8a211580302c3d03c04949090380502c2c81c0800c6c000004518000d0003204510345000881001d000b9514001c981e0700b80c41000e5107a11030001c11046280c2041180040d110350f03030041c025100004080d0303507240200d501e40301c17040750701044a002e40c1010313a082d90010740d013000e802c0c803001c806802d024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209753480 1250 209752230 209752241
    0x9020d02130e070e06180604140c0403050601050402310503160801060503070303020624030115092405150c010f0c0216060207030f051603050f0d0309050c010521010306 74
    0x1c16800388583c00a040c00e4140881071054502030b000c400e8043c0a16070380c6181100c018002d540c055911501782c02280012030b8014411388116084a47d184e0031810810301c0d115050744801e104c0c0e8010080402c032441916001000710121a45582c40d00a00e601da0701110340c038541145401d8030805001484c000101c11a00e011a00404000c101c3c070340e240c905068840c0c1ea00d010280250340100c0c0840d1003801c88448940c411003204c2e450340000c00c82c04000900b510402511022054207001007808013504a106030030113804000c0000e0799100040000c40c8000702548103a61164035444640800042d07803074119600c551651008011901281819200800c1d107280808018072800d86080e924000c0708092400303403425900146682c516507600c51100706100103049505000307102c601050002c0401526015512030009050140800e01c085460110f940a4440800d8100078850000c5040450420301e10102880c09a9071081c4d0f40d840c1c09000d94109205a40444041d00000180034155004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209754730 1250 209753480 209753501
    0x40b0306040b031510060c17030910090f120519050c0a08070615170615040618061e05011b05010902030a0b060a090e100e0f190b2809020d0213 63
    0x452039046d04c6001c201c0d6031034a0248010002c50038013401030002c47c011405168050b094408840b8005040d02d10f09040c0c400d0440c0480740c4a00e0300004008105c00c51b140701011449030300c1c1060602102020a0095086140850307050040008282590740c0c01400080741058000b1812581c0b000b051502c500100742980d1004101820f40c0804610130707880b40350503022411100f0080c9a40c0d11011981032603070301000d18040d032082d40c40d0300004601450f0101c0910605c0d045d40b00041d0701d840c0500004940642c02c044680c65410701e20300380200d03030b00300c410040c4191481d4102c0342c44410302c0c94043d0050002d00d402039894030600d04083c0130040f030801040d11600301624000c1107503580700048003e440c0940f9a8990f01c0e003000840b003054020319440021040701040449544003800d005650a2100401404c0480b0400c03428000500c020103401c6500107070134222484501540340b91020150500b010a15100794030790f40d014041d55035189580c003040350020b214503c1c03c039106c17402c840149041c941 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209755980 1250 209754730 209754751
    0xf1a040b01050423100309050d030b18070e01090f150e04020705060903040617011d0a060e0a060311060315060f07050706030e1c08070c1502030c0903060a050c040b0306040b0315 78
    0x11041c0c85c0500c28081e2a00c1141d004004103020310901900b60060194403445681005041c02e2066242d0f082c4801180034400d1525800e0060700d00c10001000030026400c14a18084011001c03c00c20002da8140c5800c000bc500c1c00303c0000002e0400907002e440b03007410240403441510140a90b000d0003200400c110781c22030716001119003c0c003000d850320100c02d2040c484000180340c07101d4014154440550350110030300b0030010b403035a25a20356100c0010262200c0b00c3e82541c0740030900c10003415103903001360740b002100c85608600d8000710315071b5255201c00049001d0b920101d8111130096280d001d41b456103a10805483c41d07a621200010018142ca4402100030b201d01c00c9803510107001c08030001c072522002e81d50340d5076a94400e541a00c24103007141003160702010014101041607000d10140d4082c1182d944410740c0d5880c4a81054507155000d44040c60f00c0d8541006e120402e110601100c04581c0c0c414266a1241d1384e40c0c001400510500115a070107000e000c0303088050384448006507104110001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209757230 1250 209755980 209755999
    0x103150306020a08010e010f0303050c031204060e0f0307120f05040b1903051f060f050c06090601090501060203041202041d0102130302040f020913090212070306020a030f1a040b01050423 82
    0x18a0340041b28070030b1050403403020f0320107010b00200384150010060018040c0460f0324210152130030345c034090411a81a1034840d81c650a807440000140410f0000da100b0000550a208164940c60b211503d54018001070141000e00c03036012a01801c166070007403444440c07a07034450b0b00d11400c0514580701341c80103c0c0024036050011f00c1804805170b01800242071200d041d1851070400e1400d68a9600c03c5c181e40040c402d05000c6180400307800c0200621410000d00039011551610b00300c9410f071681030b0000300a6400501c014403800d030a00560303103440e54040705c02040803d4500c45000781c0d40c114000c480d010b035000003221000d200c0b00d0064079044078800d48040140307030020003403034003207006050340355500041d464616620740741a90030940b003140c001458408101d03404406070f0710740803ca500c115003494000c82d50f00b840b642c00d40701d044c132000400c41e001d002003415103603108025101040d48912603951298816500d0340700e40181c074098081c041f8011502c1c03020446041015104402032840f81200c4c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209758480 1250 209757230 209757239
    0x18150f101b080d020f07050c0105031e10030b131203060b0703030506040e0303040f110a181d01020c15060a06052b0c051213020a140103150306020a0801 67
    0xa0038401510015901c628468491096101d041d202010054039200014030100341c22140300d200501d140310b140d0081e16902d82c000c2c07a01c10b08001c0480d030f00c14117004003481005092202582100700c82ca1811210b0903007561035400c0005c4030705a0b034002070039080c208030400c0a890860280e0345100e5000708409403401003000002c406903541070041020307a10080c400800006d00a0300855000340c40104041080b880e540c552600d15001281d05840002c20040304100f4011120241d0842d1042680c40704040d900700740264109460006c0c0c80042241e803030032541e085c0180030780000c4d001d0b41214002c1d907896084455240c2d8640c03101101c01c605015100201e00d4901d0450810002c46045841c1c4a00300145404221011041000081071040d4041d00d501600001403246003040c03491034440d940c4600c0345544510f5000401404c3c003a9400d80f0034a280c01607610340d9500001c0b0303042000710361044a50000100c0182603503180c03403014100c04507404400c010040c3c000c2c08140706030741d076020007aa9030b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209759730 1250 209758480 209758489
    0x30b061002030415020c1002011d070602031b03160803070306080708120f0f040f030b13170c070509040506160503070c0b0604020403140c13111818150f 67
    0x104600c40c0c0981d004000070421103070800448041c2641e0303030041d11000c0b8030400101c0c68441d4407440304001130350741c2c48011f2020125100f5841466040c3e1004007441c1d414118080e44d40e100c2c6445480150309040954084407000304200d030020700349910701e404103090b58a00213296400c00d86030080401d04280380450b03580c900250b010200d60100008045d0924046032042d07441d4040d004140075000104070400300369030305034010002003601440c00502c080c51410201d8076080b000d17040105070b1b8100d0800e0800316500c14400510707104042c800c00d0382d5441180c4054a400260b902258003d104c0400304418001d0124482d84204401140080414003000e8100d80c50f220441d10304000c640d0380b446443c017103214480400d603c044094401403805490b9200d158921480c122202003030791007145000043d0802c40030341c200c1c181c402e000501003180c0c1034084000038000c903440c0003102d1000d510035a01d0340e40c80380c6040e45000700e8407250303151030300303018004410041e00000242e029420441002025061 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209760980 1250 209759730 209759749
    0x9030109050705031002130b1e16021e03031c0b130b041a06030a0c050f070f02031002090a0905340305010b0a0c0602161514100f170f0d09030b06 64
    0x10004c0d0800300c01400c1812380358464001e58000713403481055051600702145400c0051500b540a000c50300400c40030362041080d90020f400350001d120302c0201c0400d44507107001060b10040c4c141c483d13200311582091400135009141e0141610350000e61800300250b03a2106070710001039403500b640d00b802040c000241c1d000240c0f16601d500c0c1e4100c40c0400c005070b000e04180d489621110200d240240ca020442441c5040c0f035006010181c8195003892412021450104005030f05410136072001c0d410700500e540080d1168805100340a2016180c2e400204201100e15200480c01d2081400328080900114042b41030912450580f0110745803100110b46002610241c52201c804ca43d28011401e6559403140c0127500b044d0048941c0c0c01610902100103249030300d003d10354014601000403102c01e030318480061020301a113010780c1c07260001406d000e4546400350000136201030000819000a0a4070003030304e82141102e200c4824000d90030f0500c107039644403030182c049034000d20342c4008544810781005072050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209762230 1250 209760980 209760997
    0xf060b0c06010b0a0201060906062c03071203031103070e031e1906140f0a062702090303040b21060402030708060411040503010510060201060602070e0a0b0609030109050705031002 79
    0x5000700c1c0104482d000707010080494100314800030845c180e5600149082d81e1f03003608103901082c00070000c001d40e440c400c03844a40111000c1c030303407140d80c40c41d00c80445c0d20307540d480c014090340c207030440840c40500d4002d801c03215040340c1e0617008079541d2030100401410a002000d00078400d010707040c08001d003903021080b006800c05100001d40301d800000c000d00340481507194822124642c552941180101215200a02c180160f0140c0c0c0b0061805030100c01c100c800540010f00d00301550031550600c00d80c260f1418441c4564802c00607503038180100042e00d10f000e10303070000c00354800014080a80141142c184004000700410002880d2162001c00041e80400c4074540b0004e00c3c1280003400c00d1919402905903080f445001d80c0c41c242c0c85102107070030340c0c004a480349441201c0034400c2109650901c510402400c070740c4043d020840c1444980a03111001800d410320f0b0360b445528410300c0781e40f0304040b502c4554004000f006102c00c1480c1940e1918004e05c942c80c0300c1d0141540240002c0700c10300840e0b490b031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209763480 1250 209762230 209762233
    0x308072601031a011409040609050d2f0c0402280f0e0109060c02090415090605010f080a03090308090102070b070303140a1503060e0a0507083307050903010b03010501090f060b0c 78
    0x944c08a05215186000400a40d0f00580322127040c03003c01d406102d03021800c5400c0d61400614410900d0988020111170b001c1401c000603080120011a00411040d98003041100c0241e82e6060460307903000c41c03413511041d1801c85424014030781d0341a600002d04104125076034644401d01206200159200344c0584124000b144404003081c00501d014007500740d100b40300c1d070007503590001070460510403101c1c4030108a500990b105c006020628148444100900d40a80207000005103035170010000300ba240310040088c80c0108100105a00a101c140c0140004030203007601c800803424018007514070700402052110030a008a20017400f1800b42014001f20f040d400303000d141c996603d540003081e100307524500d140034581d40840000d030b0600c00c440c0101080c40c020030100c8900c100141e10030400b0130a0000761010400e00030900c8a882d09900e5010300d2906100b500c80202001181c00f40012660aa038103520317140000c20030380780b20303400ba060205080c90200400c1d07445007501200391144200c00d010300d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209764730 1250 209763480 209763509
    0xf030c0609120709050c131a0d092d05060c03040218040609080f0d2004060c1e140f010203060f0103180b0a15060309020612180327030307020108040308072601031a01 73
    0x22406c50300070b03603521444bc410b0301110700c0d1491310640800f040d5841e40008810107040b50350601ca001c001003030304884075a050500d5030609070700181d02c0c03d8800314007003401106580007a00344480c550041c00025009540250f0f1101d40806140315513010540304070748180380001034500b9030540700501260381d900a044a10f8117050480c1070300d035009a264101c89403a0460b1014140d0302010341050000c500c24600f00916100c105051400c10540c01e040701401e078414800c01220b903440d108045110142030030300040c034407514030100941c2d001034030000d480360b9000c1c81030008000d050361041c6c010409420780441c1d07003916031804409507401e954002e540030600340900c5100c0c905441d55540c20220915070b1000100b240718081c1c1c2190010784005228401c2e03006000d0300780006150350300311004201c02541c9010750a038006810601c010f032000c0c081000d060009102d1500507a03134510103400300b42152088001c4280503460742c4100f40000c40b940a4250391059640d40f100e12454162483e4034a111301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209765980 1250 209764730 209764747
    0x71806110604060e011d0309030d0815090402040f0903020a0c140102060114011803030f02070504021908041403040f080f031908090a0b090c0f030c0609120709050c131a 74
    0x2401001c051458103568603406c0402400c3c00c0e5845054000e9002d01070f6888803981c400301814041001162028400300608100d00002c1141140800c0002210104000c2e210b03030002c80c1c001d0140030ba4130900b140c580142d2106250700041c0c5100041e03c548440d8003c2616101d07500d00c10300d4001c00690140e480070340140720580c00141103049040040c9003010040601050341105401c0560054010805414051207015418000c0300301418040e1815446c02040396600f100103112a42c4038010002c8203c0480d00f0000130503001082007076041c00f243c0c1c03120344070b40c03200440d8a494422080c403441159125080740901100b980c0486890b21140e511030200b01c0703c251003440005080c05064081c000020380081c20000241c3c3c01004208014001523152409100740301d0744d6030103030038460350054827881200e94600044540002c001d07a0b43c3d07000030740c0030500d01c5d103030903515040650464204020880722032003280141403010303010300340c41d20b40964a00e030711590b0104004500f03086400c200000e10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209767230 1250 209765980 209765993
    0x601110d080402030c030304120c050301050118020304170f040501020105180a0210020c0d0b01080c12031c02070204020c2a010c230f160602370605071806110604 71
    0x40d0b1060000c0d003519080f5141c8000170b41140e209400410030b404a0f0340c0141c007402410000070f0042c000541c000c019550500300b200d80d0100e2401c640c0f002498000001408214280300c8c080045410b80016585038a01954407104c0e9402038040e0380e005601e13280004060180c1d0300e14804a1680202c040d0407085840d07002e0007040c007507111641056108134201c8844986401c450149660701503002c402a550514008905001781382900350720036210300260340c2c920f00d40030046503a0880568603010903590428400f00183c001c201d0065031140c400700d45005050f07400708203004ca1840f40703281c6090700c0007010700c604240035840c1100ea0021b07881c0045400001c03020048121440d00d102c00d60328a120000000c0c0d4a400040950300001d60801c09a0b42002406491110050007203070004e00003640e90b03c4880b00c8401c0c1c4030124082240c00041c410380507050600c0c4a07000c0c3c1c0390421400d1020b440e1899010303015499004c40200c1c1f4400156000035141e01c603d0203000b400d00110040d0400d62507503250320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209768480 1250 209767230 209767247
    0x40b010b090d05060a020307030506030a03020607110106030611131e0e0c0c01021602010e010906052a060a0c091203080f09100606091a0301050d0609030203041d0a050601110d 77
    0x300d401ca04a8032100300803d600700025441281c641c140983d807031030314003c024143c640c003418a034007940c029410400002d03008145c6c2030707015072980380c10a4021501403031107024000c19400038065920700f04814140c83c0c1044010051480d0f11546940750039070b51000070b11031089442400115442d895814441e01440c8400729400850501d0300d20308040b8445182030032a40560010711008401c1c4240760119600a40f0075003401109003000c0100d01d15200002d0407600c01d40303222400c442c0310340ba2141c0c03841400c80701c072003000c92149045031464a8042d14602c0240030703c0344c2400105007011340c0001d151394101d5110003c181d055842030516142c0b5209080c2c6068041c0114107140500c0c902211189401d00c034540003800103940c0c0807060b9103015140101001c021848010203201000144a40c0e22080e503694412036100d24000780070007560604034110f000b680c02061502c00c402c60380c0b0400c150210411030203140c00c00400c04c581d03104c0c6801501d4140000f20400b610ba004081c0c46040c040c00b80b00c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209769730 1250 209768480 209768497
    0x7140403030c020a09061d01060f0e0415030c030c08010f021305010c110603070f080609070903170c06010905070e040c0e0d06020903060403050a080108060c030a02030a14091e0303040b010b 83
    0x35503200300c0e01c45c0c0c1030806a9409401c2503201c1554605001c01e0503c869807039900405007410441c84120240030028810711000d54170b10b00407620b80c03a00002c01c00c000c0044d0380081d03801004040c030554681c902140b40343c025110b11201982440c0000d00007040c3ca208880c0f0b0510400d44a1015928141c015962001c4c0b0031819a1a030b45450b40b42201a02d41100540c81010f66a031122244001480040c004030005000c050285084804006c00b02c1d8002c001130007583e411901042654041664406251040e22404007c074010030703000061801d45508003e00844071a01c805031008998020300c81160110202031001540380c42c405841800c1900d40d40200750b019100240ca440c840701c01007072503d41705950803000100000303640c05203da0f00651060142800b140a4809820a0310302e40f0700502028044002c2d003640040483c16510f04e84d0f00107101031140c1c0030041503519003000c180761902c2012500c06c02c214801001c0caa180000802280e200da03501c241c030403400e6400d00941182c1504007010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209770980 1250 209769730 209769739
    0xe09090712111c0303051f080c010c0206070507090501030b0105030327010203070c0305070611060c0f1c090308040b10050109090b06090603040f0c0b090306060f010915050304050607140403030c02 86
    0x1158166518160f2040c0d0046000b603c1c04503040c2456941e000300203d440030116100c00350400203018816020030803160300c140910781016150a140000740d02842805001000e0703100d07075640010b03d810181c028a04a902411503904680ea9400505490b4801e4440e581091404101d80c1d813544001c95003409490078042c81200e05018450788d44114580e15034106503a550b101c40001c100c0c403540310503000740c03145089011b4016410480d203158080c0c028420031035001c1d8004188200d05a15030b4014800c0c00c42e8410080c004040c580c100500b842c402654117468607145080050f01c000d80c000826401c42c1c0069481c50009494030b10104010480c550700158482810084801c0640da441d0141d4042d0780501502c090704411850b00400c0c54110340c1c800b5644420a1022603099540071400390f6200d8030030342c2c81c0401c0034062401280e504103641c10007100741840b00b0808021580c004017451090744600102d6009484240050b241e45d100c052419224040400042c00041d20030344828810620103070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209772230 1250 209770980 209770999
    0x45030c0105210c0427050703061203050901030902040c0518030c0a180921020f0c0d02010305041103010c1808070f06050706021303061e11030a0c0903050d0e0909071211 74
    0x2c11402400d203501540417005000748003420061400b5100b001e401c0040c605042050524241e40c0700e402128130380010f0240103000c0707804c4046d80d000b82c1041d070380941c3c010010004508080005003854211050300500030810818910a90500252864850f0070040a40c0c0a541c6032081001c129004d4144003880d86880d06042c40020f040c110410980c00303031205e07500240240803c0000d2078054158a21622a40448404d054588131800c3e0400c1c003d8080c82c01040951b900d04104507038428019000c3d40540ca004510010a64440c00f07885441c10905441281031382c1e900185075aa807002e020320581180241e0301000f0305800f540041040a01c14440907080c548006001818015145d10984481e40c445500c2f248d070401c00490703140c0e0285d14403820851190b846151100034080200100c0003240e03142111500c00d0b001c0c1a49038000e40c1c0c010116488455003080003807581205503003141c01b4191030008144446008500d80003554410310070150811029207562120180f00c6101caa00454550b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209773480 1250 209772230 209772239
    0x6030f2a12061d0f0f0106030b040e070303081b0306090f0919050606090108010c0c02120f030304060912051602040207020a05060a080103030f1445030c0105210c04 72
    0x10b004070720043c50b112031407980000c80820012a2858010070382040b51100e5001c1140c640800404241926490b1800055101d600000301c0d000f4071140d030b0104c110b07100d030b02000030030998080d060394880c040344c10000112020444040485000540d041a4416100c10000d10180142d58080da800700c8400111000e4060003040d4980d8002d01140545040d0840800c2000b00d0400c1c40e152401002000c0007080145034000b03004100c02c0400c42d001b4407460320705480d00c030208410080d503801c0340072800075281e40e4140351a100005000600c1e04844003443c44401c845198040c80542d90000b01014002461103e02c1c0d007084029480a04201da21030381c0c1300c07030124040c1c8403100980440c51281c2c940c00615411805c010300b0301d0200d502c0300003c20070403c0c1145a03880b81e413400c0e00e41c40d8450303090100b0800294610f900360b4250303c0d8500084175002c4099000668003030360001c940044183d090740c030588944801110240b269420300040e00c004219441010307080225200e500c104201800c504007a01e9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209774730 1250 209773480 209773517
    0x206090a0e0703020403060b010e011d03070b0a02012901022e0e03030703050609010f06080406241508010b16020a0305060c07050c0d0308010b030a060306060f06030f2a 74
    0x10b890301e0300040e5000c2024020070429104070b614022003404e00f00300c440c2e59100000c0c002d600b0300300d0840c48004044a108a2034608200090142c80c24203011520f03860001c1e8024000c2c005400d0b8880c098489a6031140ba001b1402c08070304600c04103170b0103045401c0c0413035091803500c054002c2145910501c049419a21541d9200341450a000040950398906242e400101954030240a852240005400400181a04080ea130045507018100229581e4407820014010a03600c52961203800c40a0081c08018580032108400e03142e8010a100d4170501e554412a40d00d94240034154040d441009104070200801340e0030703800d041c80140903a9071152a41d80b201c0c01d0000540d0403251400010460000f08101484100143c074420780c4c0300300c14243c05450050042c02e040c40342134914240040400c0e00700c600d640041c00515080401407154075541d51001950b03000c41d2240d400001d18095107888802c0035401501c807035403200c40030002c1c11851150104040f40204d0744881c00c0c060b6110b15004d0ba03864 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209775980 1250 209774730 209774759
    0x3070501021303020f03010e0c0d081236061503160e0a0c0e030a0209040309080604081206010c120513030204110a0201050f09030703080402010c150b27040206090a 72
    0xb034064641c0310395155106019541303a0704080355100c0d90604000680c42400040c9140c41000b04964942c00383c000b82c1030030640f52003440c41014214180c44100003e40a02c0040a03141c129240f80d404010300048450101691045101c0180c5070462804140511303000405101da008009044e5540380c0102c0a0b1a1001c862990084100c20086404c00550b04094032504900000e036080c130000c80301d0345900182d11090300c1c0c0070003032191240e00c01180515100d401010003916074001121a1030926052012300d0b40c120524903410350039600000780943d4413800800e03402c5a030154140c581c0b0142c00b01c1c00e07541a005102d0440b540301c50158008056580c1e8003c0314001d50010944c96580e0b80b5000c0c0007400c0d140006c221100300240c2c0d9003401054100002151009a054505441291518801214130481e8480d019004801b40c5004c610f5080340ea5101d25a011000c42d4001c808807125014000d0000c03800101402d242c14100c0040c0145c100107000740b00f890f100406c2411000d4980158110741031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209777230 1250 209775980 209775997
    0x601020c060412151112060f0312030a0e030708030906060a1a07150b03100b280b0304150f051006020c2209020604080a030e01050913020901030b120d141216020307050102 75
    0x86c400420320178035080c00b641c5004810750a40c09000c283e01c0c0070341899004d10001e000544101d03035170f0204070b1000310103000340da001e42c0d88446010782d80d0502c0b504d00c0d030355048255038040c42000c40700b10014080c00c50302840ca10f44083d4541c420306040c019200c0994201030240d444549a864003140e1081b075800f03000b003241303103090180c00041100c00c0c54140301c00c0480c03200d908180d0703180c007681030703c02500c080411a04071000d07680c010b035490741e5034504144a43c100c90550114141009010440403003243c000c41e20031312800c40090b4400340e071140200d0390348104140e000d8011072815001d20071502c0784e03251458044800b607000b19903012213501203159940f041c1d10141d003903000301c0d040c40c0030150310045852140900346070007800d010b94240041c802da900c1000f10819aa4000794005c05a4000d801801c10002c004004020030740c15001c0b10340d141d000f1b21032075000150003018413410508c0c503141541c46083c1c82803010b980c039540705545504c0080441c0c2c04102980b1003841041d000440900050030040b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209778480 1250 209777230 209777257
    0xb0f1005131509230a12080f04060314090a11060d110412170301150507020112050a060f0e0f01050118170705090105120a120903050a06050601020c0604121511 70
    0x614018911182c500954499141c821340b4000c51645941e0b122210015200c152440d00ba2500e02c0d1320300500c461003008007090080c2c1c0081000200b580d0141d0240b1202c1c000d2845d07880c810358841d102c031511407000e240010500301c0041d41442440c01c0400240884014401c0c1c0040c1d13510720705c0340300e0f90f0300e0300180c0c015401c0098035a110020805500121300c0314041ca4248181154180030640a401400420210400001240f02c105583c812818a01141d503294020005030400c080c0a1000d0003e40c0544804903c025600040508a0090542c4508042c4102c44402c0c1d00701001151028a44800c2200c00400b002e4049121030700cd070007030401102d079800100045490a4103101c000041648868404c0c825100b038241a07050224250030460341c004540c0c100041e281c44c1c291019902c07a00054481e02c80c9501c91001c02c103c80e4092401390000f40c003101e514000e02400c000040c829806401e00348079903410380c500014800070181310302e0f00100c0d5000c1a0b600307241c45940082d03000340c0d4440460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209779730 1250 209778480 209778497
    0x306181504060f06020d140d02031512030f0d0906091401050f010b0306060316090b131d06030a1202010b0d0605060a0807150503040206041a07060b0f10051315 70
    0x9441c140c46044000c00b80e00b50f040040b6840d01d0006512941418915800e1089500410096640b80c508880d204100950210340307d00740f464a5000708649120320f03600440400e00302282502001050f9540e10301c2c0c5200c00c600d03210380d00040c100a009080802c8500d0b03602e0301c2c3c2031000141000c0340da000361030b80600001218600023030101d03500320040c5d0041c61004000c106218841d19820101c0c1d600841011002460344a8008201c0385480d503075018980d011004981d1035410003482c1d040d60102e903c2c44c0390070124500da00b1742184d400c5000343c9501e42d040d03200d070005100042021400500305182800000390280400300031981c49503c403c42103c0c03580e9940e082210501d07007511041d0203000340000030304069062401d19003a2100350132500e424001c001c0000340855079200200c501604110b44040082110907402a2141c0c1003039030102e88550a040b181e40f254240399004940000b4010301d510207801103c0c4090315503600054030341d60005410b078400710301d2007001344000f0440b2903a680c81a0b070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209780980 1250 209779730 209779771
    0xf030b0415020304020f010c02031e0318040b061912060b03010501020d0206040818030304030c030501020309100c0212070305120103080a020d051602120a0c0803030412030209011202030618 83
    0x1c0c50198040d440368403520500502c800368850b02500c002e030b1103080c00c5c47c1e1000480b44c00002c2c541b4040d0800e503441000026184410b0443c00f001402007001070122412203203600c07604000984030022521030704100188030101c10050038110b036100c5030422742400c180302c00340715044c03c055030a5034001030742400340000104501d5038100702404c44803040b44090401070525a850606078030038010600c010303001034030400c5880c1d034050040303900560340883c403404029503070f16110b4040e410032200303203880d80030321000131018180d00d0240c4182905554007525099022a034181c2c40c0d60400f1b04190f0421009101606000541c0e0882c540698010120039031900c802da80f00925282200030104100034050008040c4207a2840c00c001c1140da044450703020400c680b580340c80c5012607441c4003900f20380001000007540ca001200443c0901c0c040e064402d103546440c0b1090b020b0384a81c3c10031600144581d03031200000a0310b9406182c102c100104841303040c1e40305295400065206a0b40c0d42401d035020084800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209782230 1250 209780980 209780993
    0x702150f040909031e08181e012a050f030711150103020a060509031009061104030b0907050901141e031b180601090b030403020106050414060103061a0a180f030b04 72
    0x8641044683c07017140041c0c1c503018010100760340038201904032881d40b207a058100100340004a401b00245050b0300360210030f5456035010344000310030000c107082a958520110040e0320618954440f99031a40380c0303482c1364040301500030b03400200714108010390b07241c440300000014003104840380c030841560202941540104a42400554880b2084c000708005545154901040c3c5040c0d05480c44000549590541080d101420b051400e9204405c40010044200031000304000c0c06640c0d56421510015180d1091160303200082c05090300e801c1d0746040225843c80c080c1c0c41c20380c2c02b02401500d40704501124002c41e2130400403100d00102e43d001c068a17119281450075002c00c9000b480c402107440b500388100068866882405240d4480d440000001c0600d07000750040f000820019000b00030b09001c1801403040454103903102c0380000d0526800141d4030414181c0d403913004003414045032400013502c1c030541e455003040341c01c00c01c4914150700000300032210b21158801140101c0c0140c02514103440c108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209783480 1250 209782230 209782247
    0x28020d051522060218090103051f11040e10080d020f0c040c050708030406180f0b180705011b120207180203090d11010b0301050a0c0e0a05060702150f04090903 70
    0x32945020b51402d1801c088190100e4007080c00e4100300300581d0348070084031001044034601c0d07145800114040002041050004814910543c04684051400111203861050b078031005030303900d40300743d0901040c07005508903d9190b400a50000d2004c10450b9104640d900f0034001d2420180503030481d900e0180d0301c40080c80005c460000481d8200b100006100b0080d11a000e180c83c05400d001002c0009001c01449510100f242d000580c200040b248091400b00e811140c070388403c0350f44e040d9004c0410151030711100d1940c20240c0441c0500915401c2000445890310001408900813404030f20800200350080703a150980300711540078281e40340c2003025180041000e0039019100520400070003240c1ca07c04240380348080442d01e000346079032080154550151220f111441d525500e0082407102d40e05083d40040150005a110f13a4581c0d1018030420041044038823545800a4003001410b00620301030b00c410329401302002d1801d05100d860102c0031150341254206216950343c0705541c009154100925 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209784730 1250 209783480 209783491
    0x1e010b01020f031204030e011b050a02100503090d050d1401140a0f060905040c1115061306050a03020f031903020a150b0303070f02040e100605040f0501050328020d0515 74
    0x10b51401c0b00d002c00300e130313410f22000b880030f01004406840000f01d82e2092600410143d00d400d10b41c28102010301300151602d080920403481040f4080c40605101d00030b5080d43c0c0b00340f0741c81015200d06020103405851325400810300d40308603607480c2050400d070086591441e0182c07280e4510803603004200c0d800d01c4003485040c1c100c00c4c0421310100c010852240e002484c0000e4490a807004112000300c21010348481041982c0d030152402010202c0840c3c210b681c60f11441650120f0f540440c0c0c243c200304034001c1b1025805500e400c045140c8091001d0b0604170040702d081c11b8041c5c2101e425400c40011036458005484044006801591200d070074817101a58810030546c7c414001c00c22000200c00190f0b50340b01d4810020040210f41083d18155030713b13035102000c3c0c0301c200e00a80c0c41e8001a22081002400c060003220b01c201e10b080d2031040d0b4442c040c40303042d041e51340c050010300c0103854421000c0b0800504a964442c0f980132001001c0050711250302c0101268800e8000740082880b040e125450101c00900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209785980 1250 209784730 209784733
    0x5070e090604030f0e04050403030c02010501150c0f020a08030a02060103050c010228060e01020a0306050a0e010311280b03060108070806030706050a05130303170114211e010b01020f 80
    0xd01101000c0451036a070840d600d400c2c60004c00481c850140d07070342c04c40300070419030107850f20040000303258041d0020362031304515030f00800035a80c80f205942a2400c15143c00d40000e02603156400005030122040307100d9030700091103050702c290350300002451a07021032403c80040e08540010000c0000c20011540d50740c60900140c090807480d0324810301140302c2510000e0f00e4001c90822a4244501d960140361804292002550f8481c0084d02c080e01602207440703070502032014020001004080301070900c1c180e0b940000b0450010b181042081500110a2240100300945101c01804c5000710140003004090413240b03940c90789002c0c400503009100080019043c06200001c06c02c01d6500482c040e410b4580a080268540d5440701040b44c2074005c44003000c11000e04884040141070b00581c05502c80c0001e0011541141e0701d13000d0b04020000882020343c0c101c0740c400c2c44214541c510480c0e400540340e50000b2070303803035200c29007400380c450110280e481d8241e55103481400255905000341424040f0190 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209787230 1250 209785980 209786009
    0x30210260408030c0a111b1207210c090203240306041101081e0405070f082b0c02040f0b0906060406080a0e010908030705030f012301080603010204050d0f0507 70
    0x48655078207100062440900c03450020b1726040d003900492034554401c411900301c41a1084112640c0464185908218801c0141c2401c15181c03490000f034000c10788205090042d0460324103015920110004203084503100680c0c900460402041d2010350b00c100711001c100c441c0e0300e070b25081032031012010501c080c0c0a0741222007003002081a40c1c401410306c1c1300a10388940e0075511b42804d1a400c04400c03a00302c091061100134001804000210b0138141d498591f44504003c1c0d546c60032a64031030200e80c207901c00d0349584034956001c1c209003210720300e03c00d41401c080115103a1980002c007121a11940f687da5a640d59140c0c0300c2c9410700003005640400156a11403a0a041034405030507650b0044c10f244800317480703c40140305c142081d0481c00c0d1195210040e1510f9003403270200a85160000c0b1500c050f004903030350001440c1a24849510390329813688403221152038241c00111840d5030010042da07011741d001c010000c1c60380c0780d084010900ea80240103407084102d8500e40242420141c0d0300000c105890030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209788480 1250 209787230 209787233
    0x30f09091302011b24050f06040204030c120312050c070302010f020301052b02040c1e021204050909070e07020f1005010605041211030607080402190602030d0c03060302102604 77
    0x601001410b1445540130704d030075441c40c0750140388529599900b2000c800400350044c1060490b4000901500c8520400c4403950344040510040f40100d10010340203003074803141001060040160000798902034900401074000d142209029035a080d07900014a601c0040c12406150342841090300b0f01c0344e039140651455240034005441c0c0050991080c0e8480300d0701c2030883e002540c19141d41c0702c3d9580507000784011000c0c848080c101504000340050041209440ba907038462020441c00c1000c50f04c1c004560409040c1070038449a03020042806102d881036000100b00c01554020300c42c45059031758001c0100d00c032080c0045050591205c5405440c41c1080c3c0140b002a4000c402c0d5800d03a0401c106c0d501071211281816017041c0300c3c28403044c3d00350040b882400206030340311494604c180e00071b46844900010703034078241c0c0f8804014415400107800500a000b00440c5030b4121400c0c005040c83c003c21300d65203d40016039003164907a41f20010840c48055246180c00100c0c1c0d0b61010700040c0401c0100d89080e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209789730 1250 209788480 209788487
    0x11803080604090c050f0111060709051e0303070b040f020a0b0c0f010204050310090c1203120c020c01141308060a0603050601050a0b041401200106030c05060c0a0f080903030f0909130201 82
    0x60003911b1051294001c03c125503403261280300d010400820860b4801d081c0301d98060701517212802118010792030310f00d1702101c0300400075025402c220b0150003140782074242c0d00c4170302600c0c00c0a04115202482d42c0d000c0c5000da681d90a58501401c440d40b0364550b00c215180205240040c0e40d0340d441407990050204101a81e008650f21a011031510804a030003000c0349070041e00c0c82403c0d08102c401c0b003400c2c40c180003030583c0804020010700c01e0304070800065a00c010309076076624080408900083d0501c00b86550f1014180103401c40d007025004110055464039156070400d0400c036041504140d0700c0c0750402c144602040010f006100956000c040d4509082c071030541031040340500c60581c490061200d41907446000c1442d10f00d00d20396a044e10390034090081c00c0c00317091070b4030050300c107400c1000c00481d0b20700d062812500461300d00e40c000c1409090300e03650b58100f1034030f250040e580e88905101c0c04501c1e4074207000901d04008040744103640d5080c00003c100d80104003030407512941640703040850050341c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209790980 1250 209789730 209789753
    0x1e0f0c03060501081f03201008040803070c0204060b0708030901052d0705040f0909020f091504050405030702060a110601080703020d1e052e020306090105060a020a020301180308060409 81
    0x40003800d150780e040d1a080c1c503045800d4141e20017403451f030002e10074180b206504085002e22420403117202c1c07503844100d0000c50b400d82040d64003400070309081011410700d034001c0a00741075843c40504042a000e80d03c10b440e9406030403841c0140e80c042070020812400080c00c1c803c1030703441082450003101010b03e00210300b015408802126107282220f902180f4114000c0d0142ca0041050760003075001d9a0f01e825101024080c03501d400c90198400306400c4445d45041c0b0341d002e11801c65440c0c1104840c4200c400c100141c8400b90060701d03a40410002400541c0328180100305c000700984a1140c11802100308525044051b44440680d4010741024030040c0c4c0c51441042c0c0d03030ba8110060314011411900200302c5411145401882c41c400e03a44501000c10a4210700e198824002007060b0b160502d20300014141d12040314102e600c05131400c01032103107140802c050b0401001510480d0052252030340840d0071204606807801e49506005041000c240d4007603942c640c482400d8506121081440c0e41306801c00c4c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209792230 1250 209790980 209790991
    0x100303140c0c2b03050d050a06060f141603031506020304080307030e1804210503090a022209060204030b06062a0f0a110307060212040506070201031e0f0c0306050108 73
    0x1640030040386003542d2009010540c0801501d9000f450450704c0c0c003070030a900a4400540084c00c2c0750000c2c40e0500039120303c2c0100c81e9107485021004400244c1207820350b002e081000c000c00781c288501e10040c41c0215108031068480d490000703403100c40452809100d00e1a51040c41103600c200b0040c40400c0c80481503500555160901b000e980454000207010701100b0882e62008841010070001031242c070003540156007104c5001c0e8860802000c0301200c00703110858100c06540d0000d40300d40018142508100820307401080d0548049104001010a0352050641503c00540115060081c405c0c3d40340d0481d082031003143c2551a001070702c080e401e095140750306010101c408401280b100b10701c1c00c1c40300007960203000007514842130291510039580400100f003203009200b0b6410105005000060007025000303c0711066051602d48820445540c0c40404100c0c101500c0d2140c24480040240d02a21b500311318440101da0040c00c082c201c4101d4003a0250f2404040c00d06030200082c1c5d802c80c20300364004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209793480 1250 209792230 209792239
    0x3071b030c060924050f07021516050c0610150309021e06040504091b050604080319051c052a0d021806041e080a1e0302010b0405100303140c0c 63
    0x3101582041d024031840c000804e242540c01ca010f4003040c0d51140c0c0024840c0130b20107582c06158032080022a42c4042000d04aa26036500c600440c060121410503251a000e0b10728040b803800020181c1d45003003a0082c3c0341d529120540b014144100c1e048103030b01a00e9178030145020004503c3c070f0307000a070461610341c10b03c00c90703115150300c0d00038103072106001c640c00b510380a0001d0001c2c00241c40d0060034107004900481d40f0032450480800c00d0300e002d00031502100d0407000107500f800d0681000286080c2d164403242e0910404004185542e4200c1803441c2e071109108000051900e4034220480b4401b820041454103190210112401051a4015110200c0c01d1400060711048071101d80320012450241c003ea00802c085000509885152400d02c030516401c0130613403143d075035800003582e40c10410800034090313500039280880001c21151a010070500034400030424820503000707c0d00b1110305559a258034100000f060040c950403030f02903000812003a840d9440e00d0700180b41c0303a0301c0b1a0011500341c0314 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209794730 1250 209793480 209793491
    0x60d0f0507080d031a011803050303010f081009080712020a05060f0906090d09060509030120031008030a0909051e0a020d0e0c03061f03061b030c1707080703020c06010b03071b030c06 80
    0x210f01f000c60405018640c003d04695803035071940307492071000d001489024424816141e030658500d5040c0218201c0d55401000c590901d50595502c0c0d0404100d40001000c40c1b0035801050089882000301030f01529120384100070354101580d00509001004040e030015500541009403a03540c080b0320641115034510702151145a02030029002d445081450b06452503804103030402103185100441c00340e24a07150070502035035181c3c80d0700e4503406000c0700400880c284030002c001c1505603030080c5a00003900000c40c5805810800104d00c560300a6900e4a0780eaa40401c00c0340d0904494480d80480452510081a004451100080d91118018054005d0000c0122104206805007040c180503680c405014820094050481100c3c40500c41400000a06040002c5281ca0050300f810401081e80b02c41103582d5034803044191001c49026014100700341d4204105420894140003c40c068802d0039102c0d542d0342070005004001688030301400b100d0f10344000b81c540000f40c2003885801c6940d40030308040382 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209795980 1250 209794730 209794757
    0xf100503151215070801030b0a1d0609010b0901050f0607060c1107151205010b070201031a0d0507050f0307080d030b060714010c031a010512060d0f0507080d031a01 72
    0x31aa211041d65038108000300304072520351802240c90001108201c560350b181d9603801108a503141401e11014040c10384880114010000c5a0060744000b0040c0f0125600310040b44405850618110345610705a5903801a94031079282c0164202d00400c01110403060720b6800000068843c41514001400c495a03404034031940c6000702e00e40018003030344001750703694540d40300507501d412400380c0c0380c0d0b1000542c840010382d0250781a21610341680c005c0e01c0d07550b0a1500c1c2e50b00540080904000600d144007a1029070702041c1d4410890380103541c131440151040526100604c5004030100142900c43d400c4850180042c81c000600c3c0100503101c1e03c4c01103503004240740803603250f100e02c0360003500740005095068821901500442100d440071303681003100a4032840150460b1403210a018001030b020090302c6150018115030740d0300104001c0c00424206900c1e515000800c2000c101291980c01400702001381d80000c0c010741d44122400d080c280301c0c82006250142039052030380580741c14841010070081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209797230 1250 209795980 209796001
    0xc020a08060408030103060c18031b03060608010207050601080105070c030f0e0303030c0c061e06060a0302040f030f05060a020c070333050105040c03020906030106051606050a1a0f100503 82
    0x80040010509444460905040400f400d034024002611a5400d210b51810300f94880c2800c8250300280e01034401e8402e055548a81c0a0352048007803140456107240080003044862042e9001020520001aa54400c920301182451416405211303103034501000c21120740d8200c00c0b90a00503134146050b88002103581c030252400c0d9114110340e80c1500c07000c410400c51088810090121741101d108680144d42c410a501c001400c84841c0303009030040d0344000c90850300704400540b240e80c01608000d41081d03140e045100b10782c22154010788204959140351018001d00344461034128030401d00551070b104840c40035075500c590b60b03c00100320520340340501c40c04480041d181c1003030003419034081c070b40d490000070281c0150000b8010503104030302d01204801c01c01c0c001c0c800c035404644090b18503815603103445401d80b102e810901051040d40103694000c00007030b0300303031042038492500e40c2c0001030200000c5154800214020031107500031280484c0000c1c05075201c0e0000d44a04030285803540e84d0b0b50314441001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209798480 1250 209797230 209797249
    0x1b2f0304090203090d1e141804090507090513200f04090302061008010c1e200d080109020c0c10110f0a050f03040e0a020a02161e060801080d0c02 64
    0x1003420703031000c0244055528041125200717890980e64400d9810300c17510a540c81e40020283c00c1c000b280d000903c58402a0001d80a0820140801c0c0049088034040e40032500391081580f089842d0780060606010540b410b11807140c116010070080c408001050340e5540d00841460031043d504686d05941003500c0d65400c0c4540b8092502900c2071056a4140c54060b55900041d136520701440390000c2c01081c01801480fa03c0208400d50303860900324072030100011141807a261000c0200000d0100e6034411000780720309000b406043ca0020010801d01210080c00e011060300719030001c0d8010402c907800c5031400245074180b0b485c11a03155031309140e550816210340382c000403c051140a00340740200c0ca544042686681680607009a818015200e07000503101e118074000c0c65030307102800f4049548035503598040c0c50300b101580100c411032680054000e040da05642e020000704405000001080b071000072800c070042c50113044c02e241a50410a0f981d440ea100d085200f020448804043d105568a441c201c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209799730 1250 209798480 209798489
    0xc0c030e03010204030c09090302010b030607020a060902060f0a0f030b010f090302041a19140a030c180f02040b090f0406030506060d1506031101020d020a0b010b2a011b2f0304 77
    0x11001d203683d50307c0c12014124500d0250050351802100d0f501034203020a03480d1052680d80e0107414031031000e6644000405102e442640c00040c18059440b03101c0c0800d00800d610005600c0c1d09408070480f50740142550f0000021604020b0140d49905400740c2004566065030307411038021805041e01210703164080b1040d400d0a5208184160b0b00314904085030b62403064610100d50300781400101d20a11440403088d01c0b0090070024000070400040090b0340d020b10f1601802c10f0f001c80d00d604180e070420281c0c1c11640000041c10400141340425103000a114038a24900b44d9092064600e0b5403a0f060300c0d5800148001d0294500c01c0400e4101f00052410030140707038044000f0045581c5074244003a14030444100c840c054803882200d020b04600000728006066401442103800e80c0c2011002c0c0302d641c026180380a010903543c02582040a0715440d1400341c0c100c0c0000009104018905a1803a0031800381c0c0c001c00d01154440d0b4140610150418440b424002d2508980f14031080035024518406c0307601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209800980 1250 209799730 209799743
    0xc030305030105031209090601050f0d05010305010c0f03050405120a030603051005100b0c060105040b0d02120a02010f0302040b0d0e0703021003020705060a062411030c0a0b0a0c0c030e0301020403 86
    0x40109904032000d541078a00035001ca400a103000100640a031180303100140d8002c0406d80051160b600c079400400c21807264a65480c20550701580c10425100d003070b001118165140d480595649034408200c4c480380b0080d02c0e0510042c05c01780c0fa0103450340019800c0305114107000908480035400f0303800410085620004660b8005c03800e1400740010442660f0f41490582803400008500107a60b00355000d165041e40a04401d920f440c00b040700503c0602d0704260071a541e06070010143e5103880c03c040040c02d03204040c0110106074400100702c0b0030410b40b004141403050005000c0034900c4402e840246142d00c400041d1400c1d40da00417460194941d20003980510420407000c00c1e1030349a0094000148036008030f078041e850340c06000c01035800318052118610200800c105c1c1c00d03000c01014141400702402c0200d000c42070312035450b08591004000075440d6012040d858200100803081d954071501a60f01007000d00d00084c40106a074440090140400641c07841001903680c0039070488004562180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209802230 1250 209800980 209801003
    0x80f0604111e120601050a05030a020307030609060323060112080306043309021e1e031609090908030609040302010b0301020712030b0315060d1109131e08030115020a 73
    0x7841c00340750781c04550b100041e2110f01001c203d0950142c000d60b000c000c0d054940310b040d9980d404841d802034000422400415440300c0000840d610365100f6117000e18003d0303544000c803c02002d9455188400c403a1807400a82c48000104410080444410281d90340011115600c4e00c40380002400f40440300f23400302c041960211903071100d112030f03070910800d01440c1040141860b900e8100c0700803401030300e45109030310810020303102c90706041d00c1c000d0280c2d01201303695003800c0b507140c05200d06540080350010f503a8040c100301c41c2c00d99608141e0740c00c001e00c0410000e10481003959141e09060102404941c0200d101d00c000c070b020903000f90411840c000d4054000c5413510540c0c1070000782090406004030119181030a92801c5043c041619181c1013007042d02e0301710f20b854043c00c0c4a00805000c506868030301703c4d1500300d11203942d04008135000f48600e00c07503400c4044490401c90813141d00c10841e41d04900c070581e513a00005031031600b03482c1150800d103242490310103005401d82c181a500000200308143c0d10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209803480 1250 209802230 209802277
    0x309050a050318010906020313051512010e010f08010207080406030e03220e070219120e04060e0a110a0c02010e0d0f030305010312020a030c0204020c0a0c180507080f060411 76
    0xc90151180000366940701200b1b076503920a980b288a6140e490310016600d510070b0000c2c1c100300c419100910600220b0f1464a598500018075040c2c080c5c000d00c850410300b2004100c0103888800317210240480b680210301d040c10302e0b6900c0f86c07184264801c10040c962184820060000c0c1031055460511160300200604034800206008070040750085c4411124000046615940700250904900c05a207142d110e20725190340310200002030b810681010060018511003031502c81e8001d0400504250751442e480b8104856044256003105280302c0b0203203c10b10020030a664885814940c3e80e40a0900842c005900d201103044a940410058103e07038461503450201545580114100e038045c0c411848101107004049031611301454001d40002d20189400e8017502e802e40c002c1c6402c0c0c1b00c0034111141c0c51410369490010600b2944100f00a02d04003461201c00f081d50b00409a011195103040760303ca11300003840f400100e1000d050039010f103641e201107440c40c4005500301c5800a48240400d205200d0700b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209804730 1250 209803480 209803507
    0x50a06080103061a0108130c0807120c0e0403170618160306090e030a051b06180d09030201170a1e020414030708071a04050406141e0a060309050a0503 66
    0x2844200c45961606006400e00b04c034890642d508544141c0d00c024090300c5d00b241e011041ca022403410365803070038041400114140308108000007040c510301a0446040b10707060841038480b09034070164102c003102007088002540446010000720303003031070700440b41c0d200c05021441c0000f004500150f810a040f00b80075545100070040045640c10743d03414000d094a90300c0800594402000c4034035242d1062103015100c501990160800c0c404c00f010b00002e160116004e603203030940546114000c198414003143c10307054180510040500c4604081480c2440c541c0000d1400c4204860201011400e00120342203441e80d800c00e200e810b45c403091402002400d0349000b40294003910640c0b0021031060703507480ca01d08002c81c049045404c1d03100600a564540b101049003d4041850080307805002c000c007142e0b56540707100d0480070700360454000f0104190030050003092169504c4400b850310442d001205556949003107e0213580c000d1401054072521032826900d0308201445c000e010703000118a040c8030108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209805980 1250 209804730 209804747
    0x908030a15050102370809031204051003020901050d060e16020105130609020109080a0308010e01050409050a0206090409020405040620030c120601090504053d12060204050a06 77
    0xa48890802060340100303050704044681d441001c0c0560424a4900b407202041d24107001c640b000c003450322a840d44940c64011080b054141c0c2111445400315000017036003010404401c600d0600800c90303203014100400188040400e2540408060300040e0364080303644510280c0c2c80d034001540c8144021910364040842c0d0700f0040314004c049014548102000170701c140100c0d4020314a01114040003002a121708000d015110070a03414001c0f005000104008204600d01455010781c2d5007a039294140014805000c0d03060740001d00c207a0800040c400401d401103201c3c02c0045c2c2c11518182e441c5030341c40125010f0302d00b00300081d60151a2208000c01e20005070401490b154004005114294081c0e116aa850105a0303e07942e60b94801d00c43c2a0304486400705c91900080141012001c8a68440028060340d008403007400c2610070b4002c410039402844142d40f408a01c18102e081c5055a0f407030014040300005208041440850603140c9080c06100e0741241c01402000d401040703a581c81c0c0601515401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209807230 1250 209805980 209805991
    0x516051e0a0b0705070e01090c03051302130c09050406090e0c0306010308070b0403030609020f0c0f07050d03080c0706020c06040308060d0f0b04050c0a0906170303090309090c0706090803 82
    0x1102000c4010302198503440d55120010000c158018031400c203141003140b03400804007103e003407060040210300303d5034000040d40208044000882c031031000e408003c0070f641019003405100c070340c00c0b00d05170010398604003c0310000406480c00903000d03800344001c4645002a40c0041d400518002d000b00c0c000c1c3c0f05801c40001816002c0031036240481c40c0041c90b40d203074800d01c805481803406201c500000380600001e02d4002d0b00915001c00d146840e000c2481c00c036404110701800701c2c000050441c6e0203c1081c0600302602c0302d544060841c182c503080110310f40400318040241002100d400256940840d181604d864580140086403595045842700703985880135101a00400c00613000551245401c01c03000f46080e0b030100341c49030612001e544001d0355000142044609025007007030015540c444c0b042a1004144041000c19407901c0c003902400e90704402800c401d5290002c0040000300140001240c580341001c0c0c44050083e1717507180900440b4090318500030b1050381030010060074000301d640503602a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209808480 1250 209807230 209807239
    0x50a030f1d01110f040510170a060305010e01090b061306120308040510020a17060d0f0506190902030d11100606030c080c1207140903030d02040603112503030603051605 74
    0x1c00c001600c203c5034020b5074011040b002d001c0200b80414100021b450041c4103040c245103448001310041c540909008540303040140b9540c800400a01074240500090078003a203000b0030a044840e20351540031070000708402c2c05280b000725142448400782d0320001c01840e2215030002401d81900e402070041a09481c25900c91140303003880c4110507240e20032214150320383e4490340c0c240610215828105e201c000e091aa1094000740705902107005203449000851140c0c01800517450203d44140394007400c00040c01c1c1e200d1402ca40b420050314009030051101d40203041c07240506554a031402c1c5020b110680340a681b9061030000901300d0b1301500706e542d40380741e15210000c0f903556010413800c0c03038001c986080000041a00c041000310740542140d002c5c1110748109280b134000c0c43d001207469544075100e40c60042d54009420031005a0520846054003046002035241c8680760b0209940b80d582048410005101c0f0341e404400c060007503210000840e484425103010300c004000c4078899203013520989008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209809730 1250 209808480 209808491
    0x809090708010e0106140c061501030f11030406110405101e050702090414010f240603140c0901020a021e090f0106090b0c010f060810200406050a030f1d01 68
    0x28010804a4180c03842d442c81c0700703181d1703280c110116006a401c286604107074108011000591a040c0300542c442c40014105505503400d15000404490f114041c4c071120900d4100c8490010207403904032604143c0002006c80d03003c88106030640c091103070340e0142380e028840748164048107030041500d010b4030041c103051918002d0903680547e02403060315002980701911000240000304641518510070010000005000e228200c61400700c80540700012079040c41c072a103030488203110000000240a1514040c0102d100c0046403110b0340c81c004d0b00c0080051408151002e450b4402c20481c0300c034030380040040382c00d0803005a002600d2401c8992080c000d030024400104011082c0d0f9006040310900d170b0b10311040c0d510702421034816401c0002d03005415502c40f00905020811b43c002c0e1405000004098128070881e1100e0b0412a04541d2003210555185182c8404002c1d441c01540c088540e1800c1856580209003004c030010421414000000d03850040c1c0200d1040f0307028007000011001e40d008000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209810980 1250 209809730 209809741
    0x4150305010c020604170d090b0c070b01090c020a380a050f1005011b08210a110a08070314070815060301050915010216090c1706010f110f0a080909 65
    0x8640c002205c002d0190810100302c040742c042404000d006440f1035041c00a01e03419039a50701341d40240181c4482c50365840118200040c4401c0c00c0c0c04500501941408000341c0c828154040d4036454540d074041c0c025404040e20201811111800c020006406512032841080780b02c42480c814074140d50107404070b45844001516203040c0e6003d1409003c5040011203054a010011a40082c02481c1200301140c17288007400000c1260000e0304c00c052011030210002a600aa48003452a00a1072500b5880c14003a440215415401c2250303210022031074500c0d942d0352002030950250191460340c0e0b00b615003070f00c20004004e0340902d1460161050454082c10701000703c1c1001190b00003805240d84c04507010012400c4001c2100d1382400e80001801603404515440609888442165014610094131a100600801c0d0b100d0900350700300e40441e40c040302604110000800742c1c24143d42c00c40500c400b15030102c12042d410495444081c0c018001c45801d1012880c0040c10340d040300700704600410032031007c00d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209812230 1250 209810980 209810983
    0x5030c03030a151202010e06090102071a030f0603071a031003021305071803241d160609140906150c15010512030a0311070218090607030e0d1d04150305010c02 70
    0xd404d250143e480d0502d584100c810450564840303d40c03981548502c83d0001600405111030000c00f42d0045011a264038000b9050005204010704644c485d40100205121090360307d00d1148044014480144e160b6444180029440b80b1940000c0d5000c40500110340e1011001e4110314400c034041d540d061075220f80403442c80328951644c000241307000c002e00b0607100c0c26402d400041e400803c460b600440c1d805041d020344454410340e9649036056400895813034001c00d0741c228022004040c140741200400e403400525182c010140019507200350402d601103130301c41d42c41d142400c200103c4105015511010002c4056442055040d04160401d28100004840c034020300c3c0544102c0301c58018615048004508500810350795a4030404003c06026980158030349001c0b02e44544004040c8101c18200710707042c24a003040040034001014100440c0040b11070000c141134485510a090282c0340302001060180d00c0e03060408141c1d003007843c00c0c0081e42e1410310a007000080300c0c0110020844006198002c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209813480 1250 209812230 209812259
    0x7090503030a05070b06061b07080c101b03170709230612040812040c140a03122d020c010f030b03031e0d0c020f0114060f010c05030c03030a15 63
    0x4404900c0038040100404e5039104000d9100b0703c01445c0c5482c05023891038010b10862200d08502c0f40e0390088600f031041c1403040000090510f411601c44106007400500100030701c4543d480300e5082c12a2050103410540541c491500f0714248855204030751500d4000106070101d030b4400c42188070082c0f0300040e00021002c05141103400040d06040c5042c49055196440d4100504200c2e103c18040200d410f4044c01c3e01c1c9001d0145100b54414441c1318508030441205075680344416210f1000014200001441405402c2d41c0740c0c414100340c1d0303007407901139078003104800f050035468003d07085a01104850340d801706612040034026211030301440c90b0030f002207044a02c0981d040383c15500c100b12008100740120388280c501a1407408103460080c20542003c16607012202201c09a0b00c01115156414000e01a4400520581c3c03180c039160703d4144000740902840d002c1c40ca05000840c00081d0520000340121a40d0311282801c407a81c82c00c00100c0c80d002444013000c29200d2800030035010070100c1c02260344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209814730 1250 209813480 209813497
    0x9131a0a030c030b270604060501050f0d03030c022b020607080c1e04080a0f030905060909040b0a090b0112061d0307030f0207090c080105030724052a03030709050303 73
    0x39481242d0071984c41c80e4003c000a815001e40803903c5615642160701078040480b0040040058181070030980f41c02d005030b40d01078018510500084129059645880d1100b00c43c140d014640420540c43c01c400990420b03207030054108800c80c2c0004d280030480641d0304980380d00681c81c1c1c00c03140303243e4a07400d045507030240031f44640007000e074100900e80d421038402444000f640503001503245425903030798503036191811650044a14085100c0c0210500d82c04c292a2802080d007a2031240c6880032490004d03012403002400100041e4120011031a80c800300e60011441e154043c103041003550f1164014058910400403c96080307090030062801e0f141c00100c03d1120058210043d400c004440d901940d284c103100d000340085210750800080c05007214000c1004080081c2c99003400355040c8410b040c10700900307410954000c414044c0c180700740400210451030213400b85c5802515036200e1941101d480c0042190404030701a450600301c41c50304044000c600035515a240c180d1056551030a2540707030302901c0c42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209815980 1250 209814730 209814743
    0x60e060114010c110a050a1d09070b090618030703140d0f0c0209041403041206180201170c070c03080d050714030601030e0c130c110c0607060e0309131a0a03 69
    0x550030020350703c0070440c4004c000084c10616680e8a03000800d0700048035074410184000c40c071480148120311021456040107403440641151820b20086140c607118a0f02d0542c09120001a07103141c00c600c0e43c1403030503400e0000f804d45400c00d6603824012840b5404c508480e6a40c0100058002c826000c0c82d010455841035171100c9440d0a550b03001c001c04680010402d84203034020500c8011600d805200030f00190400500740a140030b00c1c4d04109044480c0d0701582140e09001e00307a10390240c0c1c2c100c5d10300701d502e80700d2200342c8050b5550520841030500603c0c100a05810481c500401080104009001900070f4140c04004543c0d90348c401301c8100d000f802007034507608020404a40c06500c00c0c2c0000580300410400c4500710207410000ca007004c80300498040c409581c0d90b014007600e65001c100c0f8010301d1241c00041c0100301800000480b544a00fa800401c046c0e81c3c0e804020301c1e004144166207000d440284a5828000140750200143c606024080520340e00e42c04e410341c032841c080c05542d0a4903001074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209817230 1250 209815980 209815997
    0xa170f0105010f0c0507060f02212a010c1d090403080402040c0509120303060301050c030708150a05041e2f2b0608060a110a1416060e06011401 63
    0x100103440c481e08240903070042092104d00c00d00801d204100c0e81006000c1c5a9078030503c405a09002410401c0000d0700180e401003081e5084540c003008419903400390081d89218031203005203001c0ca070902c02074640d5200c5550038256620a0741d81c106120a000300f03411400c8100c00035110080110440007110002c1c00700c0e0124000c00c0150070517074400121341c2c00c42d04103145008000c43c0040c10107030f1302240c3e0303244550000080014608081c0102500010509201410742c1040070700a0001c0d10000d0a8144210441803000031580e1031401c000e0041c41c002d00100080485001103070060b407002c500c0034803614100300c85201d90441f5032150791000c449916034400d5400b0a0042c0c2c0080d540180c482008140c008a145240b4980101d403050700080f002100041c0c43e80b07464206810a02c0040400d40d0f01d600c1d18030040200743c00c10085480d14010b42c070302415582d502c503a01c182c1c54002e10b50f200d400b00c6488e030409001c00030980d201941c07400394141260603503070340c3e000e9480000c0c1803014003c4c0000d00c1038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209818480 1250 209817230 209817239
    0x10305060619060c11130617100c080117010f0c02030d1401050303090105090406080303070507110319150e0f0109020103050109110405100302040812040501030c0f05041a09030d050a170f01 83
    0x12042d17901d00c0c501c0140505517000c010054a8140d400517044594180c0c46104152a500010017103070101c540d0301102841050f0784d00801400181c014031485510b050003090070030b8152404c0d804840361158006040081c03070b0103080020b40d00d81207006490515480c100c00c8111210240c40018103d6034000d00861609009800464054001141c025041520f401003c683c0480a0000d503100300c4051352080c0c2c40300c03a6814000d00045042903c43c5c000c0c3c006030400034541d10703500e500207100ca8210169586102e10f020a40d03004280c90340322030720280161602c82102c440190080c603c114000d070b0707043c803160f6214003800e02110511006000c09180420080181c2c5c24000d204200300c0d82c2e507007070041c00d0554400403581410300361012000029400078041c0025a018450030382c0d03103005864401e0500d0076a40c1c029085204600844d210145408000701e2000d100908542422038003a00342e5200c4c0b480310358050290380120311201c02088604450b51081410312400324813a0301810004c0900b80d191 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209819730 1250 209818480 209818493
    0x1e08010e0109020c0a02060a020c19050609010f0225150212090d0302070b120412020a0b040602030a06081509011d0c010c030e06031302030c030d020c1c0b010305060619060c 76
    0x4208521401c0c00b0b21710208016a582030050800c10070306801030000c0401c100c04000c19208404140c09400d207420006001c591600c10a41d514242c0a0904228410010005a1424240d00c110313110b8180412042c0350071500242140045035060300010108500240059031920845000a410080c0921007004a444c3c0800704000310740c040c0c0156031030aa02d440d44d141090344100000218402c0c940203004c200000c4035044c560310b18540c4050300189005580340816510050b1001e41841c0c0c02001103000e101895200300001d040981c111455001d2850806036110001c5411003130380d5113050000c0d44000940c08a0442c2401e180000c2d1450002c02001514480b001c3d030815000c100480f0722104207031711440011030245031310110301c102100d5544105440e2658034022540607812400f80b90407a00d40006092252a10450f808084029064004556120f540c01d0144c54540c03039000000510501088243c0500000d90f003180741c5078840142c40c2d0078a2080c0c80b4103000070302403c0000c00807582 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 209820980 1250 209819730 209819737
    0x509190f0201111009020a05090702100b220f05011d0c2206030e2a0423040803090f0304030b010b0310090608030a0219080714010e0d1e08010e010902 66
    0x41410009805950100702c03500c0d02c401210344c8184141d0700c2e2049401d5141a41010300100b2080314a81c0301890310b00002921442000d004502158480410740320582d50400c69241340120741d001c458001d500310442e48060640410142e41041c40c082c001304c2d40512500180084c0d40c5401410346c00c503103038140c1068490788403030352800c0045a5a400c013094030035940900001440301e07980c01300704020034030000c9007080700702000280c0c0f6041803c0c1070f1500602c00102118100d000302c9002407907070000303811010120f0305140300b1105060b00c0c1c0d00708800c100411001d113005400820441e503030b040003110782603a00d100c0e5010191032000c08000411031801d1b118000c1d9480b52240c0b07001ca10707155680358402c0a5440d990045000c40d04042b07200e0265550401c02e00000100b0403800d004080700c02d0f20781d44500e100f0780d0300240c589100d00341c1c50350f60010b00750400102e640e20721040b41c41d14003030400001c01c140c8424441c1ca050b0100c00e00580010b601c1096494181d03810504014940d910b4040030034000d51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 209822230 1250 209820980 209820983
    0x7030c05070503062d0106021903090302040c08041b050d022b0822050a0306200f0405040e01050f010e07111605030601060518040507030b09070309020102010509190f 73
    0x825070001158948062205600825a420350400c03070722408a9111144103820b54034081c15210000100000c0303600140403240c21104105250580d030036410121000ca081c3e4002139009806c01ea0000304156010041601c42c0780110f52b551307880e003410f0301c1c3ca8418002e0b5129051344401c40108010251400e107000b85416000107a100d20354130742c072417181d40c05280070f030b0000e271481131000c04c41c1d03800750764960080d4804840c2800303019411400e240009224070134900003d4407042e03072404200102e00c4000c1d070480c107440b0442c4485403a1040c41c2070040090303000380103060007642880030b8509501e5050240d1401890349000110f4143e00f003290020109070028080d0082040c0002d82c0700c46050700f400a030004803840050580c0c200d06050a0525026043e4010800c0240801404812070712031024210301480440b0046074a441e920421405482c501034881d40c0071035401c06003c0440c0d0035500c0524014402c0c3c0013800560b4030354640c1c585030a6040040e207401d04442d1202800641d00521408015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 209823480 1250 209822230 209822233
    0xd0804031707060903020615030a0209010b13210501060509041e02010201020f0f03010e071e0503060427020103150807030213150f240e130f0e0703060b0307030807030c05 75
    0x101c460340350740303055404d41c1c10182d015030440d03018001e076100030360240f14444074254014030440c10300e5808508130900c1440750140011012803a0036800c0303180740f910401842c182d62032030004191603101040040103448201e41c15803910400203000e081104a9510454101d11894403c80305407130312110f510b651a40c00c81c11550308004e00c0580e604180c1c041e12a8a2040c0071250b00c0c2d6041005c1030303110982c01b078088001c0c044107402039840440502c6503010b482c54185006501c81c0c0714240030074058040861204143c400e030b001c00c201a043d000c2550032416001366800e01601440c02807801e072500305e50190720b0198100060520150038640c02c00380d24900c41d98030010301407000340042d126906d141d0700b002002e880345010401c000b45107004011001031a19580d00c60407036a07120003624440025075014090141e40e504540882800e50180d6403441406c042809100c0c6100302054691885000031207901c0c0ca4120000c055040010300c160940381d00c43e817400d290280d10f4030140c5608040c0340080702e03203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 209824730 1250 209823480 209823487
    0x2040608031b01050f06030c191d070305070f091a07060504080a081b04060e03030706090303020307020d091503091e05010b09070219080928090b0d08040317 69
    0x51a010030042c42940e400e601c509070b6000c0c0007400b480c2034510280c604060056132400f8442d49903804105044100c0e01203400c520311100e00b030000d40c0c8510199000c1f00308501a0f2007002a80d50807844143c2c03149685980401c0240c1d01da900c02e1702c040405404030400242e0f6004144202218030241c00d00300005032650504141c07440c1e8039441a124100ca0485a070f401c007043e11a503035604504e00325005010100359814282d800144000300b40134a1081782d0411440750990391190305c043c01110385003508103109112130045800c0c050b0181d40103640560061003131703042482c90644242d08001c01d455049000d9074000302e008400724050a140c020a5403081240c242050a89140a00c8950030b58451400403440f54031910400c001758000030301c110190b4021000510342046041d06200445a20900c41605c40070f4640110321030000d141a045080e0151240c403080d00150002c900089a4020200f03104400a00d01030102030b02c00e4290042264005100c188009840c2ca01c9005c00d044000310060308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 209825980 1250 209824730 209824739
    0x60412200714030c0907120209040e06040b04120c03080c0d150608040b01050609031f1d01140108031e030a1404030512010527060a03140d0908120901030207020406 72
    0x102580e5502240a1086000d1042110300f01804040003496040ba60303080da501e40100007402c2000b00d001c98034a40ca0740010b90304015070744c80d032080008100210448599240501c0c103852510b83c21340e020354480c4149030720803d8051003485207030f0000b41d0580d6003498030386070144c1c101d15580205214450698880402204d40d840303604a040003800382c2d40d205090350400b4103145517901c4040c0c001d04c4c0149010802201203031000581095104404c1d240d8126484682c10b0b01c000410010104a01d1084210300815148405401c80301024058440e06240343c0d9035045055a00d20848a00810903030504606000340700420010b998040d100e100081440c01c2c0b43c420300c418045040b1400c074017181021400030015000c07a01054058001520703202d4401c589404a040407000100140075007a0000b80003d900c2e031604202c2c80c0041d42e000038503200320301031124050b440b540c402025a0010305260703c00030345803030001132002c1c11980705a2254174114200380114081d41c440e10041e41c005460300300014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 209827230 1250 209825980 209825983
    0x501090215070c0f030c05011b06020d020c06010509070f1d0a09060e160801210203010c020c1305070e06090102012c010c0207030209010b130905010306090303060806041220 76
    0x1150301070032060700790b480c80c007458a080e007951581c0010818a1914405000281400a02d1002d50b035007400c0c206441d61a03040700100580d00481c000303000c1400070131642440030142c0c0140c14001040c809864580e070726542804004002142c4600000f405040781010b84c9000345101c00541007031041c2c45500c1c0810901060710b00425910007417400343c2d1402c2c20017410401099080c1c224410568170459600c0744103004051401c10b01807214031945031140d1440c6402d04822040380729601400074001000b072603502a407200124045180160892030700c404841e11180f1a15114116a4840128250b0581c050203410341264100c40e041d0741da9580030714010015503040000c4000e001540c1840c2c510312010740d900391000c803105002958042801400181d440c801514155102602000c2c3c8039154a18801c607100e6140d40107070a0f9038a404008401d00001c2d410005a85011351010700005035035541183d550101100c000c7c00325207402d07015038030b0b27035101e024094002e43c408030841c0048960175030b115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 209828480 1250 209827230 209827249
    0x61d030111120c16030806100f080f0703060801090b060f0a03080415030e0a0b1807180513020a0f030c0e0403080402091005120708060a0e030403060b031c26060f0103050405010902 79
    0x150046203e4804001f52460304280f210208025490401510b600703640c00a05089406001102c25a449600051016100c0c1d800300000780b001c100240000315039414140003d85003900c50030b0041c2d0045248403504d01f012540a41100d500c940c825190600d0540e12100303036240360b42d100701050b0320b600b403d80c05444104559032840c1d0080e407a04030981040000803410200d000742404c40754204d501c1c00c01882504a00b4500072034030030b420100301035031a051603200104100d14020352140c0b205002040c65526141050152071040305200845915440c600f034120004503002070000f241c810000300141030000400f50400c000d916000c1185072684000303400030007a15143d00f0154843e800c200060b04003004000d420800d403071400c0100c4c02e10b45a440b40c8900c07407404054030301ba0b2030b1403c254040c0c13030400070183c40b8800702043d800001c010201c01000c00910031010400703001404501c000148070b40501d140500d00051415841061010054002d031400403c107030340c0b079540c0380b28180150b1114a4031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 209829730 1250 209828480 209828483
    0x602070204110c0c130b24070b0103080301060807020318281d130c05150408150702010c0201050106021e0f03031303080a0b060702040207140106061d030111120c16 72
    0x5440601300200034011403c03802010000c80c141030948042040d100c80c00428002c4000319002290405000120146449000c0c0010402d0070805c0000080c04030040165040ea4095503440c0781549079205d04982c0d81c00fa12242c000c50b0040300107010914038000c120204210f48183c405182819000f02d448042e01e03055001c9030071907002040e1016034140c58107041d5800302d200c40c0e1000e0401c03201d445190300c080c000d0040f14041d00d81c0500a0007020729800a94004144100803034000176003841e12000f00d5041136540c0c0000d0740c280703000010914018014036043e10219801019a0181c007080c140c4140c1081030480c1044c0a8130102410401d0b061006602c5041c03040f88407007207000c4600d00102080c0c2c0c014810400c4030300d06145c0042656a40301200c003040d40494015031070700e600d03080004007a4600104105035602c1c0600024a641d0001040310307030400f164003003a04042e42c10b0b0525080c0c540307900300030041c403004000d12002d0489000d041038002d000b07080360300c0c107125462203918908042d0303150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 209830980 1250 209829730 209829733
    0x21c110f07080d030f06030803040303020f13080c010801120b0f0c04090f02090a050d0f080f1209070e150102030403080a05160c0905070e100c020102011e05090f010606020304030602070204110c 85
    0x1203000041360180200b1016120900341000000c0c91030300ea4006901019100504042d0005030040c03091003800c090b80e40305084034036081e210a90b502d9951703549040c03d50b416404145124000555640d40120704503225401058000756a03859580d855142d160003000404448030a00c40415400210301c5903494080c4010380041e030b00c50054007040400740c802d82c0403d108404000190001038081c11a0f031072455840b0708807580340e101c00d0075910303150b00070700c68041c3c2c0c60b1055000f0061000c1e800a200310448244070000d540c20b8440144942004000400e45405a40200300400008000a00504642000b4076040e801c00c1070480410410200841e03042c2c42c0a242c02c401449034400c1c80c4a03058000300c141c02c03e18040d00e660340104401d10110004a1700303000c0b00040403004d59000b90041c10303020098076601ea218a492100c0200282030a40752a5001d1003050034600242c40b05208080541d0882c1d0000c5040c28555034918020b540040400c1f40c0181c0ca40102c80c02c0c403840072000e080800c90410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 209832230 1250 209830980 209830993
    0x11010f0608010b040605061207030902090403020619020310030803060a0e0c04140405270115170601050a05030a0b19020a051b01061a1305061204030906021c110f0708 73
    0x41c900d4251929404000e202d42d1030b1500420182e6104012135251000d1074181c1c40c05941c030010103600400040390302a41242e50b080800040503804502148644a05a59000014080402c100890001720351342c88a40450718024070100343c41d1800b1355400b04004200212040d259290384003200400d40c2d420b804014049000e01c00120f01c10781102c50ba500588040200d8904004291401031003003050802c600c000c96421104490290080c00040c154002040283c42e91103032143c850300c2c0710203681003060150388000310383c030b241046403003080307480080c0242000030703d903261404103c1026141b02401c902000c07803004441000d001802c2100d50380d85515440e1501c3d00c5034200c5601d0101460892a49006400d00c41d9008295080700064000c1c0c0ca072646840900d041e800100c3d80ba90001c503880312020451285d5207403100c902a124078400d54401410650b651010390f07440900032610108074203c03003a81f101941c0f00f03105050baa564201c044030104940301025a041148542240c0426042503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 209833480 1250 209832230 209832239
    0x30806010f020a050c0f0d060e03040609140a0512070806040b06150a020a080c03070203061f080a030c030c1a1003060e0c0f0f0a0302090a050a0501090509030904090311010f06 77
    0x1c0081d184400d1600140c007030200c0075510745403104d0001010758440d0342000348103d06500c42c90340c0d0107d20f550090082111100100305035940e50031038419078000582212000c6640c400341005203011400142200b1550740c1890700b000040e03603a0202000d0345100c1d031040043ca1210801c417090080c0d00034203680c000c5007404001d00465120b4540c0385070028604010307142c0040d500059030219550060002a00d5410100c080c41c154801c2c0c000c0a54144102030a0005000c1c1500c030030400c91264541021405941d503030541e4844003444400b501140700c0f000b407500071074017810114540500c18103981c803c401c69034070203424611041c0c640c1124040100800d0040080c0d0b4891592074031071800040a5000890001031400f03114448a1409410400050861038546002c414040c65000f4214035141c43c0c450180c60080404888508029050400010300392038584500d50081d40540080d600d07004505080c400035161040303044081184050340001100740c20301c17400601c140f454801091051a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 209834730 1250 209833480 209833487
    0xf06031115090a0f1e26071706090c0405010501051c0b0a0e0609090708070501030e0102040801050408180109051305130503031503070b0306182517071103030106270303080601 77
    0x20504442064601c1079410b06c1a507600300281d4100c5410200d20903820040100e0b02070a00d07803076a03c005964a00e0009810b248400420018440c0204008450b9801480070810046d500c00f84075560101d84200401c00810001d100390003215a014940421024010404181858000c0e4000d5040721800014407220b40f0f4641c12143e0030102800c010718596042141c095101c2802c1d2045905040d0b540035070b0078030003000390151001082c05074002c202c107103170a06015000303503c9003000f05030746606082260b00c59030054000c0c10070340d40301520a02c0000301c00f42010008280140851696544007850200011803c00095210f00403402400c01d1100e940401e0516002494104107043d80c4140200b15094451900752040303017241ea00e10381015162000e00440c403420030024401d1001c609041040384d41e4101e030400128842d48610343c0c80307039652a10111071400c07200c400c00a03150010001040b050388151302a0011942c060707104103652840c003845186000c0981d008130007180b0b010b020462290b80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 209835980 1250 209834730 209834759
    0x1081e04061a04050103021e0d0b040f03090905090601090f0b0307091506030e03190c0507030b071209020a05042408010b0319150c050702030f100f06031115090a0f 72
    0x20b055070305010325410341c0d0002d00210914050074103145101c030080c0101d580ca4004c5500819003005008281d0b0a1030300f4404811401b00d1010381c04607a802000040c60b010a2060301d00c2100800003500c0c1603404d003607046020b06415403041c0486621020410203d640500c441001403035140000500c45401d00c1c618a2b0a480c2944404285403402c0c01000005a01104443d400c5284040c0c3c0b80742d10360344060a551803c992900a8841e100c0d04c03002000f0003020862050081081d034803214060511048684240c4c1c0302c042c00290442c41911040146003055001b2111a00c24403c100806d52224490703c4641441980451066034440c00590601c0c01d0a0240c0c001008203110595011080c80c0c941e6070044036805540090b03540d0b00c0b508501101c0c070990982c0c0d920b03a0b0003400e0341d43e0450003440c0c44c4d40c1d07030041d403580103240c519001c0c00342c4111b0114801d480440740c1c000c040041d5401e42104020040d0114082c0d401000805c0084100661359201072901904041074000c540c00c0c2000e1204c0c40b000c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 209837230 1250 209835980 209836031
    0x1314070612090203070b03060301110a050c07152f012f03040201090b0703090b031602010501050108090a17040306020f0409150e04020402070303110c0d1202071101081e0406 76
    0x42c900781e548070140c1c07000700e0401c050398407007915aa900d4403180082030045c048004825030200f004115180b41560000c02080490080c1084800b19a11882000701c041080d00d064400b242c80c0c101e46030b10303107905400d201001c82130300c0307035503070218046181d001e8292600341034582c0d002e03984218504102000b10201908143c0285080ca00b5460940c2c00a4214802ea0282080d0b0000c045150300401d031041143c000a0400542460344034141141d216543e0042040c00c038000d0f50900001048552144a066208a0000000300081d40081d19011462010500442c5c1449030130000440890b0b154002819a1a0b608031101d035101d103491102800c07541d10101038911840c1614080080540d0540429001901151b0040e40c4e40340520741a0018541c2145000d80d080340818880c56445001c200d1005c842c1403910741d990002030341c2055900324860b401c4010400b050700305c09d502e100d52060100e0755101070f01c0c3c01551010312002c508040045002c40e0304860a94450702031251700c84441c00140e5485 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 209838480 1250 209837230 209837267
    0xc12030c0f0705102001020a08060306090609030307050702010c21082802030a0f090b0a0c0212030103060c140d060609090b01021b0112051003170c07050913140706 72
    0x20350800340001c0400c4501108401002589001c120391150041c245038000740c0d8505c021550f5450750803025205c3ca4048070701610034000c0c0c4000485065000c680144902990005140b13151341c0d54a00b541c56400001c002c2c0c1c1007162420a60340008c0044103034061981c4500070040b011006140010000304004002c0b001009400300c880d030350900340d6041c52032010441c40002d40c40ea99481d00100c000c11014040079085401e00d4504400d200c1c01c40038050040114180c20701551400100590307448282c0b640000105601700010404681c0980c0480c4240c42507240c410720030046240f11030720f82c1e00300a0302800b01c0350b5144010801d40e40c101c0c090034010030501c081800f080c1a2800043d440f41c4142c0800c1c6c0032540c101c0641000707a0300c50452400740050225040145040010151072201e8081c001182c8820010b1100841165044191500044200018400c043c1000d00380242c641010b401445400400881040002c0c800c00c80c0b800029501d0000b4224189024401000c04240ca4082c0c2d00c44e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 209839730 1250 209838480 209838493
    0x10510020a030c11030318040b041401050d030e1002030901030b1c031202090307060305011a070816030c0803010608070e10120207080f030c040329060d0201020c12030c0f 75
    0x24140c010404034803080c0c050600710030007056420031400c1c82c82e95102207a030601001449030f02c20450021b083d50750f803006403070402071142000188412254510400b4910083e4407004121519080c0d030825130181c840d18100c1c0c40e00c88180e010031360340d480002007a000758001150100540d6414801c845010300c0c104c8038803040d0500d01c2007010001c00c14103000b8040080b0340304800c0310141c0e030350111000741c00050222100da503030381c03503008004140c28041c1810300b18a000c0080d80300000c03801500d40050304a11080d00d0311801408803d1460712100c4224140400e0618000201d141c6001940c0281042c0d04e91100c541b41c2100c0042101d19222281e40c403641000010302c3c61160311072140c90703062000704001a0781c0c07080c50400c90264002c0c280841000100007040112003002c0b03078090012640304d02c40c218091844078032450400c6038058142e40400d41000300107910762422340b081c03958250040c01916801d01001021644070400c403003411019500003d10b00d13112010400074014548002006083d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 209840980 1250 209839730 209839759
    0x10305060c040e1501170106030f06120525120f020907020d02030d150302060409020c190809090a090c2d030b060d030908070e06120610090e03041d09060105 69
    0xc029004d842440707134010b450503000301c40e40502d220898a108034000b52040f507a4400000b005000c41100b00140c85040070400542c0b1b0300d014114030507407540f100152200e408030305000c0d640d46401c18085280da4074100c40c001055603425042d600000e00038800303103207074407a01d00600110040c0602040115800800710030b01056000c03041d550a0401000c001c92421907a410310f89001c00796800c040e40c032041c0080d00041403c1e0581c018500e5000c80000e441100c13400002c0302901300d900c940c0103003126404011010b12840c003031a226520008941d40040e59128545034149911000d4008186e0b03101c0c00c80404111050f10062105c0c8154503000584030241181d45000d815080508000e000e041d0f4207240004040c010008200a000100c0407140d403103507a217261854043c020340743c66010f004010340710526010b0201740c0f5407080c41c3d05001031802510300003241e00209144102c440e42808140000f08103100e44010241840390490b51201041c1400e4040c40c0c20001c060b882544500305c250180784 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 209842230 1250 209840980 209840999
    0xf021c090317131512020c010603050609120409020d240906050415031e050a0f230d0c02031204031511120a02090307090603230d0e150c011103010305060c04 69
    0x10241c071803a5101c07102d0703859480805e80305003480e11481c0d01036500108080c4140c1e00e0540c0203034110b034080d0040b0b031600d44851900c01c2d00c900a0759403d44040c03d0401092004552030b800500c481565030b60300146400510050040d9802000d081e610118840e000c1000320513218082e040c0070f45002c550801026658001c03400044105200040121074000515224028104400c2c00120b800c41c00b6100400c2052410401514654408858084254007000c1c4514640c00764400000c140c5002001000704100b815290142100b4007241d2612070f0b0700c000c54191401c1c1000c1c1005601c0b481c415080c0040002020050350700700054404c0390a0300380320a60380c2c208000311583d0041d401107801079076452000f02203410a03080b900084411400d02c40300100308030200300198002021680115411000303182d203d9207862001c0e15140c006101a803074107100349400c800c6403005450882d500b528006084050f542075031501c000c60b4800d181c01000402c04e01c0024411150301007040c00403240741904011488 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 209843480 1250 209842230 209842267
    0x6060803031005151b0a14191b051e040b0d0507060807110303010b0405040c0305071e0c3002010c021b03030c0105042108090a030f021c090317 63
    0x92052582d2590004c15071013031000c451100c25188040c00841d01800c2d03145907200c6200c1c104480704c070828064201c0001c004265103407103590120200c0500046501d58110b102108601e40c031070f051801100140c1c07940d03000102080200040d401c1032030103942e1402c0208071010205102d0042100d010040b0002e8004120030040e1112810025225250490708a400b60011111048240300000010500d04100341c040c00c01c0f604220740030300030710003500d404038188c4000750340c41400701d00e0902d45007500d059080350300e4180082a10f480400c0503501c0d01c60000c01000d084006480c03000c9030b01140390405852001640c50300784c5000a0000100da180003e43d202c0000310b40c26004182d960440340c040c0d038240b040300e0800503c0d40080c401d5041a00346107080030000448a00b0081c8803401400c1c545015201d0544942c0101d0003a00210607152015544186910080400c5010b880c10070401850340f52107000300c40d40f075941c805101c1821860043c41c100400152031400310000d026801e5030140c800400f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 209844730 1250 209843480 209843489
    0x306010806010b2a0102070c0501030e060105010f14070b01050916140a1115060132090a080a0807060c05040e061e041d0705010503040201140c0a020904060207060608030310 76
    0x107041c1d9442d5101004c0c004c21300c4801c05100c20007616a00f551100c14150080c2c040540181d508001c050350714070040d011a2010805510a50031040c01000958090680c900d4524100e05001481315845840156030340c0c4286001c45101815900620050070b10080c4194000103035010580500303805480900384803d06c950034a030f07002e0009200152244100d03130616082ca403400c12556040000d10704005205011a01d8a0000b01c02e842481022110000078403081c860507501d41a0a01c0380c441c00198540c45030110b103030000310402e000620240d00708030160041e4011908162221140e18120007541d80200841c802c03c00140418030803503000816464000c10b00b2941c07901c480040140540d800c0e60a031685981c440e240c102c8079105070462040c0c0c610404100816200c0194840300103568502055901a0026041030030702d005c0304401800400074104000c00322803000310b00760b0000315020000c0302d0803a09150049001020040e050254001801e1568017842c190310b010001c2c6210060039109 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 209845980 1250 209844730 209844749
    0x1121e0c05071e080d020c0c0f010216030312180507140402090108070e030a051c030e0a1109040f050a030e030c03011e02071a0c07140d090b030601120911010e030601080601 76
    0xc400c201308110040b80e039480403268055440d001465400c0307803600700144980e4018030011514040c25032010880c80c600340d040c11840341080742541c80440d0000c0f00c10000380440c0d40d5030b110241940742d08480d407100c035902c80c000900805003058075800614402141480c0640e006100304201c03688c010001e55440307a142d01c0e04450f02801240041d03c2d007000c41e4001740860180c0c00700d00100700e05240032081041c0b81e0351020301c002d442a18540341c1c0d541e85290040c0600c801102542d4540ca0f254074141e4016014260580a00d460b64031483e081c9014004200e001c81c3c001c05139070b492410144030f03003000900b044008000340c0154903244004001ca0007074102d40e00d030b40024540100300e20480742e0b403145070324459454205d240c2081d80d689290b20440c0182c41d00386c2160380c1045a040c000034205542d030003545d03420b030102e0b280c50f004030307450303000580081d050190f07510001c040140f842c07040c03036400750003a40c2c0f080c09800d12200150101151400d4a40660070002c018005010b0004030607044404a09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 209847230 1250 209845980 209846033
    0x603240315060a060c0209040b041e110a06090f0b0f04080303191d150c04030b040803010603052203050d0f1e05010609050d11040b030604140d050a0e04090201121e0c0507 75
    0x40c0c600301102c841000b22f0b034840c0c0350700310709820b11020050180c0d620006032084c4030f00700e44800301075400c040d0b10b100c0c000440c0004207003031106070341250241040980100685007015202d844990035504100c505c040050f03164401c4105e140c0c480d011399450300704594490b0351000b00c5d214009455415419410400764520004607510903074203401c0350010358110440710520705152034429410b60080c881c1000081c2008045000303a07003000e40322500e0400a0f500c07a062440250340969840d08411800c20380c642c4e980a01c40e555a500d4020601000342c109041d10508031001140c41c112030041e044035082040c480e20610182c2c40d5600d181c90307180c0d040490b40c8074001c0071200040203000c00182c00d540500404081c00300f0030a5140100c803034103826205444680c50000c45c11141d80c05200c60420010310319076041500340c01c180c3c0c00050420b00616003d5003080ca80e1042d0426100f84112050100c0d00c403044084804540e8400e1403811000c40c80c0162030b10445482d542c45004190f4030313201d940d41150b07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 209848480 1250 209847230 209847233
    0x50708160806150d0908070212010b03190302031309090c06090803120a02040f06120f09020a06050705070b0c1b03011a150403020d06290603240315060a060c0209040b04 74
    0x200640318411118441801005d07a03a2030559125081942c00300d002c3c0c0d050510010b28058107014444001d0000b800402c1901d9140041550081c507414081d404c0d03000402c0b041c1e0713014289100c11806054044c4002c5982485890304840e907030201e5000300100003002e4824042c10b8400300c100c9126151103e45210a40c8500c50814002e2145a000c0421080c005100180094009040041c6500d908404001d810100d0080b101a12400d03900207502c15090201031001e64064001ba10600b8010012941d4094803460b019046911007403001c00e066000d616034299541c9941c1543c0f410007400e40c028003000d070040180c1c1603441010038101c0d02c11842020440c01c003c0400c3c0a65000350f800420b44240c03d003541c100b040c01881c0c0312002c1040d0f0201140da4a22552160b0381003000070201600c030398603550300c0c40c1f52425a036900c0e510300002582540d082e408a550200700c1e003048022a14204400c60902504100160100f64400700500040c81420350150f41e9038800c4980c055040501d9684075980c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 209849730 1250 209848480 209848519
    0x3022512030306121a01090203011202011412070206060301150f090b011404060e0906100c0b060102161e050a030816020f1c02030c0f0303032e060201050708160806 72
    0x2c581100f5102d45240c140c0c20b01780202d4100d03171307481c0d0b0440841700041750f42ca0b413200034180e100034061040c4142d4503140090040d48507920803003280f40d158040300e040c03010103900b01c501c91209540040c010780c41041070128a2800303104400040d900344521000c198640070301c03500d0b0f000c8a842890b10860341c8607004c003016406111507403180000078100b40d076107d80b100c101034888460482000d00a072030220000d2450704000040b41d01c0244c8036180c068aa40c040c1d0340350341d1044401030280d41140529400040c024407a21040409080a1080d054269095044002d448070f0350343d0141d40b01d00400c3c1c0c42040810380d0142141c062201640001c040b4100701c4c00810300c821000d00455030400040c1d81050784820548648001c064801c40c281c801c88001c0900b000303120040c0d240102d5047d042000415810351006601d410000880c110f441c02041400c80000710410785980f0940150f516001003005860b440204182d110399008504482069004130041c800940106400c0c00780c00091840c0b110b0411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 209850980 1250 209849730 209849741
    0x31c02010e07080703050d080108033c07060c08281407050c0c0301020a170a09020306040302060115090f03111302160501060e0c032a040909030225120303 68
    0xe2a001c0b07421480e51072950660794403c07031000352001e000b00c0709102909482007069034125000080110705058039a0042c0340c260811b00408402020444e15680c4815404808401c44804141e0150380724480c0d414003905031040300d5014820003c80d4010048101401c80d04200690b43d1543c0c4084c1003070400600d6002000403148100b420200481045421076100c2d0090400c0003514081d20024052401490700341c3c01589040004500344850030195008144032250b400324500f000802c440503607401090411000f55816030068100c00014004500ea80714280750135580c1d0f150500d605854803040030303aa009240001008007003016070320010343d13666158180f8401000c1c0021555a0b0320700c0100451042c43c0c0030308940355400d0040008002c8d0801043c02e02c0360005942c10703851940d0b140804030304c130540042c1c0c1512071451582881d5078100180b01810152055103000a826040c80c203001c0e2902660614034515600c0e13220b00340c0d00300c0d040c0f140990304440c440c1061021200c01850150b001c0e01c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 209852230 1250 209850980 209851001
    0x3051e070b0f06100906082809060212071b0303020307021c0203041508040503070303020c070e01080706140c1506010210110306040615051e040b0d060314010b031c0201 74
    0x440640521404004180310207016400845504d0780d8540c201d04242c034809143e204000c049010b801c0056840011300103541940f0070003045551004162186c40406c0b922a102c06490f2a42c0c00b02e0300800d4882c2d20462603400c001c050030401c500945021000d6102810000020100b64000c00400c03042030082000c80800720404541e56010024998001d54903045882071000519450401820550098000710f000e0b5411001461801e0040c0e2403d0f8081e50081c680f0340300c584550000062017058041600d40a00782400c0a402d420b450210300814201240e0101950008100000002004009a40d5400e4200000c410000396a000b0050f4144088d1082d072001d01400d2058054094a2035002184144005c40c0c00b04400c540f160060541403500f10700000220ba010070080020b180003050070802028101c01180c50a616022145c03c1d9400001c20340f100c06840303040500c10480744a11540070a0140802004008050000241d03030b0715541c04002c12290100644603407091007074002d085000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 209853480 1250 209852230 209852243
    0x906020403081209010506010e01140711220b040203150409050304052806080103030914030a020a0306091115070609111f0e0405240a0302040c05071e03051e07 70
    0xf00258441e646090508a40d112000d501c2c00000031003a6001d100f440c5001d01041c0c0d07030100301411940c0c2c1409240d0144000340c805a842c1c1c50b04e0321540c1d851144203000ca0818801c0c0c0b0220400180380341084d2103020701d40301d1041c1e006000f000300860703500c0300110080380c003140d0201711000d06003080c508501c219002107801c11803c032070303130015452518080440c18851204082042d81d6580048444110030b010090020342c0d0b440c02001400d6860a203840c1a80004058492400c590340c0090807001d1154021181280c6658017282407003480c0001d0b8103050304c2a00c1c1e01c0148030300ba910060140c81034140042c00641e880050005021146249016001000d420b004000d40c0c01903080c440441599500d000007010340c01030325002d080c05e0080c940078090789440e030341c020240380c8d8058220401c80900542c115030300080001c0541d07140c2c001c542d40740c02e140c2c030b616603200780340c0c20840a9014008040800307000142ca001c00065441000c65181d5423490064180c0340006220303101003440f5811020300b21 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 209854730 1250 209853480 209853487
    0x40f060603091514060904060e070608040b06040603030e060a0302090d0506010510020118060e0f070b03071103040e01050918030d02090f0111070611070b03090a03030c170a090602040308 82
    0x2119015407098007124000d0100012111420b946103003603c00c0c0c1c0b03c048003038130503c40102d1014200490340a0300584190804a90302c2070005030585403e55130b0340507000245000060009214004013000d820903019142804120b0a6407000340290840c00607103401010000b8114500600c00c1c2d050724104280280120260105418150703a2040c3c00c0c0210f07403051602207034042c00326005200f0f40c01c1c090603455940d80060001d84480006101031149080c49024000c0006400e00040c031505000d40f1000c07504ea6102c2c280140024034250172141d8900440c0d00420080c0201d182c40da4103a811103604440c0c606030b41d56840303040340c942c4d0780184001c01c0b2072202142d40045520f49401502c601c00702510b4042d0035140050045600c50b5140c20b5091340c1d80c02c20f02c410310010703220751000800103810000b16901c4179512900c1c0919940200c1d00304034560005130b0b1030010184c1c9400b44101c400300d14900425030001c40781d006001040050714403000c507941d0714482c00c01c002560701030390011030b0414112031301c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 209855980 1250 209854730 209854739
    0xc090501050318240601090f050f0402040b0309070f080718110c030708040320060a030b061b16050a0308250803010b0a090b270a03121205070e090a0209040f06 70
    0x146440085001d00c240715880000a2040d4440d100c0c00c01100c82e101e000c0d4a40c02e03c9c242c1803140e0b5400c001151034003c0d03003c00c808600412810001c601076100f4030000e02440b0b1030b0403d1034141d0100c1760480141500544c5003000300e6408454282c601106d02c0500280d103111184c1c0528075840750709035504041c08045280d03018000c09402a1003240c0c0607503448041d074000139550505080b035448800c1d520050500a001d43c880c801d520a00d580500a801d075481c08001d65103241c101040c0c007504155a070b00010446030082c08001c0c03198005c4c0400e0700c3e00d0980c0ca04580c0c84580703074011121882100141c6280f055aa820700f004441d0403550859409a40c1e07507103074100030610303600c0865070f100822060400064101041c400311418941300d011119814500b5042007103111100c0707942e440d81321080c01c201202040e07543c1c10310804101c3d20f4076075600e03035a01802c0c42000c0d19402082e5405102c1c0c0c120350302c8110b407144000141c2c4010000801681e900d0614000b60003003501c3d1080ca050145404400f04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 209857230 1250 209855980 209856013
    0xe0a0f140f2e0806040204150c02040b130f060e07200307060c05090405060d17070606080f0106030302150709060c030c06060f09112a030706110712030c090501050318 73
    0x30a610b070140d64a00040c1d42c0c480c20f0000342d105503c910f94035509910341c0b000fa0188201c150818580c8020000700d503100e213207000035070a05151416518002d5581d0b10800300403071107205601c001c1c10b640c003425009103030a22015041d44100c0642000c0c001c0300102c1c119003c18144215000540e0105003080f20440008000f07000d90051659540110714000c0401d85614181d405210340f82c1e44104626100747c00d0b0b40e01d0140d10780180c0c00880300c06071500400b00e45513034284500500c042c0c00d080002582c61460400134504a000d069481140641106204a150340070300308d00c095546078100900745001a01e42291034441186024208074940b070f2010810303070108400c4c02c044441c2c50b00180040b4000c484084a82d02c40c116907443c00c80c44002191044030310110002c00a030000700b003a60305003403ca407030764030a690380e81e03558645400000401c041081002512408280007610b010001170b16074200c0506108144d0142c0c42c14030202000240c0c0074190140049050402d04040d1131051100900e800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 209858480 1250 209857230 209857309
    0x6140906030a0b0c180f0d1e02060c0c04110408030a0503041a04030906020c181602030403020307090501051e01050a2f0a120509011b020406030b070e0a0f140f 70
    0x4180d80e840c04048822149030000e03081d015040001c107910600c1450350341c0c040620075508c1c9110440724a08201401594484018106d102e100c14080c00c207080d80441048203c482344444c2e48e01103981800240700070000041070710719002c01810215503949850801d074103007090404c9841120300c0d81c5000c010425900c14180c4044a1880c0c0031179001805160800a20a4840c0034001510500f18002040d0100314165001c0a803014010750789440e440c0c0c0c002c2410088507801000c0307115122801008a4181500311042d141e109020140003030702c1100c002015485007958400400243c440f00302c0306104c46411400750000140002291041c00d080001c2d00d80150503420340300301d40500503801c1124010000c440c0317460030584d41da25010520440186248210140581c1c0017980c44402000049850005900403404e0b40c80c0d106802c9040f10070009003111a400c10003900f000401c003041080c400394a408081c11003100c0d4521a03000c001c1c04965005a4440442c80b10b141a402c5000000d9610040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 209859730 1250 209858480 209858497
    0x30212010e06060105031909021f05041a0702010e040902190f05041b0e0603100803030a0e0f0a150b06190c0b0115050f0d15030c0f060306140906030a0b0c 68
    0x1039402c1552224015500c0d80421240d50700700b0791005400d1241c0c04999840840802c0c1b000b043c003601d8950301d0b200f43c01c0311b410b5600b1110201d40002428800081c08411034580840d00300303042d6181c2102540002c140c008200c01b23013030296072203103e0042195135070079512828802c0c0f11050a02d80d40c0d1131504420f0000135205090140b4907148003581d0310381040c072407981c44240544455103600c422038207002030780d80020500b10041032001c0340403a20010600095000d000324910121302c0e920160749071030071b000100e070100300c3c207610102181e80010325440030500e80c0e46c0d0480000030400340034008500c59101d40d2500015000c0084903442020707400c161001c114a001c3c000302440c1c3c1e03803242c01140140c440f13083e41c500031800074490a440311038010000c00c4e100041000104031500505050658002e03290411208a640110140b0400c16100042d070001c0140345400d0014038a00040c4044080c51803c8840c050846080000c20741e032400c02210078441c0d48114014101d240042000829030002d110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 209860980 1250 209859730 209859733
    0xa0302070303033206040f09020d0803092506080c030907090e0c060304060609050f0405030708090105040302031b0405160e060f0c0a0f020a050619080405010b030d02010e0106150914040204030212010e 88
    0x40003c487d088903c1618070301d0f640544004034100980c0c458901d150401041c1014038841e000080034a1701a0400d00c249109018494207030703890403c100601008001000000c1d2020140f04001c0e030071400140c68021900d010713000183c038940c00000d01d402c203040d6102d4103410200000a00c41000016404134040700c00101c0100400e45450b00c4480d460001620040e0141d4400c0c070518010400070f4008100071303072050400e140f405543c0e40c0481c1c1003036811150348056001600040006081c01d0080c3c40e44070607450307604449a0013144026015400c2c8004640c00741d80d02003140c912400ea50750132940c1d041c1801040710410202440c2200c200000c03032904038011800f04c4000105820b041003900c0718643c1c0c0188203407200d03a20040c21606044010030075543c9648441002500351010301582d0fa0b032803903030350002c42d81042815920f2309580d1f5913480001e40886036056000119849002d13501074138140c1a13100c00406601d00020b029014503000690b02181d0715070110901c00d01507000c000d080c0300110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 209862230 1250 209860980 209860991
    0x6010503100b030a2d060c030b060a020a32030309070e010b0904020c01141305160819030302040902040b180301060f090e030f0a030c09080a030207030303320604 71
    0x107141580c1180303902d103800d6409150b4010000340128007418540500c0d003090054202005041161241348003c2594140d50b210000d449042d03050298541003c011360b42e00340742000c0c410b0025942e1200c2d581c050301603051515004403400d12162603000b00b103505070800641303055010030240c40341d00036030b0402c030b1a20548400182d15400000c000341201d500500d00c43c03c10241a062101071b51042d0b00c0e0000c00d541e80c01c40024009001402d80c1c1c003a4003150390641032364480d458000e00d41600c080f4400d07209514540100151440080d03020004603548000c074080cbd100914055000e801150455002706001082c046210501e500240c650302004a940280c0b81c040b40d01410b00302c603a00c0c0249407003155840d000b8080501d080d04104644041003049a01c0c00000c4600041c0640220a1510000751074012080d691680302d81000050082600645850b503620380d4040d58800c000c0c84002c1c181a00e40940c041c0c49014024400681624981c4040200a103100c0040c00c410081320041e2280d071031300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 209863480 1250 209862230 209862253
    0x10914090a0804050d02060915031005060c0303061216120b07030e061b040f090b0a1a0d05060d08070302070305250308030a0612050609070b031e070e060a0206010503 73
    0x198181607607401ca42d61601d401d080000340580219030340c0c1c081ea000384003000044800d442d44c10f00c0c9903104c0422800700e600d074140500c0b01d4980b0030f080d5018600c103940901201600d0000402166041181210161000500d01000074140602c40031401400d003110f500c0015182349000084030000d2203043c4c10120340e039840600381c00b2544140d28051240d0310441c00150a20b07000301001d0f11150320012224102a41c4024049070195603400c1002225110f03150b07a1f182e400c2c00040c11020b0105480350034000c0090b4508000c550003803004881e05151038102080c600d031103500d8000902500441240c2d0303034040d01d007000303542c40000c0c2c03100300c2d8584115007006c081c0340442d8120740b1030941d07040009102c02e481c580303540703209410151031074054564940c00010f43c2511424240e20007485240a001d540c40e1008165080c02004d9200c1046441c040080200200c0c51500c010011300c9801d0702e80c8100e8440390000c6800310700b6183d0042c1c201800159805100c0d0f000100c590403584224110f407840c0c03191 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 209864730 1250 209863480 209863483
    0x90c0f09021c020a020c1201020c010c031505090f0403120204090603051f0506100c05070e010305210a051b0708120c06010506090d15110f2104120c05120301091409 72
    0xc4e980004016002117500c19a907191004c00c0c0d00703c4103001d40002d802c0a00000c01a1b007141c004400c0180400d40c3d41c6403504940c40300640520060004441d9001c080c0303004081e032020958010b000404002104188600c1c20f00301c0e9050310060680003408204a030f480340743ca203955000c1e0100c0b203410304804408034502e0380d506002d0b80384254000303003245a5986a80106590540140d1400c41d0240600783c2c01140c00c59021003518002c0d401103004200328044803940303100145482003200c10b9144100000090540c00c00c003220103006094510004500090101c81e00b021082d0700000041d000b40c1700d1340140040301030060944c204042c0203031860b03641d8513010031500e40300b40110250000d00d00e4042c00040307000c4c01c0381b0000c5180740030b074003040400d1010100501988a2103441c032045802083c24909405840100c0c0d400a80ba44814440380c00c0035120300480c05001000b040c104103101251004002090144000f03000ca0032240030f071256101c68050001d0040315200d100109078070030014490030f20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 209865980 1250 209864730 209864737
    0x30804091a060414010c050105090c0a06020c0120010e1b1003050f040f030c1403180108100b0a0507081201090c0203030f04110d02030a120315030312090c0f09021c02 73
    0x40100b00b1441e0078a4540704c1e11054002203a0b4505104040e824600030070828042c407845100c1110250005412400c20030454003802e4000304115807201c07c4c60140340c0d030404041400708100038510b00d002c010340103600d0301401d100d5907c1410b50144001030714503c62a1103034548100e6080340d0000c1900d40e66001101114001c45404003125501c901180110f00107410409102c0d00030b1400818020880d1a1884103071560b2100a64a030300001e11011940504002c40341d541d00c00b4606801c1c0c50804040d10b8411404034043c0f01100a800212207428500903000c86004039800340d00251504550706845070500c1c402d2242400e001d0070303c01075116092021048a104001c00c02402c1c1e02d9490755200e00c4004040c02e100039402c4200d0307a901e0030159508103d2044c100303211352800c0d511341115440080c2620f007a2901c40e1185c0007003143c140006500b11039400540c4c654444002039164050030000150341c29944054600342c0d070360341c0203d40044950005d000300c048940c0302e2880410f450039151708070300c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 209867230 1250 209865980 209866031
    0x30f1a090604020f0c060c07020310060509040210051b0a06060f1802071a0a020304111002030708090301090204060308030a05060a0320030f0706030603110301140c030c1303080409 79
    0x140384800168040c0b40590207000c5030768035460224205102c96007418540301058602c48001c04001c0341020440c0fa0030001c038004800002e9080c0030007803920010854658015200a00c034401c48261540740d140702d2401d5500d80100e10602a4621000b402c000c0c4d1900000e1606030384017420280040380c2d211080110100b01c6030291965881d0035a005000e80017900489804c13926130401c0000e48121409485805002d4100c042c1c0069030703030400d4070b070000e40c6103521702c6214000d50b5a400c4900045802006544089803c5600d0690720501c20340003a005103030880d8020751040c07a150000c020322000402852055001c0d038403c200e262110010008001124480100000e801c9110300303d00100c020307103086015001070116020031041c41442400c1520039001030000a03070fa41c0080003480b80124020076250400e400030003541d034040d80743c21035002c00100005014900003007c9810000428200c440c403281c801e002a0415403245000c11096105100d107044c1d81303007070000f0200c49000c1c1c00350880d80ca0b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 209868480 1250 209867230 209867239
    0xc030e06100e0c03220f060203190e0a02030303070e0109080a050a0311010624031d0c0109090b09130804030c0f06090503010b180a060506160b09030703020c13020c0d030f1a 76
    0x1030f48035005c100001d04420314115207001d201c0d0486000141980040c41c02403001401340d401c851041c45110080b0381e10201031032040d5001e03002c0301006d81c80c04000c580c1c0020b41403a141308414a43c0c00140c1e059030665210050324401c12401c00d061000c017094035010300b4401da503441036544055245c6030030f0f16864040c100003003030301205500a4882c80903060b40c0100b01824046241492001fa4001c0c1078005d5400c072086401803200e0340300703545c3e1044009001c1d0481810403c402c02031400413450390302000704032a441003c0d000c0340f54188013045054074025548280d0704018035464091404108080707100e10008100c501c440429a441e06002d44400c010001d00951004105a03d447e4071426010b86100c400d55552000030803103131105030003407804040801401521000c2031a01d0101c0b0240207101d016190024001e05000036070200702c8000d8039004441c600c01c2a00d410500100920030056404280e1090540d001c99098054020400b840c0c860182040758603820004020303214850003527076030300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 209869730 1250 209868480 209868511
    0x8011b18060f090503060a0f0516080a0203040201050417070e130b190e030d0212060d02031f14150f09010b0f03040c09090305030a05010f12060c030e06100e0c03 71
    0x141480344414002c2c01c1c00350301d4490381d203070b03916400b20341001c50a68903100300c59101e03000d160ba91a500d0060580080300200c01500c4501a070000600100000c1e004006441e000004101035a1107901624090030b15803510b1110f0103072440c00c00c1d94691b5103120300c010106003c000195180703513200381d0b1803416422240b10016076551030341240c90504821350000c2d0060b910851041c4c405010805803601e40080c000042e40c03280d400b00c22020404004061900c200c0b200010480182c0300402c1d81081d4010b4403000e4030100305e003d41d41601900d000d038100680c081851041040c0070341018003e0301020b8060755000d2250755400184000050300340100c03901c2c250b08003d02c030300301c2150a0003141e110f07010304a440000b948844100c000da070741e0300c0b100b80c00158011042c8031049505105090044c0850909021003502e4010000105182030074090110b41d9209030a000c42e0b4003d8100280305060034041c0c810500e0044004449011503000d05040c100e40080094510503480048900071007180802507034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 209870980 1250 209869730 209869739
    0x20705031b0d1e03092102010204030605090c030c1003110324040c0516020f0301060801020405100201090f030e1305090d11010e0703080319151505070309090f140108011b18 76
    0x7074405d0b454221092800003021424850300e0100107001d06507160f0025070f86501d1400c24005441c000350804c0025003080f010903a450313a0011b241c00f10300105a0740c1d48001d0025000a800401c1006480141c48400004020782c21004100e4140c0411f001c0c000d00200e140f5010038802107502440099000c20720401042c540079400c6c000c000151071004001c121b0000300e5074042030a403000f660250a0a0f1b4000c14103001c14a0040c01e4419201b40501c000c00941441c1e446442c010800070030f000c1c0c180221000c240b0040c0d26141c40703c40c41d61024500c140400d00b400c980d09507950301d0841c510800503048046c400c158540c18001c0340011480c0c2e900910340103095031034540c1581d01c00780c1100d40d240300202c01901a88258043c00038040010356003071021903d8a20360350035200c02c4407a1030701045400c0040e000065081800700c5d06543d40e07488001025540b801c00e0380000c204412034120301d10040d80001503064015004140c220048141e4428048006241078619880034a004040382c85485c40030b20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 209872230 1250 209870980 209870987
    0x90903091e130f1a10020607120e010c020604060501050105121602030702030607090302010f2609030c01060b071109010509070c0303090c0312031a031f020705031b0d1e 74
    0x1000820010164010040455610401c403400100c05404143d03d44c00084080d4107030500401c03d10b20265511080c01c1c0e00400002e40b42c4000515070418415203040700148410150b018260400500c0b000300940c00202c0e102950311310b000c803022a07129003080004261948103106840840582e07405170541c1da11004000e400c030754050580c40c03003188020320202016941c02c00c0058041c500b81c6e01e500503014110700005000c61038001c20320301401b480c10040601d100c64001c06255203031141520610b15110300b40c445085100d4120240f40c2582054400704035a0b5900008000952069a031074040411017800e0114002e024454268000d03480400980d106009000c04d421451091400240c0100195640307a4904480d400558424604d43d510721130030350301880340c41424000000792409a0f000d420004e0f0b540c84014100c940076250780388042400214a406454070345078000c05690303c1c3d101071a40008010a0000094118410120f510791068025429181921038054080141141682c070a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 209873480 1250 209872230 209872279
    0x507060b03121207090602010507120504030903200f04060807030b100909030f020f06010f1509030605010803031b030105030307081b01110309150f0105011404080d050909090309 78
    0x1990580140e000701d1001e02e0300741000f0702c48a41c40d00c02c02c2c501424001c1e130040c1421000d421030702c20b41e803610092010780da41108000c003050040041c040780c242c0d100c1c50100c071807403400d80c801051050903089810510401041404a0b0842960155805410340c1c08000c1a01c0a500c504200b54210000510209040749240b0750f0024008844e105020381d03a15110084854108003540060421940429582d505001c11003104103000010003055050001d05609440c07107220380009458100210881d01c3e003358803050007581c00100402c00366a4410a0513101d0713100b01d03171030040310124207104100342d041070342a6816144007900642c2840340b40d5481c10455072081d5080f110007120f10b0b0502c185100e00f4094100351a246001c8181c0b03a06141c2c501a00e04407001110340344840c4544100000640c10452032811104d09191928004200210156079071041d40c000344c42501442140120b880d400c4402032400c01c0c015500b40c0c403143d0354940d071a43c6070b002c1c12038401d900c009480c4134603480c002c8100a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 209874730 1250 209873480 209873501
    0x60509120403031206090e0c1003110d0515010903050c060306040e0d020703030e0a051c03180803030103030f14190509041401080d030b21120c010207170a050706 71
    0xc55034581180e50000100d50001d42c4201c2c0000c1000c2c001c2c41e10b210183c01280002d0039100420f008011030f200714141c507411001012400b540c4800c03400c0702600d1082d00b008a0124900c040296104004810074004e42000c41d900b10080454105000542d4440d92200c42100d07001380281c596288034004100c040c1d44003605c407591184d160a03541d940c2107014040d02042900070307001003846a1461801404522007286518400d100701c500c2001030b80c40e0340d03040b0f44044030f0107846e081c00014a032a080c4c0310ba80c001c2e504042000e28409010480b101c2c00801507044e24081d031220300c1c804084030310840701080c0d19910b50f44c81160510082410301c0f074803041080b44c1403803403c005041a0784200414101c0c0c2442119482d40d030305420041118181c02e00450070036506a1a050041040c068003240c2110f540285001c81280e410300e201c8409038040c00250303041c0b0310b0b41c1c04280d0384000e4004000e011390071041069a0b002e8241381c1080b80b0340e0803941111100c102d151682c0d0704140c40c2d41c48440050007a2100e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 209875980 1250 209874730 209874733
    0xe0d050a030525230a051806070501050c031905070912150c09090b0301020a050304030c0f021005090111070f090c0e0a150f020c0612062707030e0a0f060509 69
    0x40c40e01007004809080301035851280d0f9500250702c507501c0b04203070070f1003400d804a040f00010442500b2150780401251003801000c9104e0407c2e0700000081010703407103444005031440d4600380034404001075510045002d9000c0b25420000c1e411980306080807500151a2500030680341340d0100b144000c3d040d003802e0724a006541d4551070760710344000a800e94510380034100015030040c00502900d603046c8949010004290000c50800480e04400303003a074400a0009014000d12018000801c120910b031601e8440e40070780706401c0501c03907000142050300700d5580140459881800032403d01c0d40054134034101c2d1078824640013054035001d00ca000400d640c59002c42040201d0b0404c0c3e00c41d40701c1e00361240080c168946150400007488400a2030703103000c0c4410400715082000008295500c3c90181d580c5d40401e00c0030b01e44a9120b0f50002031040340072084c0f00950118441d40080b00f00b8203001c100c0d1040c10261007e00000c829200076644135284040700030900d10300c041e0301401050069016542c450340341340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 209877230 1250 209875980 209876011
    0x3060f061b0606150712030209190b09012601060f020a0b09150c03010b0d020d060504140a1d0303040b0402120a050f120a211107060b040e0d050a0305 66
    0x75490a2581d0300108040e110740d00440034031505060a094100001e8021200c1504180f002d98074110329198000c0080100754000c54030b0f401a54520600382000004007551130b20701070303807880c90001740d8100b4032181b4046102241105090802150950941c180d4040440c01030307820120700341e07501c071040c40788501144241150800080c010940803809044a43c00402c1c000d14003420301703540c600d0002c000c0c4444100600041028000c40415202e50020a040160711b905103400312131300501e40780d0b0003941c1c024200211600034a031104c0a82d0700403400b0352810300c044d42002c000c0000303900c600c0000803003650003040090040350720500b039581c006100a120f0500c1c000b00c1d038070161625200080a65098002407559102500d04006d0003910358058900710341401303c19a03000d0b03c5600c0992400740400d00349006900802e0255019041030807820480f540c445040707003401001041c82a40f000e015030716001c280780c81d80c80c001880c0c40c200402da0791114a8110b00c082c04030301500b006041c045070300441c207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 209878480 1250 209877230 209877247
    0x15020408190605071814060708030a0504060b0a0506090105030603160e0a06050d0c0302041a1c060e2b0e1804050105070f05031803041203090305061b03060f06 70
    0x51025558001c4050100540300046062410880310b000d8034070720900210041c04060300315810f1140d000c0324129511000380c0d005040101c0c0e114030450300c009100203400810070003614515030056000d54082c00080040c11121818414040c0142c00740d503920210610000b40c2640c400d00c010340d40050041c0584198403a10035143c4010303800c070307000700e1000e01400c010042070308814810117006000407180900c8000d40b60b111402d28125502001e4040d0f0b0711a20300352001031844410008894010b003070a2101d1841c024410303900001c0c40c100700c482908088030b01048650015009050510414840405980014420900200b01450f01d030600c001107103a0001d9030b1742c28104034881c05107640b01c2c814516003807030318030b0031114001e00c55001d1000c0d003452800099440415a90710915003040040f011000703400d01f07451406654130035220148d2201603130081580c0b0468800c1101d01c202c0031148036480300ca80080e4002d40c120f07040c0215080520002d0704c10310301030000e00362114001d030550f407904000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 209879730 1250 209878480 209878483
    0x1e030e13020f040305030a1e0f030905010b0a03030504090c030e0303130314070f110301021602040c0201060816090c021b01080705040e0f0405060601020f03190513061e1b15020408 79
    0x44d4000e80d142e80021424042803a00070500400c01500313407503141901c400c01c500c09400d10401c20744050825690384051360401c1425031050718884001485c3e8044a0758070b01d8001c3c0b040d80079000b003180700e034141100304204600a0140700100d64442d40518219510300300b905080301091217084d010804440c2003010f007a040b0303c000f803448a000360440000100c80d4280f10105801c0401864020780c41000045460b52440c030700003002c00c4c0c1c100c50106115122030012409040c517900100741d240106680010366602c609421001c50700090b209001742d8592810590303c0ba201d1040f0071181c070801d00c4400380380703610880340a03a2184441c00d00c68105611408400603c1408450a20b1965110000d11007400342c06c1012a43c400e40034401411015648002c05499004800005101403222682d01034001d000701d081d5075542036454180c43e030442d510040100442006d400d4028020014000e2401d400e110320000841152441e00f58203c010050b40c0b54200f10700304407612800e460f0f01b44004102042c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 209880980 1250 209879730 209879737
    0x2060715020a03110c100504021522080109082d070807020f030d0e090a060509070216140d031b41070b070501090510091e030e13020f 59
    0x6545030060312a400958050200c8100c882682e442c0310050080141c0d0035000107915900c00151100401c80f0f4545202140c943d5549006082d40c0070b4012481000815420b92050514150340300c0d9944d030b0543d2080620b00721262401c1c05005010104000168000c800c243c08841d818081981103d213000b002c110745064002110403500d90100007150030039850000000512050b04501074180a62000e002030426071000094030700400511001610100f410b5001200400d0054114140c3d0319191100a46542d0710032068880ca8040e00b1000c108010f111103400c41285026000402c2040c09460685040c51b420092001034203000c203540c3e002414801002c1e42d4982d4040070f107520b10341540c0b160001014400d08074449910010f5005084000001e100002c903041141c1450382d656080c100180034120541001d00f5030322a90b00840c48182c401d030300c9480240d002e06c243c0390740800c101c5c1d0f01e4a803503d454800680054100b185211311440c160602c9031845440200062a0410760300c0054003540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 209882230 1250 209880980 209881013
    0x1206031101030f050106020304060f0c0c030f170703050d09020d0f3509040504150e070e01120f03030b0105121005040b10080103080a09120c05011b0c03020d020607 72
    0x80d40c80d6030000d10758050060401c5040e50500034816076046c404002c0d034a0103230b8032580381040b4404400280c602e0048980d101c0250308000c2001502da101d0406035000f2007089411595601e6202c0620b84840e41c01c01622040c542c55035035580b038210303050840c0002e0300104100381c1c0d000320f01e0301c84800001c0c500e07038081c4c8026105244000c1040400e503250741c1c4283c441448810200f03803810214107000010412075080312402c0b10001115140da0405496180f0707415081050356280020101007281c0c0000c83c0350444440120320b011580c1c80d01c040342912181c5640081c283c4240360b510b100024042e4102002c0108103140039400c005458195001581041c0d0784220120b03c500710134440c070b00742030080e20a46102034510303a2a4402500d00207000c05030500c4043d2903402c1c0812a10383d824812194407001740114074940106a14a081802c007500c1984a4540400c290700c1104001c0d6204008480d242c1c1d070040782c54400580380d5028003240300240081268082d1042040100113440ea03079910720b044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 209883480 1250 209882230 209882243
    0x20a030f05090f06062b0501060f05060a0509040f18030507111206040b0a0f0f0c090906050d020d060212161205010e150102010b1c0c0b0309030406050307120603 71
    0x24504101100c11290040d001c0910764110000302c00c580301c00050303e5074100e0019900403135101141c4094042820030710148010b1450440ca10350180075054020360140c62080c6032200342039a44004001035407051511600c00b00d030040c0580b075a40d1815030700c0081600c2e0306540100342c4640000c1c44504131200308500b18082180403501c03900b4000f1800c100c1c0d40900054504c0058140c01800076965031000400003030501811100140425403560171128201c3c554030414049851245035001c0607201942518001071400342000070780c01d5860040f030b0300f110b20207000e171584c007a155001e001c1032520300c00f03064078555001c0015541803ca5010010301c00c080d001e05890102810384002480340051b4418000c509003003c0040c08070f10201c5d402c1d181c07c08100074003e02030811000050340034001107007000340e00030104041c0392040c40300c102d00414824411407003d000e00e62100d001c0c000c2400140d5826401d42c0c01800284403c40c0294011074201c030382400d00c0501e10048580810540b030303103504105e604 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 209884730 1250 209883480 209883491
    0x302060f04090e01060e04020d0c08072c041518080706060536130605100f0618060311070b0406140f06150904060f0b0408150903070b100801020a03 65
    0x42d8460303100300d821031803002c0002e1001c00d152845120403d0006000a0710820851143d5020008451122801801d00006a5800c0c2d0703542c0705050b6880342140c819000c1c5000034481c0c40d40290348000c4103449a513100c0301c6040307010096002500207104815454481e0001d032203000f408214641e0107080000d00c95000403616078104000d01c80100b408040340f5009020907000c000b0784051908110301101c0c031048400039503030f43c0c181030250a5991600c02400d80b601e480d00340148415903200c10b10543d46241070042c0304554070001155200312a490381a0004607011090094500c20f4000c1182d05080d9144a410007a013910f5007070411800b96000ca0f1203039640d90103c001800200070240d8008059002c803155450100701090314030803110fa03408000c000004801c60182c1e00d60307014501400c03030003614862103a159070a00e042e1341e1060045003150f1180020600d41c110483d1542480744800002840c00d00046a603900310311030006e0080802d0405200340412a5503091001e0940f041e1a550302141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 209885980 1250 209884730 209884739
    0x30e01110403031112030109090f1202010e07060923010309020612010e01050603041509150c0e0906041e02090103021905030f01050f01090b03090a0203060f0417030601140903070302060f04 83
    0xc0e51075102d40380e0013982c00514030700507991100400d69044a40ba00c50106503c041031500f0b103030003c19442c2c02002d0b00040241d840c3c81031750551104015001c58012100c0e440d44400040e03840014902c124001007040004047c003071100703806414050b000604012420700c0d100d82c00078245401c0540c861481c40709800c0100f14501c07048005500402065400d1807a40c2440e0303c0c2d0282c010040101f1000040d00c5009000c1009112001094502041c2070204006036101c00003c1807808810741440c42048224040741c1c07035117000c1c400c0010f40c404100c1065800c82481100c038019400940807181859820300c2900440c0c0300c450500a0000b0540e603985940f4584445d1890320f034030040e0412030040c901a91141545d907004408407040c1c4000030710c851b44940c3c418480c145130000a4200942601074041031061141c0501d80c03882c0510301c03d00b45840285040c100032000b5000444203280001c815440c500e0041c2c1d800c00c010700e018103011b000d81d160345031690089001b541c091042c82d110560001010031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 209887230 1250 209885980 209885987
    0x916080112020a060f09210203100b0603012102090106030e010e0f061306060314030702030d0f0e0603090a0507080c040b03010603050a0219030605070c03031d0a12030e0111040303 79
    0x14007401c00144034040411468000c203001d400d86000320000d21403c040703888081e6015492541c000e1081d48610000c40c09038000c16001e03e034280c031080740079104800744091f040080d80904035071058040d2515003140c0c41c25a8102410b120111040d060941c8100c0e0324002d62a00883d0343c2c0038214549020602500c0840c01d61b00f110440c0c0c108a50a8001c0b50401038071004c04105550001595000d8072580c411504212006000301d500050140b503007040f4100d16980f0200150964a00031020b03102c52061903101624451609140c3c40d000461401e08500b06160400c0516003060f00441140e403041c01642da202d05d004240e0704031292a45c80441c001e401032504c0d005121a004080d4001c1c4209031941d40c940e6a54004590000d110f400b842d070300081220411b031f12120040d0f80000062080d8142070102502084804405900003070030840c0a202a80126614200034000140204001049500c0740c417680b00c07002d0751070000c040c2c458845851004090007000701c0d800301c0240099995180d8500903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 209888480 1250 209887230 209887247
    0x709050f0d020904060f0204091a01020d09080c010f1704050601080609030a090b090d1505060f18042a0e011805010609030809040f060306090615050607061a0916 71
    0x224420500c0901c04401615003e00c500d4000341d2201021a0b00d500c1d844581002c0c2c0229004444868030300b8100411486024507000005007080e002c0e070f40d40b40d4503a401102c00c0f2507240115215a84003409106181d4800c80b0750000802241c41c0409409104200c1602a84e1090794107403201c0c0c2c440d00c0144440001030040c00c2d080b11140c0c00641c98500061006040407007984904001c061010402d8032003911502c40140106501c0b4140076102c0000c03050240c0104015503000b40036a0416804c0605814500c1d000b42c460a07020742031092564507940c41c1d01513401d880c40180740d070a00c9071030350108008840e00503001904041c520001c4a60401d1055200603800c1d003903d1f00514100001001b43c0d42d00300d40b2003415207401050903580c0b20400d8000c41c2c0608071400f004d4404d41d183c44400400e03c8445d41c864100c491148900b400349100f58030004140e40414001e03664003407003c00100000404650180300a01c104031041103114200c200026103000c41216900d5080301350b500015440795108048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 209889730 1250 209888480 209888509
    0x240909090a03020705100c14070801050f0106020606040614210102031303030506040b0114030a151412010b01090603090501151202010206010614070303050405101e110301050f0f011205070905 84
    0x1040a00d0306c2e0584002c00500a000014000e598407040c4114210003e000c2c01025054210003031042d41003402c180540c0e91024421500140a0840803540614290040c08112111004000051078135039041110510341c07074076204c90880701d4144007100e00d1801c1c00554841e40104071450444241410050300351900100f00390f01c22071038048074244c182c0c1c211012074583c0c003c055009031240d4801c05801e00815032000c010940c0c0d2501100000d291390740340d081c80c040b0b40c010360700d0a240341c1068100ba400c2c0c3d812a10b0840c0400c01000003489803900c030343d02070301855003d0b41c0003207a03a00505c100c41000d1005c039007282d1120107008001c1d10655804100d0a80103100783e16008501144075030307101c2018055079074014101074a0b0780101d02805000c11032104200031000013001b40701c40100802c03e076001c28a01810080c0d003410183c0f100f201e410000c0d01d04841001c0c140d94000e48600e82001076040012207000e040c0000194150b040001c01d1050038450401c50b11a031540c5030401d070400c850464101c1303c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 209890980 1250 209889730 209889739
    0x7090e01150b0403140f0102130518041703100b07050303040209011703070b0406060323160501020c1009120b0609130f1104060b07081b0606240909090a03020705 71
    0x182000348507100b4003141d007126004000d0725801020f40303008500308495000907165030f40c00810104015900c0380241d808441c0c3c112810301c10001d1005902064130411078015100040d541988134894612100550703100000e08000d07004070f40c94803101011600600f0702540d544d8070101c02c020071810a079902d1805004400000060341b007054081d26981e2148031300c01081c1c81e030600045001c0002070f4200c1c3c40550f0307115241e110b2550f0b2210303400c401102c041c070880f05a03118120940b00f14004110a0f44242c0c2c0040c0d0182c00710805080503c030b84580c850070320a08105050708001546172a808106183e40c4c07080c99000ca60741001400c205070a60007520310309480c1d00c120940d05c00100304141007500d86030302062420405074554002401841c0551180e03000c0000000e40208009070702004210180e4034501101030402000801c0d1399550f07046415a070401f018601d141ca03e1424500300800c40f40001501c0e901d00016103002c11840744041e10185496402000448101501480000003401c420f84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 209892086 1106 209890980 209891021
    0x4050a021806041d06060712020604111507030c051005070c02010215010303020c0114131211040902060318010f020708070b0f010f030b07050c07090e01 67
    0x81d0440e09040405800a00c1c0d1404405650aa80d00c840002c9020540045809400300015112540c400c0342444a0800207036682414a404d8a0541c003034841402c103403911040c0b05860300103451081d031031080301c45100107003801503036046034041c074010540071540c1c102a4102811051000b40c40c5040000700219a504150300c854054800e0382224909428001403511001083c00000c0060704240d001c0001c4d580305526244584658284c0185081d5400b007949440c02c03a01d030b00c0b0b8450101131700c60340c00900c28802032540101c0400ea505201d400702a50004146100c014116205800b00040305d40c1c40100940c8010031007078400340119515000c030704000c4465008500211803a4901c034000070010702880e00e8042c102c404625207411124203680d100ca4942d40c2c010801c000700a400d109072503504908001d050020030000c00000703511080420350382e007943c0a0403254402d00c030703481 = true := by decide +kernel

theorem cover : BRFrame.Cov 209712230 209892086 := by
  have h0 := BRFrame.cov_init 209712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 209712230 ≤ n) (h2 : n < 209892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
