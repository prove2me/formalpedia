-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:01:24.97056+00:00
-- url     : https://prove2.me/submissions/9cd9b06b-bc09-4af3-95ba-ea9de974708a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 259532374 ≤ n < 259712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 259533624 1250 259532374 259532423
    0x8030a060e090f1c02030415030219030203091501140d02040e010e070608160206070e13050103050c120604150207020a080a110a0b03090624040501142b 67
    0x10954070038030400a082402885444002090310003900703105020b0220b21070010042140c2418900b50091801c103803805900082ca500105101420154208000c55240d508071044c0c11050b278090b50010b80300c2c680b03d0302c5079260060290028140188200c010000802d000d5017042c07800800b0758080c010840180b0115015101c0d000e0200c0183d401c02c202d02d0080c56000400e2070032200540c1d150b000c580ca070003803903001c2076980703110940041c1c00035000a06280e0140d0455105c4a0024150a84420003a002402214002c0e0003c80d903c0e00310100c41c01d50b03403400c0c0c4c14288410f40b45201810352401d142d5030307402c2445407035604e03200440d1f00070032000155a98644d10100920480003599803000c19403605582c4ca0824014151140745000070100b074a290050603288200804001000e064558462500320510b20328210510214074031364240440c0c8039801007a0081450349100c14400440d1800c11203414120141444018031a0f0101c16800002130310031091039420060a0791100c000d80480983e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 259534874 1250 259533624 259533629
    0x1521120314010902180907050306010315050303131401050f030f0408070203030313020907030903320406030207050d03090305041701060b070302030304051b0f060d0608061e150105040308030a06 85
    0x40800500000b10140150005c184c50310340e20f500f82901145140400043c10003e03120f09000031010b000256141d402a072048002501d05100c04142c1c40da141d000900e194004001700c94100d610010030049400500e0352005c42110034207041c1e0500c1000c031480480f42c0001020351424010400101c0e0a104007001110070703840d005001e0326604d1401602181c0703c0800168102d01500d000000070f03001d2482480381d180390030750688e5040d107143e14903000072603004110040303e049050180c015511212204009000030201e584001d0303180c010a003030082c180000b03840c2003401e02d4107140174000025070100440c3e003955401c4a0060740e0304c5040e405a401448160400a40008006102d400349500040514402c41c4910126400032281d80000091040b0440d603160700985001101345041c036081d009040c4190445100007a07041d03860766000d107060300554400c40e0900046c19800043c0d03000f91103840d0301c50303a003410441590340d2501c0003c02c03501c1644400350400401001003200d016050304500c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 259536124 1250 259534874 259534901
    0xd18050301090f1203092f040501080106030b010b12061009080102071a090a0209010504020702180c0c07090c0905040207050f010c030501081908090118030803040615211203 76
    0xb81c000d10b0800440c40c0b0440d001e43d0780743d5000d1a0600c404e4401e0159807540ca80c030548503114500e201900d0400f42216804400029100c2c8a0900c0c2940301e602c0b0f524001c10000d000421101d2031341c00c000c2110081070700304e81c04520b000c101040902840035076603900188152001440021100c404031415400c03500000a6540000399440601103c1c902d610031090f11407859020f25120200c0103070341e844407004000d400200c414010441498142d01a000d154000f50194521114840d42c545410404079030340f070600000401d840105140070090303200644180c98041019055006000c0c00c000000d00c61030703216580001d805e4080120900c0a03401c1080448024007185c05140000303009003100740105800c9201d14001d40817000e040682422142d80c020003114a851095001100c40c9450074074001e0703150380038440020001d15180d00135407040e401031400241407402c82d10240c95000e019840303081000d2040d21114034460700c050010b0003190303206400b1200ca0352907440a4000c1c00440410300b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 259537374 1250 259536124 259536131
    0xa050d03050d09031e020c0315060f031005090d08090604020609042d0b010302090f04090203011d0f0d0905030d0c060b042904060f14030c0607030e01031506020d18050301 75
    0x405030001210f0b004a001c6800d010040708a91700308a96030f2a240001a07899400410b08041302c601503420942c00002c045c1c480110f01e480307440400c0c80e29440c1c040e21994190390390100404070380144405c0140d103a107450320403000c0c00d01007840c1d17907141c20282c8040e200e041c0004203800140c5e0fa0740c1c40620000c0010320040500c0400b00c040d004601ca403000d030410101e0802c1c4040d8000d43c400c1c421100c00003002006504545150014403004000c5400100d826640e100880f00482c00c0010210202100c00c9005107182c0403928640781c1010052200c1909001c0c03c40700c2480700d99000b265900800300217107040300840c803103410b11102804c0e203d0340154019180c181e030003c800100200501260b0400c2c041038142ca41c5010a01044842c076114035407003511201e6041c05001c010070010b2011250040c11a801002c500000030219448035004601060300c113104903807503503003501402c4111003007208601c81241c58000e001e5101c08051400601b0882d525100c08031100400d0303100ca028040140082 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 259538624 1250 259537374 259537391
    0x3060c16020d0308160201020301081f0b090f04060f110d0e0a0b100801110415110106050a140f0109260109050609060108160803040509060402071a1b090a050d03050d 73
    0x14061000640d2102c02c150b224620517400c0c2c2c2c2c014001c6034102d401d48001000c10718201d4140700c040500c0311440744980703515145501e5450356a003404501800c121070010415043c607140281c00c944070b41480711042402d0140714107501c002d00c015181584129000441c41042900d00e643c2003014aa2008000c10307071140074400010b950104000a41c0c2d98500208074001014003d40618043d80c402e100464000444086000c0d10803e401000006d08200200d14542c84800040029030030790000c1505159520048000349054403000742d083c5800e080003d441c1d4202403641c0c2500002c0d0126a031012000960717800c0491096104918003600a401d0390140d0400500d0380e130b01c0709401c0c8608481841544c0150710301e0303007203050480101d540401c011860700345000207001d0b1212000b84035a600583c00c0c0508004102020100940103206e9040f40c2d0711890403c10084062a1f1100c038400d00340c0d81800b09440a443d034482903030130b0361000c498400c0f8403c4585021101480741044064005040c02e82c0b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259539874 1250 259538624 259538627
    0xb070e040e060a0e07030c0b09031f050411061c0509030409050a020a0201230a051902070f0201110c060d0504060615020c040c11030d0506060f0705071d0603060c16020d03 75
    0x101d80a0f0201c0c1c0e200780f0070240283d060070b5035405036010107410250240b0b000c01114010b00c00604200c2005070568890540341610241c400c03c49840301c10000e6114010401040b07440c8800d2403003a60300f00c5009060072400c2060302c03110107205c12440c445070750f0717170001c1b421051003001076070002c206065092260b0320b400031602029400c00e8825401640c00e11200c120310040000c175030784a2403440540003006644560441c005888054069000030359444407540c201000d0f40003e0104500031500d0200300c3c0314510004288859403251103050b41c00902c403064080d0303141011203250740801480428286c0b620304002004003129401550f182006001005023740c001c5501c2c004040211000c20582e10000000d07100c9040103403002c2403541080140790000c0c03456902140e003040000d000036040001c0411600b4241c4c1c0299070940f100c0d17100760380810120f0750030400d5121340c03401032125100d6400c00c0b5001c03a588510150603851010700c04a0700d1600081c2b03c103450980140c0040c0030341080c001c1400c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259541124 1250 259539874 259539883
    0x10f0c020c0f1503040b0c16030f08010b030105031b1203130f0b0901080a020703020c1c0b0a020a020a030807021f02270a050114090303180a150801030b070e040e 71
    0x921800791810b465140b0311032a00d4030041c1d10b000440074070b040ca1550746079100e01c00000002c2c0030303058039041882180c8581040c074601c62440c034860740718821900341d03e000280030300e80305901c0a42e00100400c01031143e900d0104803190349030007103441100340d0908100020102482c85050210074400403805400385c40742c05910b0b030200c0c2e191280100e4095101c00403501248186000240410380ea2000319410454030350080c480b10340684190380140b00c550002610201e000240380d068907801c00c1c10343c410300888090301a0445205402140f0f0030542c580c000c1e4503510324a03c043c003404507480001c3c02072402401188901202c0e250b003100c00b00c2a124121000b50404c0c880b0000110494181d0400c2880d420081c2c02035160041c046170900b458200115020b804600c0308a913a0300e010f10040c032450300c08001904032017400321400c14040d50a201803020030a411b9002c19140b034400c02c036000e1210781105040307041d00d401901850712039a1720003059031814a00080c55401500e04504004150380100d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259542374 1250 259541124 259541143
    0x120f01022805030c071a07020f070f0e0f041a0112110105031009020a03060b070b0f09071203050d06050d0c03031404030206040b09040b0307090507021c050a030509010f0c02 76
    0x4104541c10820540044144100c810380100070440030000b080388040c1003c0980030a500c01c84480040c001224a14800458181d91441c0940d1040c404089030710400c1c01810060300c2500d0070001200c0c5006190941404094140c40d14401d5040102d42804aa08929101a130420004008550b03551603108100040c09006403140c000c040d645040d551b2141003168002e214087c1c400070118200302c4030388001e42c0130303c8a403014155120800250f44050f0005441000d001e10700510051824071034003294000c0051828035150070000301840011506041e40c03244640500d411500d44942c10032140080c42660020380d88005001ea0020800041100c2501528403030b940301c07a645603005017640014000ca000c000d500541c00d00060001e0000b100107048103410051001c41e074055501d000c03030708003181d0303800030100d441e211300801490907010440c445200040304070300c035848140c0c04801441c07401420b00c40000c00d51228046489484250044050000c1194041007440503071000a1b50b074070306a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259543624 1250 259542374 259542397
    0x20a030e0a050a063905270a080d0807030e0a1707050d0513030b130b13140309090105010e0d06050a021c150303050a03061e052e0509120f0102 63
    0x80c2c2900381384160301804030360b26480320901860002c080034041826501d80717244403c02c1400d1089010111402d460058590041c1040601c6003048400740020440c003904107412540c0054800004caa07840103145d40d00195500d0001010604e81c0d150354280540e403e405000030752042c42d0702d264090003d00618406100304c0c1103d4080c2420380e801d40c0c440c05454001ca407088413540c0100086441200441e81c024042e0031001505291a0b4480040780d0061b103208050002c0420b00008103c0454034407030a2807015001942414004c0700003469050701401290704020010010300f5060722607000c52400b80b64401c0040c0700e1761501c0c0c008003009400529010255510541a0261280040c032940354000c00c1646c44d401450300319101507640d80d00012070b22080694615000400514001d0b103a41c0404e078060b0401d45003403030300003040030907204010220083c4080b1895451001d4020b8411400400681443c43d1940501000030f140f104100740c000303006015600e190055024194000c0010b800702 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259544874 1250 259543624 259543631
    0x105090c01080117010204051f021005010e130302010902040f020a03060f081e0307050a0b070806040515100e060316080106020a080f031005030d08010302120a03080406020a030e0a050a06 82
    0x44120940d65031256510a9000c29450001403180584681d440c40000408500252510f50360300d001c02c820355403158410a40304d80c003843c0b5240041d41841201002c1c0000c0c06e044c0560750510140c1c0038106c4016180e413607904ac014116904040c002e40103010216002030040000c030040e80d031200040e50040103007500003464000f010480407854101c00041d1407403080204801c01d030b000381007c007010304006015130901c001c2c060303800018000c01c030009005109403c032168508003c6009400307508090000ca01c201c0c03c0c8410440d6032180c0c2e040c0f202040108540b0141018232030300302074810591031a10250410740000c2040111800e0310f0030315802d41e0150740c407620640c1ea51041280c5a0755094001041c1c09400c0080048918045014540115031218203400e560354540c00a482d1031201004803012401c3c03600104250301c0c0092070800d804445030050102e04040b075500500000c0000c0c00240601e0307012403400d0b20713544240d01004900000908580b01458582041a0756030448a0203d038180d09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259546124 1250 259544874 259544881
    0x10b270d141c05250503040830070b1504090501051605160605060109050604060f0906050405010e0105070602070507030c090b01030b100f111c090f08211e0307020105 73
    0x40c640c40102c044082e80e902ca0b0700b07019040d802e8038040e210007003021203110404a081c6021030700510007880240001c400400c807407003100380084403095807841489020520402603525400140c1c08650b0342c26800b0b02140c81c075644086900300a10140c050340f80e08540f41418602c10010f055100c03078002c413034210340081c00004131103044480344a10701b1a680201204801000003400c580c10954124405040c00541c0588800220304142c2080e4080c2c40003400d10b981c0e035902e035500400790b040501040c0c03508071325250400e4000703403000b04949203007410040002004001d021460303064a100c1075000c01595496943ca04019809040c280107042c0f05601c1d011000c44a0740c002e205081450034080d042e41c1642129890903150035141c4410710050144150509400a2051004c200200424013202004160312038004007404015000040321024603402448007a400098005d24030304880c07005004640101e00c2065980506414050b810902140d03072000c150030f01d001355110b803402d41e008100d0b81d07a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259547374 1250 259546124 259546153
    0xe0d0203070b010e06011e11061e160f05090d120201020909070801230d141b010801030c0e040812010b1c0b22142706010b270d14 57
    0x980a90707400e400b080100140588450035402030844d40d481c241001da020300e20084901e81030a00441da41c034005240b60402b0807801c01d01c2c1e444ca9421035040c40c04c0c14403151800700090b000100001c006401d200d00800e141d203455a90782a07402c0110341c001c030640d6105218041c068040e400400d40c442c42051004002440310340700b54251412142e101c0c804c0b1200445d021101c400c814181d5030541e801c10300e0b0f20050404540226000324000c0881c800800003000e4155021385404411810503042008100040002c2071502c0304440035500c44502c8243c2c1907c451134008001d02c59140342d04000031642c0000104500d9a2020744208420444100c80c4a44810040011191100300c0703942d0000a146d00b600e091406046e48407080161582c0c0040c0040c0325918000e0045070868003ea0007040362000c1e0340e180090036281040164949000f401c65504288096030103020305024080e84038542d06190011203400c00780111501005401100312400780e0809041080903644405280d128030ba80f0501d500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259548624 1250 259547374 259547399
    0x13020310082e0204030206190e01020109031d0a0510020303011e03050316060b3f070312090f090e07060206090d1110061205010f0605011709010e0d0203070b01 70
    0x418407a484070a203060000b801c18841c040c00d646000b03606900340b20100042c1c0700c0000404070010b110b0f071040800203c009005200d4860b030000c29045904001e0b04100107074104003040c104440c40b17662140e0445c08080400d044074803a5011941c0080c0d418141145143c000c00118140e581c96218100d100c1078021400e4a941402c4c8001010750380200485c2c040c040d503a451380301100340b05120115001c203201002036200100b001c803109041c4211030360500c2000241114180c400e000000c0c07408801e0381c002d00c0584481061101815195038001400320080c411403440010b030002d24001c2c8000b40e20341e61001c008003414917410003a8881c03a00f010a00c1c6c0d00000b5500e20031451038004140038000c4103411150040207001e945141c6c8105a040c0c1039480781c50240001410550300c4044650245080080c03d40c0c0d8110384e42c410a0707180c10402c0c01542d03401162a01004150700c142101610349a045600600d0203424400f80e40c016140c41e0340c1015800f02c010b01032180034400c4a041a600c0358200d01e0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259549874 1250 259548624 259548643
    0x3070f2901030321060906090b031006050d0b04030c08040611060915160918090201090e092805060f060112020c210706050103080702040e0613201302031008 69
    0xc100d400c01c101c80f1246102144c481e040400400116038140d5451010040d03808581285500030384a403019015402c041101410a05c2d0259051146c00e180001180113810707030311005000e03821508001000c0c0350140c00010302c0b143c0c3c0080b103959540c4c1d4403600142070a1a40c0d101a03403070b000d40c50125692010003d5005000c4407100400c2202c1e031a00320140500b42c03481d81d00c01e0284a41740400240103440c1a425078007100d50f00002017051240c80c80014140d2419400408200c115641401040040044c01d18141804a5805d90038903c1079041c01320300700301030040200326119400400404420a01c4420300403202038807400d17040d1010302c07809016406018850703030300c41d4400b0101410b521404000e05011880c008002480c18045031520740580e18241c00640d400340000641d43c045017001c0c440c091800b42c6400c040d0150342005181200004528400580720b40c5a601881034442c2c058404009610030042c08210030311204100480a17400458240740304141492000680c5c00012890441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259551124 1250 259549874 259549877
    0x13150504030e24040801020d39031404150506040b2803170a09050a140111031312050c09070f05031009090303020c01060f0f1703070f29010303 63
    0x6418000014811002c0d200c0510020f140075184825000c518a00002e00141400e100090f94500d02c2141c081e00350b81884071031200e202196440c68440308941c0e03000c050504001c0d540c5038545149410308030041c0c58403145244000c0c0d06078007030100f00410344000340f01000300e041052011f56038200800c012160035840050304042c080501d0114010380a01d8500c440d1410441101819107036215054605103600029404e85400141c03500c80f41e804c8203282c00180801c4071040d02c040c2c101a20005001ca0003c002d40c14054030700504030b20450103005486121403025441c3d000d0300e50321521140c82c070751003c4050b02c160007800400c10480c00c1c014116480790000f5103500100005107201200e580e80000d03d0502c51b10416007010484816501a15507654000e139800758a030414650b0b080c1c04c503a01030f40041030b09101c0e030000704000c91400f2181011a80c5986041c00c590789400115810342c0b0452000a10540d501200e1104000d50241c000c1c0c41440c000c0703240d00b9105e06414086403802070a004c00740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259552374 1250 259551124 259551137
    0x3060c030915061512010303120603030519090816030b010e070c0f030908150117011a01030e0307050304090e060106111507030e07080d021b100c08121315050403 71
    0x304411000b20403030f800038000340200d010240748000f00361182d041100b600c800210003000410a0541c4008400320702d00380440100445851550301038028410000c101c11700b00c207204031103401c0a01449039400102039010644000c01c11034649801d041c02d050008480500d80d040001c1007188e10341d03609510408060f120301d1941c0c1c0013602c1d0031120040d006821401c0040e030300004a035400c0140070b18104a004480ca01e039840d410001c01c242000c2500c141310507143c1c5080d50b0303030090303603e00440310141d21400c0c00c0009140420700c402d00d085125041d070103449840f00140014008181c0da0080720320f0810740301501c4599880e40b40850315010800350a89003944284603040b0b000041442103030700002c141c100000d01e40c16205141c1c1c00e19a041c1d000345103a4101080d9400603035014401c83d41e07818414400c0c00c000031078000000380c001002c07420080030000070707080000822083c001100d54100d910480010030349031040014407440c0c116002182d290266140d40e0b04800641e0264500907a4035450b03a6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259553624 1250 259552374 259552393
    0x300c090f020702030d1803051005071b050a02011b0b010e0129030f130209160815010203030112260c0c09010308070b0613020d0608010c020c031e10020f0903060c0309 73
    0xf05c6e0380303807841e14070910341c0b0403054000000101c0c200b0000c03015220040c07010481d1300e801000540310030705503c0c010b24003180c8070301040c001501c0450a030042c25230900b09440b0140101c0c403500e1400607006002010b6600f0000003064080c0c00d501e07100d040758035281c4900798001651030110440c0036202031403100d000c8240041060b01c42c1c201481035000380075000001c2c0c2070304a41c0002c1c01030030060b61000980260400c203c49210351004150380e200c4031120303401171404d00c0800000e50300c0c8014482c94640030f0480c02010100401880c24014404c4c403c890040c501101c081c080c44103503c00d82c1495000e2154249000305810702007001412a504844000d007000301c0d646071f031000030000410740f962190340c0040c900c1302006544050b22084030a008001421030800219a007120750f107581107019580202109038482d94005540d0b03c1c16202c2144610800740018411494050080f0500d86244e00100d0641c200d000b0718000380c16003500c210308407840780e203600c1c50210701e501c8195213551068001540f40d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259554874 1250 259553624 259553627
    0xf010c12091b0603020306040f0b03030a030911030607050406030e070e040201050c010f0501180b090f0c0d0b060703030e011b090b090102070f121713300c090f020702030d 75
    0x12900c10b4007420200004080036400051242e005800000200b603000c024010241401e100d111401d2004000801503803d407200000e5890162980480401d03445d02044800c0002c03182d03643c030016002800f200c440b42441c00e0060b00c1303a0003e000f07440009103840641520781c40001001c42c21260301da4180300241e03e56800443d03250303000501c0660b5035134880044a000880501c61103000b400300410000c05001c048180b034081c2c1d102c055460380319945038010300c80c0304880d83d4401c681240c03001c0009079a403c2040c2004002d04041c2030f905900040200f0750310181500b60700420380f26201c800082042d03140712414485206c40380c136904400511149004c2c45090b0001004000360101401141c00d139683d100368404941c2d00f02d400c07015030300300317204110001c000c0c1c0c5200c0e0003c1c224030401e40a04101030680d4409488280b413045170b40008207020210300183d0f0300d4600356070320398440840941142403402e180d0066040b6120b440f604926018000001c0a5640f00b076450706640100a060207008041c0e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259556124 1250 259554874 259554881
    0x302030105031b3601080c01030e030304080a0810030f0605060112090f0201110c060301080313050d030e04110d050406050403020d14030a0c180602070e1503101a0a0305010605030f010c12 82
    0x30782130024164481040001c103100303da640c02408000010142d45095100041c19100b60415000b04c9900034024400043c4c484000d03501400140d00d402c044030764070110f0020440680d940701809601641070448203004582e0042445000280c03201740c02d2514000d0150700711654920040c14440019000c00010340c810700603810b00e4a1104100c070074516001c400180d140c0c1c0280e1010030705130b1001600e06220201d1003141070081100b11110117141c03040d43c8000d02100405150a80300d07a50ba04541d80e101c081c00070a1b02d400808600341040503251914083c0b0080c01d040e1000d401603c982e0850b4a0094442c0d100c03080e01c00703c003068850440e100c18004402800c0d16509400c00c0c03040c10f10740f0070f40080c0d60440e5240181a103500500700145031801540e10701102a180c580c032040380701d0034000c240d1400075803200d8209a105000640c20717a003840549054044045007644600305140000501c141500302d0400c1d10011015602c40c5440462024200c401200121000c0740f0030800b4111341e134006a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259557374 1250 259556124 259556179
    0x141303081308130605030105040608030406090b09040609090b041b0b070f02040603050a03080f0f060d02060313060f060602011410120c0b04060f030e0a0b150109030606060302030105031b 82
    0x224550f0400300b404004074182003c5812000000d0800300c010841d44ca01401920300801000010354030b000d00703008000345404401e000d0544403a1f40000c68000c0d0b81c6035903001c507004001280e8100000592441c00500c42d80c41600e0079030340301045084001041241860030030444d041811f131a407410318207507152000a495148261b03809a9100780c000081a014405140e400e880395850152a01d00b5201032000d2600180007101c13024090340030404107482d00b40d5221292501241e49035180d580d0072000901015075640005c0040e4100f020840310322040c0d030040810b4820a4000348144007480c070035a00480012511880c070103003628010004201004246c0d0392a42c01699000e01c0d0079103800203062654040d50120002419841242003560341c580718034801c41d103502c80034180c14002d64a07002001d51000c1d200c60102a8510304007006603000d60b02d40e0006641c04582801042c0d92030380050001e4200f485010302a000d0003007030404d201e0700f111156502020040c92400503203c40caa18102180209 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259558624 1250 259557374 259557383
    0x231b0c0913050c090a050601080a050402090a090602090a090b01020c01020a080706090c0e0c0d0b030a170a030b0a0b0d11160305030a090203160303020c01020f120c0a0b010305011413030813 83
    0x21050142e5544440d03131114402c514030b80f804112814203d000420190300200340c082d07180d04e80b100740401030780e6446c503c85d0440045040852030351b89509019000b80303d004401540100b440c4000102e48070140c1190128940980a032041c01040e0401aa218010b00c0c1d0b001381740450400103100081c1440d0f0004903058000e0038400f203015200c0d5046da817000016207100200301004030b02680c0d41c6070f880c020b80c25942e034158007424910945a60304000380003181c9044034040000b20700318022034801d0340082c0f43c0120003804204001e91302c0000000030780c0001c1d400d81400b030505c2c03100003010144004071050b604000000d2000003050313460407182600b018014090294550802c01d015a800300061200c80d610400c004601a2a62030081c2c81c2031184ca0140e4159000350a440c480303100003183c40d01c03010309440122543e0700d25041c805401c2c81d05180d001846030200c58004010302c60305500c8000030740a8800d4001c12500c4a4480c460503900d03e100060024121000180c415403612480c03284442c4078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259559874 1250 259558624 259558633
    0x5100e03010c1d151324030905060a05040314070c080105010803040503030a030e010b040608060604050105031903141306020303100503010b0904110a0902160512030f16231b0c091305 80
    0x10b00382d0968407030600ea4400302c00540122252040c805600c502d400000320341f81020003852005950340d9854030700040845004541e9000000c0515000b00022000e14000300c01c091340c0c840030b41ca040c2e07a400d03c1d11302071012107601c0e0a00202e0100000011601540c20040c01542000c907102e00c214090b00000c00b016549540b50702c5004843e403100d020380801b808030140900f030245401c900f0b2008031913050b80050b00c07a034801a4404000a451104c80004035010710784082083d0032200c10040d280301303031001d82c4a01108101d0010340164044041c0d030060150364035a04000365580105800d84a064552980c0328003110003040c001000300e11948004034014151480b4941c2c1c8040110403a041800c55043c1a41844003482c01c20105000f00300312904490135050a5083c4841418007882008113071640607141c171400d100c24603000d01c9050403850303503074411110b4600403500650b41640059904031184440d404100c0481980804c1d45688000c002c1c042c0204c65544141c0241d511303142c52410f81d00b0380503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259561124 1250 259559874 259559887
    0x12040506070507091509180312020706060b070b010f1502060114030109051615180e0903070f0c030c0506030f151305090c210c01051305100e03010c1d15 67
    0x281350017190394400d0003540301643c452a107a5548207803021400383c6880e01010550080003c0c0c0c0010301e0748001050004010389038680382c5041001003009400c11819180003041403410046001282c5050b190b08107100e180599481d45000380072040d0401041c090b03081500184a881d12600020481e85401400402c502c85039443c3c1e282004900025040301461490040c070003c0c141440d4446401d110380303410014005032100c91604040c00c0d000b511045510440031442040d400c0080e0340e800740d0805c034400c0d0780e00703068134040055004900c0200e6100e41401e40006841ca045400c0d2481030791018034481165a4280809440e510451402c42c0e008108010b000411f0030300344601c6214440c271000501c01043d0510400072520120070640d505940c0d10f020b5407c00490114901c0c20040c0c013800c0032511080030140d600c010392015085a5005030f105649400315913070100c40a440e00348141c00030804120b01c00d02c1210070500c02c100c2c0d00000442e00680190700d040c202441a0a02d8101d0907103410f140c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259562374 1250 259561124 259561139
    0x63c030209070903050610081f020403020a0807030c05040507050909071b08090906060c0d03020a09050d0609060b09060a051203071704032d02060912070b0d06050312040506070507 79
    0x1c5040ea048000102c1500040c13080060802c00141c0044003a0b642608591401c0c1403d41d45582c00101c20046c0b07140c079040305160b9087c3e60107807805103500038245140c4a8803a058180d84014921054400e140c0801d00041c59042078400c59000b4550740c1d4419142002da0018000d450402418400400030144151240f4030702e01a0075174210761003400095a2484030908000403100040c0102d803041004012031410010006a0208124003e017070140c1c540400d031006549800701c950103250441c0e1054102010000c0c41d50002980030700ca041c0402c001115071040c419140c2e800c43c0d83c0c070b80002b00080300307221038a8803001d81011503010001312443c1200c1a962100c908401514000100e00c0c041b500b032007004940c5c4004004100164043e0341003a4030b00f40c2d402403040c0e032003070064010480015001200e44841090410a059076021981d929076140d403403a11950100890405072498070001240e1072070081070116142c42f09061407030905080004108190740007510840c1c440c4070395000082d107075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259563624 1250 259562374 259562389
    0x2030a02041b0201151d100302100c260301051509030106150210050c16020301020903010519060e040c090b0102030d110d0609020c0607030f0b1305010801063c0302 72
    0x15441060060102d00c00004041c2c00d440c000c0c142040203000c18117080c020340d90000d95820b07203201c0d988028401610b881c40e00303030854440c03904065009445001240d1a10740c2080620a4661058a03011303d9400c031004403c642289406903c101d20b002000104001e10304498911a170700d8041720300c58a801c02440019003102d20b01d90001e41030f007056001d0340d022580c050103e1000040d132902c080c4158a0704000480140c481e07407041234000c0b0040c91140042d0b403425030540d00c80546c0907008026074140480310700c80e00060081014034407400d0580c04034902e0483e44400f80601e9002042c074601e40d09098603038001d000003245880c11488144203c1d0341c0440503002c0d610807441c120580d81d82c1c43e510314402c0e4090b1190740e000030107105d004203e60556031400042081e842481840c0004540311141c4c8038001500e00c00c00c01d958001458220302029084c1644503a04a2782c020001b040115900c13840712160360b00000c118500d0354130385500520882030050f0bd41c1441481002021071198503940003c081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259564874 1250 259563624 259563641
    0xe09060301182108040c0306050c04081006090f140c0708160f17040501020a110307081204050a050901050d060207060f0207030e030c0114090d06020c03030903130614090d02030a0204 80
    0x95480009000a0360268a03e540600182d14505a40c880c58540c598400351181480010000f030b039690005201e00100c001941c002d41402700656804464511004004d001c3c24001c440e02c447c03502c120004081005e02c24007090100d40701200002d07940340c0862083c96005010241d51902c41001602c5a20342d07a080d01022041c410020381e19506d001d410406840c003a4807012240c00ca80c10071091040b40e8000600080c40e680c44104180c412008001003800c0c10002e9100b6010b41c81a00d0b41019041a20006441a60030648182e100c4683d1002080300b403000030301c2401d0b004070301441210042080d54008188650103918042205484c00a03a2012a402450150300051086071060140e00e004c0c04940f0f00341c00b0034a40000c18882c0700440450f5489080a60342c030031000084035408118140d010f54000c0c420706410307647c480c900300c060552243c2c071154495202c01540e200c0400c00c41e014001000c04036000da0031160522120343c00303000e9a044070341e005236407621540080034016615402103100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259566124 1250 259564874 259564883
    0x370b060409020c070f05060711090403032418110a0f02010b0306040c062318040609060b030f070906020a0206090102030d050a0218061206010e210706140306010e0906030118 76
    0x1341600d040011000284c15030480d80c0724013000c00c14a0003140907809030340b41c5411300311142c52031a02c403450160010161f44503000da0014032840074054a02c894000d200840303c1da0000c207030200020000c1d0104070b44686a800106510500540e9030317003445030702401031904660000060082c90322700002d01d02202103c0071590346058a0b4148810740e80300c5885062204050344280c50381088a55540b018058000c203040c007800703400310018080e5907a07007101c001460003104c2000200d88550410030300e9030040301c801d1000d000c0e0001007103030b680c4100700980888090303074060b0020030741e07603030812803158000c4004ee811444180405046000e44d481050701403c1c2c05940107039503049154066020030380008040d4444c403420700298000100b418096903200409190110b803040000c000601d94442950070100a550320b00302e11800b52000181034010b0396001c1d00c03614040145980d1003811440b0445945000442040304100e81d400d1450540c0c1c1c1011000b000480c505000c100300b0010741104040030748 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259567374 1250 259566124 259566133
    0x70801091112011505011209060e0604020102120414060d11030a09112b06020f0415030b0d03021009140a062007081c021b06370b060409020c 62
    0x455842c22284078000188100004c1c0414050004002d075940f4461042a0510440d410303102d40729003850f0310401016a00800400420f5862002603560703540440c0c0c124054410f80c54290401480a015102140c0300c90b0718280042c0d5101c414800650000042d41d034250782c80300005d07032420381418007641c440d403602c0d44002015402400d08074104002c13100100d0041c0c09140011a444008003019101c00c07607081080f58041e190351814400a02c10f282055412100105011811922070b0348600700d003406694060240d03403000d00401000c041007580040140c0d00c0340081079419036090300f2215a06003d2900035002d114628206810807900c60021510180c4e24041074050304150507001682104002c401c90030a500d0742d0315010341e03114664503036860f0348920f24010310961003901264030440e48480c803d000035900701c00c125a00e00c42a030b506001904078800341c1c01405c0c0b8002c00c02a0185d000c1c550802110000d804100c01443d4042c0340c5078000c40c0070040801c00c12214002050b2200c8100d0041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259568624 1250 259567374 259567403
    0xc0a090b15250c050402160c050612040b090a021c03021e1908040504060605031603110a18030b090607021005040210260a06080c0103020f03010905060307080109 71
    0x340d9507040450040c50064184000c01204588401c2071803800040070000852000c03070b080091880d81268000f5912038000030b03584042c284e284801c2c101c2588101e556010050b220401c20001c0e0007450120064100c2a0300000c02140100500070f0300f00900c00d09507000d00c0d44d240c0104100d03405e42078a040f00e0300c2e603c00d1003004040e41000140c0d00307400c0701c00323000d01400c40e42c00e40e890700d4262200d8200c0e0700c9403c803860207013808001030454006100003401044070306d43e01d42c1c0c00b40139070300100c0e001c0e500701d02000c031b41e61100f5002c0c1c00b49100903000708861030324040106000742c3d00205a4468070960000000000c400204482d00d00c41c01101e45200400452400e581c00904c0e004002100c08092070606040c400141c807071600880303440b0404e0914280d020060406040540c0c903600502c20758141c0c01050120740c852030381c00301c01078a0f003800540b500b03003a5402c010b4040e4440d10781800c810328003c0004005080e2590b001c2a006a002403d9403a001e590340d02c21401c1d80d80c1e031981030300c00c0f00c0c882550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259569874 1250 259568624 259568629
    0xb030105010e1b03040f02150d0c020a060b0303030f0f090c03010e030c0706020d020703170f0d0c020111120103111c0606050102010510050607110102031603050705190203120c0c0a090b 81
    0x11540040414103600d50b140c6a6180050206d026000a0044100d0002980e031000640e09aa0031500c1e12102084044910308000b55a0404840b05681403460031000c002c06050101c1145d1080f614440b00d484191590226100e2817000182002d0403809488100002540c0078054031040c03131400402151240b4004030441d003440515070100301590300200003500b00540100b0b03440e00300e070b412410b030b0058100d00c0b5806501901c902014071203806400940481c03502601e07070021851070820390080004141c07803c0005443d1040003002d02e840660800100001140900c817461410f401901c030201c0c074000e26054080341d125120b41100c955888400038400e65a09204459120205508072090545048003280551040c028003030851254206400c88a900803c02c6510000740002c03295002112410010b205802c101c1d4229440d0089100610085e641c9940340c2c408a50001c000d800e0503441101d6411940c0e00650b020952801a0707141401d069880301422002004612000301c0c1d000e521004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259571124 1250 259569874 259569901
    0x10e030c011a0604120807080403021f1205060a14040b220f02040302010c021009081f0609020403170c0a0602040e0708070f0210090c0302040f2f0306010c03030b030105010e 76
    0x3400f8041d200070b0100f00304480504400e5850960018051650b0f120b9900300b0403010301c900e800280d0401c0000b414681c500114070706d03132000c5e00c00c0343c0d4602140320301d1030700e013241980d2042d42c0007503000350211800c4c401040a01c205003601c0c80c2c010030018a4021101c0401c4e44034004020300c800c50348113407459603800d00300b1380624000159040b07802c500e800d0444e8006800c061040328064000e40000ca451030145011b92413181c00b81600c1000c907541e130071141001c1500b0705a00f00c1100c92103800c11400180c1742c00c6034002d44d81629403204044203102080300000ca03d0350810170140c03c1d44c1c4070300800b50010a02510052014003546c0050302c820b460280e00142c1280005042d010401c08040500075066a020030a1a1700c494411070114460b1000e0500c05215042504041c0d40035103020200800da032150740c401d090300c1491400c1601c0d002201202d024002d500419000e902e14810400074050358895010558598030900700000c0c01c80729200402d0841d0b900341c1200700d075490030380148003164001c0d80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259572374 1250 259571124 259571171
    0xf18090b0a06020303070210020702030f060103060b01030e061302150409060b0d0c05120f1008010e07170307080d270507080105130809210d0201050f131a060102010e030c01 76
    0xd41c510304140f4070003941c8d094020303152111660302042080855070140083c0124034602001c40b000c0f035840c0e0a0000c0188180d04d0303160b01192801c891300d0f019807404140c45204080c81c920207071030034541e1303002e10034544190103001040da434081002081684282c400c200103070070244210398a0381c3c209004002241d02c4803100a00340802444040382041d142d03484150712803900e4030085d030035403116140051800d00c1038002c4100c1e542410841c3c1000b03500055036030102e03210440d00e41d50301081d030f940c019140d20548030050b000c4902003103100c5005c1a23540081c1c0d0440c014400451911503150410301c40010b000408403056004030404221701c81003400782d030790404020100b0014421482e51104124421aa10140104001c966500780080c145200c2e0418415000564007030100d80310009008003003c443c582e010076044000b182843c000c01080c9240940d00c841403800c030400c94607806d4640725000b00034504564803000400300b801824000303806100030010000c07070101407901603407201d4032810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259573624 1250 259572374 259572377
    0x90a0b0303090d020a08030d050f01050109050127120f050c04050c07020d051e10050a050f041b03050d0e04060503010b180c040f0b0a02150105010e010f18090b0a06 72
    0x5404400595008001c850300400d080740c41201c45150f07480031503908034007544401210b002c0400c03480f4401c1c3ca1500418800e013807120050003640e80b01c0e0010340740325242d4080c541c0040c8420f400d2120000d18bd816003410b048035a240b5502140d41d0313040a140c00b0180303000803a00f074049a50000c0c2002010003044480b21400c031414441c2e40751120031481c3c01e000d83e00010b441040003101c0a810f0080c1408000b0400c01007940800c0c01c0180d1505035a41c507100506d5a403062071824001640503400c520031f0074003410104001c0031240c0c561b52950404407081d1480c41503038071036401001000800410020000711250b448004200c042e610412040384d00d030b54807040c066410604100042d5560307840d008070300c02240407842c00c01d4030307204014503890040780c00c07040448410316408640403481101510108106a007141c030125156600300304464028071400c0c1c0441c1903071940042960150444000e02e40251801c8011407142c010002c0c41442c0951041031841e0b0b132101c1c8c490b02410148034072005403856 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259574874 1250 259573624 259573631
    0xf020d03060b0913110706090209010915030f1a162303040308070c05071818050c04020a051612090b0a091a040801140f01170a02060c0a0b15090a 64
    0x1000b02c542681c0c419400580c3c41103403640360301040340386640c0c410840c030886414855140c40f041c1c41d200b4000d01d50104141c0c820b5482c4800024161160f0085000c0914404100450302c5d04c0c5903980b40b0100c2483c40c00715007840c043d038400d610180a1018a501c01d40110320600f044140300c04028000ba04952a4100400301140d010541001140d044075002035140ca8500c84640e640c0e0703012074443c14100401016400307044000100030711188040d2942e6288403400300100c2803811601805031806036401406074101408559040c60103034050101e0490701e0425507c0c1901111036034990045a0b0000c40d1014003e1180041c2668055240c82c0501404600640703011440b003000f42a0344881d100361419101c400c000d40d10000e4402061b20003c25407040207104101c00210311f1400d81d0b0089500100d60021040000b880c1b8400340040b010b0101054040c02100300c0a0302804000d0307010000f1541d0380d20840450200151500984610840c2c21090040009030400204854004081d103032210b0b150a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259576124 1250 259574874 259574879
    0x90c080a080708070204060e0109020304051203130f110616051908031303020304050a0e0610021c05070f0203070b0d0506040507090605090a15090501110304030b06120106080105070f020d0306 84
    0x2410400c8031046500f0645041c1c440e0b2032480000c024080b99040707965985000000020503800c99000341d4002c0b80b0420542e903503110805210900382c002242e081208040004400c00485c5088800003203050142c83c04c62602d4213600041001c0340e004602000456100750710000c00d011040c454410f07000541156400790045035190609c8600000e0f1445c0740e002100505002018020022200200300242c0f042000c01e80d2083d4009403101d003243e280d800340031504480e62100d4404124080c01c061003221190510410315411201604400310491300020030041e1100503a13010400300004200c003910b8103aa1b04204c4407910b080c1ca03800740c03040303000310b06140c140040a0b03004000c00302a5060361900c02d0321400c621002851460856108101280c9461172918140e64084403881c213550003a04c0d86440c0708000191140d8a04c11072001400304d44010012460030300c2c0003004041e460302c0034000490703299200c1c080a421508142e5454021810f00030010100c59010710540c0d12404040c02c0c1040700c00d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259577374 1250 259576124 259576133
    0x3060408091005070203060a02030619060807050a2f07090e07030f02060d1a0a0f030c0b1608040b0d050108061603020310030c030c030308280c090504050a090c080a 72
    0x207144006441400341d07465503110284144256111a0303002000c0360141c0c1044812070009520603542c7c04d01980740c072000100400a1042e100701150900da907000b8480d940ca00c01101c0640201d80c1d60703000c1100d131040c0d4a05032035074043c00143c0130b0621000341070801c2d140b4080b18680040ea60100300603504042244819940c0030904c0401c498000004190102c051320014141d40320701c5005c04c03041ca281c50106000c0c040307000051080c481066544010b030b6905c9001141c210030040c80024030b54151841d00b84400e40f1904c024204040c0a00700b50340302c80c80300385c0d174106d9640c0045c0c0042941c1040820515810051070051384d0040c01000050050f0342800036a07071121a00540c2188241500000868509111505480011a00010ba11440a40700c0c80c001100c402c8030f10051340080e1030340c401f20702041321081d070010115007450f00300c41ca107030750040c07456000d0328a28005805024400000040f9621680100c0d407181c42c52090000c0d11001c0c41c903151004100e03540101d0300c40d070b110071402c00008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259578624 1250 259577374 259577377
    0x10c0309090f090803090f0f1605120a0b0109020d1805210409090b0105090c120712201c0b0609040203060f0a0e0702010b1014070311011b03050603060408 68
    0x1d0700003034004540065240151406032070310390b10040c400c000000810070401404156000824480c80549610b00010f11a00741d68800c0303056003906c0b1002d070345001c00036440c292518400c01c0d08158140c2c0d01d9054981c50300c403020f242c244d00010f0810307000a01d81c4902c0086202d03240107d00c0c03030294002800343c141c5601f41e51b83c40d2007800600c059a000e01604500500070165802031400031018000c0020529201c0c421210a106903030241c10369201142c000c038595030680309280e413910f015008947d101801140d2550344820301e0110543c0c3c03224848034540221300320510102c41502c01d156203000d1803110b000743c22400541030032054030301745c841c411607601c1070111400b41c1c0040f58050384030788501d4002840901054401540600c540c100001d2101107115500d00c00c02890f00200600c00b200303400d00440070b59400d44040002e4030010641c1c0f04039858800340c60384900901d0640044600910014211b030302661007062441d4035282407440084d45401035030381c401c0c0207030054042810683e8540e0802d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259579874 1250 259578624 259578629
    0x3020f06060d1703070908010c0f080c030c0f0d020d0203010f0519081c031b020a0b0c070c0e0a020c07080304050a0f080604032601140909030a0210180b04061505010c0309 75
    0x76580013011070800d510440c103860251401f100204142108c802004d001b00c5c0c0019a03450100780034030009541d0b80218419241301c0d149250f807981c60301205240c65070165001140e03c1c04032684c240a00c1904503940d101842c0a80300d03074900d45100b5810407040200c8909404d02d01140a04115000d00403001c0100e03900140d640d005052150398222000700382d0250644110403100d04032906801001240c0c0016084400c501a5103403050a1700daa44041302d582c842c04401500c0300700103c008101314078880d11001da00c244036070f20041c149004610b20504000040c4e1107400751398004a0140030030b1810302054001410a49242684140740420b450b403a80d00003030003c0e0038000020381103000b00c88035100c454034550f604551030066684401d0300000441142d92120700030070403403001607000034000040b02e0307070030030160024503400600082c0b44014081905100c00381c80a030855642c001002d40c60680e00a0740304100101d054070465004415503000e40e804141080884212203001c00d420010002c107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259581124 1250 259579874 259579913
    0xd0b03010e1c02101406010e060a080403051c1404060b060c0615010c14010203090c0d151109040903030911190e0912030114040f060515070203070e0403020f06060d 72
    0x28407080c09102a41004e1381e1000003104907040150340a1148100c50303c1500c100e50980b1140701145102050154902404035458040b900c80d0f000300300401d0040000e41402d1280012843c00d100804c4040c505440c081190b009410000b501030004000c860b000322601842e0549100d8200140361480d242d0321100a40740e1280c0400002c00104c55034480c4c80322002e175a81100310007090403d1356104d41c0c001d61086540340e403a4003803030b80c01c00c40034a040340500c0d944640111000282d1a0010403142c001c5c44003203100407841c80c0801500302d07a5102d86c050465941d0003a00c00040050305418802c0d102c08014600c6c5200c3c0c40c03441daa036070440c00c0500120b03054880042c080203155840344c00d4a40303419590020600742e00c002000001d94400c00903451501ca41e4155010300061100208103400d55a4500841ea840003000850b0b17041c40ba078400180403018001021030f403006680c0c0c161604a060248c900343c0045e0800800034a400508201807500000c0030b9a02100011007622013030207940d40000c001c03a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259582374 1250 259581124 259581163
    0x303051005150c1b0a0e0415020a0801080d020d170a0615020d08010e07050f07052508010c03060b1c090c0e1602060f0601051b10050a060b161115030c0d0b03010e 71
    0x1414848c0d150b03c282c42c0c91060720350455440d01c0070100a04950b000b44a01c0e0410322a403212b019541d0303c0400c035405c4588441d1105102e0b46807856604881c401d00403c024900741e6905400506500000c021900006d59500070b4400c544058000610a0205070010500c0c4d40248e420711007610703808000c49500d0700781c42952589550043c0340550030000c2900d6203104004801e03a5281003120800500412941248020007004d0140b020580a882c101d00c5698503043d0305100050354a060080344000d0408400800640e2180700d544e407660140b841c2d00700c012110b51140801c401308030141d0020740e07850401d00003000c0f10700d815414030302c0010740244810b0402c04c010a0349404005082001c0099041c281b080d606101d41c9520b000d001000103c81c071411040c14400002480c0b44130030200c51404a0300b0701c41c0301c5189643d031100070803d9865401d064000716120100324031914004040e6015405290308641d0300c5551131503910654603d1003403540319900d810072842c080500001c200c44102198020722 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259583624 1250 259582374 259582381
    0x601031202070f0509040b0621070e06040924020421050705060304080406050f040b07050f0601060c050712050312070e030105010f12060b04020c01090809040c0c0803040303051005150c1b0a0e 84
    0x2403680c0796100049c107038841a5100504040e10b0100d506d8061f9461000b8041440d80c1c3d8108100031348116090103030004501a004100d03600c4143d1400040c01a00e8401610f043d41d2840036051f00005482d445000e503080b034100d40c0400c042485080000c002c120b4001c0d007035050544401c03105125a101d500c084c42000981c05040201500a5030003c1401c5400d150704c801031404d140d0313155070038510752880c2130103a100081407041c041c004240166401c43c0003000311500300188036040610000f0309440341e11041c0b0156580407080ea880ca80b0403941c6a4441500701200401e150035507006821218030a59008801d1200d9030100303002500b103e401c250042545c00014011030028412100c0d400301550800c02d0103400c0c047c8200080c68100415a01040780f0400d50004440c10440c0341c40003000c6030020004034020a10940050760007074424446216496a0340c00054944007039081004480e070380100d8a020010000d002d07500c2174550311120f039505400381000003014890140900c180700c82c0d480011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259584874 1250 259583624 259583629
    0x603050106081306060f06120605030706050d0e16031202010c080708070507031413030209060a03050a030f090b03010e07080f0622021606021902010207020d021c050601031202070f0509040b06 84
    0x1071001040e030014040d0b61031380c68140051008c902c00c2d4000400a0500c0400610340c00d000400c4801c440303140d66900d047c00d00c0d02000707a024181504050390548602880b070440f40440c8a080c03402584100242c0c421180089806802e40e502074020406003c0c26a04012405401c017880316803022381c514119079144450301e03080c1d4142c070702c004071520540c1c2c000c12160160a010343d0300d401070340d00848107c02c041d03694800b000700c40d00007800001c240350080349100c0002809104400c1007041ca80c281154003075220814048160000d0b030001018824035010f02c80101c0d0480c40c49500b1068103422803626141c0f0130081100300d641c0c5980c1c840700f2202d00d0440b1400b1003140e0706a0b180140510b407110034003026810918080e4001681e00340030882120541d041c00b0340144205d8002c50740c0901120800e603620340070000501044075a00b03101000c82050480010002e00100b8084e45c4162540003161b0403205009203028040d4229119002d4241c00600956a5500207980c1c010380c4020751030b5035079660602 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259586124 1250 259584874 259584881
    0x903030d0c02010c020f07150c0507090c180909050a02090a02040e24010f0e13110714010c0504030503040902160203070312030f052403011b020105060a0603050106081306 75
    0x5054142074035142480c80155419002040403100b039600305c907081091105042d45803581c602c500c0c603a07209282c1425030018064014010814006c80503602d085617030702d054034140e40c0c48800480000303212100300f2000003031074629107000d0b280e8046d040294034907555031169034400c1014041e105007010300005140d00d0427a01103a02400c20541c01407900d00f40850f200142d204014200c1101781d410581c080a00c1d40f00e9200402040c00603070b981002e10017a5400e02001d40045c40c406403035281c8540449140c21410720040c1040391040720b43d8000520036981a0307003110040e001c0082040010001040801c800000352420b940b0b011000580d6520700031030540300004d56080007500340c006d1400000030721400c2c04200565203e9a1001d128110010001a00306c0b28110350030384824804402c071468440f402c032035040322950b015000144040015818190030b100c0b40d40381c800103070f4440f000c21015092596110005184070b00b0207022039410984058800c030300051040744405c1d40300e120402170241a40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259587374 1250 259586124 259586137
    0x9090711010b040c0e0a0617130812040320030309120d0b0a03031101050609070507110f0a080304030623061203070c0303030509161a09060903030d091401180305090303 74
    0x4100b0802c13501e10307201c01342901090041c010321500c00d442d400138200d07004019103520b600c080314000c403030790b5504100303c0001d203401101645c81900a000e9051074500c120340c03603409540291125007200120b040d65100d00b01080c4080b80ca01e40051082c440c20010003e051500d00400ca520580c0354240001030000803c00301c0300e000e60101c0c20090000515411068007802d148402c1c0017888030b80d0b11030052001589003518600c0009204002c884007040e15084100c20380303980104205505085100064620030143d0092899900001020010031080d4810300c1c049110900e01c00032000c420381d10071891410000c00490042c1210300126030f0b600b10500c01c07030f000036500890400c640c580742e0800600415080715a8041442190000400840c00c40112012540a2078000c0d00302c000d000d296880c103411115855800907400c3c8140c1040e81c1d41407029000c000d4102c03000184030344c2c050a001c15541010b100300c8140340d15115500e580c4c000000703624031905400d400d113540d0704c0b000c007004a40ba40c032912 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259588624 1250 259587374 259587379
    0x424110615130f0e0f07050a0e150a06050c0f06011a0c0f031909050d2609060403060f050f090c0f01051903060f08010c0503010509042a0e0c09090711010b 68
    0x260240d040303c420303803081c41480c020404a45961180c424a255500c0150140c80d5000700c108a040010350307840c0408c82e03445003030541d11410303507107801c4042203900f0940c0d0040008204045078200048400300161215810444010a1554940070946546030070800040d0100d5000103005020503101f000702c501c451616404496641403030907010448036252000c031900080d58420002800d1420480e0b20f9042904001c0910388003502d400c0520315126002c509000380308040c0000307440c603991540584001c5000381e00200b07003d941546100200d600041c140c3d0302c141c01c044140100c102c00019505a4244261352040c40e44200b0700050700c0c0740c061aa03501c01e80201000e4440111603143d0895011942c1805120208a4072260981e081c1c9121a4030180051014001008549088044290024000c942200205062580d130350111800ca0300381410700e403100301d001c00070760b10789800b8550320540c4000102d040480030f00000e1181d100107440f090400c08003c071001100c032400e42c4444030a9400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259589874 1250 259588624 259588631
    0x10611070f15030e0a0602070506070503250e0d0b0108010b1207030609020f060415080c09240403050f071e060c0b1b0a210b0108010501050a0201020708042411061513 73
    0x462403c46c02035481000222664055440411b003500c1c050b000396801380c41d00155020744a10062600740a80c40e60b0345005042041d40020b4501a45034070806001d9180a01c603180519030400d03195500752001b10074207900074400140d41c2610100081100c00550360b00100c0800c0c4a42203000146e0108000d042c9140e0008000500040c00c0c1c0740360380f584403110116150740c034441d50f615152299034040c01218542041d4003006243c581080203007108201c03030401d80c00604003522900c4852030b08804000080603a03010300024010003400000410f06000701030720000e145428188000e20343c00c1c1008004200c0f43d01140481c0c0501c070059034000705441003048083c3c480b116070100505600c42c4006800c8070410250070340304495020302850b4500031041e1a11000c0741d1916004540ca90b0001020300c0440d5030074001c1100080c80840140024100b0ba50b840713011103003030015100d800d140c03202c0800c1071001c0e0700b40140840a01254042c0d0099540b10903507000030100c00400c1070b81e94181540311800c3e26 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259591124 1250 259589874 259589893
    0x20903030a0309030e01030b0a05060d090602161a060a090b120d08010501030c050f03010501110a0b0f04030806040e07090c030e070803220e0402040504030e04050708010611070f15030e 81
    0x40c5a07000f521800c1c0240e48003110040044019000c8035000c102840d0000301c3d4140c00e1119003454030080446080390000040d2102c0c05449550803a04981c2031507594088440360a400e0180c1c0c10740f055401c50b682998240c035420520f00084400c1094410004c00e0364482000007460781d01e40700032400c140001000d9558125401d5001000030b203003402910f021a107043c0d0158902c91041058480315100c000009146034240740041d00e2103d07081c4456040d03445240c03081030000c0c0c00120200d01403440c4e0980480b0070b00300b40c42c1c05000903c0c002d00c01401181303040344000300a240040c000c802c682c0c24180008422001940840140041c000460326078490024001100300d000802000900c001b20b6075500441c15603160b000703020440c3d02c14517103900481d40200700940343c180d1069401071722030f05010040c2e00020000c60241c40f4202c0b10100412184c00041103d9a00322082030030045019001c0c0038181e0034020610500c0225000d102c4103100310300047d00a0394007035807185008403102d03404c0342e03032050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259592374 1250 259591124 259591127
    0x9080d030e1b0114160c0b0a021207050a060b0a0503010c051c090302071814010b120907120809030106030b091011040f1e0905091501050a05010509090406020903030a 73
    0x807145080850b4810161030311401020000101910b800503583d450000e40c2c0d91003862901d401071154180140054004440017039000203514008082e0314014586810b103800700079040624445041c05410820048c100001d1f1011070450007203039110b0760000310754440d075020540044803a000550550b02c1d0443c4841c085402401034032203614640c0942800c03603080c00c494800d50f843d414004000d640500700a00090001d00c01d006100b245410b40061048120900f803043c50380700380d0101803034503400030b2041100c00c00e41c0005079110741c0620007090114038103040d811400c100508061325844010034404003582d020f40211005680050002510707047c551103454031101440ca100040c2460040038940281c00081524103c640c2c40300701003802c1d40740500004054a264690160030610140e001c10128003500c50980645001c80c01080b41c7c001c10113180802c4201030304414800c041c030300d4081007141c0e030200c11917202c900151014000b646413841c0c108003034011085d001b0707031500010820b4a01075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259593624 1250 259592374 259592381
    0x20a12020a0314090c061b0c0315090c0a0b090d1a04030206070f08011d041a0a05071b0506070e011b050a0b07030b033013090605090f0f060109080d03 66
    0x400c42e800110010303101c58139201d070f0b01c40300141c005410440501c1002d0407501c010047c1858182d0540c01d443c0d1000c8910006420841500300e81034284414000703020141004101900b030128007038440115641c101408901c19024403907940b40f040c145540801c080004c8103c0c4403502e032060041122050a080c40d0103900c603034044681c41c00190410300c100d42041e00c07911005040b144509050034940d20040c282000c1d007080104159004442020000002c2110240003885405008000071b054107101d00010a80510030400f02c00c0c544c0c0d800010404102c000c5041a0025200e00701040b912024000580d081181503208000901314030001d101409800724800c001c041c0f0810700c542095440c40401da04462040c650640c241c0d1000e100c0c001e5031003000810801d1500c007040d00e07030700c0103010a01140d8158040c0120006410384c00d8404c100c4d203c16401040090601200c080c11035280c011104a510000180a400c0c50000e01c000705080d40d000d6201040034155000a4821080704c684014024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259594874 1250 259593624 259593641
    0x210a06020f07050d0807080112230705100c080f1e0a0c12030612030f050f131404050403050a080a0209060307030e0d110705090a061e030b0601050319020a12020a03 72
    0x1980212a00307281342c01d20844250340304120399100c0007216400e2224000a0309403e48048a160700f0b80c1d480b20a2921342c501020391f0030301c00745c80240307500ca0400080c0234840110398254024080c403107940c100010080820303180b10b07911265829450380701440c804a1150000b080c02c2c0d1002074001007850034103038172005800707140e400341640c2c0d0b0301400807e800b20700311041c4c1d20074041100359408210001030700c2240046070101d060f281c0070381400c0c03510b07150b00c00a500c243c0c09108a0a0301d40d4080254049802c0c1740503050324101d90400c02840c003510080e15030322898082e802007001100000320054465415210003da0107001551289080da4000d07000f030260b080382111600c04e82c010616051b20880110344109442006000504d01e01030038440d0703444001e88003e402907240e2401203901c131030b141c00f10015440c02040c1d00c0e01707043c5176041101800c5009803905041003010010002103900b01d001041c00310070748510060761080e00c000d003142d018070300141c00310702c540c000a01a800258544c0000d1348 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259596124 1250 259594874 259594883
    0xc0303010e0f0105090c0d24080601080a030509091e010311090a0c02030427090807020a08011109060714060f100806130303020c07080601230f210a06020f07 69
    0x2080c2c503100c2140303400300404d101d00c0c2e40c880175290000d001c2c01046400b80c4161034034a0701c00701c0c000d06e1101050700b445902c800c403220380c0c0a03800d1040000d07560030009a401402c1d41005018041c0c240d4070b0041082c13164600b80740c0902ea0f080042170b403481110079041c104411b8260102020b5031245005d102c0d136400c20342c01c5c0c1d10030090303807012480e007640707600c9403200c0d04034550019450300c0d16015403500c17400c1039250348009800803251250282c1c0114001d8600c42c0c3d100341e00055685081d4410000b0340d140d070350003103041c0e681740014804070291080201d4070700c00e4040303034001e46401c0b141c40c00c00e60b28049402c010205000700814030000014550005005134090500b45403480c1d103911100350740b80800c592880c030758000f034a041d502003030203030780284a441800d105580855840f2541d10f440c16500381d00540b564208844c5800c1d20300310390b40c1c2401c850082103034941c51250300300000645046600d40c1011078911540c0e07803141d00700410843c50458590001d415500c3d0f43e000e20303445800307800403032040d0b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259597374 1250 259596124 259596149
    0x4051002030408010f0516110a030e0f03060901020306040e03120402190816090b1012020705390f0904140715030605120a0308010e0a090f0f0515010605040e09030d020c030301 77
    0x61a9501440210052320400ea004158440c07840c0c40403070304940d9920302250401800c90b5009100c0c8c405020b004c0c410321071030002507643d003040b03024082182e982c0d0030380e00c2013038205110ba081c401e00c2a421392071f0010380440d829480000c260320903042d401603035401003003039200e401d2000008048001034601115030380c2e03504024008864091000340c8028031010b0700021070f5000e03600031401e0329a02400030b8500032000c0b1140081823022420710b407001e5035480c40c044009496444056809540d00214900080e02c40e42011180240483d8040d034001e40001c6c25070711202514070b031070740080090700c0051144600414145205610240007014207000c1d160180e08125400402c2c1000080c0c812145a816a43d1001c103a280252052501e40f02170200c0d030b4155281c1c0c0012010482030904446007900880240300326034014030307010b031404506041d58803d107803a003801000f00c00c0d017060985e0110742d0405040f031180e45e11845100c0c154816200045100da01c02703c0c00849030100000918140c1da006161300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259598624 1250 259597374 259597411
    0x90a03080c0406050405010c050a0c122a03020103050405010902090c0903060117061b04050901030c261c0311030f01030c060503100306111c0c0f0309050304051002030408010f05 78
    0x5000c0d4400c43c0582804150b0410003086294800e4040320b00082c000e8081d6120368080740d9131104c080180b5404144502400d6240e0014010a00302d03440140080c644c1e14508026440443c680c4440b6512029040c144e4030310000e0b0070b0040a40003e40403036030007000c0c44400c0c03030f041044500c1c82d04200b00d0140207110301c038004900032440c0c0b206001d04803101d030000d1040e607850070b120400320580d038545022044414400010340392030340c1c2c641c0343c040c3d03104940c0120000c1c01d1440185c8016101c120a03200a55020040d5038a6070703003c0b0702c2c180c00e10b02420f00180c200003202401e502601c3c1846800400500000411a100200d081010305907803090428060710303035591030201c030180425200c800c448041c0001c2040085c01c0e0794000301d000e1034180d5146080c02c85099040c52400f2a0200ba141142d480d101c10301851584040c0100d84034415050400200d29241c07501c50b074078003841c05080c0c020036869500300707005802001a24000c7c9200320080c85100010704501c03024000a64a51207081d041c003115 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259599874 1250 259598624 259598641
    0xc11120301080c01081b0702060403080406030b04140f04031d03030f0c0d020a050309132a121a0603040c03050607030903021b220204120305210c0a0c060f05090a0308 73
    0x2c4c140a40e40700078030031028214107506c0300000c3c1c0c0f0601080740d006d8010000000003507420f8000c0e000401c05601c0019181602c5014041994034020404d8100300079501080060a0000b40b00d41d00240c0510303102c0007c0300038042d40640c031106e00b01010360520000ca45c0d0155801721318010101c0c02c91880c140c1d003c1403c2a02c040c0c0ea10a04944020250780061195401c1804d00c1c0c2e41c100c80000440101040c20f208812150750400601e20800300c1c0b440c2c51250284141d40c00031501c4032818902c540400c00703000c403c181d92030520706c9001024071070b560001c0030605110b00d50390020065070700101500c89500380510081c0c02081c00300c3e0220098041d08030503803140049a2840300c404c0c440644005070380b254266101401d0301855010400882d424000071510040c5c03d43ca14207001e1081d16915a01c1084e030031681c1911400211115241c180380040104580d84202504c00801301810100340510341460185c025103c0d1041584840c0d28000406c045400b0004074811060b01a8848810325154041ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259601124 1250 259599874 259599887
    0x2d0e03070f090b040b030102090315070306210203010614010c110d170d050105030a0312050604110a03231003030f0903150207110409081b031218060108010219030c11120301080c01 79
    0x60741d9141d0081c00340300bc00201c50b88042a071081c200d190001d102c585036542c600c04403e41807502104080d4001800701181001d00c0361802400050650035103822607880001c1180c1a45000203044001005480701e041d15a40103118070750750f20100310240c9481c0e8448000c0c070740d00118040e016141c20200001214103000c941d4880c5aa05541c0c3c1c0296000c01040100161901414003500b02e41e441440070803403440d58005e48986421650701050a0420000050192800c12564403440950500f4408002400d5035610f0481c0d6160070303c0c110b100c0c842e0b4010740d14041990700250207421440b44c851000c841c9a4020048544504256440c0404103230600c000c0314120200103003508010066480c90080070001c06100c0300188040f0b910380005001400d101c2d08041e540154a101041d40e200c0e4171040c184841405070000c2e000850601104d011520018480111204241681c8023075201078a486100410112004141150055095822204401d60092044580c24003961244603080e40c8183c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259602374 1250 259601124 259601137
    0x110f031f030f0b06030a0c0b13093c060603150803120411030c03010e010204030c1a040303080601050c1c180b0d02031e0f0103032d0e03070f090b040b030102 69
    0x400b481c01c841d550340c0350441d460142040e540f40c403803c030000002808041442e0003410201894030740f654080d035a10005110580c0011552500b0700b07100d2000080710b02c0c00c1c490307106241c0e01c81e552803031800007401140303c05450710350b60418100712001c039038641c0641101e540c0c098140500c0d210160340b05c0d00c003620b80c0030790343e52156110b0540011501085c1c4603642c00b0481c00c00242616215914000064212400181424100d94011804105000294200354002c00242c0301001c0701520510005075513100da03000040c140403459012070100d91055003520100c1e84800d040302c1d180340010720304504283c1120020000030307848a010301451908070071628116081c400d00c1a007004216010389010303410041000c0c1d10f001d40701c01c1401000032020341e030070300032420303000c0150165045082c0180a002540c13514915101306032443c60892070f6450003001d00700003e25094050032201c070006820300791264030500c901090000d01003036101155102801307854085804126010f014410316082c1d00840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259603624 1250 259602374 259602383
    0x40e040b0f0c04260f100e0601080106080d0518090403020604110105091003051b041e080a0b0708040c0503060a020c19022202070204050709170601140112110f031f03 73
    0xc040b0740c03554000072500310070303e41090384c10f82c0e01e240c9154225510700048030b038480580755100c1404501c1c0000910076076000d8407c4200038000e0508000501d0340e20908101d180017089400150b846403421362981404604e100108010718070700709410000e6a90f0300544041e21440e121030f0300724030198024030480340e22010103041132042c0d45000909400030203004003c000d00e5000c1d41c4080640344d04840040c0003508020350070030010301842c401d5082c80354041d000301c0c402c2d9003d00245c0011034600303210690b01c04000d14200170b255440303260400d48076000d42d124580600c108014461801c000345c010302200c0210070125000d00380b14a4016100c0454a20040d405c4580c5e5201030252000a204502200c0103100c4c01601d40b0f11560f000c00c04a6000b01d40b54800a41e00d500d051098a181650506009a001c00100265418007078408426420742007100d040c841035903c00d003103a0400d90044080d080c11205219210788045402d030943d03500072218041404003040034030402401e100c0001c0706a80e00b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259604874 1250 259603624 259603649
    0x1e1a06030c0d061503030c0c080102070c0302100201180b090f07053709020310120221161401110a08160c08010e01060501080c09030c040203040602040e040b0f0c04 72
    0x941c00340801d100d4042003d40c0c03910740381c41e9520041d500541d080310085110b962242c550b41180d05104c881d80c2140c5e0451400f69004014440100c0c000307030211426a60100c5500c44540034005003640180003441e100316006d001240304100713200a908805110301c0c1c0754000e841406c100075950710f454019a020b403940c041400301010788007035500507400e04501200e1400100a11060300d6090600c45d4541c440f9a10075000420002100c0340d041d010340082c40010340d1904124807560004800d41d0019642421801b00314800c50b0200004100d00401c1e0705980480320f04c0d1a8480703056043d0f54014090301c074040b491100084000200c00151683c807a03400424840c10480d02807040a5001c0c501c2c030040d00c00d0643c041000c24000300a1007100d4100c0040b80001882c18503041c000340803c00c0040c96604005030920030890030fa100424110005070701110010703625034492600f40020701550308084410f00d008801c1100f0014038031907503070141c0b00c1070303104038000c3e41d80340507520a5120724011a10109035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259606124 1250 259604874 259604893
    0x40b03060c0706090f0c1401050304110d0303060902070f02150304030f030b01051c0516031a010c0204020f030405030d0b030303160e181003020109090204050303031801091e1a0603 79
    0x142000c2c080d86881a980899204100d4442c0d030200700706400183c94880c2c89500400c0101ea85e4005000100707002c1c00c00c54250302c1d25440c0c40c1694181240241d000c0d15031035601340100f500c01d50040c40501110306045440d280b06040070b00c40946040780890046640381403001140c1001e0707090341e2040390315544090300309411030400c4016211804845040c4501841651000c000b1060550401c46040c14005110303d880c1141c0010008648c1403a41414501840c0342a45030311030504070031091003802c1001c0f8441e000c1c030100c0d000744100c01408102500101c01d11040080100061006020701201440340c0c00300310342050344903c01900d031403442800500801d000c05000300b13040ea04401c001001d840000a0f42000d40241903012164164000070b1079038240119a045110320000d01507400046080c01d003000080795691001030030072405000c0c00c80c1400200c44094221300c01036588030380181091b40703007020680900c03680d100040380e190040f100120764610401c22514842c0ca0010b004080f44c42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259607374 1250 259606124 259606141
    0x120b0609060705030d110a0e0a03021509011404090c23030103030804051e01200301080601060c0212010908040e09030307020a0b070e0312120106050408030d023108010b040b0306 78
    0x184142c074100ca09000034072850680942501c0340340640d04010850540c0c50807600c00040202240300081c901c500c64420080c40941ca0341e05c1881500d180302c2ca40c4035500e040d03400050320000100e80500b00c3c003150000e008507444030030f5040709170205442c0d20340f001d207105801e1030b210906008a0302010780440c14001000440c4c0704454443d0840c3c050303015a50f1442c001c940302c0d51842000d00040c1c4a580d10f590b500032905040d1072080c0914510101e609007194180b6414584503030049c440c540400c020720800600355502e00d5941d140c038004000007088000b500b858040c40075001407251442003a40440043c40c2d003000481143d10070500e0740c0c00b60410002030307654181740181c0a840107040010035003a0380803070b8608100914096008450803a201c14210118102e00302d0140c00113030801100f44400c1001034800000e4482e90a982400035854201e200014080c1c042950100703000000040315409800044490090903104050020304c40d1483c03803070510064401d203600c0d00360582c3c0080c0000e410392 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259608624 1250 259607374 259607377
    0x3071704030516050c0a120f0605060a0509010e0a0b0d120807120903020a0b06030a1205070213110a030e011104180216051e1f1505150a120b060906 65
    0x500c40c0c208242048981d188219002c04501d00440b21648940e0aa205c5403a03c03990074401800450446005400c50782c0e1004000d1410703407802000c407a190b2003c68080e51354a206000030301009843d0384460340e50b0341c0055011003401d5030442101841e01c500040076040c541101c550941d00450651801e94002d1801c07100041d000744418100114000072030420390142c0200501030340250b00030109411141480c01100901900b1031b4400e6000103c46000541c0500c18420388a4080c1051900c07140140003040a46422032450400a07140580c2e00030303225280f0000d040c2c0c410300b6070b80030403041c01c50442a40c04c03104209022200044240000c01103120b9118454441c0798542c40c2c05030401095665846003110511b8044600d90055080c8540081c030001ba01e02c1700003640401001604418601a00543d0807544100003031903c42d003800d0406446080d0303c0740201800f80040f0207080900340c102d50550018402280040c80e0350a03e4041b4070400c2c020718044107002401d15140c21000c40410405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259609874 1250 259608624 259608631
    0x9061e101e0503030a090311040b310203180c040c020309040b030705090405030703180e07031d070803130602030910030902010c05030f07020a0b03150609030109050616020d05030717 80
    0x2107044050000c195501c080c005040d80800d035840e82d1030307040d00754541075400c4000020024041c0746801c004205035a19001d0720120314003090740d107201d500ca04040c000d8980341c0646030140018000024020320b140301710380e60071500301400140c6400030340340300c02c02081e90311917030b90030005034010311a0144528103584104491640181240c1486a17030b0310206038595801c44050711903400100f482c100b403541102d01075920741401a20011181c4c03c141e5891450302e0058024401c042d40c0d01d210201c900c1d0400c80700140320050200b00c0e14070f170383d803000b00d0380d41c9900421404001c03030750703100002521600010585055000003004458508400383c4102c00600d0361036016810843c190103003c000c03034810701c001d1514040c0d10900540d1280b00b801403109100c0b440c0d0200c84c0c06903007042003080d180342006070006c6504088030180e5070740710742a0000740580002d00c009841d0f03008500c140041220401c0c883c5180100c19000d440d09810741000581c0d440c00b04890110118643c00c10050700002c0f08040c0560 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259611124 1250 259609874 259609919
    0xd09170a0606030b0603160b030c07080706051311100e09090111180a150818072616030206030a020f040b0f09090a060b12100e09061e10 60
    0x104115900da500542c2d200c0d5200f6580c2025800500c0f04d0350070b0600680e080440c45801c10f130421898203103500300310710004042804290001c200d60042009182c22212640c0e0405018441401d100703200c002000e05034103007144c0c0341c40080892412030800c00354100600c0142c0d1240b1100c0b41581c01481104a001030000150755610704103806c85000700c1019004140c0d098444060040200e000e104510505421291505881079120540d0035440400303d50701c841c007901030410200e980d4a2051610080da00034007050981042c80c402c014248810481101c1101b40444550310300803140c80400302110301019400040410006902034990740003848015150011589002eaa07070560303682d0364000304004100e9000c0010031041c0c919140003615089a080d55080240a00c1c1c001420040d120f45510060301d0600e440c0050032800380f4261002c01850015000900b511b08644280d84a5030100c0300ca140480d900680301c0d020a0007824036a00c515881e42100300300d0340c2400e541000402c2009079009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259612374 1250 259611124 259611133
    0xd0e03120306180414070902030f01090207030e090a0b01140a0903020d1b030803010810051612110f090a0b0c0d0309050c1809071e0b09010203070606150e01020d0917 73
    0x108229060f110303151060b40544407101448035007684030360819500303504c44c40341c150040c424004014803000c00141110007608005a0343c040d149400e9680d0041110341070b80c018901002c01003c0149a0440701c80c00703e00742c0e104015441c009410780d41c1401b9180725000003400407502403005041c052001d1110341e000c1c4c48500f40c2e90100452040340107045800403144040d0210040081c1401000303000b0900381342440502030b500d402248501d000c40b03100307c41c4003002080841c0007580240b0358400c0c0307040440c100d40c40c2d0b135403003c0c469652520707804280c24500070442d0701d0001680303044110903161000c40b005d000d000401c14442040340034041d003103000e882c82c0c041e031003100e0708a40d030701c65507504100c5403a9200134240c5089420641000045d030b2108e020000c103644070030300200c00700103130006032400a24050348402000c40101d00d180601c0314010b00040c904400404e400140f000c1380398100c070842c2e4411800c00714000c01262034030410342c211008035107110000d0040b0310703414251084c101092030494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259613624 1250 259612374 259612399
    0x11d0a03080c120f180d0803040501141608040b070306090f15060c032c0d0b060f01020706020a0b1512030d0b0d0f06110d02120a050f0c03010e0709090c030b01020d0e03120306 77
    0x41c8a0b0323441a202151569500d0001c0006508403031301250b48003814180c01c00f01c644c020007024203007442c0200001d010000314000144c01c18081d5010a0161030403a41c100a41440705c503841e401040d110400510382d210010700050b0a920490040070040c0d456502d0b400c107075070701480c40c030700c1d40e6003c20303894100088003d16031078103031182030454100381c0c0142512865030500f40248030920303042d06116030454200c81010301019400003003102e642a4058030040d100e55480c080d00c0810b00c500070105500240702e51031580e17000d0000018201415a400b0100401a80761040040c03004030880020075650205240c200071440700d5029082c0c840400302a5403401e40d8224070241241e1207100c1440072107440005122400030030b4441d8951200781c00409514904043c5900c08032800148510f0841801c400e00140c0d400e849640c1c428002c043c0b0780c00134071000b804400003802400b00030b900d0a005102c1e0841c4000300500c9800781d00b0661a01802a114403040c1070030140c444d43c00180425044a25031121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259614874 1250 259613624 259613633
    0x611030904020c010212180d11030706060b03160906140c070b0a051b3c06070305070f0305061c0302010b09010306060f09110405011d0a03080c120f180d 67
    0x100300110140c400160303a025058264400c094005d082d00d02441d841c1395034074522481c00235420b08440e0301820107246040ba4406920300d1441a440010314003410f02d4000118184204c0c0514060742080d9420703c1f02c54403455040b51404120722400001890a0302c0f20408520014001d00b1f0b0400c0301001d8800c2d00b40c4408040c2026803128a41000080d40099442d8a0031448541c00f205400404041c02829030346114030308004c254003486514840200800e9003180704901c440184140d0766900342c500750318048201074020f101c01c40b04503000c0b42d111500b0f00c2600e403091294078414140282441d000d00784a07003603041d41c1001100110103541d07842080c8940c81c1c0d5070a00040c02140304c1d640c08100c1500340541c141d00c2003401d92141d0700b110305001c0c00900e11031150060704c094400130300c2c1500240c403446020819100c40300e440c06030000c0d454031010080c04081001031900740c071941c0031548402c01c8480090103520a01400341c010420a1001d00c1a00c586481c844010b88001010b20010100540300d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259616124 1250 259614874 259614877
    0x120e011713050d09090e070b03010b0c0f0a031706011e030203100e190e1203010311040603080304060606140c1506040b1806010807170f190f1d060c04061103090402 72
    0xc918002c61041d4000300082045c034050214441054005000b02c1071500c015400640018094000f503000085140c00564000f0801c10131105440000c5a00b08116420003803d602c0101e4110001c540280002030b080d940200e0307044a20b101c542121541400d0604001c8009401c09810801a200307030180c006031110b000c520700313405034500070044881c0c8140070902d0022100c241106c000a9041305582d64800c1e6082000c3d24116504540300c0148c4009120000380104515040203000407004014041804500d6005005881d5251100b0309456103a400c104c13003501507a11000d0465004030016540c18941501c06071304000050004140b64490500280710f8a001034440300715035560404008156030f0244003180c0000040c1012181040c12595482d42c00a00038202408480002c02160b01041c0405407200e020100344401c00500c084104180c014000221192400701c09000d00b1000c80e140200d00d15025010408646103031920701002078801d84144481c1225901050040040d603464900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259617374 1250 259616124 259616143
    0x1050304110616031e08090a080901020c1e03070e010b160f05120c010b060304020a05010809100515031e060609040305071b150c02030d0302070c08070b07120e01171305 74
    0x5ca41aa85101710103a8110f540c1641c0e0700381c1c0c1000181010720450007404100f4150a58118a07600d40d600342c4240143d1802c00f04440e150b402c21074686417103039400c010040400310390000300e05440003980d81e820321160a141c2030041500d404010880000408010607000346407500c12024240b1030840c2d611541d0801452402040c00490005603d00ca01e017400c2c171500e08020700803190141503043c19004102844646e004841c1800080404161074034010417903500a82e110350703818462894850f9101c44480f8007407d80501074442c031032001c10f843c11142e440752540c407808801803049554a00c10044400d0000d001a402d12200b0060800851000310001000c01002003000c000c0307505d42004403480c103448031014010060f4a12400300140d5001c070342d4070080c03d95840d01580310245030800a04032a071560080302640f00da0900060700c8074104001c1d1620314002e4a443e800420001c00c00c1d1110041220503074000760100207100c00d40c1040403022a00414040c056158600e059513441d0b28005400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259618624 1250 259617374 259617377
    0xe0a06050702060f010e0c030406020d1b02010209031002070b040602090a090e03090108070806090f0a02090406090c0e150406080a0905030309011b0309111c0813051503060105030411061603 83
    0x2c410090242d030940984c9005103070001103822985001d030500602c038003000c0c1005110580004d1600303407000440d0001c010914818050300301184604001034003d611014a19000703008203c4041076034081031003070351032580d00400359100e44d6589980d0342c4001c1d804681a240e010360140f1012407035810364841d501a00d512480207541d5502d50500141841b03500620107020844400c0030031100d501c039480ba07641c10542480e1020190340314000b01c0c0e0003a0107a140c140c3d400600d41080001c1d41b8071150080c40d0383e000d2175103510003c140a02e05020076003502036441400141c0801c41048200d100c1c81c000b9030712031820b610006d00603d2581d80c0d10300b1a40103581001889e0345404144290076000a4038180c002c40d1400c081000015550760080b41d500411282c91141681d01058031201119841007a4400c0d1320442080ea1034010346000484940c2e1801481d0041c03e01c2d600044903203440b10104d030302a0320140c51350760542c2c0c0c3e5652a10551118400c2554005800340004520b000c40607003c2000288a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259619874 1250 259618624 259618633
    0x103150f0f050d2109050d05031c0203240418110102120c0d0e030c100f0e100504030206131806060e102723101d040e0a06050702 57
    0x501040d10140d08198100b284120038248a074800130341440c421200f0a0304403507003500c2d40452800c059038520300c40d51003a41c000c43c0c404102d0081207804002008580d10003d00c202c0d1280c41840d011040780030480e01041ca030a0805100e14a03100e1081f124084401c00500100b090409401d1142c0d02d20401c003004c6842d18041c6050a030a50780600000c0801414a0b0107141014100c001a60f611984200c000382071121015100419890030f2080d50030104007d003105006030204440140700c9010b030650103000402540b4209460f14000e041c24891101c0b6544950500d0300b103800b0801c2a0f40321124011601e0410b170400260750080000016149c02c0002000807060b1800750080c0c200700000000c0f622420118580d60500c541050002600248514040c022080c90180300325074010141c002841011610380c0980c1c0c2950b440c550251446015601c0103400c01c84c0c620107803400301c4e0801030140000c81114080c036079820305034049264100407038103c88070303a4110b4955030102c82c0c00340c1d50100113800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259621124 1250 259619874 259619879
    0x51204060c020414071b030908030a0e01090f0501020703080a2d0207090504150216140706090605120604181a0601030501080f06132f0910080304140103150f 69
    0x10300b8030850105142d03007a0892685d03d09100002c0a480d107481490101c0300c1e050021105152088074010040d1090104980e44c03403140600260410880983d031600042c41c007000401ca96105030006000c544042e002440005d046950341c0c032907500001c0c1050108081140c0400c0151120f810040c0740c169289c084510151900c2da0084c14a0035940004d202c0c1400d1030300340300001d0301a89000d0503605a01000584841c050707042c0600300c01c04d07940068600a80d015908003010408150401100e5650b1100c0703444075510074051710140500341e06000c9002c02d40d00024000d0900c3d4001c0e00004800300020390b000421965505003440c1065a040d220410100401c840d135601403140601402c0780e00000d1400250754460150799140041072108d420b07240320a904200034012452404403a19521071045140201c49041142c00100800c2446042800d0100303c40d4502c240d07407170080e9160301c000b8510b010f050440b00e4a408030400d4900f810140d80b501ca440907035000c01201d60113000e6078400f0f840302d42d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259622374 1250 259621124 259621129
    0x7030e060d060e07020f0c060304031412070207091107030806060d0f050a11070807120c1502070b1f051512070f0e01091202091b030112030207080610060c051204060c02 74
    0x518044c150350165010014818000584002e400300845100395641d80e11301c1c048404484041d6290a000b00c0801c410311151000462a032154400e0703400c44a5180d6548418000c0d60900e964841a41404120680100344145043c03540003001819141c0380047c81640d4404a41c0b1080400006035640d40910000c1080c42c003c5485000030704000d98185a1192150392407480391aa0003000c2d00c0510a41341c541da4003035032801203403541181c00e2070004810b207501d0f1800307503022050442e07204814074002500e40a0b00003401012900c2d6010306500e081c1000280311905804005d04594400240f01000c012080151828460f2805540740107003400d042d840a00311940840c0500d0522407040307001d101c40c01a11011262080d011100502e0030744503101c041d00c1c070007200c50b00c3e2074841c58000000300c1ca01d50244191032030701c0d10941c00c0b111020b96480280341c485000340c6007a4204002c01400300f02c5603110719400b640240c068429101d4101c0740211510995021703070b0210002c145504594010b61 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259623624 1250 259622374 259622399
    0xc1119021206090303070f210606081003050303011418070e030d0804150c0315090c27060503060616121d0a030201030c0c0506010b0421051207030e060d06 68
    0x2035541c0c40102540c2c180000f1a5441e8000104540c04020b141121110001d108113007800c00000c7d190003491102d121440d020020306010300940d000f02d00d2040204550340c680300260812290441c003e10304503424585801050a44041d40f540d00c6503401c60f4200c2038070004600c480c025007164590172030040104003414185815510305500303005051040001007542040c24185844c403551000610000c14282a07008007202268000000300fa000085014003603170344041c0d44076141d501c03403c4800e42201001d40516102c5845000030303401e0a0000c1000c90700442c095904160300030500c600701210290346801c541840c1800362051450a10a9040603421560f4131025001d100441c0d0141031080c4007090740301c0d406210003810036941d00d24039401180728a17500c449030740c1d07c0b01c1544d20559403102c0080342504240202105464a12400c42d0a0100d0b2111440100da011024016020103040c0303219494000e06815818070000381038002d6143d60301002860390240310702c030000e115030601007014030b034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259624874 1250 259623624 259623649
    0x601080403080f062805040609020405010509090a0209060d0605090a052205101103090d0206011805060a0902030702060414121b03090907120b03010902090a0c111902 73
    0x1405040014440440d81c4108181c1d880b08800650340d21940b502e401150a8043d22910522805201005d0920601244151030100c3c2e000300c9040c41499100d80321382e01203215501c16180429000c00100c211400d140e240d00ea80032089400045c01c010b02c8501142441d8000c0182d01c1d900d69640c0c1c0280517915000c00301d150003d0f00b41d4030411140c81c0c40c100030149141e03103a4800b411300100c2c0017840c003041707010800030640040c0801e0a2000501c1d0b90031a1109800643f4038085c0b03800303410f81c014006407000801c03e040f100c1e0148108a044031032908080105006001203410200890b000300e84e1401d540000e500071030a6070f0040c0064034050405041041445c40008403940010420100485011090f0744034004100c440000d400d40c0c1c0a0414174510403440d5582d0050580301c108104180c1010915030400e00185041c88140d071188101402c035841d000000b0b5105070800f002c1041d800040e800215510f6240c100030207080603410410340781881e09810520701d01c4448220340c0c11404c024081604d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259626124 1250 259624874 259624877
    0x6210501181104050a2705061f050904080904060b040e0a0b010905060a021c020a0210020f0703060b010c05070b041403030f030703200a09030311191509150b03060601 73
    0x401041e9556112036444402d20107500c80d030380b60320104807440480d41c41071800d490382c81805405200d02180745c4144402e019026a01c0e400b80707a0015030301c0f0000c440721003040820300c0f0300031304405c0c2002c0c00c00c41c2d1484094420340746444240411784c3c80d5201c13071160340e014007042e1032825111880e040c400044500d00422148006081c07040500083e60040c100c44141d071400c580e802e03196000258200d00c2c0441d04404121880000030410f4030341600440e19048450003615010028080218117036601d5410a03810885036004034003c00204560b1741c440c100341c581c1494101d01c000520344882d4a06a0ba6401043c05104001020050701240015400068074142c01440c101080c484001d00540801001c1c4800e154403070884003e00406501e140291144c1008401e4495046100081082d40240070840107d44c0c2c0300b60b40040e00b04002040030281031030882034405028150b49030950000c030102000342c01c0f500c414914002841e000c1480704004400d000001c0c0c154154400c2500d00540548980d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259627374 1250 259626124 259626161
    0x509060f0108060906010302070f120e031c05070201030e0114150a0e0f040804210507090513020d03031d0312060109060903121b050c0117060303071506210501 70
    0x2203003a40c1014010754401c504a42c422156a030302d40040e400b0740f103032540060074001da5030158010803200700c00e640c3c01c80d038007035480810941982c01415070b2108000641e6002c48801030064201ca803180c0004c005039803041c907001c03901928880c103244c00d403560700c403080d46100985010841da4034001e41c0c00c0740c2d10303100850f128a500d518020f6496440080940986451206e4034000390900c060030040390001c1c100809404c40c00f030f01c0c4000c1041c040c0740700c800450300c1d80603c000028501c24103000e0280560045210190241e047c2c1d4200060403144800032000e05072074207000c45464154021041c0c48a8000c0d001d16580c0b000c001040801c0580180010306200400c82c060144a500010010a680c0e0040014261031910350302950b05c420303811025140103007218418400c0081c04101d5060200b401c1c3c030343c8100307030070806504008108211641231f01a48117002800101d103030b891f0000c5000800d0b400c001002a2224800b05842287d032103400c00410491403d002003107401d00c41e035219801100d4285 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259628624 1250 259627374 259627399
    0x601050f0904020f21010f0e2701140c040503061e0705070c030209280b0102030a0c1b091b02010507051801050912070f090209062209020309030301050906 68
    0x403070107480340640c06240e010031180d400c951500202c0c0c03800b460b0a814110481d024a13000403114009001d50150a4048000028512034203410076019900706140d00968403007580803440c044880c1c0341030600c55920390008012240d4001001400b03440b000421aa540d410700d4185440c1034009002e0701d602030301c0086203402c40c0440c0150181c010780685405951001e250a0804003803a80350800b0354440806018003c044031140b041c1e90141e2a890901c503481d060354000c003800c40f03060f5030313075a80076030403c000c1c19540a11a200041c1c2d000c2c418121040d90481c1c0c650101c101c4121900040383d240e54441e000455503000034411122510759200a0100c0e29001e1030045c05070017181075900c03464108900300c1405a01030420380769540300180c408034850041da0090b41d034980b0240b054000301600c44d84045140f4030580215403d03140701410151400c4030452140242607280ca50001007440032503c0403440c6615800250700a1420380021900ca50500041110004015146034403070f0b45031090302c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259629874 1250 259628624 259628647
    0x207050103270308190f05010f0603020903120c0106170a030216060c082107090608060613030b04060b0607150b01052106210303041205040305030d050603011104120506060105 77
    0x300001d0943c507203030642e1141c50354103800c04080c2c8282d0090407494103200ca001e00552450380810704031003044004055155403541e069049102e808029070301038009151079045820b420004042c108030380d0b400010b241d0b54035070241d28070311107001248250340c0041e140c44041c5541040014102c211404070812041c1c51302c01c4c05440c140f010380c0014102180810b5041c0e100c0000c402100c00e01e1035002c080011482e000368000c3c0140624090440441d1048002c5031b2141403200a607815640860440c0d0300e40c41c2103440341c3c05401c0004008450698407003500f21003d449420190484038403902c909440c140c8000b204805440002003540c2c1008401c0c40940c400c1c0c214103200d40b40710050260001d2803922070030082040b004081850804c184002e40d054401c00134000b0046200714041d000c25500e14240c003104039001d01ca0361001a10541c003e00c011204510f0541c4041d400003001000000c1c090440d070140160b41e0415400b104031000c1a50280040c0700060100c01d0b840f040901e002031400544022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259631124 1250 259629874 259629941
    0x7231f080901090b01060c05120a0f051602150d050c0a0c060c020a020616060e060c1b071208030a05090105160309030504240207080c0123090d030207050103 69
    0x500200900e1101007014150207602c108400c58100348107080542e10b600024000075049130301191903106418940b104140340c1c03802d42d01d000d0314943e20500c02e90a504001c9805420105401031065421502480144e0b42d002d68203100d03070554050103489554510b0224203e0340c00800950604504205a217040359201550507031003644000d00103481c4288190881c03070700304464070094120b400000c9144012146107050001e0910801040c0460726015041c0e40d2651820344a8100c23984061081c4040b45904542e85901600d900d022510790303503590200f0a0941d174000a050360b4000002091029551550140070342c402c5e1808005e000038203100ba030011009070790304400410150344008000406104904444c001e0107a03000001103800121300c1480d22180d43d890703400162180e2540007480c203c01051005903189c1c141c43d001c100300005d481290f014088014101141c043c10411a0007950b5400303442c49659002c0c0d070091000e0390a20001400321035200300301c200800c10900301510502034011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259632374 1250 259631124 259631179
    0x3050c0d06021201140f0109050d03200633090c0901140309030d1b020d0503070504091409010c05040e06060a03110417060a0e0303270723 61
    0x5032141114642810908001e020b80d225011460341418000071301d80f02c00c1d990140304281d044400e040e10b0a0428019295084288a02e91b00a00f02080ca040400d010304c0810251400440b550100d240580c0142070501d60122031070942502c1c40740210003c80940582000d42808c5180749150103101d410014412100003400c848241800041c25a02640300b181000c0c0310346080030f8801d07200d0400da07200d10380341e0308128951091640b5001041048010b44299504d0b041d0041d00a4200d404000608035002e03400204498180482000002004401d80c40380c444048035801c890181810a00030050a43c7c040180e8041008070031b0200b0310810303c035540c901c1d401000c100d50031030b0b5802c440d03081030700506031014483c003100c0b50210b400a070b821103104140100c003408500341d4045a540440352812500016115040356005100184400c100801c4101d41050301418114042c50000c00b003d160000380d8000011080070500c41b41d0101c0403031400e2450444007100d188150760810020900e106007103a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259633624 1250 259632374 259632379
    0x102030d110f0a0c02040c0f140306030c0a150305010e060105180a05060f070c230f0d080a0f0e0d0809130e0d05073f02030408010c0206071803050c 65
    0x10010050500c503500c1c21120b004003200d01990700c900da60b00000e4804007110900340d01a81c00c101d009916988112040702e40001c4548400b0142040d805003d41c0c1c40d000101255094030450f85031b01c00b6035607000f40d20801008041e2258403100e15041000b03059910603488503080340d20710000d010f6241c2c0c000098505443c20b4001c003003a9103520300001800f510f02940b03d1504400009204121461118000c01880d801a40c100c20082c3e982c6101c00342c103442c401012100003000c5c3c0f4180807146001c8102e0003444030000d000c007001d02d459890300c584030352101d01da10021a02c1c1c040e09071207035504108114280d503021140c0000e80b082580307640001d03115035928944180107400d45180c04a8140d03001e4890140410102e0b581c80c0c5840314060000d80c404030702038400058010340303520304c0c0b011004942158000118214039103201000541c0d000505881c102c0298003042c031002c03030b051401348900000881954020501801c001201400c004920448070301600e114402c203001051001444181c0a180bd = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259634874 1250 259633624 259633631
    0x11180604020f1603030902010f0203070b06040e0c031b1809060a0509120d0b090a0b0310020c1f0c0e0312090f0d0204020304110109091505130615020703060f0b0102030d 74
    0x2000702541c981c2c800c01c1501000100c814015800345a85031b800800c0c0240b0070723268900d81107210b08090ba50381c002c1d610f00030105a400c0e40051414201504100d000c0c0204504640707405181c800020b061a044c441d0102440310f04072070703d031000d103842c0600c03003070b15104094072046a050040c100c07a25150700501d4503025030740340c0000c61020007040014580b0f0480003e03d86842d0300e01d251415020b0b00c07910ba4094822004080032490034401d520600301c1402e0028010492241c1c01d001d640065000080355a10382e00440e61205003a2210282c3c4881d00306150700d00180d4803c4581c0003408020702429598025407110a02109450a82049505280b0101c414102003201040060700442c0c69544c000e400c00c0c0048240000c110b900300c7d035a8000c01003603d4542c910781d25115250115621610301c580f580001000400540c1014034081089240035800410784540381c420390b03080e8020800f00ca80050740811810424000c1902c81c3c0415a041e5038000d01285820350300003952070080c540500f0f07240d0f0780d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259636124 1250 259634874 259634887
    0x4060b031807030c0306020c011505131505150403140a2a03060e0d0207060f020304030201081009020c060912040302150d1b1112030115180305070902071118060402 72
    0x30200842c40086a00801a410043d142c1c9090400307900000d032203049660030030510201c4211015040010f03618050b144643d055150150800580340c00c201022a51181010109658075078100707070340c1f801c03041000311a951840c40c9409040144401c40225440e04900a4500003603200b411030081d1060900c42100700700e0500f03401a03507000407036000170a40c9280448102d100500402d0b0407070320704415003d03038500c560b950f4000d03511120b508001000507002084140019030081807c04e0b00300f17800a020002007901d80c4000b400301d81c0440d01269099120a0030000c1841c0c00700310540c402c0b0106071b805810a071071580803035031500340c0c2200b01d1000080480c1400d0b200c0305641c095039000400c490201c10f16a45001c0c050b000840820440526014404104000348040c208482c121805c00c21100620300340c40e08100c0b071519017840c010320b038604c18880001c0821010070000c1e0141034425030043e5500104c1c42c019103681c020010b680c0c001c20040406034906151008400e81c084010342e13001da550b52 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259637374 1250 259636124 259636171
    0x15050112060b070b0a0b100915020f030319060803070302070f0b0f030105220507030b192603121e010806071403070e031605090c1620040c030e0c04060b03 68
    0x111b5968800d800c20406000328810b25403103080030088410348120808503c108a0301262101030032400d0300031550040000c12450820301e40b47c94804c0318208800a512500c60140360309607444000f0903001640510020b02010400c0824032004080c4909058600f0040c0310302d401e601d010500c00c00344909a1741240004e484082171413020100d800f0201005286010640a0014203841e11402e005904c0c0f0124580418407909481d8283d0300b007614103802046c60794200a00040041d44a00b03418003084c040e12070300015500c0b03018000c2400c103940c0400320201c504945040c0b030050780101030f9a400b4100707000001e038008001341c5d0f1100803800003d40e40e0b81c032107501340c45440c0442042d58040c81410300400940080408680030344034221100308190300c0381c0b90910045c5c020504a080045d4555042000240d1988032011031f500d500510030601c613206100043c211915882001c1c00310352200c40007840b0705410301c0b8606c4c0e048412a001c1040a0900c41c100c400c40c00018900c5215404260b60b1481c280f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259638624 1250 259637374 259637381
    0x21b0103110d050708090c0117071106151e0f0d061b050c060906040201080f07140f0304020406150f0c02040e070b0706141509100915050112060b070b0a 67
    0x7004180001c942d52404001218001c0c00102c51800c00034444001181208a01207030503070b00b0700310580d82c3c2004451004c81401c0d001e4409041c0105110f54983c190b00010410700146100d224080c1e4102c845c0920030007440301d1a0400c02c0c8828944003a0010b8200a0340c41c0304800b180c25a050300c43e140304690a00d8001e0042100c45250031f102044812003000300342d809802440b141800c4800d6641c9515a500c0c815035034042910024046030500f000201c80c95040849954824094034000c0311002c410400c080a5620000e486802081c00100300800e5007494002ca00042176251201c0d40040c1d1604001844400411030b420704100322440361360159a00c98002d008260103071002d94030444d40e607001c410415400410100c030038606140c2c4001204040c034803510300c03c03041c5030114590388601600b00415040002c08010485402d01404201d4a0842c425105480740c0c03010314403007003406c050014180c482c0c02801d0340784142c20100d091165a00e0a0140d50003150f00c4040ea5459403550300d0500042e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259639874 1250 259638624 259638641
    0xa08011e0b09040b03030418060909082704090308180f0705060c070f0e0613090302101d0f0d120b0f040e070e0709050906010309030f11010b090a0c030c090303021b0103 74
    0x46c803021401040c1440c07810348a0350b84004c180010001035a9a8051205940749480c0140a005060000705c400806c1c00712803280d20340e8000344422403100a0b90000341101d000b540f05400189868003045a10310f0304d0710103c6100302c200c1004060072280980c10b20742d5235201c0e021f0940074207000b05820084000400076103020300f21080f800c03a0443c0d12280c400064201c12900c9504c2102210700c902e071108504e1041c00c030080c2d01640a86403885680c44042d0281039041d5080016020030b455000941d0018400d8401b01c010142c05401c048042400041c0030f90358080a0040151906040441656038204030121100007074502140b015071449a6501b04041070341304a00c42c1c0e091800b0080400d80c0082c010701641d60403588160b40d1340716a4011000c80b500103600070003040c0340400304d4100e58090109100b2803076041c40007084210002021a514550a84403401c0141d1a42520307580c40341c050003000d500441610782422081c0c9951030007941d03500c0d040201f2486040c07601c000551a4400e8000444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 259641124 1250 259639874 259639879
    0x1c02030105090607020d090e0604090f0605130201031a0117070c0812010315020a0c0209040c120614061c0f03051204140d020d120b0d0204110a08011e0b09040b 70
    0x96241c05002e090700e070303c0304450030801401031850040e0b035140946c0c2c9841c29581e8281e102e17025543e5070b5050000604000038141c503103442a00320440004d0a50040e1803094980ba1070441e2103005520002d81a15100b00c03e80401c0302007241c1240c003590780b24102c00032000f50750800d4001c0303860f217200a80e50341c030490b20040c140e400d00080b004461200c0648060483c1d101d40388800c55290099103581c200c0c015210386500007903051490310003501d04500c404c2e400c10b0142d002610850796610b003806e0041c07030141c0105e4480d03449000c2040c00001c150240b80e4400800e80d10555895040d548070450300e50343c40c0b0014511044042c00000380f6200d0f0302a2a03c45c00119250503290406082000c0e400360010001d15140c8030703428075003000300e00c0458141250741c1c00e901d500b03407480030702008100035210388004643c200000c0c1c0c0540c8096691801100849080c1401140c0c0e1244814401441144160070454412145610030928180c4051a1200301c8152155090301c407125540014003a01060000c0c1c0d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 259642374 1250 259641124 259641131
    0x40f0506130504110612090709060f0b0318060a0f060f050d02150702180103151406130b0405011e090603020d12031509050703150305030d0e033718051c020301 70
    0x4506d501400c00560044450310207c4400075500e110b800c094402a000d40944000048820814010280040d6030001e80c140c0c5089241180503519074a84401103e20003032181c3c5074803a9080c1800035104140c040c010001400c0c01c07503814040451060358024200900a5040900102d20211900103446132564001c240320165410380e8504000c9040c2800309880e1080c80d07031007008219000e44035542203240980740600c1503682d08002c110910242a00c50100c1a40707031020202540c0d924400c040c0039011102d12005454204282802c040f091908180007540c0b60031000e1016948541c0590119030340491041d40e0408500c800320040c014080990442030078140001c140e03000990401849000c4558040228403e0900984042c0310113100103020780e0030802c820035041c4d003a900f01c404000b0f0398508a9185ca54960640d91a050900c14509490318a42040070b45421311040400c40180c0301c0c1c076020b50b6440c214250010003048070f12500303103c3c8202031522500d180380400070780d02e250340050082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 259643624 1250 259642374 259642387
    0x8030c1306020d031406010e0909120d050a0c02030705120f16030c140d090b07050102040506040f0303020c04020708340305090306090f0717010902120309040f05061305041106 77
    0x60f5a0311010381004021a04020305a004800110071003841410140d540d003210380000e1090110451010f4040d40d5940100e290103031075104400007d00701010300032800112403808510400c211440320002a045400c204940c40200780c0000d901c24035045c5401002c0d640b1030480f0b040c64114450705032030880d407170b991a4444040c16044561710507180d026600e00c0010600000741b858030780040320030400c0841c440785010b2280c0486034018205e0746100307200042c40e0545802c00940c02d90040c1c0c0c4070b031b0801341040c0010702c00c16605004403800103005480a42c10404a0b581e024158040c0071501340742c0c07550b062000c07600304000081103440321107921801d400c0c1c403a09040003012540030070b02d107a010b8807035440420100740c00016403102400701c1d0005090712500344007140110060f0180c811503659201d5414030096a103102160b09030104500046945d1141c0c0c0c03040c40107079030302038803d6500315280a003004110307110260a580042050386001610f42d031f5034500244040d26111078940c1060012804 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 259644874 1250 259643624 259643627
    0x30b1f021006090203191503050f0d030e0105010e0c0a021606030b0f0604050904030f03061d04050c01020a0804090c050f0706020a1103071101030911041a01030605030c0d08030c1306 80
    0x325051001c0680c801d0100507240c1e03254a05030700c0151040a008000724245407a100342a900c02400032000b00b8440f249503030b907038903400e1070181c42020907407550300590326241003a9014440c0050142080f0300074002507240c141175160104000700000124a000110581120302c244000e030414007138002001d182544a2030000e004110050070702d40a448000d42039983e925190042c2c42c11604024040b084a64035a68100c0380885a00d000c00d0500d0345881c1b002c1840c1802c1c4004060844040c5030a035218078150800d00d1401035403480036410b64004800c0040801e9140b011101500d20445002c10380742c0b007950301114544a24000c0003002d40c004a1400100001c580041010340b030702e03549480034220038505039501ca20484030000d05c54691031803184107950003900400fa50501030643d41c0f14400140c2c01150070f0b20000c0c0d818100e50002104024269a010f220b1240585410350003010888611301c0030440c0c6100408000e84000e0000c000500400c071050100c40d10340824480d4050255a42c210 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 259646124 1250 259644874 259644883
    0xd140c19150302070c12030203120a050f06060c07080609030c06010b0f0d0c09090c020706110f1e01060b0403080c06011d0f09190521040e0106030b1f02 67
    0x18818400d0400e0410020040384280300082565006509203140002158040d402540080790442d105880303520006208000700c000000814000d4024543d110b25401e86170f844140018911902645840d0511820141000e500ca610100030b550080d03407140325040961030859a54031025540c0b04600411962800201c050100d0610300300488603240d880c3e10070200d03540180541201411801e010b51040004140c10480e0b02c1807481c1804031105484100050a54580401000140e842904108581035005402400700c4001802606112601c502070940b11200409006c41824a444000c41c0d0b8081c01c1d8810f9008003080030800d80c0e1955240740c4480d0301d401c5488035052a0248100000d0342c2803e9440700c0300004c80e04010241d0347e5a0304007178081c1d0040301801c1e0030107520401d840c501d1880c507854140d20a81780103e005000c1e48010f48140885000303c1d150071000c080c41408108526400d01d600d10f410b40d01b482c00c000c501c00c0d2298010a41e105040c10b0342c050010840600700206c03d40109 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 259647374 1250 259646124 259646143
    0x90a06051f080312010803041a30060a08030a0c0201081b0a090303091509030201270f1403010b0105070f080f03100501180506030703020f130308310608060d14 70
    0x7440c84c5820703a0b036a60610345901403881107c03000b4203400006c0722150801c07001444002c40d00d6440c2414401035442c10381d4440440300c1d80528400a13101408014607012440c0c20003001404011840c00454960050000c24100e4002f4144000c000c00f18180320040186425003403c900d100030740750081e0000041071104580300640c081741d1984004074131607202d40f0400d00c1540180e2030341074090f45540d00440e1440b6403403001d036100c1c10780031180181c16084010750500400345240104105818140c010300c8017244e01001d18400c0e0304d40b161840035031b600903090b160340603003001512301c450344242004600d82c03003043c4043c940540d00100700600c1149004c406025101c0a036940103a40e00402d20210f4080c81038059aa8001d50601c0029175047c480e03001030200801c10100f035270070400100803101c01e68005400c12034810700003184003c500c224105004100448078007071030002c01c080007190744454446002d490108110007001943d20740740c5c40354100c07010ba80243d2641c1d070b8106080d031960f00d5040c4d0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 259648624 1250 259647374 259647397
    0xb120c041d24010909080412140106081e03042d030807060203010f060e0904081b1f0b0a0b0a0c08121014030f06132603060103050a05090a06051f0803 66
    0x10b000214058129200380030001d54401c035810300e4242020070701d1032003824520085400b150300514102994138207020f803200420a8070010318400031f88050605034036101000240160b88140001c1101207a94080d0220202e08040011a9020148086504411540c002800e2001c002400c03104105031a40118122aa548004182c3d55180c490440c1c1855161401a45c010040d0010402013004100145042907100500c04071001c07107504510304000b81c47c1251003c06e625001031001d444118002c1c0051140c0465031f86100b141000f5541c980360050440040402a400b0718000404c4040d1080740c0070b03200845081045403400400303500c2d0781c0c445030107070840840c1a00d1641000d4240040c4011242d07049001400300390343c0341c25245182c15450a41520310890b03090b0f0550b02c074581809140544801000340719a24030b044000581598000f40c00c2038010392602c42040300c00d48010a1103d41568020710108681d12030500100444880200b18440c0c4c0e00724101c00030f148240040140700e607040d01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 259649874 1250 259648624 259648693
    0x904021002161e05090708181c08040605010e0105060706020a0201112808070e09090c060c0303100602070315020d0b310b030c0105030a0905030307120b120c041d 71
    0x360b1090000703174003054990401041c11040450030807035102d0742141a2451841c1155020720b6440d0600008010205800c0c01107a804001e20007440642d0182602500c1c03454840343c160351401c80494918071030400058801c981c041110345402c0e2003904084e00074804600c1c1c058681d00b0b8290a882c440852010100d4515012070f003894410703000321003507880703400c85d500e411141c074001d1414070521482c001c100120300c2c00341c40b290042e1640d51001600f60766a550000310b0b02c0c1d2911044042c40b41d9070503044081550320509041000410311300d034103031440c003c3c64070250b21a000c80500e0005000964142030780582c2c00d82e0010450941400031b1502c86000c007201500c407a0b00c0c0c1518030f048401a00303520340c05402694086c101035009000643c2c1020400000051204180d1507541c00e5030415101c6100003001070800580d00740132800760f0420f54a0465621002c4000742a0072503503040c14100060250380c960885d2808681c5039041240c0b402c10013001d80d40070311203100d449003032501403014802c0020311 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 259651124 1250 259649874 259649879
    0x9040b040c05160c09141815070e061306112a0f0d0c0f0f150905011103130306090209090303040b0105010e0607062a030b0904021002161e 61
    0x1001c0c01112866032941d1289407408214252008001d1141c0c4025111908919000a0300e1801c038410440f40324895801c0030311600349625440b845080c462214030096010440400da024804d18030346400008600740903120042ca200805e4150051800201d48820b51a0001401541100c1250481003120f015254905403110300d4003031801c1d42d081e424070b24856901c1c0010b0540bd00400e425405c1100070700e06500b00805079200070003013513181c12a845a65441904002c1e40e00212404000341c9004404c00354003404e02a40100041141d209080c1006001558038002c03031000e100303c40110f004000c0c03100c0300c03e03240e0070804040d14030031108a004840702400200c000c240802640c0c06581d000c0b0500d40240d103032000441e000e40480c0325096021104010900018a25210350a03c0000c4411078111054416107000c680c4046502e005c810301d8107217074110006607074118046902a5049900c3c2078802800c070000c0745444412030000340355a50b00741000c80c110710042c810388100c85082102030300c110b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 259652374 1250 259651124 259651129
    0x21b0a0b0a152403021606020a0e010c03020604110604080304060206180106080a061a1f02151b1b1f0e0d0906120b130e060114100807030b04090809040b 67
    0x11007611903010540c01d080103661011910303070050400c624061130054105080000410300d00e01041300700300c40950303000410051054029032031191584003401e041c00ea080341c6450294640d0743c02840107111200220105210b44d03560410b88014040c4c03082125196a11254065a00c00c8241c4440e12108208030021080d031105000d40c80646a90340083c148402d01d44d80c078440a40104c003000c1c4c5041b181078048810340e45070328011b141d0004004c403d07017000b18560700021f8280802680c2e5020000c15001c10000704400c0400a10903400c2010711650f621261401c0040c0e0f04500c00d0a41d0301c4502400d640c0c0807100898056007500d0482d490406c1180617400122103039154144041000032034a60345017080301030301480701098a0b144c0003801281d20303403e000026400d03485051400d1100d40e0b0341c1c1954100c0c00d00812806000d40142c003032049586c0c10820002d500003020b18040c0741002070040000b81418802d411010942c1005001032210150303e140c00c050b41d80140a04034040c038a402c0c0d0380312051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 259653624 1250 259652374 259652411
    0xe0a1b02070e060a030807140f03180f0a0e0105060a050d0513170712050703030b04060603020a180803030c090a031703040204110909040204150f03080915040e0a021b0a0b0a 76
    0x5c90b0b00c42600c91a0621a07580c9201e55042c2500c44070490081d96240d01030010700b8402401541030400044407420303850001c01c62400c1050700440c0c01003c440c5000d11000308100c203294103507441103030300300d0b100c00c503452044416104299500b011a030801c0c0a00c40b800c0003140104040601c98403e03a10400c04440c41c400d0540143d50000d8240485450000c1c0c0c110701800c000c0c642280a0726011071450b00003004101650f12990044001941c002a806441e5030b128618074411491181c4da92945450108038035a02d000142031084201400101c00000383d0f103a0041d03600441e888000c080300065400c81c5078105810460381030303001d503003008140341c204540d1a045500200008140300c2c07003500c0b07a400784001061800350200c261401d50801248402050090740000c61007044d406030b60383d0000302800035412016031403140858061009111355010340c54034590044644030b0058440a032582c0903116440d0760b4040500c07500903150400e05000305110510700c600881c0780148041c40301c0705602b4614 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 259654874 1250 259653624 259653629
    0x18060b030d180501080c0408060711060105040605030c090604140a05010302150c060403080a20090316050913060912030218011e03020c03040504060617100b03010e0a1b02070e060a 79
    0x1495030302c020500456000324030150308079201c010081d0900303407130b040a1803611400743c8201c00820380c03441000342d0082081000c1405000103883c10301218ac501800300c3e0395103015158092050984200082203503c40398019502048110f20144242c10b04410044c010b120a00080c2d01603001240b402c584800140d08695007101d201c0011f0109a4964400321409032000c2d100040c0345455260000070107440b070310134003d4811194505540c0b03c0ca2402050b1800c100c0c8111040c1c10560365800b0040d40c0c1c4c816403000d6000040030300d0301e801c076440d91504100504000344010004030101c0112000242e06a003d003c018150780700002e01c2110f95401511140c091980f1b41c14501c1545004540b0588260041c0c000e200490017104c2c2855280c00004041d103031150400c3c800164541240402294040d12160308030484c0344503500c6282c00c0110069032448140540b200d40d5001d1030101e590950380d80d0181107084c80607946030240002045000303480d45041e128411001410034040380f45860405020002c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 259656124 1250 259654874 259654907
    0xc1608100603020a09020c0f0f0c0306060d030519030b0d0b0f09060c030a0c0c0b010b0a02060711060106110a050a0813050a081903180902191e08060418060b030d 71
    0x520354600a45039001e03600007c96480c0300e00551241681c10075041001c0c0074818031b01005400360b9a4850180b610b480c80040010748280d920340032000c0400e400c0411524001794003181c003403102181d0001540542850402e05810240f40c0503200c0611050b803917610b0180c1c1030014000d160381ca131445401d947e00b0341541c050140342c03400c1010035140c00056010640d1000e06040060140b0707602d1303c2c1c1142c00340c8242c0c41040c02d50f1001480034400d84d414072086505c09510304000051600307034810141d032408140100d0701403145005004140a800300001c010099001040b55035207000383c98140046d400203c441170b007000071101c0110300c1d40760242001d000d86009c02c0040660f8203400a8804410010f02d000b40c050255120703000c40300c440b00c0b01d5010080d040007040589d0386c0c0c1c100406941203245081c40c403c1001030803801442401c0d8440000091880700380740c07010098464200040c001c0031680480c0d6801c0300c90081e0002049029040076a01c010110266554a42504400d503151484444a5034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 259657374 1250 259656124 259656139
    0x5090102060705090a0302040e030301210c05240a020a03091403032a0f030306100309020102150a0f02070c080106080c0a120f02060a1709161a0c160810060302 70
    0x2c45aa00c5603000d013480b090010401076050340d4903000b2504690180d00c0d90039142d00000014408101800c492800145800007034046142c01c540f41c00d42940c0d4540152482600c02c84a207016004619007075204800042860f640e0701c40d0884000780d6911840e40c1c0490100751a03040000d0700800300b10700d8441d105c002401071468240d1003076030024002ca01500d0b0358480702076004404001d00e0704000001d04038408200960740c0c0e042080c108402d5000346d070704500805040804840050340d01043c4000310740d00701c040c1400f90313840710b041c2e0390302810344c1d0f9860811541c4081094000e005124124008440031503000b00a02a281c414064a40120b0000c00e038220380034a0b400c00c940304245c0400d616281c0104031034241c46d90150300017a1164003070210f980009407a070301701794508208410b19a80217001c0000911a050002210103110b001038400c00f07640f03c00b04101c440524464200305c0d007158182c1c00a55111280300c18070f007401c5035001d0107031004034400c54403100c034210140d12885041e6500105500d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 259658624 1250 259657374 259657381
    0x1612020304150c1716140118030503100302151c06050a0312032004031a070e0f150403350f03130c030804050f09161416060b0f010509010206 62
    0x650320300f900d125084901005042916103901100300140c07210740c0e0504149040c1000d11700b4210085503c600c11800b280e4034210000c41100c0d94102d403c2c2c1010740c142000750301d86e521901d8a2411078030301c1d840a500050450010000c1c000705c0310003403215203006d4141a000ba02d046e030640045a0090149a4105180d00b6081c8080351003600900203514451a010800f03480340e5901e0702000d10034220300d646400c8003140c24010044040488c0400846041c01c402c418605a00300810002c95440c4150003042103240003e03081d100c10400c40c1c101c000020680e03030344998a261038122040c0d444014203501c00d580b8040140300030701844820b00c10b45081c0282d820841081070f841c51a600190101400c2c00509420800141101030700c01c0066000e0300720031741c85a1500f810b21840143d1480d83c1440351190a003040101c1150421003d040d9007980707054040300000301055500f0b03214000b4806820185005114100300315504240c20440c0107842c5160901c45900c015030380c41c02031070030041c0942c0045000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 259659874 1250 259658624 259658627
    0x10e0118260c01020301090b0d05150a0f0e06070201061505030a020d02040801050412030605030307020a12050312180d0507030804031d0d03090503060c030f0103080904020708161202030415 83
    0x1038010704500144241008005121041c0a80d44003070203000b65030750003000401c0060628400c04ca4040001d41d48000300d0301141cad0762561103d408008242515164201240000245034840c1120340ca030030701d0130490920212080390344d4034800c0f14144019802c1000100d0900100d922407883c907004c5072a07a5082d6141e07004000302030f402c888000048558203100c000307004034090042d81d0050f4010302010644001b0304030b00034181d59542c2c000c0707270080c0d004111041c0103865604c441802c031002a450060300c0c5000345840ba08500c40c1450403ca4078520006104442401c00aa0340a81302180111180d04004120a40c0c3c10700808001402241c1032030300190200303009450484441080f1065805d00d4070710680051454031210b007042d000220448414451420100100c80e08403922420781c03411450106105a01114140401004001e000c6200c1009850380d4042d5031010f9403080e162070311031062030804901003c0f40c1d2003d80d1074107401e00c403c00d007260000c4212402c1e80c4011000d5003920140b280d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 259661124 1250 259659874 259659893
    0x60a0815070c120e010215070c1401090b07122025050601060c031d0a031421030603010b090f0106030b13021305030d0203090a14010e090a0e010e0118 66
    0x741030706100301c2a00d0440052494004207048858684649400c013180900080c84c00a026540c03180e0090144140400950410054039685501090294042c4008040503015004c09100242018007503800d118680c2d0b0800550320042000325070401440c141c0300210020040780070100703400c0741c0040011120a50780c42000801030411908040040c100690b10301c3e1803e04c00740c0c415000918004001c0c0304042d8082e844c03400310102c41c207200411000300e02c002110000c1c1ea200c001d002c2001171000400c1e0150500c031043d08885626000c1c0801410b84409480c183e2048980c113209518040070000d1514180c81c900c1d000e4051055420310030781c241801034004242070301801c3e52020100301c1a09141540d40010030f0341c00241c110048840789031005162410000c60241d20664100b8042907001d82c8070300c00104100c455110701c1418120b200d40058410080442005400117420070810201040e80d400480d0a18200c2008000d81c99101280724200c0d0700da800e45418801929190402284084a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 259662374 1250 259661124 259661131
    0x20706020c070305010e07080c0a17070807080a0303060e0f0606090402160c15021c080709050d030903020906010c05070b090609030a06050f0c0301030b0f0a020903150f060a0815 78
    0x280149000c0e0000e40700c620b4242241c0c81150940e440d462a0510000c0500000b001418810700524034000c01c00d0000da03500c0c1c00c4c3c0c003403036030910856031440c0344400c410010f5100130702200007903401c826110100c06844041d180802e4001c20306018000a04007211401c4d10720a20b4003128103480354413030504010310369025900d251ba12540910071400c024003030300c10722000d03580704440d640140c500d02614145800d030803207401c2d415500400e16080f00204107403907140c000103451a003600b0319074480c41d058030450010b4110319045003100601a00300758020040d541524021101020316543d007000442d41c18201d020300801641002d60100040708840c1c0c098109010020a542d040901d501e002c68135040880d2820b4481a4840040c4420b94416821458010002c080000e182d0342c159100c10750f50b100b0281081c184012800005601201154180d8158600080c20b8488034a00414941048071041e511034820840c414003040080ca4420358000856002c200600041681005410300411006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 259663624 1250 259662374 259662383
    0x615060a0c03030e01021602090108010b22090812190e0c010503100306052508061f0c0c0803130b0703210902060a030912030501060207050d15140402010f02010902060d0207 76
    0x80c1d05080444d2002e001922850b0300c800414074003e035207801080b41144040e848142c0176490111032101585070084011036a8151111031507012217001d100130014525954041c0c031551020a50507517000401200900401c1804d001249410204c10000c0485440070610301c42c2c3c1c2e01420300d1074000e500401c084d681c1b00c4c140f602070410703182c0d41c5d85030720068070703411604042d4180d18500c5100142da20940407212003142840c0144451405101040170141429407403076040400c00610702c940c2e0300c101950b090712584000200b00c8c0079644d4000c941e07242c01400341760f010b00c846081c01003000a40e10342a0b03242907805a80f505a01858940102c0651001a100f0155541c541d9000c0303001da01ca041c01400380007115580005d01514074100810b501e84003074080d4042604042c0104003c9a001814034140c0d03008032140c0c40003080c10700e07007000400d6913002d889000d1170800052004031080070902a1141d0b0003170300e4654010500e83c00c220700b09c9000c1040254001400d00c011410350300d442c1e0180004900c40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 259664874 1250 259663624 259663631
    0x30109151208040302031507050909090316050f0c030619050603031603020d0e0418030311121e0601140307050702060d050f0406180c0504320105030615060a0c0303 72
    0x2101c01101d40c10702a40340c2640d8018000504004500303007002100a580c18415610000c0d040240005000784560061070f8402c81d031840100d0422172048c01180d11344d606101d24100c03108043d00e42a5110030514601412034044c1c9002200f5070b080104001b8400c090300c407221403600d412549841c00421014001130f07058801400b0402060301c94640c0a08040c0c020380041ca00310321440d00043c4801041c94245001d0360804180c4003e0062903080120841c4d03040c1004140c03402c03030508400103030003400708090589204400703000000d820041c2650207058101c001081030f580c1d600064810340708038107440718442d40c10000101c88a1150002e0038245200904403840c1031078006c8014280ca00030f03104041d043e08031000b0303c000c2012034400c04030151000004004907190381d031a020b00361034507441346a0041340c549a090310704100900002d906800d0501158038100054804002005c40c24082e10f4001c0c8100408615076101008070700421341001003140780741c25041c0d81c08503416460000d08805040d203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 259666124 1250 259664874 259664879
    0x60c100c020f25230907031503060e1e030714240609150a030201051305040204030b04110303091c02040f0e24040b04032a030f121103010915 62
    0x40c0201400611224036400f102e0b025030002c080c644030664806151103004404820081e419000c801d0002882201c00d460203569985050f805442c0c00700c0004204080c12001108000155000228801c2c14408407030720401341c40130381c2100311624442c580c8154800d21904000450191041d040000305030b086c1c030007540350070125084881a04584860032034091082104504101c07400365403001d0071800040c06501410045045804140006810000005003640d202e06905031700f203008000140086560742e0f0381c0c0c00c0003411391200b92000c0741c402040407102d01007440c000086c4d038007a140040cc0020b480d01d403003c2401307460800d841c2c100c0e081074440e04410341e8041e0f180700e00d0341d6000c500f60281140d03c005d00d00504501d01e00d01e07000c40301142c04c0303801e10001c120f02c540c141c1d6200c0d516080030302c581c0244404269654808416050f201c1804500c0c1c90708041e8400305146171800c00f900c41107000c000074034942080d50008046444211014001007106800729008006885034407030741554201d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 259667374 1250 259666124 259666153
    0x30c0b0c070501050c030f070e010807110f100b03150f060913020406150e0114030126030a05090f0d2105090405090d08010e010e0103060908040b03070903050c060c100c02 75
    0xa02c1114912031172040801080404000c442e4034990045080c42c001000c8841140041c0030300901414100400c01c542d20024607400d001c014110036070000200f11615680c805886030060005c44103198082c0c002c0e1142d14849460501009002d00c01e12102640350756510f0090080c0e0180040c428948001001d50003005a211489030030050690a528110040310004000c3c1848010340b903041e04000102014000304103419003170b41c1c1501c241101c030f40d890400c030074013100c04401c104079111060b0000058007003d16400c0b0000f00407840050b0348007000c1006a0040154585a40a015007001d0b403005070300e0b031017020300c952a0030703003800c907050144c2000e1054001c0b50484008403035101b03841c1d0150304490010760300940103034014100c80309408050f41c10315800592442041c40000c01d05500c0b500702130300700500310301500d000d0503100504603140e24044ea8010446011880152031380d018483c0403010300d00385401141e88000031440248000790340f552105000b8114202c2d41011409160601e028aa = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 259668624 1250 259667374 259667381
    0x18061b181a0d02071101140a1b02120708010204050112020c0d0e060d06090e060a06120305130b0a0305060109051002071424070b01060c0f0308040c0e07030e19030c0b0c070501 77
    0x251700488649648030f000c1c100141549014034034424114005200408803030354040540f040c0c40e0269407601c1d203424243d1012840d40007410308243d07614002c40304045a00001540a4030484000343d076455009000c8000c0c4c1400c07442a11241001c6402002603404040e005140c80700c00700101505452900c200718014004a0b11f551304400b00b619100c01c002401d1190401506400c5000141c2c100040c520b48a2400d10401c001345006040c07000c0451041d0754505225030744401007141d00015503441e01e920000038001d000071642c0e0340c04503058510100f40380c2410042c0c031400030382c0c9170001c14225080580211184a01c0004075500000c0894160f840f4084040540400e02840e4420740e101d07610303403900c0c035100c0205070400020007180741b07004408184040900c48940c0e8050500785001d4030750341040203162140e81c201e02c51400c81d0000b4406015411741c00780f28503001c1c0300c0603a4410b0882c108900a151010301c0081e000541c152003190100c1c6100106940004226003168501000c1da9141c5095 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 259669874 1250 259668624 259668637
    0x50708190b280911030f180c041a1804170c010603050a0c0303230301031104150602060108010c080c0a0e0d050a030c060b091603020c0118061b181a0d02 67
    0x4030201c80000300f001d800039008075070311003031007130012410740c58030b6040100b20714001001440d4a181d915190341c8251001d00454040080c0a8800e1100b00004007584180b80d190b800c0b254007565405140c18403c00d2000d4900d03000d9640b058180b10304060005048455802c80070f1240159540c0300c030001f0000f0300030011100418400c0650300ca8082c40c6043c080d205041c4611107440d090140440c03d20150303850300803241900e92100c0015020b408080128000b130402c0c0580030464034102c000801e9031b5070000380c0c44d8102e4003044002d00c0822125403007103800c82d1055440700042d5000380b0900314090b016030440a10048094503919110741d05441d12031525104a03c1580410507104082040c015a80181c1d480450242c1d0003144a061031454400070030400c1c2036034801c140d404262284200400c0d000755003010021343c68104800034074244a4002c124204840b1800d0545462600780140103844c4403544090f610b80300c281040c039000201b20300e16450700c0240c10100d01040364640e44083e61016190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 259671124 1250 259669874 259669939
    0x40f0e090c01050406080a0f0e0a0c0e09011401030b040222020a030f06030818040f0905240c03010b07170a0518010813060902040603060509060703050708190b 70
    0x9a60a2212040e8100079859480e40d04100d8108014401540c000b101e16030000d8041c4c20000b4503d109075145401000440c03003a0710300340a003599820501140207460700c01e039102c40e4601c00403601ca07100a50300f26010fa0350b52840742c5101b000100007242400200c0d56210b030018210610140f0346818000c2845101c03100908003a60100341e00c01e14a515224405415003040001c02007030341035440e06422405440c9120b00d400501d264031450359292504014400c0b00840704c140b1401d101032510680b80e060040790900c14840c03180d4161405180714856501941e00608268a564202540c2ca5030f00d40c0070210a503110400e4280c61100000700034000e001f030a404c0e40d9819140d00017449040008000401500c0c104200c1d03500740820000880159080680d00c0f120002c0c04201900c0824050b2245600c040c2c5050300d448104907545202041042c8500383d1550200260780d80e414080d1011441070769907075140142a03d82220781d503413642c05003030001800cc0c10440d0340096002c0e400c402c50000d0311801c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 259672374 1250 259671124 259671149
    0xf01020a0f090f0e061e060a2106060507031107030c060c05012301171005100515031302010804111002030a020d02030f0f030c07170403030801050d020a140105040f 72
    0x941d10b9200380d451002c2c144100c45800d0349484c1c0f02c401c202c2c05001510340c0740300c1d040718100000c006014441d20240c0342d5001e01a5502d0380c080a0000e01619007403850786c6400b031603008101424401c984142c5003540c0003a2215810884103840c104c80c1000240c8100043d07104141c40840800c60f6403074983d008000e02d03641c0880d81142481c0003802e5030030020b210400c2032000c4080080780741c01214681c0c1900c0c0d003403900c0561086036003030007481c05080483c0c011145240106200512684000c5181990010b80d0300001c031003021920706c1d109120440c2d4a100c000342a40c00c080056109a09041d0418020f103500c10303850881c540003c5018112019010140c0c0c000200d0040c401d4041c01070410803281f90003d5802e06048000d492143d02c102000c8003202d400020002d010052128103640d411034012141c40e40c0c01043c0b0380a495142d20600041d0046201d40c40002802d00d0700301c11105000c3c0d80584010000d40c50001c17584101100c030700c5c3c068144001070001041448850b0034013401044511802d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 259673624 1250 259672374 259672397
    0xd0501020705010218010809071403120c1b090106020706080a09081b0c0d020f0402070503041503060302010e0a06050d09031413091802010c0803090111040308030708011e0b0702030f01020a 83
    0x1748240c0650003281e044c03000304010401d000d0300115905040f1844086071956200c19000000c3c00c0c103800c00310306401003901040344001c0036000580c0381c00400503100503802d541c82c0c0804000904509124140c016400b00005000340380c450010950825034400300840d0501c12696220042c0c2c1140104041c1d4004040c028000224200501341c0400300079100712814038003980100d0212500c030745503280100d40000300c2408002003041158000c24040c10b58441c0742c00101d20040180510b440203a0010b40c01503a00c00c104d19110401100312110394941619240c54003103800d000c0c000020042d400d200007905a400d520301000005c0c4079003040351030844065824410780000b22480e000010b4805070040c47c40a0040c3d030404101c80d859a000a51640c4a40d141d88119025145022000c0c0428002241c0042040390101c00f40d8000c0009441d1006242e0b00c910351008a008020a05160412903038820030031075102a0081c49074034005002d983c01c900c00b91a00300d00ba68407100c50300b0b00060b84007114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 259674874 1250 259673624 259673647
    0x106020307080f0a02120705252108040510050c060a0c080601030902030f010f0f05010e010503061f0506070b150d110609010e0a0e0103120806090612100603030807090f230d05010207050102 83
    0x5070400c1274002101c0b041030508243d44c0001280c0c419140140040d100c0b1405001e0140351403d40e802000020705050107024101d1000b001c541040414070250320440000c1040304070705005001101040d86d03100991940d4100045010b03201e01c041c2640c240c094040c440300072030820f01900c180c500c580b41000c103040d5880303520700b03044400c143d02414000d012000140440d640200d070070790300050740750b42071417903000c040e884941d80e60100d51000e580820002034910801103c06946449441c448a2035041015407400340b209038081d6001c02031600340b40c0400401145043d9001c2c0298400600d4141c10342c98241340401c12909040d04910140908000100304000c001c4260000d40d110a1811407002c3c20407401240c1c7d00b410141159100c1e40030452241800d010400500e4034001c241c05091101d03540e2410701502ca44400d650600014485410205110800203039480c200d596148185101d0710110380705559410039081040d0344034110900c4035000c2082400981005801400010399440b840c854 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 259676124 1250 259674874 259674913
    0x1b1c0219020a20030304080a0303050a1407080601120f050a06030605240f040e0d08011a0a02030301031416182901142a060106020307080f0a02120705 66
    0x80c0c08640c40089140c00160214a284036941c0004100300d4100403968002411400360780c102da0842d00c141c03134110041c9a890f400540c02425a00d204002856a00ea062460004103c46200201d080c1070301003501544141d520004424502c1400242c1c1e090070010f5a05442040c1c070300419064840c413044c0107204a921600b90400c400c11031686814101ca01c980180c1c8400e103000b284038003400141e0f007102d900c0319006032010b140b0340e00c1540c09850300c129003d08440c100780215800504500000c0c03c0120701d41d0215004031100360020740c00c5030b196a80c4c0c05150414500782140ca0700400860391221903c6d40034102c064a84002500309200f002000310007101c01c0a0301c02c0810720302003a9844003e4102d80643c0c851540c081c0fa2184500400d003405e150b0724404c0c00c00c0c0c501e50480e80544c291040105100d8440380c80844400d49203c2d0f6615501242c0e28000da60300504016010000a030701c802849000341460700460041d103030300c0e0b1141440307082d03a03801c47c0e0016210360300b103502401c00c0320f04400c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 259677374 1250 259676124 259676167
    0x605070201050910020717031f060e060f07021f020604050f03031612060317070204050a09020612090f0106142103040b09010e06070302070608070809061b1c02 70
    0x8001c0020b490107050f1155a07641d0301c400b950003283d0014402040c0420241a58480208110010740d64240802d0f00b590607a0500d40d12220100d07901c0020800a1080c5040451490028079003070a005070354080728442e9000d614101c5e4085400c030182d501510340e401d640a56100365802609680c41c1505105040480917801d40140b500201b01704048001030045030360002c4420300d006030254a092800074024101c682015040c9c02c04c1d000321000300100500200f103601e00c281d4041c4515225014800113403020020000c1d0b020701c0a0003166455491808102c0d40f1180c0c00c0101c0d404403081c4050705084604a42154481100c00001c070202c6050084850078440346031020f0410801d04940000d03200e005a00442400020010300c81003942e02c61030145914160003048247ea078052403401940c3d5240711310403080400c0149002400740c0380a0a0b64070b220b80011006001c8a6660341c00ba0003129201c01144401d8050505c861001c50004e041c0c2514102c09824006070f88000f03181064007440d482d207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 259678624 1250 259677374 259677377
    0x80903060703231909060b100201110306043804050c03062809060824090d0c230115050402041a030705041703090a0b0c031207020c030712060507 64
    0x1041002d0495071504802d0544400350301001c195124413214844603a030900740b00c041641414100310600c042d0ba4000c0134031210449540c40940c45143c010b900362103a021950592010500015445044c25007001c0d244140150029240b4a101c84900303007400480444111490180242ca10007810644105500000300815030f43c2140b91441c0007480407c09102810001c540b441d000400c201c40441c25071000d01116a02031240c1a00c800005551710110109001c400d140180c83e0490a02081c15641c05004c0e81030280000740d800301006e80c6c8640016a086681684100036550b000c8240f4000c010703280701900000c1185032505000c250802d03143c1d08414841d6104000401560f0020108502030004200606440381e4444400340d40f1401103074421540b44c0296501000c04180204c020410214115007080c140364589406241501422406544550081000e07410001e6215041a03101500c6d00c111562134090601090600c0b030203601050f0704080c22000380d000c1005900815905c807586 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 259679874 1250 259678624 259678631
    0x605060903030304201c11040504030c03030504080d05090c010206150307030f140102030103080a120605090a02031807090c030e030307081303120606050406110105010f0927080903060703 82
    0x800c00000e80320720001d000100503440080c0f00700481502000c045011740310081c1001880f81e884000e0b07016010041c45e086500d410000c800c02d01e280303014030415011b03641507951074400c1202550242d009060240c400e4032600400d1011600c546a04d002d11440340c40410064000d03644014006890580050020248800d41208510054400180c48402c80f504100d0400136481c0c54200250020101300c036110030b5500001c0040305010b40c040040100220341d07602c007105030f1074400e4110103c40c1240100d55000240070040f82c040030325a005143c009440b079280c801100d41c0100390501c2e0100aa01c0610116152240c2081c1a6050b1141000302c05140c0099072851410410003801194000d013007501c20511024450249071151f01904640d004254040100c140c44003030241482e00144550300020742d4402402041c84010700500b8100ca1011040c034030251f0600c00b54030003501c940303801100039104d0100400c04205c080800d4184090040315039a82c1d0b02c403070b281458141240184041c090504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 259681124 1250 259679874 259679887
    0x19150609020a09242a0602070c0f062d020c030a05011a0406030b04240222060c05100c021f050117031c020a0903050a0320070501020618070305031804060506 69
    0x4000f1040d0401d05e40c0d00e1700c0b175030144e8540501c08510040c84007014142504c0404c2c42c00420044d00480004d0706d031100394255a1550b103420072101da2281c100d95003500c0c40c0002140088001007501100003100070300542c0d1080c81c52002082c030340034070181c003921079a4480780110003c0000e9040c0b2404003106540c140f02981c1182c60350300039103c000e0401020040740102050003030075040e8502c0780d18010743c20700b5542c0e011100d003000120448280305044101018000040741d40c0600c2040503280d500002030704615245c041460000c1000034a00303000c0d030241c50215030608011110030441045584800900342d41000000309221003d41801c6005034001c02c20f41c2c4614900d03400150401140260140c0c0d03401c007824085840709250b5000604510810803178004140d0843c821001948200c02c2c00304440d0110030700d0996075801807064a000d80c0040010a50b0b14006011050110dd03c0340119011280d43c0ea51341c500c0d50340501400300040c40c00c0880c0640d140707401c0c0101d1000b03007400c0710403604089 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 259682374 1250 259681124 259681127
    0x5040b0412060b0d0b150105090f0121020a020303010e06010309051009081b010e01050705030709030803180f060916060f0e030a12120b0319150609020a0924 69
    0x800c41c080c8600c103002888940040000c90b4208903150a00a00b000c03280003814900800f5107a070a8a40c005143e8501141d03140390b500c2201501d0201200915440c0c14625400043d00c0d818007140704034aaa00d000d804c0321801c14a40e00040842c0c0b482039004599940c5001e114101564010700000c2c10142015200c1000c15000950840784d18056036002400b52030919001d00144a1040011400858034210f5200e0005c19801141031000c070308000d000540d290201201d0310320007200c0700e401203149102d0910100d00c8402c09594003018610040c06074640070080d05160800340480d81744181d01440c00c00c07100303080c24802400090b440211141c0c1d02402e00402a2146808810140c100f0080440e075280b0780c0d5007040304400710b68020300c0c41645642800c9008140049140ba141040d41c10700746d103c00701d41000200b0b10509080b20001080f4200d00d40e460508030000c07003042c1d00c1e01030789500b0007040ba01e282c0d200402610b10180ca803400ca4a103400e85440643c0540c010003141070301088212064107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 259683624 1250 259682374 259682377
    0x30c030123060613060f090f0f150c02032d01050f04120203042102010521060127140102030c0609031b1603080f040308161a0103050c0d03110d030606080705040b 71
    0x42e4106e06051050055a110840d03030012154401492a18014000680104500454410340d5806101c2c100c403007c81e4041030b918031045000003034055204104c044c0c14210040c0c450b2000100c0009900c00300681145000e0030755a081c1e610078480e222030800c0c07008008040d5520076030b031215030001d10304043c42d0001c02e1080041c0380c640403420a104100c910210383c860012103424011030292210101010001d503140550210346050100ea20b000b0074201e045c0c1d0b9480650601d807a40d22907a02a00e0400350880004070107900e520381940b01c00d1100820071441030080c1407080f6440c000840d110048030f0060b2202d42031405940034076400c404610f1000031420314128060780e400a45099403240420f4180c0c2d0984910b901c0502501d0f4046000011851075801e1940c1450083c07280b64036459051010129a04003840001c10a034400c01c00c4100a091015803056420300030f00704054284070101e002410f240001c140f170000646c0e20641442855041460250044002e10f051420142007001d0100507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 259684874 1250 259683624 259683629
    0xd11031e0a1101111c02071202090105060d0608030705030316030c27090e0105060a06030506030a1104020f030a0c031401052808030c030a080a0207110d02030c030123060613 76
    0xd160340c0b440700460b640251a041c5000c081e01007284c0c420548001342c0c2100200303200c0464014003680b980011064145004000460b80081c0356050503440c0900b000015889034038a0030385c5a0b02c0750700002c1d681c2c1e014006001c5030390041000e1750350b0f0715043c813540009000440c1c04100f414504050490303680e82c050350a03021344040803002442c940031840421000d440507030042480900b0720400060001040d0000d5004920a07a40d642205481d031301c0540564504452054140d17020020381004194129408000090044c200514020b111207202c001075208417004000c480d1103001036850294940701c1e9540c0000c0100c481d511550521000922841480000c1007003107103443d040120100000950200420b1444d040326540c0c80b01d030707141c151203820142c3e0040100d00340700300140f5550614004c80301c5031603006141040034402c2c03804010409055800c04d03030301031080302400e0119441c24461081c800050f038944e00c1d40e0400c405103200e02e1801c000e1005003d120240309940c020304003860008103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 259686124 1250 259684874 259684883
    0x210021c02070201120c02010647041a090f150316030e01050711060106090f0b0a0210060303090503010b060702060a03020724050f01061b0b060d020d11031e0a 70
    0xa03070b04031900048030504510f880b80c04d22145841280d4a41c01e40560041084603089011100c000035180c0710f810500248040c00082c1d000e01c8030100303800380f0703030780307004060400e255801641030076143c1410542e4991005190b89501100154a112601d02200551040c9100715140b9010300700141c1a4031440c00f000e00394965a8840201c0b51020034001e8111240a819039402002607140040c80103050019040a6141d0ba004000c0081401841048190306035a04c0b001103a207030702d03d40011000b181d400300044c0b41c11401007592640141c04280210001940250b45024003141420101400c4400f00010203114210801c600c00068981405643c003465040c2001a1245c1e868105000d0590f4001440201c00b4402144010900300d1903025a0085280f091918202da0700c4072030949201c00c00f9441c64803111f0130303001c43d1000509035019281c2c1c400c4002e00409104001a070100340c0244814000700ca51810410b851001801e0400192421024180d2041070340341c10900107603190400d4500c081d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 259687374 1250 259686124 259686127
    0x1f09020906070b04050709112803021c0504020109151b0807020306040803040c0e06061e0d180203010c0503041a0403051e031e01300503040806070210021c02 69
    0x41050791404151031003960031442e9483c1519041c038007a074640c10540100043d55280169078013501a410742654400c81655100c0c2c4650800b481250845100c2403401e882019020016449410a000300e40ea01c0d1003003003000890303903080510000d0103030381250300046d0440c24101d101000090344540d1403030b00e2140c001000038030580507003031080140c480c4400c041d401d44108030501007000311001c000d40c4038a01503024001041d845040505d131a600540304590303c504140050f0011482d01211000c4586881941d94580071a5484203010f4424001395000d41d0740d000d480150a500302070264011a8449140140c41c52038595900e030140e600180f080d500900c0080e000408040c01801190364a100706407004860220f0901114059482280e003001d00e040c0c0c1510402ea41c40d08241010705a800d09010480781120541406180c110184040d45030080c190550b003000c150284000c00c003a0034000007603c03082c640440003903d041110f8905114032881003001800b00b0718201034604240d6130194015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 259688624 1250 259687374 259687387
    0x12091e12050106030503070b04060f0b220b0a080c040e0c22020906070c03060f0903140702011b05030307110601080d0e010201140c040602070506130608060a08030f0307081f0902 78
    0x54010001504014000d202c0051f04809100314140e201c6d22036807040c4002c0c024200c1c2d0803800c909540c00301880a401180189154903070031f24180030038407101500480045e9038907820000409285141c2d01c2420540c008289108890800b4060b104c00065003400400342030118001050040308020090a0030080c007182e8000d01010940446500100060003144c44050504000315141c01522045070100e29200100d400c6e06984c1c01080b0035260580c90342c0c0c0c01d04a2030104245183e01c511f00480c1006090070030070f100051210650028540644021601d0385092003000e440001c0c1c4201c20552603100b0001044bc140000690194074401441c101c0840410600140d016118543d10640b001d4213440c100301000101380d01400454001b6400c03030b8104d03540c50050090500c1180c901c1c1100c90101d950500025002d641003a1b00010054420342204d44c1d06e0b25403506603006002404061030001050040041e40420307030303c1c1c00011202818049065000400582e00c3c2c10307101d552030168022800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 259689874 1250 259688624 259688633
    0x3010501030218060a030c0b031005030d020a110303041242110d0c0e01020606060406050702090601050408060a0905210d0b0f040606021c031e02090f0d12091e12 71
    0x5c4da0000c640c8251598640360f102da150980719002210010a03240500b40c1c00112464000740008200120b0303000b5150300c200545402080c5440000b00c00c1e0144400c01000890480800e401c00390140590007402c510300d010924100d10802900418030100c1c2415015651081441c1030320002c0d001e070410002e0188180b00c000001030241c440d00d4050302c1d15007901000b149800080050803243c0c240d0a0315940d50350402084030601807801940005030b030030301c020b10043c01d00803481508040141061401d00341c1c0c4803915868040e04407909000c0f652180310070010071100300300b801c014022500807060341d480741401e140b1301c9014114810528544a0340d4080b10341e06c540390043c01d1840c1c080d100f4444031744c03030713010280d900e0503110440f0001c0c1e4182c0e0b140c100010312038440ca2020310000c0079a000c408050000e00700c084c1d0040006517034424141c0c44039215960360001030312259445203092070344074200541c014140d21215481031281c150052040d8848558614503c0250756480c0e8480c1c4003c0b206050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 259691124 1250 259689874 259689889
    0x1a0a0807080421080a060e0c04090b041b05190306050904030c020a08030d0c020c0904020303070210140310060806010f020d230406030518070e0a0203040609050d0302030603010b0301050103021806 86
    0x8090350007600611040c3c81280c0c091101c0307201d0030407030ba4280b00081c0d0340c000c21000310604407440f18581c1003e000511044029400c040d40320007004202060401b01c404454030f0051208414102080c400984111100b4041c006d03081c6400d040d0808000700c0f890140402c0c020700c00107200604015018048808564490b00304501415444003200e84038844e0050760f03c01401c0c0390320303840c1c09407040009007035540c0707070200a007403007941d014001d94101201642404003030118a040302051120f40a500707d4203001200241d48240b020280f4041100d1410401030094000a42914104071411603000e480540008242808524510f031a400d29894142c3c0500784400104242c540c02c0c0303000800040055154001c2c03401080300d190360030400440e004040d80d40c0d498600c95519000c8032880042d01c038110f941e018590040c059200450341c80083c4c1d540300d040541000c810303404070358048203100709403d0901c2460041d0710260007c014a5042d0340002c2c24681c061500d040340211701000007002515204d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 259692374 1250 259691124 259691153
    0x402091c03030221011409180105070507060c0e0109150e03060925080d050a031b0903051207020306240303030a091217060d0203010e0f06011a0a08070804 68
    0x615008035030052400074040e40c4030000c204c1000e018000300c10407000c0c0d0781d45124101c07481100c40e040354a503401c051000d041c400404410401c080c58400000d080020300131948594055620359650314207914024003110788007440e440401900000304c04007a604002188281c3d00000c41214440302c0c0007004450001c800000d86416014500900028160010301c4802400c1110740c6c003146200706001210301103d441c801c40364198441c1c1c906400c458011402008444160301d004030f03401c40042e056401c13803d0814000f80c00545620000c00038080207000810740c0c021503030340c01882e00b51150006652101c01400c1c001800c4803d44800d80100b03030701c1404800b01c40d0090196601c915000396000c0007012080320983d6142d5880381d450780c0b507034854038400160343c031040c0d00c110140d1901d50030320445440000301240c0642d07036018004440002040050004002d8000500a941c105180c20f10803000341000442c042d90203100c0c500980350071aa03043d5200d0690f00d0549e070555107a0030504203904083d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 259693624 1250 259692374 259692409
    0x61d070c0204180807050127030f03230a050901061805060d0215030a0b010203030c2706040b0a020f0c060703050d11070c0e1e010b070c08010e070f060801030b06040209 74
    0x1203c1c6904001c4103c1c0900206030180000700926038030301442c409003c001c4c00c0300c5400d000100d141000000d00070001c201415803a0720300050b0f21f03030406600e071301c480001c440c240100a65520030014031245a02400c0d501000010080c8076035441c1006d0295100c1c91840b440b00066291000111076464243d0400c071616002440e40006030300303c491040b9207a0060301d81c50003050500c16040300a50001086074001c0c0501c0c8170082c0f800c03c1c803103801c41d80704110b1014082d01d8200c0d1540004070365103550180028000b00346080340e44000760300c400b904e40b10000600c002c2541060107089a2560740700213660f01660141841d503580c2c1d107003249400040c140c80400d04205e1902081c0c5405000c9142104403e42d5803403407420702d16480340d1030b100080c105001403614020600400602c039442810014040142c416200c6400c1181c58030a21400d64010314200300d425803002e0401c1003c280d00300c00ca8001045131342068070700c039411030316040000c80e00141083d02558002a00c044503888080290f9080c1010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 259694874 1250 259693624 259693661
    0x9170a02031e0406080115050d09050c191706010302061228090c0b090a06030c03091a0906010b0c0c10210b0406080c0120031201030803040501061d070c0204 69
    0x320300d85482c054005004480001c0c03590000464031010a04034000a4400c5c0d8483c0c5040620403015403000c1c00b48800100c40a000310350085509441e6a800a0000f8045040f264412800c3c0820315407584030340360104070785512020041015859680172030b01c10310181c500780c07800384c1d44910b01c940380d0b1070503685440400e680c1d50300160099001d0b9800504084c0c410b100541c030300c036031718001d04069020703640304190300000000040084a020768481e10711905a4100891044141d494414448085100c80d0b101d058070001040000340b410310819000d01060443d07141020980d0704499a24003031842c030180103140d000313000d5080740c8c05030081c40c2490b02d143c480d605d451111032030400060002c0400311801141400b0000c110b03402c001c200d24041c0303141030352030f170f0b500e803c16003118031002004001009190008000c0004110200301c41c0501840c0030b001c200c1c0e50b900346441e2241c2110202d90000d01d209110340e0215511082031104290401d00303a02e041903240d802d50001500520454031252094003a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 259696124 1250 259694874 259694917
    0x60904060e0a060227061602010e0402040305010b240304030e01120504080a11010c02030f0318120703110a020918070b041403120a1704050c0406031a060409170a0203 73
    0x80c1e400402c0c03090140300b0030300c1505e1054008426540a003881c81544090140002d81259481d0042c0c0074186005240000042c03162402250813030384079400548031039469403413070090b0741400703030000400c16150704861403810302c105c0301e0401902000d0300040030000042013001c9660310038050101c0705864120300700114182803812400a81c0030f1000c0101140800600d041207100612031240d5001c2590003452400e04690a0041203030b0005220b00321402445007089210320b0100007002080c20303030221441d9034103418140a45800043d0280c1005a84440e0302100162a030220b00c41d0060408260011404c11552015050000d00d8000d940c3c011000700d070014900c01107444072288001d050707054450306a500c0750710307411610841d0f5149001c512030303a1045100030410000c1c07903401400303142920040d0b141d40000400740c1d21207900640c0d003031410141784030910300c00032181e907001081100c040211503465a07910074240e03040000341002090226410462070300078801c45800c2014452100d08090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 259697374 1250 259696124 259696133
    0xc0102190e01020c0a0f06052514060c03010510030506010c0212011d1209100903060e07030314090a030303150e010e01090e030408070302060d0204031a060f030114060904060e0a 78
    0xd00c80c00041d0b00510890a00d00014103200c8060405e075005d207802002180e0034084151419401880f5510004030041216a03500700d158501043d0701c6d110701c07040e010b1198015012403401a0140146c04d00c50070401c010806d0b5514080011180809030402041a030344110042c0c80c1c0c20b02e00440a504410119404002d00b40c042d80551445200c100e051880c140341d4080140d5240b000104c03c2c5039004080203c6001031520364076450010f409881c2241c4c0c0c10f5240c0d40c4840507548824115180380d40f005405104154018035404c041c50b021504c01400c1901441c0019000c491502c405028075503181b9403c01d100d5008a80040030b4009213010654950b0f50f2180b10100c4a82489a80d04142c6081000b46544401004841c1103448482c01000c240d4155001c102c881c2c3c1c40301058004043e801c03c80000062240074132098800304000c41c1030f8880c504002401094a00c1c080c0461290340360854032440c8194140705c050b0851000c5e12060310550311482c2000003051000920344003441041050750410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 259698624 1250 259697374 259697387
    0x1b04050a0b22051f12051c080a06050f01050306040906061d041406010302031e01140106020309040b040c1b05070e0f0703060909030905010f030b13060e060915060c010219 75
    0x102401030080149944191001400c842c0050301100300c10004102080034041c1c620141c1d403071760700840a40311000740b04100981100c07181103c140102d440401001283c1200348a003a00034281070350340422013161a0b00091071440b005041d544641e554044c2c802c01e0210781d601c984007400b52468401c5400950800503d15900f0448044454407041c070340107000e210010031000e0481ea8090001c025516850881e82c1300c2d4140d211180040d0b66941c00c1c040814100198603a0003040150041e40c0c2d542d5040e400c1c80159182103004a004030305009084010320303449200d00e007c1704400310417031030090101e150090902800e58001e03043e40e000305040c404c0750b5041d454114000c44594030200280c0307540d81407841c141c52246001a0120740c000d14100560750084801042c0300708030b40380000d43c00c82d0a8002640000d44205002002e650b20304081c020070311807183c504e4100308212510f032901c0c68014011000c0b078080b10b02645c0600808120400c803260250107032035030308151003000003d4a80141c2c00078040d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 259699874 1250 259698624 259698679
    0x207050306010f050901030201050d0f02030a09050c011106160e030304080c0901091811210309030d021b040b01050c010c0e0a06031e1a03030403050303010807081b04050a0b 76
    0xa8001c00c4000540b0842e840320500441c1d10141c2503d0150f0300c0c1da001500c240c1c100e920a40003580d11050001e0901c0c3c0a407004501c158103403100000c0c0d41c0300c2420071381d00d08086205103d0501480e1250a1101d14000514070b40c81200d451803035510941d19030044560742c17805403800390507110114010611a8010510703002011040d680b100490b03a80740003400030303500c3ca104181d02104a01d562103000c200240300c00d01a50780e01529005d04013440031044822900c4907154952180c01c086103084080c80c05010518011203280300810512061640c03224100c03c01850040c070440e598031809126234000d0060b02c140b241304a000300000c00000c107010b40030585480403103100c0d0701c940a012401d039019100d1107c8c1d6001d10340e8100c001040c0c9180003801072071030b108098070400700101c04402d942e40c2080204040c40c8a14081c41c0c0b0395140c24060b52424046e40c125422075044402c3d100210310440c03002c0365204104403070201780340c4c0300c2d410414010031120b22141d4200e01100a28055040c41032400350305c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 259701124 1250 259699874 259699879
    0xc171006030e0304030c030318050306090a030315080705091305030f03040312020a080402150d0e0307050105090718020a0924020606011d120309100906030606180905070207090c020705 81
    0x124060342c42c0d01c0e0f220710135800002c204c429804418008079205070174030500a100c60030f00c2090107880d040028a0080f0461b14501d0950001e01c0d1764003010382c1401520b07003180e9003034134462840e82005070b89500c8000742d01800f4001d0561000091484403405003644059403c01c054030369a029094160b12164404c90b02980807c218a652612880d164803c0b502420515a100e0040b902c6079400c0003c0300c0303103010102c0d007101001d001000c084217451140817041d80315103000310754a1603d40b0b41907095460007025a42c8507000850100040d80706145003404441d1031520060f174480345800181c4040b0001c1d001102620004075811840711072084c981c02111000b80c00315605071ba2002c004550b141001c40c0c54211886905003d0314040c10210300039100030400b00262409d1184440c045440048c5d000c0d8140000780c1c3c0c0c180c4c10080c0682600c203020240c101850b04074180d1084a840040d441c0c0a0b100b1054203e55074000245414400e129100103440030700c02c1406401040040295101c2c40740c015a032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 259702374 1250 259701124 259701131
    0xb090a03140304210c0213060f0f0e0112050a1a07181503090309030f0b042303092b200301020306030a0b130803090d030c0e01020a02040c17100603 65
    0x801801d8610559100783e5000c10a09011310031407900141c40640f8004000c24020442c080340010703540c00314228040ca140040004103245040642680e802e4140c1c00b00354442c03003211060140c4000050302c0d80c15a02032003030b015022015807511320b140012080016000c0c541c06940c005912101603180350244d00f860382d99a5807080d0240031201901c80c00d1280d49042409060b0f00400c0501035001700403030758068107001c0038140e941d0f00c0d0364402d028407407000c40d0b21224070410001000100c180380c0710340c8103130500249030305082d4030a80e507500d101e075144041c410080b1300d15050340442c0d408100c181c014084011800f00c901c41b0720703216002c4080900d00404011443c1e40c500c895040c1442902e1086e00000c00601c140000c50301c9403540220054005011800c02d418000049601071000b18003e02c1ca810081c40742a4201c4801000c8404107503030002040012122000140c0e8000703808203000e84c0403030b03001643c203a182c401914030110041c10b03a82402206020000a104141119411a26651400e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 259703624 1250 259702374 259702397
    0x90501060905070e102708030901090e04030503010303030b22050420060f0307051201170d140304024b0904020604140f04091101020c011806080c070b090a03 69
    0x10350f0300213a9130b03a80e55000038034070f5020101e0901c0340d15012903070402500300846a40d83c21642c0e804140164000d0381855000048580c0d40d544d00002c84002003000f4a5401c0443c1015a4018500e100620000e0100b585a000e0107140d5581c0d26107039003480c6840a0100074021100c42100041e12080b103055801d0181d894440800c0c1c222030a45041014004203c0b5182c4612440564400c1e04041c080b801001428000f4040c465440507805001c1c001900d0306900180d9021480b03480c0202d100100c0c810420341005100304552041c2c02d981d0002c0d41141c02454051024183c02015041004103507400d00c40440035896050500f60300b60070059020076584c80005982d010f202500c81d05503802500504104003c1005403e030540d07034034080c20020844032800d401c100c00070381a600e0403402a90142ca0450381030229680400c05005c1c600c900382000b014640b0400758000d4101d10a200e90024855003400203038601010b2811580c000b40d10000810716414291300c841c0ea00c0910070300880100e801850303217 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 259704874 1250 259703624 259703627
    0x1507140706021c09061b0f120605041d0601060315060e010212160506010803121317210609070e010c150f0605240d110d0501080d0e060c03070f1509050106090507 71
    0x1420449410391511581003031413174408c0711498081e0540c0c820031540d444005c2840e83d954018640d03a0315403480405081854810628288041a440075051600d00314200c01816240b504281c05c941c500d00309121103941c80e0380180d04140076113840d10801100061414403070605003012280d560700540807526241c3e2101031480d070344e101d46414010782c50350400000da100303d0a0342610071414440c0440000a000704924407410b82c1102c221000035500040d4001112003403102100e1340715904482c3d00d0254145004068111500a01c555040280f0b04004009100c44480900403071301e0091800c00c001e0440d00c400e900100a1401039074803c001c480e14a0800f04a040f80c960f40c54001c0200b00303440c2c170b03c2181c1c0003c02002e000c0c1c805000740c0d00621061107200c5007031080a009000711000342510040c9910010b00c1c250307405100b00c1c400c0000380000b1041003000000d58060310303400348028418480d1410103006070101c25a503c1d600d141008135403005c005041d04840100c2e91141030922054554880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 259706124 1250 259704874 259704911
    0xd020609011a0f06070f060e0607030c170c030703061e060305010602161e030b0901051602070b07060b0607050a030905100e0f09040219171507140706021c0906 70
    0x2c0b203a409030300304050454a2900e4401001414401c40042d14001e50f03070359820040d1011401a43d0f202c0e0007510401c03501e41d030103000b0b880b013000c3d5501c0c1a41002d1010f503d10000200064110401e03844007200144a1074004c1c0e000c0805001d00114a41c190f0070031920101c8030950320301800000a0410000082d06400010030091001d1705903104903603035080910f41080512125400038881c43c00c05000008603902280f041e004030040360000c581450304981074a004107a04041108540c0320441c1040004900002d8608855205c080071859030600000030302c5c240641003014000e0701401d14842e0030140c0000301a401c03a9000d403003c070321158030507a040e504160700070841ca4100300c11141084284c9080014a40e0252005040019050100c000c00e83c10902c260080b50950041c80040f586c00c07682040301490840d03206003022202c1c42e060340000c1040603035406100c4107140125459040100c0d540540799251007140840c4001800c0d500d55001400d26008241d03a0306d0318107498062460704110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 259707374 1250 259706124 259706171
    0x708030d11091e030106030602030103080705010c0908030d0e070f06050a08071409090601091802070b010b07020315090309060310051011030a0f03091707140d020c0607080c0d02060901 81
    0x144200d00883d800e1440c10b14150012020a0b450756940d03c0200014000344091400303980998400354032819580344c0a421034413030201c6407007400401a01000611800801c9501c9071440940102c0c54001081c2414640300203600800183c090340f1401060240e807100107000c3c0c445551b40c541c0038988404000307580741e1020410f10090450100040b86d003e040084541da08580185807140140b41d0b1421180e00300040d091540c1c0500c0e4001a260041c09040c828203400341400590681c6480760550020382d559241400c4051280d0702c06000498400040c802e503858200003504003696443c010081801c544250b010310f5200c0d641d40240e00345514403c0f840c3c5010100703404003c2d45080501070b4103940d4201d03070607001401c01da00d039400603000407001c040315408903c078490029251039071407500c43c0c1011050404110b05510146281513581d500040c141c00700c1900f6510195294451705111030640f0403501d01104511031f070a5415082980000d10341c0c414451800200b104600c1c0c00b001000048405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 259708624 1250 259707374 259707379
    0x4090302010e163c270b0a03020909030d2f0702130209040b0d150c1e05070807080a0215060a06080c0c03090a09021305090420120708030d1109 63
    0x300301085484c0100650315040001d000246501d01900c500114031403600f0403007080c4650180441002452038408a010152440c14007803601903101103510b40c0d01c1448064410911000443d082c3c0c08140100d0b00440e0140c8010301800c1c1c4581d142c00d4808621004a0b0b59240e003191a80ca002102602035400c0b25500074040036004d0503611282c0040e41002c9200c640c0030390760b2464015141d40c1c1080c0d5100b0140b00c0d245120f80348001e000018112607000c1a8441803000021003203a0285110034030705114402c0d070805035100c0f469820400d60500512200a101030310020303819005903000034286559012944c86107409560796414044880150301c1101c001c03078040c00105110f110804041c22006817020110790a04843da0b0000703409818550101642c42c1e030000f88102d542d000000305401625080d559095a81056a91800c0c51141e04c50a00321349805104075452559614840b843c11078040011203103899250185541c4aa00447c100074a4174038007181c1e001000400382c2500c1c40b03607000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 259709874 1250 259708624 259708649
    0x10e09040605040215040f03060e0102030c040b0a1812060501051f1d0d0b010e0a0207080301091e02030a14060a0503070312020127060f050f060f0307030204090302010e16 75
    0x16695041c020b844050002c90384428095610450740c0380c0c0d00f024200902c08181d0a1144904d1404c15100312481c9420405a990040040201c1c190840701102c048940c451040c0741e4920940c0c0c0d08840d085000440740e00c1a4844910002d0540c0d80080154807040c01007104000341c1e40c0e187e013004004071207880300c55108043c208001103030034019904800c1c031540c0380c00b4174008504024006804081c0080b0111905464500103106058490b403071198040c202c01e60452a11032180c8401c1254081485104051a20b8119822010790318001458210305004015034413814000c42c3c0001425040d003514505294080002d102d44c500103c4a404603607000d005080c0e4282551221600f00100740b06050640d0341b42c0000c7e10b010440e2080842600d082d0f040011261121450528252007900102c4444942400c0a1101c04000e2080e101d400000465080944451040c003003405c14034a42d00c003a600c245070000030024150113420200d85510b01e0400c0e0744882c118041004407481d0383d03005030200d0456 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 259711124 1250 259709874 259709881
    0x607030603110402130909080307080c0405090a0b1c050c13020f12060613060905100c03170901090611070b06060307020d1b12090504270f0606080304170705010e09 72
    0x241a4004d205500b02042802c25031500c44091b001500c0c040401140c01200000822841e20361005100340c00c41c40501089103014074040003d000031001816900d0300703560340c454000243c0d6803525040c201d1a24902400b40c0c3c8000c50429540301c1241c2c0c070003240211150301520340d6091580c42110000c0c000000c034507051010482c032402e00c0c0c0d1802490f80f078121508000921000c200741c8000c0000b008181c1d11940000e040000340030079980150b070150180400080c02c540001d0700482564280d0791100074100d4a588c3d5280e0841c0901070380070025100f1482c0004210b0010010b000900815004090101040d21444103000b12444204e03003001c0181c00480c480242d4520900b00c0e501e414403040b0503403005d07224030340310190a980180201408600c000350100510f08050007a205250320000c066005060a41d040c1c403104da540410041c4480c420710300e020100202d07503004101501100007240d84444d1214070722481000a48007003c1140b182e240d000440d98400d02c0380541508020748920701d1030f04d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 259712230 1106 259711124 259711129
    0x20a030617010f2706150510080a0b0d0b0705090d0b0112060f020c0a24060b07110603191a03030c030a08100e01051201180f05060703060311 62
    0x1075868070001031a8244401c070a413041d41004000c1900551800880112030b40e0f034024039407000d15203001c2601e031075004901e1031007448081c2041002501180400120650062004240a540000040720315105030040c00c4004005801c83e5070700031880d950395101440c240c00c40499204001000020701c100c03405142c0c0a4032488008602d8000d14003030250b124200c41001410f02c514020b6401e1032504022100002103950001c100410740d166400c010780c1307500c0f01c01c0c1030300c50104288000c02c2c107140c06821240146010018401d21440a81c540c001902402d2070b0841c200340314040e00642501e0500041100c0a00307500611358a408c61071000d044410f010f00910920f035400301c03080c460512140450f50541d142200c0001031466040c00080c0542a40701e605200d01040051510410000214a0504921607801d45016030384404003202242e01920026200c0400004a4861030 = true := by decide +kernel

theorem cover : BRFrame.Cov 259532374 259712230 := by
  have h0 := BRFrame.cov_init 259532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 259532374 ≤ n) (h2 : n < 259712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
