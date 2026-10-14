-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:21:38.33351+00:00
-- url     : https://prove2.me/submissions/e99b1453-f326-4ced-a10f-9a8a52a9252a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 272482014 ≤ n < 272661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 272483264 1250 272482014 272482019
    0x405060a031104030809030c120309210703031107060906080c03060d14030915161e060203070306061b02010903171c15290307090e040f021201181506 66
    0x5190340d0b0064109417112100400c40036451310b01000b00115000060750f1074044042c12083c17842d503a000300d080d8a4481e80c6c4c500e80e504200c010040303d8191a000e03000c00c0300c6590b0794a00b0054190316003c1c50b006c2c0c4602032444041100e50007080382d402203807030700d0703407054550b030303280d06024030140c2014080b9580900e506100ca800b00faa80c0005c036591a20000245030f942d41501e00b00940b100058404104075081032040745010690949000d40706508040e1001540e46810990807545101102c000c100364070120520400c142d060b88510309544458541015076042c10340401583ca100300340c001e000a007205420b1000a1101e941c3c481e000d00314414403410910803c40351811101040c01c92a0001e550f5401c101d262400e1090810080984107070743c2241c510200c21906859619482c034141c409000000705040e43d06c2040c581009050020342c0028501b001e2a01040d034100d2010242e01c6142e902110858104d818401d4800e00201c803d92400e4266455031a110701c1d81280e0080c48420303640341e900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 272484514 1250 272483264 272483291
    0xd0905062d061c2f03030d020c1f050601083904090f02071a060307030605040f06050c0306031c020a02130b090f0a05090114060f0d050d020a060609090201050405060a03 74
    0x30b83d85001d1151310700b844042d4181c0b0040b903003001100840550464040c0710703444076403000700445940c200065800b50fa2104a802c0c4107240696a0700305108004005106100c80100c0c0c0d4000c602464003640d0b20913743e11481c1d58030701810b00d48030000300e2900107203202d01c040390110314080b40d4600207410f140d41069170700c141920440f103010f041d4015681e0005200030400510b202c0015080c03001e0704024556041c1000032aa84010501004022503642c1001c1010302003120146c0c4e030a02c0c2d00010600039445e1102e0214134640003901c24a0183c0f1404c2c0800c0d0415000c8142130120b03d07403e90080817111529020400060130a02c00f006555603182903a4000703454180b80301e481444a182140c4460810310400d02c01c07600010040d0010b41d2404458003090158281002d40111044950030350307001d5240c00140240b0049a001001841000d0041000540204d4205c240e10300504081181c3c60385c5114440c103841d483c00000307000460030081440f0301d01e04840a8080c440f400d150010b080380100d840c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 272485764 1250 272484514 272484559
    0x70804050c040f02091912030c031806200109020f0f04020403080d0b130603020a05010804150f27050a060e0f011109040b0f0f040203090c0301020d0905062d06 70
    0x5003004000e0300050303603003240c1c1400b10004c00002c10854011440c1450f1111f01400c001c2c40d040010304020044669405151040d030b0300700840b20050300c030366400b04d82e03c00003d04040750304c01d600e4101e10702c2d00011904415061003250305960f0060010800c80090404021840304012601a0b0081c5c1c280008030104840c0000b030146800080c42c0012203c1200e000c000045000480014000d414800309100603102d217030209003102c0003802c160b44c107a11103160900d1002c82d548c000c403200b1440e00700100c0308105580c0040001c481d2030000e000c0403003000d4019582e86640030701d01030700e1740d44861840d01c00030f081076012840c000c081c0c206a0b0200816075542c40d082d2000641d48602e506004907158509240a202d4401c050004964000c0a4403900d400314000c0b410301203007030b80f00b03c1c0d01100048000e07800344450610480024002c42d034680c040a40d00c0020421a18262030910501000400507520103180050400c12829a0301e044145010081e88401004001c0c50b0000000060414cc0380460740 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 272487014 1250 272485764 272485781
    0x15070c02150c0f010f0b0307051005040b070c0e0901051504091a0405012406080c2704180803040b09010605092e06020105180303010b04060e030c15030108150c03070804050c04 77
    0x41c0108503000e280040510340409500274900c11424040c04842c0c00340c0110854080751038848010b0f8072051a03040030550704503503a01480841c403044040003000601984407034480c0d0340654450a40c0384007482408215246144010300e01d4a201084c0400245400c40781c0354401d100304000b0405071200e03c98284c52000500c40b0081c00c001143c0f0900900350410300c500e074020210107583d8104107642c5c105020350701a0222000911804800020080e29603400c1881d0030506400181c2000701140391040e0306920440e1300f501c4401c601c2003c104110411b015034000c4500081c0301c0c9005446203900340d90b00403002c0c50301c40b2202c0c1c0218a512000010030403d04000e02c034030f8000040350301e4050000b0410b4022001c941000b43c200308010321034610388c0829641036904518048580d2079aa001192609c801c00300f45030350200c50100710401001c040343c001c60596210b50240c400d4805e41c5071140c000306c00c080d0b9402d800c4100c1480010260380c41203280c0e44d80305006404803110200c0e1100810200c03425007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 272488264 1250 272487014 272487041
    0x6040605060703050301080c010810150c0b07200307020603180304050405040f1506050901090e1603080a0f030b010804061e0929060306040803180f15070c02150c0f01 73
    0x100c0100704880023840020003010082c00d00540714602a411004810307064054201210780d082e013140407040c4244103500c07280e0f43c4a10400782c14209030358042c1c003804601c480c007002c0c14514070507018946000301c20795640c0381c0e000c0c10007030071519518141009041d45a83d01074180c0302c180030004503a41c4a0040c00e0156000b150865500402414414080b8003001015081179042010400c03040e06c480401a0440b03403510030000724032808107030550906211800000b03200000303403004014461128010078984646452761807894210070401c0c0d040d83c0300181413034007250080c0b0009001c07a110760844a01030300c5642000e02036240c85000a4129603c0c154213a0343e8403610100454200203041210703442c5501c41c0015002d500c1c186001a83d8ae40c0001d04c010100343d00800440d180a9001201901d05100703681611101030460070741e82c0c0c1e1060011540008151582d022808440c09076101d007801d0b80d000741c40e41802d40c4000c2400e1f1403562080d031807244c42d40304490094240349428400e10000100340e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 272489514 1250 272488264 272488267
    0xa08070b010e06040219080702011401030c091d0316140303040303060f14030a020f0103180f03020106051c0609020a0b0c0102070c05090f010905070507080c03030a060b09180604060506070305 84
    0x1404121200b508005090b940201e20400032544d08882e4145010103045803403402420b1f03507541d0f960882c054520410021034000c4d040c8004010819a428000c00351009588100000300c002600d541000c50003464a01172508100300305081e4114014200d413800c5c0c0500361a000304c812140c4001c0c42c0d5402200e080c0c0010f0b646074414230100c41100074000040071001e8210017080405e80011f6114808914000c2c03041a22844541159000b500500e801d580010000c4640140c83e080c0031101c0c10384540110015445d01c02e0101d15072612500e4441c00240b47c00a990307800b071450b0b403410024078840e8000d9030300c0240780c0f8000906000440c000d00c2464000000962110b1407481d105029640540000d4810782a2004010504003901e40c900e04641030300c600441d964440f00010390302803291004c0035080020000b03503507200b6040000150b00a02d0311080400c165955400100484d002d8550b000f5403040301016000d0244103046130382600494010400290680c4d18400203080781e21503a8200d012400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 272490764 1250 272489514 272489519
    0x30a020309070f0503070b0304050c0d1407120f06050a1506030617030a050306090709050603040c06020d0c05100209010504080f0705010815060304080f12010f1404020c0601050108090a08070b01 85
    0x1040c8910b500410221501426450800c00000e4030b950711070060251a0700e02200007018031004100c09804000d010703051198040b00350804400161844901e1401441a100c000032082d141e901c41d100a0f81e0400c20138034883c0f1190351385001403c00030708509041900c51560552107280e0460382c2c0000d080c5a02c00042d041e00d045a0070011400185816100340c0060222410399a084822258040701c100c6d110b00407560340321000e41d905512500560341000002c02040204443c000b2010180d4515030211806001c4101040b144a80410030043c0307503400507010700305a1000f5801402a01805040081c209506e8655036803030002e81ca019011160b014510030011940c008c5032864000e0340007040580c10800b030320046091840050b100410303c3d540040d242026103008400d0303500f01c000c10cc4207000996521046008518031500031504107550010035541d00b80303010310807201c0402d10741e0054140782e032a04005440c2c00c0c00050606881f4043c3d251098000b4039810020095144215202d0382c1550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 272492014 1250 272490764 272490781
    0x40801060b0301052b0510051005030a030c031817151b04030305130512070f06020a0b1b070807050607090501140d050606040f09020702030d0e09040305090102070308030a0203 77
    0x60840d4003000210204200500180d1100c030702e600304600054540701c5c004220700c000c0c018900c5134408042c0440c00b07081c08285041d40305402485c0030b12072404060701580d8503802010f49a00342800010082403000c0c10b1680024096400b00a505c40d0090352205000d985030020f41100303020785103102c49908601c90041c00941315510258108901721416400315400100c44c0034070303114900014090000200c0c000e4001c1d101060780c040503041c0500039a2070152400e400303656070707452070003040303280c40b0040804580c0d075100050110000c0e400400b024103036218801d000108081109951010b510104402400701c0d094900a25059128900810103441c2004006111104540241e410402c400c12148651360002054030502056840c0c009040d0f00d07000d0000d1b011f84603a5006051612060390005150082607001c1c200301c5000350161440c114400600b00d43c0c40038904501940b050681000c9004207120750003800c018401070040380c80141d102d0f01c44c2801508100c80c1c00580c15000001c102b00d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 272493264 1250 272492014 272492021
    0xc030f0a1b050105041211060c0a05010c1803080304080c010c120c0e01050301060f03091b050102070509040503160828020f01061404020a05390304060f03090201021c05040801 77
    0x124403000d80c10701150070040000c10600c10f41c840c80b2034071810340c02194103110071103400c0c03880d200000b000d080d9580340b2050001e4949141090a8540d540b03400182c7c80c115002e60006018446562007003211941165a5040340c0d40016200780c5400c02c0034054154684400d124031941c88070151114016070368502e4401080c0d6901c030303888204002c0f16502c040b8440e6081003c0e6410740750142000b14a040310444100d004101c100c001921140745140060501070441e20090203458081e070035184000c0d294802e210f81000d00b030758000c146520030003426030203070520f10040c140c191040304114503001010080d13100e20081c448080704c80c82c00072040000718607010000d031044281400000e003e2585041c0d050420b0f50040c81805000c0d50700000d0034628144140c080f1042c2400490910035141e14080301d14101e040601040340017240801e2028480400c000180c1e0b00711101d550350200c20340644c84048010740940e61089065124021003002144900f40620501414541c7e032240c40314a805601400e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 272494514 1250 272493264 272493293
    0x40f1203060510030b03010902030a03030518070b12070c0b040506150904020d0b0601050903010e060a060611060c07060b1804060c0309030e090402061b100b0a06050a110c030f0a 78
    0x6161520604200980700c410f22590f086500e824000303140d860389808203024211400009525004111041c02059010b50050340100142d90a0304105640049001e03502c3c00c960040e00200c0030144080e0780d40c481c419281c15840003052914111100c8030b030361391545010b01034408840a0f000401080551a402541c4801c0341d001201c0c0c40c9941e0030103401241500b442c42c40c3c09080c1c0d120f02400a0b5441c0d0048041700c8003801d014008200c44c030001280d8a403210829111207481d603003817007070026044e8070511310340b484900c03c50301600d8103865602400500d5400100201c0741c0a444590840702c50b0340d0003c04400708106503141c6d50782c03441e151030094100e60906034040706041c0381181c1c1302c0c08260b00082c4079501d070708180e942d25801c3e12540009040c7d0700038100b076240300883e20364200c0c00c1c0d0f07500491254500524250240041c44400b020840d4850321401110b0015400740b0a040450384240954030400442d8402d607800f030000350000c01c0c10b081e00c00b88020142e50059840804210080155480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 272495764 1250 272494514 272494517
    0x3030a03090b060a030b13051c02010b12060402060f0a0e041b02060109021801051b06012403061a070f0605090c0f06090916050c0106030c080f010507051b0a0605040f12 74
    0x54185c25584d5442c590000548492040b403900e41d84c4100f041410412a030f4000f0207403503419160382000f00002c0c00782c101d5288050042c3c1a80d11400c442c0e120001d03609003c0c03035000348214245298200114200d8000ca01e00c6003c104445c014810a41c80b24424034071400d0144c2003884d5058040400a4985001031384552202841000f03c17a0741c00c0c0803003400c445034100c24a08180c0d5062103501c88003000d03045491000c0c847c098400005a8100c007035204103081050044c07070032412034500d403055044420b00e103d000c05c2da11b0140c9140c464040800010030205205103610030201da801d40701c48003118400c44041c0072550240000e02c61b03500e02850f08030320342c000c1240e0080ca021003e0002c140c6400c005001d801c0a0045102d44080203401842a0345000c03c1010081202c0303035403418280580c400611132340344a03004849c0403004e1301006000e40341c420a0039444070707880c00c901d42d07840703903080100c00900c45c40c1d0b030068180f02800100380307025440c0128050340c4001c1c0c8000250402e002c10030320098041c070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 272497014 1250 272495764 272495779
    0xa0b03070b0f07060b120307050d05120103121e18091a1c0503070f02040f1404080306010201020418050105011704050703020123030a0e01060911040b0705030903030a03090b06 77
    0x72003804100311018000112030a6458034514075208018210901c501e41d0b100c01e90101c003950801c4000042c10350540a0400c45003004070100c0107464500c514845014030301401001400811214070300b6003101c500e2403030b103000e07110090f14102002d4180c0014002c009940d0f004002d5400c0c5e03004114001512036940104060800807039103c82c00140a80018002c29005980551041c1004800180260041c060300e07603a807800d240000840b1000072049109a02d0821409198a56486400e0381304815403c4607250b41c4442e02c0e810040c0e000202581c0c11507408020105039000854444046000304000c045499410310001522141c514015103041c45d400c8410407000c100009070a00441e602070030318031141000f89d070b807680c98210700624444c10741c100042801240641c4c1c0c3e211404142c0c00100800c803480d122440c140076566409070b07000240109000c2803111508420041c2031491040b000c50340307088100400300b0b0440c2c0104c121701c0046603494504606001c0c030200440d600040448520 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 272498264 1250 272497014 272497019
    0xc020108060a0f090c0302070c08010501090c1b030c02040209061206030d08220f0804030f11040e12030a061d0108010e030906190c060612050111030915071b08030a0b0307 75
    0xf0988030144505802c1c6521600000da4150103503040382d500c65045025440e003261100c524a010309001c1c4540746901d4545040070b000d1034412138007491032480c010340101c00764403113844c200d803001c0320b40030300303076031096007000340301a50785e102401072501d440d100d1500045450058105400e2200f544503c50a0008150800002d01403201d101c4000c42000c80510220f5140f500f0300d101010700d60040101002e40005020051000e400c403910b0006100d001e424041404003828002036403d82800c021320f60348941c808500303c00c624006198026051071000540f1a0f0b41c500d41144404160710228000d410940117201440703003030082c050004009001140b03819049000710720a8803e24800c84001082d21000301d1085100e80c080100c6290011004d20540342c840b4504036411000703031011100356107080d06000c041c2da42c0c0350a99101d0300005001d0701c42a482d040070303c0d031040401480c800c20424168100c40d0383c8804064584040c5000791841502ea1800f030064404648840d41001e00c6944045002c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 272499514 1250 272498264 272498279
    0x2010e0433090204140415060e150f1201030510150b07021201110c010b04050f0408090d05061e180a02012703050307051614040518010c0c020108060a 66
    0x185500312041c0c0310401e04240245501e41140d03810390065403205000003400154070052410b20055024119002c1101d494054803c5101280c6445100045020407420f00c0491030800b40350081e072071084092a1400c00341000e01c076080c1d800300801842d143d00d01d500600520108100e1070300004c90b500c500b001402c11015101000c0d00f41841010071003440007030100c00b1501c0c2d05a80b280a584254003e0055004201c0c24005503048502016010341c81c01c989206180707000e020302405080e150047c05450340719a204d01c082a030100d6407207a00b01e6403050a00001880c100080340c0b181140104108210400c1340c80030004142c058404030034000a42c003403503500c1a01080d0705500f503609080c02100813180d0030100340b00c0786100f081c14401c0a1214000014840040020607000703200390300340d900254194082c00e42004085c01034095005c0d0081276010b142c00d2030b52104d03411141040c1900c1001ca09003400a013035440d9001043c0000c0c002e12801021541c11549403500040101c61030b0401c00d04010300b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 272500764 1250 272499514 272499551
    0x305070e0429060f040e010905060103020f010c030e1c05030c0703030813021822050f0f0303010f0308070303020d0501140a08010e2d03070b01080c0303030714090415090902010e04 79
    0x70213210307480c1140d40100c0d5980e41d90003150a40d40c3c0d14004d120306101410895298082440243c1c055545a0b0940b00290b103d144100009985511248030040c019002c0c0801058400c100001940d8080c0c00c84022030010000703007260741203400003443c01c02d055240c000c19048ac06000c232410041402d00c410300603030302d154801c0c102043d4121100c4140c0e940140e0f41c40c0b09261190f004080c0303030711800790b40184800850640c0f024030411301110b4820b2000e015040e502d103c24403c0c55008000038005000143e5807a0040a0301da000c0c0c03401500340030600802c0c204a0314281d01220181040b0030307540f8420f09288403220000d20920000b00320b2100800841921130104180070140e10003070504052441c103a0807585c1141846400c00c46e6110003051074000c8142c1030a0042a140340b10340c5222001d5486c000044900c15503161361100400490458510031540207609410f60290301e5500407008450003403004001000c000d1004220350402d4000940075500000050f8086d508001e203d480900c480c15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 272502014 1250 272500764 272500771
    0x30e0c0f040209010306030b15011106040b040b0a091e020f1905010e06070609030216120f031d030615010f030501051509060f0a080a0b0108041a0705040305070e0429 73
    0x840c0503950f41c41d880c0040300101800c2d0402030800142200f44442c0341c2860564040310a001e1305d980d501c403185220140d5695004560040c10b40c0346100005001900c01010260004a20900400c840b4603642d664050344000c0e1a20910701e65504003400e0a40c80c04031030301e02c250f001c16501c01d500710a14074040103007180c482c007559040c030041003280b107000e80705c070000c5039191b45d0841010024002c0340c5c940291150311444141c414281400e40c0482c0c441d1003071034461584d030b42c0030f60381200d4040581e50540f01c0c4908001c2103172418a001902c00041d440502c0020706c14046403c40c0c0c0c4100c221000050400b240d4100c140e401c1502e807100520440c0c80c3d902c415400d25101403515516034040b070001524504c101050b564075071402190580c0000e41064810b400f13401508800d100ca0515031004691b640c01c21600a4a20b41d6040da00b4900b0401c04442681c1021035458041d10740f0351aa15020b25240b03440d0300032200d000c07a40c810072091003441c40d2442c00e04001d00914140140701507a28800244014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 272503264 1250 272502014 272502019
    0x507030f051804050a02130b133f0c0b090d08070212030d140105090f13060e0d0203040e010506130608060607021509120f1011090a15030e0c0f 63
    0x41d00b504403204480300304402e00d0002c00900042c90910940c10181d0000744140301d9a0507048404510b226200701a608180540e054800c20030340350450350f403a0002ca480050151006104402c400c0034920000400e21250b10301407808845484e24110010f03040f268810180c166041c0284240d5a0f0b658003d5010503400003141501c440e80360001441c440b00385c1e90805401c3c4400203a40e0b15032407181e04280000d01083d517066640b40c2c0e8070424014408411140e25440e04c0036503000030040c8452050040c00720b070140c200050000d500d120014940341202c8428805a44041010170400461514640c00b400c02500d1580c14150168018080c1c0e01d21030050030103208603140040c941d0780720f0b0000d40360150b40090500b03d00c4040414807004030740c04800d006000300610304140c241c0c2007000419100040800c0000c0c1010004215010b004140d030008480000208120341004d40d50350303c02c00800340201d9910a001c011441001404694a200c5824107503000b130000c100c86651440104902000c09 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 272504514 1250 272503264 272503267
    0xc320103020903190c090c1d04021204140705060d14090a0b01030215090946090c230a0e09070312020c0a03030f030609022517030a1b0507030f05 64
    0x2e0745003c401e05c101e2604006d41461901c451804c2070f540c022403190921f40580030b418080b400c0708003400164030440401d0b9044500090102e40010354601c003124070408100107a500203078032440020314651110f901080110b0719900541c110080141005802020f41e5005103843c0c0000d0b91284620b00f41488084d1050044821074000c2c8002441240c1c919000202102038a180070395690821600200c10746007100002070000341054180d66205c00600140c3c2400741c00104039a07920006403420f100101d40f201021100011640b55142009082c03800d0f0300f489248104008060000131038050740039803030140c1408280180007002141e541c0640350840d84070849404515402c2e40f5116005a803642c00113010034001052503440009a014090a541c0a1110540c5d4244100680c00798000c01072105000303405c00e58a5190005003141024070400c240034201c032a440c50440142c00881c0d401461300c1e1203c100031101c03243c2814070400144d050030002e04140c00d5880060103160407880e00c8003800310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 272505764 1250 272504514 272504563
    0x30606010c020d060903050a090603021305190906170c0901031101050a0c08070c1a040308040902030709030209090d030507080c03070c052e110903190c320103020903 73
    0x5403e490031141c60340120303080c4142c444500c6c3c000c0990748148020f00c00120081c0021425500c68001c44060500403502c250606082c80c080012608007400711107500a188140000c5a210f5402484c00504400b0164441409100481418004c5100752035100b03e072004018000508000380100d81d035042842c0203900c07288507420235156042015000340c00044041800020800d8202d590415203040075011703034695000c01d881100307a00403800001c103c500144014130056003da40519482281c5290480d8526580c0d004904914019200c0c031515401c020b15030300c0800d400d401001c1e00710b82c0030700d002c601d2454201c8103007006000281c0100304000190100c032040c054100800c0c0c1c1c48100825580cc0700222100f241303880d40d080078000c0c540071420504025000b1b00b011043d6440c0c400042c1c00352895004011a411071307806003001c21030307100e5902000811804e48031700311506140d20081c0000b08a466511100b800350117106102410140100500c400356100421062207200d00104400340c91203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 272507014 1250 272505764 272505769
    0x130f0518130b01080a030306050103051501030f111b0c0303030705090d0c050301050c0d110a080115030905070308040e0609010b0a0309051f0501030308010905041a0403210b120c030606010c02 84
    0x210603180500b00d40c1d907030000410601004641c010f5214460f403010856250703101d005505582c0d003190f45144072a13801402070029402a00608918400300c00d000901c81c0121842c040c1503000701400222012100d01404100c48080002c04800d0740c040b0029401c41c60305510041c220320404810b80c1c0940481d4850004015910300d40d0406058010001d01c058034110021040b5600803847e4a80c0d000d00740408400040c1c2010100c074200c0a8a03595402c06a00304030000002d0407a00d01a107007010303a61440e81001c910103006002c0910312607804d4035981c1d032074010b1b00c03144090301900b00307445020110010041100c2c00030450709076074902e00707000c0760000041c101141844c90781e807400034420b501c0ca610001c8030081c1e0790103107050f00e21907103c01d040c507600d0307040800840c1c6080710018114a407001590b041000c403050300962040c424030f031287c2c2520510240654142105003425925900c4d0703403624a0a141803c401c01c00002258000e041c101131401c000784e43c030388000d408641881802c44e488819034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 272508264 1250 272507014 272507041
    0xb09060a11010f020d0b12190c0e040f060b040b210c0a0f0302120604030912080c1c020d02030a052203050d05090102060705042303160803130f0518 65
    0x52403090003c00019044040c620060350250584542c468601034240140f4900b41100d0310317220f1004002050f40d6010343c00581c610b91442c40c416140c0442e1310000064034070038440c15600c224800c0400700f0a561151402805441001400710300c20f60412000b4080d80e111110080524070541d81d07443d0b010440c42c8515418005165a21b40d0806c000b45d601081e003020045510044900c00d40d00c00964544000140352100c605490003400036200c603200308242d01f040c440380312009015000f02843c040ca4a00350300d240681c181402c2448071000c4464441c640d8060014409440350390000e1841e201105800038100c3c41034020152141e101150080c106140803c000d1f03010b1039000d012502040c11209000d0450380000c500c06005200e8040001c5e00c861017841a102125003a1a155980c80c0020020348000c5660110450b0580f0034854149a10f40c04400d02900501d181c070090759666400b00b2400c854000590440c15040b070182900300320356202d854001010004aa01410702074a400054807500e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 272509514 1250 272508264 272508287
    0x90303061e130b15041230030902040c11030d0e010f0204120c06090b0702060703111e100c08010b0a02150a020405090f06031e15010e040218010b09060a 67
    0x4001d014071082d0309a4158000d01c54007004a8510040190030b6448007414440c80c00307400060381c1125585000143c42032440400704c01034691040c1721030410400304182d02840d07144440043d481700000700079030429200c2c9403801c00b070a03d48150040c001d400034a80e43c4c458821800151541c411844140030800c0d808140344903401c0d070041d55110b40c0c0d1000242d207000d20143c25146031072040e00001e5a640905140c108a806844030942400d030f07071781c0030808140c00165041d814091075003c42c00100c90180040700300000000000540301d9805601d50f072501506049015401e894002c40540f00c541181590741101c1001010340d82e1002074503000ca041940c078180d100200e80402090101d840e503076030090030503107074180d9081c0e84a07075840c2d00d0b80032490307800e030799041c0c1580003802c0c8a48010f40005001141c2c003440401ca80c100d06a400041c0841c40e402d91095810050580502046141500325a5a15041c490892029504001d50300780c03030740b0554a80c240700d050005481e40c0941d008480626030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 272510764 1250 272509514 272509519
    0x10501031101260901140a0b0109060302030402041815110f031513050403050910180306050705120a0914060912070609080a09030c0801060e04080d200909010608090303061e 76
    0x10a400c10740c03005406003041da11903400d4030795111b00140054010b403181c50f20142059403440e00d000c1ca849010350080d07001038003c1e078004c0c0c2c4035400203c0071280101c0b100c0e0000c1c840e803c0c1d0b0510001080c0360134112541000c044c10145400c100501d0180211020340f074008110801c420040f504980015a0180481007040c1049040a080000b0b240d0020040c0c8503c5506503002071070620044012203c0300038810307800d00e50411702070062010031300c2039202c0c0c0d5100ca80c40c204240b030941381c0c01c56041c1d010400c82e04415802d40340e80301d2034200100c45c07021200d190240310042c0414241052000c2d101d410070784010b545800d0108140c0c0500c07249420003d0030701e07042214140d4030b14424000074090040384c04140c49034900c5950002e41c1001c1442100121100501c5000036501c03256600c2003150f01010400190755241c10782c0d1010281c0140d0310105075070b505910b066a070600d0034140100f4020503032081080c042c0220030040c01e2180401180d038405030480e00c0c050050300f141610115010100d60031174 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 272512014 1250 272510764 272510837
    0xb071401052a090a2408010f32030109060e01110301050901090e100c0c0302060108030f09011b081c06270b03070305060907030311030c0334150b03010501031101 71
    0x40241c01c50a0f24104804040c0e46c803201d2a0386c8400b00f13140c141000d4481e2108601181c41c01e50503130700c020388160950070701c541682500e000103200000c0c25990700402c141c0e1425030f1802d0303d0510345000d01c1a811640821ba80d650f0440d85050300207800a0340c1442000c00f595114003002c2131300481840f01000022404400b0800b0911028005203600d02110048000d4444c82001081110001003a260101c854031079140c6044800801141d01c403500545020990f03940d05804070000d074a00002d05040540c0a80c0880d240381300c02c2190054aa09601c501048450000701c11845204007126010182c2c01d45400b0803004107400110f403410405500203440b9010798070500010310000b0407088120b034001c1c0e40d084500860400c0c50380c0c0341d108910580400760700822040391003c040211611002d021928104000d0004c1d901d0040d000c0c4c0c010108407102c4504000d0003201c842180300340301c002c1c50190300811507981595110305211058041030340c1030108480002440b421154100c0038001807002401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 272513264 1250 272512014 272512049
    0x19030c0308090c1c02101d0f03070306050103060e06100501020a0204180b010f15090e06010e0a0b0a0c031b020d0b0907120503070209061801090203040c0b071401052a090a 75
    0x1901c085410b10812032085e01c1000d020050984100054031303521841c1f001115000712003808001002c1080d8004035058000c0110010214031a40b00d41d500940c01824041401802d6042690400500401140f44002d4085080c170890340c0c0014400019a070540700002e0030b2800340e411501040c0103a800604400802c80040b54403006a1181c0046034807810304000042c1d035022095070681044c0c000c210540391781c2000181550301c1000134600f001e0b80600500700342c82e201c03550b02059170312090071034002c038110725205010550b10084190400001c80d0429000701a194000303010700700310b010050030040300180410306214050110b200101000701e01d1074000b91031407410700d8481c0c00c5020145e200e128001c00180c071900b04044c52580b22018010441026801e0a04140007500003410982e031a0035290700101d006c0e0900e000400f056401101000c04078203210390303003e01b5118022b280f0000070340701480c0301044041d5000c40c00e1000d50030900c071a0b00d501007030300819844481980104101450304080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 272514514 1250 272513264 272513299
    0x1204140f030307050f010b0105040b09210a0302010b100809032a070305010f0e010e0a0305030a150b071b1a0702040f05040b040b060108041707020d080a03060819030c0308090c 77
    0x1d448400d1148020b00040d41d01c41d00542e270300d0007913110300000c07840308010400107450003d001030300c10803603101c5840134210b02c8440c40e4507200480703800300c0150f990740e0090415460440e00c0c48400410034070f0044107601d04844e1780b64990103405900110f881c00d44204c0c0441410701103400390140151701c00c8a0441d0343d20300303149010b0140300402e0f07003c1500d401c60b2081c6c1d01c030060090300301180386c03500240110343c4260350844e460b600081084040540d00c95004003010391400d40803005040c440c400d0787d2507a04500b041100400b500d00d13411510541d40d1300401042c504a0140c03420201603158481d02c035074240c000328010344000d03540032540901c0c040800081040c6110594025401841001e00c1c0390f035400010341f1509015500034210f102c80e40b403440342002e80f075402000510720207410206140f05c00e54503050360341c01101000307021035101c03002030001070000c002c2440c03491203a00d80802c0e06c00450f1400340442c0440d00025042101080000e0009081084020010354020b45010107100b540c1e00c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 272515764 1250 272514514 272514523
    0x17070207050103050a0216020105281706040920060d0606020307050f0304030b0f18010908091314060d0c0e1603060603050403090510020f0f03040e0601021204140f03030705 76
    0x81d8601003442c0c0000300d002201c240c42580c0e500088511001400d0003141c0042d1007507004159040300102010000c0700b05030704606800c0766100c1654940c03110240421080c2d003513a0344000c0070280039901e03211245000c00d0800040d4480180d4080b002c5100940900219041c0d1099a040c800500e080c10f40c006840744d400030041072170714000d0084d101100c0c1c10618480e00d0b4450362001174800300c40175000c960008010501c4607040402c1420129001ca0701049180c00c0d680100d41c2503c00420210310020700d07050022410f4812180c449041001030200d51300c80440c0b00c4003800050096100746140c2081000c0c40326400f000c3c02911401030301e1032521400903107100780c2c000740c3c846c0000e0070000b00280c0507000e4000e490013680c1c10744403131442506080600c101200881034210440c8581800600c55017010f011035200c8a210740003442d5124101034500310842001341100e0b045501013034118800c65002000d42d0152051700391184140c50b81000015800c1c1010050154180030029105041110004c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 272517014 1250 272515764 272515769
    0xf070206070c0611120f0a11010c02060402040f020408030304060b010e030f070521031c020d02121035010603170307021b01020a1104110720040b0d1217070207 70
    0x5039070000701152041600c1c2c0301c5c2100000c100d01940140030401101022102038190008107150a143d4904c0c240c0c042070a4801e4901400091b0f0000810700c401d40c03c060240012528400c042940f82c80e150800342d40e070b00e22000f0b10180c1842d50781e6140303180c13682c80b406c0030341035000303008048620000e01d5107009501c0310b91510816204003403002c0300042c1b000d001210380740c0d81040e103070185061800070303081156481c4090415200ca25820002d0f4001d01d041440908110001c100803a042d07450304080c81a1300724450f4110014103009001c80d0008490f113002c013041003909401001c910012000082405031040350030051507180d030000d90284018800c40030314450407040d400c462400d2204c04d41942c1403030003501c81c14016004040101d0101c3c0d0401c590250b00c03000603000281102d0405400c80042d0010402201c0d01070801c4c030003003031440c1c0342541d0317020100080380c4c20401500d0750800503c0a03400440001c0020700300900385041c2c14011008409601020407010b90b036880c112000075107641d100e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 272518264 1250 272517014 272517017
    0x6050a03020f0d020301060f0e0f040b07180e0705091203090a030f050102070c06031a01030b1302131806030311030a05041505120a0608151303180906090615170c0f070206070c06 78
    0x40c0c1161040ac1416000d00d410085801c00342c4c80d0100119507100038581c3e0714410b455541d000103070300400081154494280e60b034500d0344603c070580801000c0e90744445440801c0d4000e12510010759038580142c0103c0c3e9008a6005a0390710500d00a80039009500018000b40224540021140e415030094203065111905403c0200e00380c0300154101c0340c800f4a41d40e0404088a440180b01034135a00608502c61a20600e0000554626081d8480040c40300c01c0310b041d0f903c8d88801c008040d0020b100c4900b460740a400703942462410180203000b0b00445c8990b6240107051a9402c54141c001d0b01242d407200e2803911201d01c6403410071108030280c946480380b41a1489461401c900c00f01140e9907a42c010792924807007914014650301c080365004d011054800300d54983c4000014000030920a0704003e2290660106078a80b034251800a00401d080101090000d0b882c0081c6000303862800e003a90022540605a80b94148518035400500131444000d4010000140f42e50a01c03d070b070741e100d80171030b00f05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 272519514 1250 272518264 272518289
    0x501051c050a030f0306090e0c03010c09150e0406030203060a15090b130203151c0c0902180409080f0705030c070602120a0305040f0b04081801020106050a03020f0d020301060f 77
    0x41421011a1094030a024000d60000d8440c01c002a120f0003225811540c0b516011a000d03894808003411940001480503040d8008005021642800c1c0181e4903255024145111350625020086d14180d50304001c5004206048014a134143c0c0c0e540d200c100559005400c076070981c580b80c0d40d001d0050420843d40b124201100b100010400c05500654184040c040c02d285c0c1d000d10301c0000b0078065000500220742100c44144044103503218082101c40040320502c1c1e4104031920790518014900e101d030800c01305c680c0100540b4904108016510ba400c5030b055800044541c514145040180110b8000e4421300314000380203c10311500001410b442c062942c2a242c5040c3e50b000c00383e035103010185840059000500400404601a41c0580e80c40b40c010141c1d40c1c04286c1613913810054900032035040300d058001040f001d00c406003400804481400038002000b00500704800200010740520000b0701c603072005101d0b0340a945a25030800c00240e8060000e0041b5a2200150542c0c11854001c40849a10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 272520764 1250 272519514 272519539
    0xa110438090709090b040906230a1b2106060e03010509060f040b15270f06010206010b0c010b0d0b01180902130b0303070f030e0f03010e0709090c09050703050105 71
    0x104800220b00850454881e200b0b000d150108050151184800150b0310580e03510307001020483c2401400c1007110050402031144104208905901001500341210a803500c1d01194014207900035040000c1a82c1c200f002200c0c0b215003455112058a81c40064228100207000881c5a005a110325031b00c042100203220ba0347c0c40b132841540d100c1080b283c3c0301540e001e240208000c9403188842c00e0300003902d180b0464401c0195000300c0e0813071490040715020603440e60241d800c99500b0f940c03000d40100307444012150506000c00001c0d510745060040303102c022000920024149400d50003010f050300007820303200c9040c009090103083e02c0024420450c007640344d5070403503a0a586522444030000e40c01402203500b08081c030f20750402841d42d42d0407590148030800040300451700400d8000100ca10964421902c1103e000500203001d00c1c1e000c80b140240c2c103014869008100c0484d44405465405400042914060601031800c0e0b0342c5612001556142c1014052910351641005058035810382c1c00200341e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 272522014 1250 272520764 272520769
    0xa090203010e0727141305060a050f0d0b0106050301031a15100c0b04060c080708041e06020423040606020d020312070203040e0109050906180a0b150a0b071707050a110438 75
    0x31f504403400c0d0f500001b18030050000b440d14440300f06e01c03900058401c00c591485d81d61814001e400a03000701000c140c0c00300c01000ac010342c0059a4070389181500164189040503126070403c0d48183c11001e06c00d84000781d90240b020b10441d1480c003100d4003c1c98034503146c01d250822030001d268604080300041d04680c009072099000340d41c0b0b94007599111000d15040d034940031402e480c90a01800c1241c1c1c841e000c2100080c030a003a541240d07000c40b00d48105c0c0125a00b000100400c5030b103194481015900001c1080fa440c40d0040103480620213911034801e03156680002c00c03821886036800a030002003102c5e00101d42000954000e03480b03100c0d004111900c6031110f01e03195505550f07502452466901450300c1400040009010329007204904500d80d001000070400103032000700c0d03900444000800810b602050000d200d900d215000b18010501c0e103480c041e61101500c85945120140850405000c0c00d0741503121584610412100e00d044115980c44290344c101c811030f2151002c581440c42000303014442e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 272523264 1250 272522014 272522021
    0x2130b07021216030b0714030406020d20160204020904140f0f040b0103150603080c0a0203060c0903030301121406070905011106070206061e030102030403050304020a090203010e07271413 82
    0x9100f499814086450356503104c003101c40081c076100400000007031081000941c0009140180c0c40307080003584680c40002708004070741c8207040c84000b541064944010b0038103440100e403000d1384550055181d110705400400d02a200d01c40e05241c0042c680100b1003205070285030170501881d203d051b088402d880c2d038092039442c0c12050303c000c2d03d0568181d004000040113204c49003e5082800b81c0803421681e01e88482c4100d801500c03510a064210416840443ca024813025501c08240038003942004000c4012954a02050188160340e0030440002e605015501c51981a035100c4103045032418602004000c0003401c03284200b60200c2c5038039441c0c84d91628080b864038400d03001980102001d585444c10008900e000040b031442121061007110b441d5102070000f580710318040c2d141c0c144d1324100751040c400810301741d50025000341e01c140011310100807141c6201e60440020728150010716000c00071020383ca0b0b0b1200e016410036500d5800003c80340f6005040d02c4550804450041d8a400340c004100240c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 272524514 1250 272523264 272523283
    0x1e010b041a0d0e120307090602030c070b03062e030f090f060c1404030813050a03030906081e10081606270b0f03060f0607030507020f0402130b070212 66
    0xc015881d0128010700c440500544072000d03209101003011911414401d00f811031a043d264490b850001c10424070503005aa8000100281c0c1b0086203044220080c2d41d8550b4121301505000702c10010221340959034141c3c84007591048040c864001030303005a05c040790b203480744852402003400d010104060503410712942c039415402a62410341c1024540d140c000804a0702c00354028020750300f10180f40c5010490280002d0741c4141100e90b941d90441074210b10741e0301071b640701e13610943c40042e00340002540482e40f5001c40d006800d189025407290402820b149103544203182e0100d900500b00a01609554250000c071115074080d03c0c1501c1e040b6141e081c1ca6031103405104046100000b035030b4480480160b010040d581c5458100903000c1c0c07190009100c81d408000e103064103d90200510500b0315000711280801170003116075500d0013060344d5003c0c00d18021001c02910071070060340c0e503440e513407590b804031040b0024410341024000d44544038000c503034020000990040705004650400c404000131321114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 272525764 1250 272524514 272524529
    0x19050f1005071502040b0c060109050903040f0b0a020c100c0c050f0604030213020c06040c030b0a05160503070c020303040f0e10120b040501060509011202010225090f090203061e010b04 81
    0x10345205030301c3da82c441e01c203466102e50380380354204400241741000d1000360656240380d02c094007030313549071a0401003960310282c40600503800402003081924940340c00b18040360031a02c02140c503043d0200d002c0c3e04001c100340300140c110302c03440a01415180d1040e00904074a21590001d00701caa1100c05101000390036001954101c1410801403002d85002c0d510300e000d40441460161902d640c1401703403410481d040e58112652111400b003882000060040e00e980082c5e85a410005443e00000c151803200030b580812050040000100e881c451148002c1c000681c4c014088a0703a031581c61213040043c085520840e1b12400d4031101040280400f070b0103403012a00c0c411110100b58200b034417418004840580201e805640c0c40000140a03156400002d0007020320203040d4003000c90500000e0b0078000c0b40500c070b000044a011440c580e40302481c141000ba25003c1100241600300308032403900900035100f0103541442104d0401c01120b00c03a04034030a1a01282d10b03100002c1c0d980d0741c503185403401980034441c0e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 272527014 1250 272525764 272525767
    0x9050f070c170c1e010209030601090b0105040306050c1902061f05060f0f0c070f051f08160c0830070e0603100b03070807090807050901090507090519050f1005 70
    0x42c04070505400340104107510401c0d6108140722281c88031000c2c41c07941e264200c0c0e07500400c2c641010702e8240407082c01018800c400b130000308085000203110b8411400020030459660010a1240800005413002e0040d810042c00c0e904900c0c1e9006551101d048400c003c10914080000000090b42851141103030409004a400c09402c0306c4041ca86400540b083c484080061003660948242000008002c003030812003aa009401d0a09010400c2c058107550011403c0c00208040007507803003040d0070f80c0240302d06c4d11224021b8051a00326011200004050442c00001c10200c00034405240b0813111400e0250603411444070807000c900c0311050480c5e200d0041a04410b140e078640c1421002940e00c420000f030940c50b0300d0348416102c4029001943c0100c002180c100401400580040d0104090b00295004090071464640003500e010340c14000c2d00c50440e20740c1c001c03c50042c0030b41c1d404009000c1c01000c4840e501c1c28880350a00d0040b1034491544500300081500031a801d000500d503031029400c1e910503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 272528264 1250 272527014 272527043
    0x21c020625050d030c090509090c2e11190c06080702030d050112060b03011a190906080609010507050a0507030c0f200301110a0f111609050f070c 64
    0x1041c1980c900601d40d400c10403051040800140c0500c10340e80c4803081c589001565020302c0c0e000030040c0e40d603900702c00e001e0b02c60101880b02250002501084802086400e940703031741d05280e12a1943c3c044103003040c003110b07101d81030406850341140f8101d001660910880c0c030422440344200c1c91070070740090007514003024100113000c002d2141030503517488480d0b80102c03441c1021600d141c90803210241d1188401511440389081000f04a0269802c6500b044009101e1600100d1181140340e5500010510598404800f0002d1144614103100202541a000c105442c0d85003400c0303803201c01c200d419070420352801001404031801041a40c418405c3c40c1e40792406c02102765026600350389140390a0300d0740a20b500460b00000c8203d54820030040b0140202d41ca07210341102814251a07151b800c18940c18810700204120503842505a4204240703460911818200c62412604089201c000036013103000c2c9400100e2254200e4002e240100c0651030340f0509941c41082c100c0c0c0b2801280b000030841c68080180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 272529514 1250 272528264 272528287
    0x20f040c0e0114040f14090a0e1c030b06030112031416080903030712120c17040f020604090f0c09170d05031b190206070f050f030a06031a04021c0206 66
    0x100d24000c0b010b03080307511302900e42d1403900aa40856000d00032418508516000030b0070050b202d030390046403120007880765a00540b0300e170351a0781e05100d44464a0503140c0081308070314402d41094140071401303071a030b503030360358503540804a2001f02443c29800b054588000100030074048084078144050b014840868203030355600d5000076400f4004080d40752000780321400c0800c1094142450780091038503414414140807600005452100c8000414852110b848012001c09140440e51103503102d0f9500700e401d0071a10024049004030b03001496072902c2c0c000840441d032425400102110099204d50488030394800d0724803d184082262821030f500801500340c1458010400f66030446241c080c075011910040604100c0740d0041d43c0e8400200307440703140e16180c0c2901481380a4101019240c1a0524228000e019020307209100c41d40d800403500100041c0c075040e59901840141d40c0c080300f2120303143c040d581d00d025020002e0324242d01c114840a100311000130022040041694090050f50800501d10138 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 272530764 1250 272529514 272529527
    0x60b0613090b0607060f060302090c07150f0e030f071b060f030e0c030a0503120106092702070c0303050c07060801080c1c0209070c05060601020705150d060e1003020f040c0e01 77
    0x1007a80103202400341070005170981c081d94210b2010710f44005251407440c01000102d5101a04682e800441040700c44d011588902001e40d0f40510503402107034400341040308034000d04000c8405039960101207840780340c040d00c540041c910140104003200d6000c4610310710b070006024a00c112404145040d107d8001d160003078008040307664071f1405071441201102c0c046800e1001c2c82d001100d8a13080059400c0c5244581400b0034007402051820008280c14441900480405010605481d83c1c0c0400000c40500e800d4045501d8580e1210041131920703540e1501418507044142d1f90181c0b07005184010815a2048880758100c03101000140040d29100041c8181c1c49907610b041490150f00b180500050f844003c0d0660003540c442d43c2d2181c0b1007070f0f9814818180030019004070f045400c0754008102d117aa80d08018681e1078540c4041d80d0b40e03280020284402042580d01c8421006400c004100c1d004050b240208101d034000d071503841c4a070442c1c0081000302d030300114068002c074204444103801540b183c80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 272532014 1250 272530764 272530781
    0x6050109180c030e031603030f0902030607051303150603060b03010b030c010311090d0f0c1e030803150a06091a031905070c140102030412021c0e01020a0606030b04060b061309 77
    0x400190812031802400d0031035000c68600200c110030200002c01f016031503c964815804a01d00410114400d41c0c0000d07200d03003000d0561020400041100c40b511880c11000e000215442204075410100500c485809804a4071059400500d401c8a03070340c10707003410f006119201c1401005040c50702ca42c04015001000000451441c44800b84107002064841d05d60280c4564018220355107060514038114a00000301c0e00405408414410740300f04510443c0400f000b9260303c041d0840c0c903aa0740440c83e03034030b15411107102580b00c0c110703100001d10190020f10400a603421007059044611000001c241e1503c010790701060440c007100c14803084884a9807100350842050725043c1102c2850f40c544038401450040051840d950000070300c000c210f404680c05100940a0015240c003514600080403524030040341d04060254041e400c0500e60701c28800f210060307038451402c0007070039281e08043d400940211411100caa24040310044646800c00503070b43c000c07800340d4443c01418100b15004001e0f01c440c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 272533264 1250 272532014 272532017
    0xb090331080a0609061506050d0507110a0c091b02060612010222090b10020a0f1103030c06090106050109030503041503060e16080a0515090606040b070309060306050109180c 76
    0x144804594074034240440428075024001c007181410b81c3d814640c0407202070020925212044150400c0741030f400c0020340b103c010110400080303d5803144819150300c084903c004032180115501c0c8030400414500c65000d440d0428001c105004c4c00881100ba561001e400ca440942e000100055181c0b0380300d0081c801801103030780058184045a60410030311454007c605249006000d03061011440c10b103d122000101106d01d260205103024003e502c03124070720406000f040c0800d0449062201d1300b840c03241c5010001c0c0031265100050200756454403000cbc1da1b415465400c02c0000280340d1311032603621003a69040400f4500c2c051800d10a00e01e030040d40c1c40c190043c1911070a0026054814940040c803403100d92710305002101e0001c40040a034500107207803e20180c6402e0910503036551100c0c008071812000d0341c59161a4507600000b9a50b80201d6000021144001504104056100c0c1141c001c27900795480c03e01509480d0740040d14811418014445002000b201e42802c801858112001c004000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 272534514 1250 272533264 272533357
    0xa120c14030c0706110406020c03010219033804050105030c0303030c0d110f2221030e030f03041d0106170c070f030e011b0c030b1b04120b0903 63
    0x150303604e03426620740c1d5004254000b4003040822180d5010301402c1c03580305c0210300840c540284940c1c01045552079100110806540302c40c8001c0e588040b02c3c003600c609240aa0030300130428400d80100f111012045103601580c14040002001d06000461040c41c65008000d0b50540d991240c500125801480741b2040e62921260101100028070307008120f40c50f84140055a1002c60320402c0c015603030720003c03d44071910f58a00402406162850555070143c500e049440310084030704044480343c4181c400d880e07160007031f400491800340c00003008000700c4842115100201c0c4e100320800150401c00d106140114046140321a14071003080b2501394800400280a418003482e92645c16441012040440c0440d049a14140c45581c201c50b0f4405a003071184491802080d035940e4841d464411480f0052621141801007940303144c207000001c10300100ba8000c540c442c0e5440c046808007803600703182070b40c400241038080f412440c4003108840140742c40a040505988088040d9085141040f8014803413103103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 272535764 1250 272534514 272534527
    0x5070906030804050a0b03100311040e061306110705060a05040212100603030206090a050307020405040812090304051f080f061306060809010e03040302091b04030f080a120c14030c 79
    0x114864440070710300540741aa1103030b0600c1d09014002d10950841051468284100702ca1034800c0301c180e000380e951002d01c0d081c04241607008203020b001104510b100341d018a000704074a02c0b803204140c840340c0d80103d10901c01e181da128801d20082c415200041d2580e00583c1c0020400320390b64008a1b0454405080e222000c2100e0715640c3c00c00b00d2500340502c40a4441d0410024140c0c10401035801c40303c0c29010348001c9810707940d240d80d2880391140c000d00071a16200001d05105441050322944a11403041e0410b03460560700040d160340c0315010307080c4560303a4049001c00a907000220001701c0b102580f112403045c1ca8401268103103203002843d0641c0500701715103204901003140948030052410742c031500814200844482c0c00e442d108003002d02035900901003000940e03540600d1a4224030020158001a07004490006040c4a2a00082c00c0c0c0951030038414200301c01003000745144200d40d511440440c5450200c281507480c25507a010004d010307110840310701d415040055400c001c120140301e1034502c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 272537014 1250 272535764 272535779
    0x1c02180103050105150109050a0e100e070c0c0603050f010b0c01090212160e09120f0d11030403200615360108010207120c020102150a060501090e01210507 68
    0x360811142c2e40d4640b001d100840800302a1041c41d5407003400e10141050502001c500821598400d140c1190440004a01042c20701600c2c40f000d0444c40120345031501d0481806000c10036440c500711801c41c00e0350700002d180c5110784900750049418008100080e40f0300141c17100c03940c01c02001e1f20701c15503840300c400d0016940d010050b000f24a0500150200f101c0280e0701c140743c03200c02d030710900d1032000c10010817240720000310b0b0000d05540402c002d45c4e10703016580128002401000101100a860a012004c50b00b240c0409140308a21075554800368090000c0c1b6040c0543c146040d03000c5550220012409203c50400c500080304002f81c90040800079102035242001c1801482045e42075080e40e280540100c88804c050240100c40c009600d0040c50341d8980951200e500b00b41c00030004a00000011603100344030b20002c21080243d89255410808402d00080804e4810f040c0820044440080e940c907064862604880c5110701c4682e59040d440c84007076181d2940c600840f40790050343c00218420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 272538264 1250 272537014 272537059
    0x1180f140709051504050f0f0403090312020307061a030d0302160602030130050606150d0507080105030d090b030103080d060e0702060406050601030b031c05041d06040c08061c02 78
    0x514215401107003d0130040b4001e04440480c40c00c2a024508101c00c200e14191000411500800303c8001000a41c0e07460400f21042019038100801c540c2c02014072042c400e070f001002d031131464090300007040850828286061003010044030075805421040da0034103058000da02403c010100ca580d40083d48446540c0c803000c0707a200360418070b0075004100500a02030a0034400e86402e2200c0c000501e641003031501c5107980c1c0d40e0010032803031059445841c41d041c403000450a881d03400111940500c681d0400c42c90181422509004040c0039100b54075581841e075214070404802c0320b0304580c0407841d60b403d5840d201c8990f0701801c4010f0b07210342c45903400540700c88683d20f002d02c01c041c0f641c040c0c000350038540b4090060f140c01900c0b15041500700404055559030100d00301c82c4102003503010703207440c3c00342040503901030107203030f00211003a603140c0d00c0d031246152030200581c42084220b90030403c2c0c0b03050540540314800280c9146400070010240300e4620a85000801016400142580e08002a4000c46080c2c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 272539514 1250 272538264 272538269
    0x10b120709180b0406020a12090602190f0504030b060604081c030b011404052809140a050c040b130f0909113c09090a0b0901180f1407 59
    0x450340416010000082944540708440c0300030300a81c156400b4030780301c0300d00c484405400035004a42c005a050a5140a003550070048807400744140410380e00307801c0440094201045441c0780d811000b03031906130540b140600240c80d07a800c0e240c6905050a40d1504c61403248020003040e00110204800f00b120300b42042104660a480c0d280031422004c5c803000101550328018546051000300407100303c50a11107016241615815039144c10810780f041415820300d14150607a480c142c04481d00442d01c519990021080c070298154500500e840c0e40082000300d0700d00f154000c2c80300c1d009000c01e0207001c180c4002413004510814030300c00c8450304c070840309030020305590080b40ca00d5518607003001040010a036003501d0400454040440070307140307041710a10301c000e00c000740114258240001700e050b4000c03000440c0e81b54050803010592500d080a1991703021f01d11400e40f40612603e000600e55441400345942140094070461040805a551500c80808000044882400c2c0810b0300780d100700d040042500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272540764 1250 272539514 272539549
    0xb040801020301080d0201020301060207050907031d101409150403091d15041a060f07080c1e07080c0603100e100302040606030605210f1c030f06060c0303090302010b 73
    0x1d50f9490011542d203006544107102d0f0540e4010b100401c4015008181241190340c11303511101c1a03603540d0006c4004100302404c503a25501d061004200d01031002a80408072500041d08103d043c03001b100d090f050440890320002d440c0d00c41c600041c03141041017021500148242800c003142c58484903180200d401c02084814a00c03100c00030484820300c030101302c0b07000020644040041c09091000b01c408200b4240581c0d006404c0042c0c840c801c01c0f4500103d5105680089000b511103070100045629542210100408941c40320310503118a0f0740442d03108220782c034690080000d0700017030052001e26000100741c410000451840007450715421501d40e407007070f004000451b600c81d0452042004940440c1c100c90304142c43c0200038843c2d5110750f4018644d1102050040d406080400549031900714160310242d02c40c0140c81a41e0041d4002a01e900c2c0044510b44052004040022000b011910544200340003e40c0e46840040403e02036800902d07468002e1002090844101000c00e1000400e50500706 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272542014 1250 272540764 272540767
    0x20a140f0a020105011d1b090316090f06150c021f020d080a05070504060516060204081605040b0a0603020a0c0623090f0d140915040914040b0a150b04080102 69
    0x1e08865081c8941341c0503091200503050019140c1c0b06412602c000140400560405032410501c1943d40d80c054900c40700000741161508040c410411094203400d200329a060390074900f102c10001d55500030301d000d481c030100c0c40c2c2510504081c2c00319150520034006036000b841c1c04903011041c4100107500b0f8920501030b00284107030001180002e05612006211299542c9880305206100384e2000c01c883c100c3d803040c0750594441c940c41e42410071030300340000000c104910020340014401004101190ba01a004002c1d1202c04c1d82c4d4402c1c003040d20300100e003843d03116208000500040b802940030309000e0f402480d10000d140070301c0d42d43d01c045406c8070207600c04000720186006d407503100400a13103070304c030056a018140b04070600e44060740e66003c4150300000d200b104a10a02110292429036011850081c440e121004001003038070801d0307002e070003403500f550304102404601290580d0301c41d004075408080340c9896940c2c200c0240003010810030751100d00a003014002400b400000141000e8007400b030005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272543264 1250 272542014 272542027
    0x130509011d151c020612040615080f0607030f0b12011a011b0f080f12010611060405060705030901060f03120f0f020a20030d020c010905010512010306020a140f 70
    0x301d156a8000b000c005614604540100554562000c4040e1000c000e100d24141d0364140d10020b4494001e401c000810b000d5610200002c1c002150400c1501c0c051101e20260a030303071600388560b141e00005050120f6a8401808988500d10a0b07100902c04a03041070005039103141400000c060840411001045a44030311b00b03040c032040b200c02603800c004804d0a05a04040c00110020040b20130604081e1081c60b0b000108028080900200c80b01d070002d50100b1641c50701d140301007590741c1d4002c6c080c0b540050102a43c200440300000341d058003854100008022540da002c804071601d40c0002c04403001c65403039050000d1010480701e6400081d42c442d284601a00d1448074005210072407003844241007048150f540c900e8203030003042800065030450031070500700350b90342c8100c1c6241c0100c400301c0b6014400c10303181c56009a030100d080010075900340d803002229940c900c011240d0707000d2200e081c204060b81c0001000004c88940c01445810807034141020b4030100c40c452420a5000300040724458480001c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272544514 1250 272543264 272543309
    0x8181207081c14340b0a02030c1612090e0f161107270207031d0d02181014100c050f0303010b0301030b0f07081305070513020403030813080f13050901 66
    0x41e510448041303441c80b0700381e40b42c0d03110b080301c041c4040c00c1003003010f500002107100042204100c03005500020100c8000d41c0c80d074540815804000e6034824001040d0030000300c0d01590010301140035905d038181304a9a503c42000e9061182c00361200d441c148002018a8240d49105021001c0280341008030100c0044a10f000c4500880349840540e2200d0320401c18100017a8002e21344102200f920080c11001228581c0820840f5640c040c01035444020103040c05108031030b2024852041d010481e00440c415070361002d1700490501055803c1d0700190224200950f075108034494907600307024400325024000c0c00c29005045600c2070b0007010403040000018403d0cc00200c5100360005803080400350705180582c001801d580019004103104405000540c0911204004031701c0a8840100808480340c20184000001c0d88a880201c4c0410502400035400041e43c1d212062619007100409240404843d0f4503203c03035000360510340f51101c0400303000c205034903103c201c3e601800d000000c10120380e050003131 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272545764 1250 272544514 272544577
    0x10c050a08130218070c0206070605150306070e060f0d1401170d020307060e15010e090c0301050105030d031512030906031b140903030708181207081c14 67
    0x919082500600301d0480144c907200c0c000c00b8100c3c80100340d19480d8a6410302100d64240e8502d020798004004a105002e01600d03a01050042004580c000b070705002c0030090544440d800c0300c002c000300c3e01160002d20a41410f070f0041111030359401c400c504d4940315804140032602000c0c02101074140110040c00380d84084a03403407000c450110001d020709035848000039660f1140d12802040e043c3c131150b405d28088030030401400546406c441c002582d40c0c60b80f501200040c011200d60305540300b0b03480d0554140c00c0c1841514142da001401410790704401520540c00303000d100d5100014008041400101c03101451314086402d4880d584450100d0f280810040a031141282070390304e04604003c42400c0036803c41c0c1103843d050340d0503a0703480d11100000e000070f00714050802c0240018000080c005210a041d0941c461058011a010007840840a1000395180c90601a41070250305c0701d00c0c1c2034a0b10001c001c00e07d000d00e22519018014400c0503c0003903c54000c0c50144051010010303503080160403020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272547014 1250 272545764 272545771
    0x702040510031b030507060c08070b0703240b1902030c0a03080601140c0c0f032d06010603020a0507150908040816050319021302040506040f0305011410030201081008010c050a08 78
    0x4198208060868884549a034954031a95061143c41203001e01084540f49c151125a0303006030441000e0300d0680e00280240400020603902c129009812035032540003c24001c00703407003180040c141041e4036411820302d6504904820000c0d44010701008400c968200404500c0794466902c0e103985081801c000341000120400000c101001840b40a524880c0001c2601d180d1b402120f02c01600c0104a02007820700c01c03440c1420f2031883c41d5090640e510f2100c10429000c0c5210101120503980c2e90713410440c100c0c01500b0240000400c1080200701003004046c0c010941407488100240803050b59660f2605c542c13040d80404c040c1c2d0801228000040ca840498500801c820380c0680380f1207500c0030300c0e10303455101c2c540004d1003503110b1001c03a441250981e064034049d1071702403c9156181d80300e505541e25100a031008848640c200200e81750142800701c10300d0300500f0783c614001e45260940d801920082c800510b50096107050b0000000e010b8001d02030300840e2041a25419030310500c4290083c00e01d040103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272548264 1250 272547014 272547053
    0x11070311060f012d03060606050c24011703090405010306050a0e07060206071808010e0c121b040b0f040c0905010f0509060d02030720030d0518120f070204051003 71
    0x100412003d4050713030b00c2000c0d0440c2031448403480340541084a0f08865550405806207141a50100c3d095400c01d0040004010607400c6403400c10310550100369003142d000700c04088034003100c010815881401041e81d03d03525603606aa060045000101d400c0381c509034001d440158a40c418803840465501c11040c600120030081c10b0310301d08141c4041d54a510151281c810000200005c2c801c00d8144900407015003071a00080c8455200c0340007066443c4011914148511800c0f0804246050009586200c0e01c031071210f02a451300c010010030005045003204140c000019401e1080b050340c50f0b209058015282d52100c802ca103003444001400c0c050b0450000051010401c0304611641d10101a40c2039400c0b00040981e503907407005021504190b030411400ba000d15030414a48082e54040060106801c2c2184104460799500c0300510344088480909481a0014150980780300c0c600b1005101007240343c5056032a11500b5800f1408480080700d8080c0100c0082d201403040118980c410f8002c400d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272549514 1250 272548264 272548291
    0x50607050d0503090c04050114030d051602100e0d0609140c0915010212040602010207051203010b09040e160305010204170303070906230a020102030718060c06050a1107031106 77
    0xc0c0d56603592096203010040c144032001c40050000754042106003141800940f062000b540d480c8849201c1d03429100000b8420300444c240341800034030500607210f1140d0314aa40402ca44040d03002e10800301c40340b4150100300240c1e0550010300c0d032038586002c000c46200e144005007647c1c02d0305004032038080015103400070703821600841032250b803161b804580204001420340814120311005030301d000001e04103210145c5020400060f81764042d40a0718000e80130300142d0704903004500010980b88000d025a0998801c14440ca52050816a000d0180500360740d0465840040f15001052545503942c0b040340c1982d0006020302c420107048200c1c02480100718001d5046082c4403c0c060880b40160198404001350b952003400503440d500640c08c501024048110750303a00003000c0c000c0c040c1d401160307042c1c003003581501503464207121034202004070f8100d0364548006001e640e43e403102038031001d00528106926011070f5040454620020020399101b500c2d05c2c074900c0640c0b810107081800c001e1914050519 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272550764 1250 272549514 272549527
    0xf0d1b090501080c0a0e030c03060103081803070e0c1c060b0703110102030105090f0a020720040b030a150213240807080610050906120f1e0928060903050703090506 72
    0x2c0c600641d40c17940000e0070175402088510000ca460500e803840015454400c01c4000010b02036180700420308141042d218402008501c410300da80c4101a100b01440c0908103000144e080922102808210302e600e0b101c00c45003005802040103892068000204041c40003440c1c41c20143c104403031650000d0950f00960866140c00c00140e0401c1000b40000861500c40c4e000034840c08242d03045030f803036690000d0f0f4410007080680c40300811b41485030030715000d41c3c07500e455502c40d450f0004a42c000c1c55400241d000b040010072144101070342004280369100b031058180070a40400a82001c0f406482d00341c804900701c10024402040010040e050506000c14001440200e86a500000c800142582002691020b400f0085540c0b03120324035078445c40301a00424491501103401d0f00ba4020360903031042041c0c1e2282503112082007003058400b007006a0240042042501c0e000001c00c1105420808042e0442c0b05d07601c2d10810368101100880000d800000d41908042e00040203074050a01a185242800e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272552014 1250 272550764 272550781
    0xf0705090105040c020a050312040c06110d051608030406050901060b1804020901140d06090c0216052107031104060f06020318061e0403050c030a05070b0f0d1b09050108 74
    0x20010300440703018a0b140d48641413424020449660745e035a02c40e0803039035226000d040f60281400700352400c0310f030740784501e20005030203202d000d0302001850600064541c202d0b0000e400d0ba4503a0000303071110307102d0716031490341c0c4041481072000e903119901451010030545881c0c01a5402c6450741d07000345c5103c113000e0000d02e04c00d2520b0f0034034061128050b02c0050340c0306d01850050790b112800801043c0301881c0090500ca010007035402c240304440c0c1d00401400b800c0141d1000303986502c64940c5002e0070030b4045004000c00d25081c0c45070110300c01c1001c0e031100d5510700d1030000380c1014426041642d0315400c01010700c1290810340726a0340241405940c443c40d890407c10001e48a1090440300c0f4013001000512100c0c55503194111003080d50007952140200c040203914035040c5c0c10a10007580c085c020b1840c02c90090801155600006c0d6200000e040311504041d0f0310391450300641404143c03071500f440310f0804100750348600d0140300c180c140d24030481c1d4440000203005440540100b8100017449042c0001e01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272553264 1250 272552014 272552029
    0xf0d020304030b0712050103060e0c0901050105220801110406112d1c211a0904060e010c030501030b100e070f02190b011a03040206030c0d020919080f0705 68
    0x2654040e40001450301e030b0102c00c40391515171700e0b2001c1d0700516003070000040000f80c0d0300020119003075000b50742c806040c138030400031051424440c0301e01044c020040604000c821803070039003800751303003040460040361034003e00c5084900306500d400311040c00040501c600c0750011301e0142e001c03140c1d000400d0b880d40c09003403600e020082650880c00c409403214080b150010188003000500030411114201c9551406004100080708400c400c140782c0300c1c2c100e03c502c002c124010070701001d92141151840f1025031042c40b480c54030040040d50503031383c0d810800d981000207019140b142440b42e07401003800d50650422001c00a4003030b01c14070014a82e100100300c0c03038043c800c00e9617000c0a242404044165070070300982c00d0111a07252240441d00f80340600041001c075400ca01d06a4680a1106c052031445001e50300c3d4610066030b01940c8030780d081c0001011148483c008090b01001c0c0d4001500780603c07076000c50711014004610302c0b001d09482c3c030300b0700501c235080011030700020904000b049090315100105610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272554514 1250 272553264 272553269
    0x30809070e0103080f2a1b0105041401081905010b040f0602030a0c03180b0f0d061706151f0905130b0d0b04031806020318100206070e0406050a06080402030f0d020304 73
    0x191003000c28007906440c00c121208040c0d0b511b04410500954000610035103a21544000400540c0f01014413003640d40b080081d1000c1d10103110120301c04154200041d206858020300381b00d8085d4400036510200c40503400f4560003086104130b03154603241032500724a00c900d07594009008660050000840441d480801420b0307080d0181000080d03010401242d0a0009150304102e401d254005240500036043c200148200c825003041004010340f2112001c101e40ca050305120758aa01c9103002c110f8100740018003285900c0020a0f003540c1d03552410030740022003046440c0c2004100384c09402c105a041040c80d100c4112061003040180c5502d100001d0340000d208100a8501d03041c100014040501450744a00b00c0354911141c0700c00d043c1c0c3c5100080da1307a07000101d00c00030b50070314000450700350601c40c4480000c0390154000e0012035480316000c4034000c4030004820b51003900d0307003000115500c480244001070001680c0310600c624103401850700d01213100c1e42c03020050703101c64801c964240d4084241e805 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272555764 1250 272554514 272554537
    0x908100b130b030316030210050108031e0a0504231008090a0602030402040b06220e070e33040f1406030105120106081507030e120d15080307030809070e010308 70
    0x5600c800c440c00303c2d2460050140b480c1036005003440010030706400203440a1110060310302408a80c4e03c1d900764075101d018515400c180d024128410304103250000b8050b15a800b018a07105080613030350046082c140c44400074259054007500f48080e920308000c050500e01c0b03032940c107103603066080a20490795118140c1d980600516400f10126086503166000116449001001c01d0b80741c3c40c81c1c0403408049032403e0a01c65242c044142c1c0015038800c0c920a0034031540b020b840b010105562001071102c81d40c2086104040351240000c1c04201a881d0840185030421005082d81c0b9142440d04422002089803c0501803c2146041074420382d141400c4038150b62040c0c41d0000802012412140904000d8000b82d5850141d440b6500b082045000041e2044400d90390a000c01010000c0040d15a000d00c1c0c50515010b90811070800c0d520740c503400c080d0318805c00b0001032070001d94600d24035065400890381140082e034040309200401c04100b201704090529114099a9035155540d0f880052040c18040e05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272557014 1250 272555764 272555771
    0x9191514061e0616420902180a050106180b04030305091507030c0b130b010e06190b03040201030b150403020d0f080a0f020d0201180206070809030a030908100b13 71
    0x100d860b203a603c107480d600300454400c1c4a044000c0e20308500a10b00c011958515020f51911001404604d60300174451000c010081c82100d1301c81040141c0500a5464241d0b0800030b100d1403011343d000c00c031014900c503080015001516505025008000c0d403140d00d104021020a11030034000d107030345d2208450480f649400c2c42c40d41e90032031902103601180440400e031034070000403c000040c550050746150301d50b840f403028180c81c1d559805405044803105e000140c0114130420060200303044200030039800103001005181400081c05d070b00312214072160131808090502009010841d6058064400400d50480d10801005442d0b00040b04600a61201908c10f0f901030060400740188528014001e0760807119099890341609406044d603103541c411400140700d24400958118818480e169024105981001e00094283c00700402500461002d4035046800c0000e9002c0b80d8041001c241d000d8480c1e01c46660540c41c1c08151405c05800d00e1900c8101800c04040070206d0341c0744014503081072a01075001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272558264 1250 272557014 272557069
    0x80601020c03150a0e0f03030103020a090e0c0907030e031803100204080303071b0204110306090108010c0e060705070518040308070306140d0c0b1602040614060a080919151406 77
    0x1c02c085c110f2404034018078024003200465489000c0010b6050b00d00a861000f1807560354075240e411104050740c607040b2a000070078454100c0c50311264031a000051490081410b2642c0429641581c0c02203e0851940ca041500c1b00c0d92400d00703201d1014142c0e4401d40450a00d860007064030744034800200300740104551802d0300340b0700300541c070045010250090410040c540101415425941c401d0750002c0c8609404000007608110500848005c5030460350343c108c2982c2000709204c2c0079080030030300300d40f03e000d00340c030124650f00c480703801d03c000c5c03d4540d40c8840079040605000c0d00016004e8003810405090000034480c144249080d201104006c1c1c0350004000f5181c10440ca0740092a00140360b000700019040c044002010b850007880c2d4000c8030200845030fa0b440603032422000c881080d0340c10150078880ba0003024014030380c15901080440a0b40c4095003d40545411301100300030855102d0b80c000d02e00406020070703225589a0b1030180100601d64200000000d03c01d00b00c04901c10380154005868 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272559514 1250 272558264 272558281
    0x109090507260105040b0708160203160618051e0c010f08070507050601270902310c02010504060b042c1213060810121b2301080601020c0315 62
    0x202d100200d640d0080005041ca440c050241c108203a41c00c1c000501e0060214a0800c0d5a1032424181d0605400a62030303d5012041c2c82e080c03400c065400c1d60326076619480b41d007030741c3c28002024103003622480c0909490700409021103030031140c05194002590200001c0303650790344c01a00c05204056682088a801d90301d40303501301d403544211781d40100729026013800054281141c1c1021504422a01000300c44900d00440395400c98520f001d010394030505045035130000a0030f11a140300642440e07007001c590318100b45480d405842c1c102068100507036482c0304000a02010744038005040c3c0f003c4400384010070400550480b01d50055201d007a900210300c2c40580085003c200c48000d5400345d0b25160f8441084906600302e5042c0362050101280b2481c0002d44042e0050203d4000c2d0350303a80440c02d40c007a660b44c1b9190900a400110b02e0340c2100c0d5000c2c085040d20300740c0c0d046446004000c0e00603100d1000500014140386015004a0540d803100040075116074000c92681852031845c44480003684d40d0044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272560764 1250 272559514 272559569
    0x4061404051009060216050c010908210a0306080a0308010306060e15090604270204060e07050f0702010e0a0314010c1d0132040305070b041d130602041701050109090507 74
    0x240c141041000341b05034200003010405403410442601c0b18000b46a07105202c0780c49a1a1079211505100c444000b90038041051002d0b00b1147c0403480c0c0000c001d07480e421503d203450358448042e804641d0310001002000307501c0c010540500041c81c031110950401142d1000011050002035200b84503401c0024110f85455100f40f0844000e481c001c21001141000c008941c0610f01040c0e0089003421030200d043d41c018108540206641c3d5180c0e4588200b504141c01c2d00d401c1a0412410806000ba00b120142e1301d81d09614095400f6100c0710408020b2060b8136800c540d80f9490038428807804081c20f880d0350841c00c2d0804078218007803d1510000b5850480c0d203030000c0d2010090110451504204010b401da4540030f0320aa81c454400c958000d911041141c00c28001e510800c2c40c4100d03107412000e00c2582022804e0303000000c4c4840310041500340d996160030307604a40c1040007143c210402d030403242d00c000d000302030050811000c01c01201e10291102078440c0e00a0081815041c0d15051080e0300b1040d895 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272562014 1250 272560764 272560777
    0x5031308031509150a03080d09120503070e030604050c12010605090f10080a05030304080703051201080c0406050a030f020f0a0e07030c2d0f26040614040510090602 72
    0xc040c55600c1c54440064892440380c090103d0190f0762000004055003080c0200f8071489500604104609103585c1c2e8980070f503408050700611050300c0b1000ca600241d010503e5100b4680503864051312031800d81c07001491031101c0f901c00c41c801e0b40800148000f00c0c2000c120001070181c01e0f28030214040e200711540d40907060940c001038008510a0410a1499501094500400c0440c009040c559035802040343d60715040c002c00703405a08100003180015295031300500003244642009030805240740941c50651409038000001500588420b2566107070520030704006d08411103081c0700032825078032990701d844e0362008001c1c01651951000110765403140014001840042c107001c140c0d25100c83c00801a0103800302c000e011913059241d40c59081440250140b0b00d807480f6080c4519546454401c0b9801644c0b448504240011803502400f69000743d189000554a41d031740790304c40343c14149000320403925400d0680c031240322304409010001d440441c200500280c072640c0880c941d0300d1800c2a00082c410704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272563264 1250 272562014 272562023
    0x302030c0c030f03011703030714070f0209040b16170a02210703090c050d02060901080604060b0d020403051b0114070203150a0b0906010806100c15050c0d050a0b010906050313 77
    0x320f14003e64030001c000440c161400100080c260340303511201c40f0754a0000341e0b528004101c01c041008140140079014043c0f99000390004402e81c181a004100045030079201a514070745440204070041d18407001d0202000c0c59894a8000c04a04000b0000c031140040c1c1800303038494000440117192941003224105042d0f000d10b00103031500381000090010202d080c1c0c200c917410312486000030f8030f107052820310b8a21600030b05964506080d51004584c0d204000708250740c4140d952001240f100e80b0080a00840511005c005035240d086050072403034003840c0301c1d003098601c111000e25000359074807230405003003185e02e145210303107840c0984000703400d0062904004147e50366003410040d8964442e005085a110290390030003458844d40700442d0031800c2104c02a81058a00710616171040c801d144e0042001d000d000c5140031807542c52407a00a4841c25201360034031000101e00701451080030301c01e0030780102c8040410080700e82000c0c0041c01a400314811041030001c080001611904c2d005a07000c18203510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272564514 1250 272563264 272563267
    0x9090a140304062a02010804050708011d0606040506180c0903101b03090c0b07020103060803070303050714130e0601020c0301240b07020a1202031c26160302030c0c03 73
    0x808203480e07072070300103128820001d501c0b01642c2120000e182000034110354140d9244c107682105400640300c11030045c0c011a41071050040000d0354407401e1242d09000003088000582241d841c16400d89020005444c251046280005200680e528041050414849031103806200c3e1b0303e05004042a0252110258060003200001121011a9800004141e40c2d1710440c80300104820360440807501d520324003e00d0b400c4003c00c2403205000110203856031a10524000c2202071b212101103065412010302100402d0315482408131b0903812200c01410b0b00c1030144028205108206c08003480112449191000c154031404140142d10030700220141c440094001d01c08482e0910030a4100e4181210900095034801000f2440c11420380466000f150010520213a41d401c00c07070b500360f460704816422641445402003120400e90100301300c403040050f0351518060001d85020103c2c0315152141540c04000900041103006420b0005805a140042c6070040e101d9071103030016506840354100140242c8070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272565764 1250 272564514 272564543
    0x3060306010e092a041b080c090406051c021807020606100c0f0c360221040b010503010c0e03030706090507050424080f06070c060b06040801091a01080a0209090a 71
    0xe04811113440b43c2001d403420015038403500240c1d42d40c0803005030341c480000c40c40c2010500700c2400f03001070080080000c0c8001421030781c0d00b0000312410840e030541000c490005187c0d0083d80b800385109456064440307920348952502e070b44001d480d024010309051095091820f0704010500c03603076011030140d92106c00ea0490381c3c03079801c207444485100c1c031070304002c51084101c0b01407070508000c01c0d6000404403d81d02c5c4031030800740c0166000c1d4014440942080c400c10300055001800c911500d40240e00501c52032105504010a150a465990100d80244442541c91a001752030010440e90701c541c11040c0003d51100614150782081b1542d880194850709051144143d403408031410302d82d40700c090101c4401c49950300740050702c90005401c2d942d4250001400a1041d0f070203005c00020003072082e840003c1003440600000c10b260000d81250b03c0983d5500380210410510615810350141c0c08003100215614203071a2603940d180c5540020b01070380c00300001c90085101002142d258a074081101c0000e0903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272567014 1250 272565764 272565823
    0x1c02030a020d021204060608070b12040503131215060308070b102c060a0803070b1f03080a1b05030406110a0b010303021516020c091f0b130b03060306010e09 69
    0x41342650145c0320700745000c03000941c0d020001046811540341c03040990034520340e000c0b40c1061440007441035901e40006c0010030701007036035003041c000980140e42201070345101c2801c20302030b81e290b500e08100d1340d240b6152090011031191f80070740f040194461046402c41da82d460003130341d5444950b40611161800d559070708290700144050140c055032302015081003651227034104104c40c1c0d40340c46900c6a03a0001c205503404100c8403a82c95070b02108450011403e804424000e140c00c840541c000c1d2a164000305050442a901043c00c5800e4460940321459030902902d55075120320951055100740220f600307800321071807824003070745210702c0c0c0065002d1440d6a403414003075180c55000150384509000140021301188554410810044181d4020300421540314240048084040c0c80500c8404c91504449040b0340994040310183c0300f007415403030300e840c040404081844203d401030907100c08140104030964800080b00d604491031600d480c52541c031103070b41c01400d082a40c0011503040706918079054624 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272568264 1250 272567014 272567047
    0x207060f05190b0102010b0d020f0a03080f03010e0705090307060305100f03060606020c01050a02071a1603020c0301051b22150503040b0f090c100306080328051c02030a020d02 77
    0x7024030b180a001070b0075800012800ca42503071252560184030901d400e405800d00b02e81d0f42d180c41c403020740000701494403902c3d441025040072024400212002005010a200100d03455421600c141003242c24004000d001035258400390041000301942c03040040c110754001002c0c03e006041070034141e1803454407070824001401c5c06000355800b44c81a1480c0d100294421000c503080743c2440d9014082d8a0305002600c1820740100c402d00303044220500014607886144429410864841d8000b0320740c1c04000020b15003543d40c0181030318035010034140c2121801540d18225008a0380c1e40c4503003002e504c0054043c482d150417540282c0595001c6030001c0c1080ca0700000214002c0b80100301c2030009a030752880c202043d034001c6a044c6156003103154085840e050a01140070110110704011803c940c68841e1070b45140c102c841c1100c0b61034003508035008840c030141a00084844135142052410501c500c5461240603988103008400d0f50020000d40c54002517070640711302d0300034031005540c0d59003207a2555505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272569514 1250 272568264 272568301
    0xe011b15020a020a0204060608071d06040b0a05120907060203120a09050307051b1e0f010309080c0a0326010e1008030304030c06150501140c07090e06011a0903060105040207060f05 79
    0x40d4900171f000718400380039212261064009594013200e813a07036040007140b410380f10b801d125080340c0c0a02001c204100100080c00000e0110f82c5c40c40d4840390960094400398002a04940103a041080c0900510342d020003103c3c9c000150b1507200c0d080d6200c0c8a8003200030818948054030900001c9048002c00102040816040e607030b031036041121540c03070002c011101e0f500000b10f8002d00c5140e070500b1090b04180c4001c0e00480e030141000925002591140321003580407801c907103003039084036200e0300425402100c01250001c01003900110f250051746004200f42060066025402005001030601c20a0803001e0000d0320504050300e07103e06041c6400b42c0a83d01e0510101ca00b1070601505010400e2160301100445005039100c0c000390001d001c0c0641d80e94403101c1c841c1058019030102084041290040b2030481c02c40c00024617003585401c41880020070928841c1110300c00030400d035485560001026410b648084a005a43c0e41407450682c000701221022032010a041100708040714080644e001c24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272570764 1250 272569514 272569519
    0x100207050a0e0915071d0f150c0712080706150911130501051c0c0c05010501030b04060c09030c0302151b061005010504030c03170c060a0209100e011b15020a020a02 72
    0x342c40c840070002c04c10210120348940028a07010305000040186c42d49a00324844d0281c80c5080e5034400001240601e8802032610b40990400140200a004100041002484203000c5101511095500c500365031060f80070180071942c4074840c455441282341040d4005000c0708c04d0800c820302e0420518501030700711040203044002e130b680c00001d065008404480020902c0e2034813810112030762a00c1e600401d44844480208075085810000040302445a54042c40c02400c00e0341191505181c100280e880556481c42000f0787d005003000060a262815810781c0d0741120a03006030400e21860f01124040c2080e40010708030300e81d5a0142c045c1000c203a0a005000000d0402c0a42e6258001074a00c3c1c400c6100050003c41480c2d020000709060b00561003080840b000d401d4074142200001034034060301950b032092220741c0019840000d14200070080d03e01c28840c1018041440c00c080080e052000c0c1c42110600385058410590820402107216030441e500e8510440d11800d280d43c2c029030316924030748101d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272572014 1250 272570764 272570773
    0xa200d1505090412111006120501050a0221130204090b060a050312160809030f0d031a010804030804020d02120c12061611010f050a020904150303020c100207050a0e09 73
    0x90729003425901e052095420a00d0501140d80008044600021103502c0400e6802048000045a10140101001002c24401c102c0b04a6568181142100c6c4044e000c00e90707051041022000d00540030700d2040c484405a03501c108030341c0c0d8010350884c5c410082c1c031000754000d240030141400c0040c0301400500840041c0e451401e165100c806043d030342c0404803440da01c20441408007405034141401c21404c120320401030203092201540c003107807a06804000d40740b41c582110710441d81c4550301d0710406404902c0b800029a0035000340c0b001a1a44001030405401c2005031320001c2e0664980a041002480d03010342401e60101b90790988686815940014078460304002d040c400c000030303002410754041c000015158400740c640c000166846041c007182d0303400301d54130b4401008000c1c0740c0b44178007442840c00b410f0240e5184000e40400048603121440f0040e40145a203060012076400a8090300c0480141c594081c40d100d1003405030300e80a032960140368000c180d03c20100d0440c19500101740142c0032101103c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272573264 1250 272572014 272572019
    0x1b170408060f04020105180a08070e190603020a030204110910030606111b06090111010f051006110c090a0b030105090a03020d170f0a020409020c1b0d0305030a200d15 73
    0xb0494080c1620080e0014409006a603800880c00f001c2480c503050013010290113a1381c410401c1d00340030140d07000d260144a024100110356581c0c02444600c0c61040b002000241d0030340c1d00040c000b4080b0b00002c2c0c0a20f0380c4500d250481c0122000715009242d0080409900402c0444001d01924150203040c0000f112802e1f0042072503070020300090015149952089141d14030400c0c05101d401001c2028100078010340141c614080c284564001c90a80301c030086154580412406000f030065448a0108010602503c8440130040307240040414100d0300c1084a0700c98801c4c42000c0d264051740c0c240e0551a040031701c00001c034005003c1141520030380907030b00b541070709010503140c04203070305411080221a06c00140014560900071588014000710050419807625400c400302e80007600c10f441250301c4030440c05030408400084200e0313600110740e084080e036a06da40090140c040030b809d20643e0b5441d005000d0201601e5002e4012002000d180e01e0380358000131180a0240505401c20a01d584800e00301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272574514 1250 272573264 272573281
    0x706030207050a020f0312030414060601050403120c0602091206010302090a11030f0705070c29041202060f0d050c0d14070807081f08010204060306170d1b17040806 72
    0x1c1d501a190010090a44a1001e03002c0c010301404803c0300f81d600d07000d1415000103803148070740030b18003860240012909041040c0141807034500090719031030500c04180000c10020303070400c82c40120740d02c1c1403a05440c503000301e140c0903000e405a1031402e03900048501480d9181e4600081c481d040301c0c02114061416210b04481c54110303280403442070520740c02040010142e850304034849800280520b485490003101351200075290320282c00c0030004030441c1a0911055034000f19041708011017060152410f031402888074041d80725090003c0c0500b101150044401030101e017940e9402a00341e005200914003a1a03880d150360141c01801202403134000c01d61201c440b0b04082501c11084c3d62a081c1082d11950300136074003480e0041c11002590205440c0c0520b44108000c110300401c208000540c965051941c0602500c11039002400c0440d004100d81a58002c00608880905070313230b040145415030520f0000c18414001d00001d004003c0c4a04440c01400c5a480240304071500103055411503126540f1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272575764 1250 272574514 272574517
    0x50c1603030c0b0709120807140d081302010909050106020d200a02040f090501091518050709050717010308280917070305100c11121804020702030a06050907060302 72
    0xc0c0000340d200b1240030008614103600390300f05605007050586990346500980040c0100c203400c540c0d1007004200c0000b0841c0c807001050f40011032030b000c1d06000c120360701d000b8444440142601d090920310ba590800f5a4000d00048015040d03940e000e00c015a11201c0280d075801e1686600400500f04e0408442007103203d03965200d4200c20341c4042c0c22008015001c10026145c0d6070183c41c040360b61200401d0000f0801d20a401d0524880c006820f0460805c00942c0304a4182602c00260850b00001410000d480400c5a2056070702e040400075013034940316001c076240303842c21000348550400c040010040c000b428020b40401d0304c0440350460300141a501000710317590000300c048003207000030701c050004924030141c1e4800c01e0700c0c1c0012180481d9072519800c0c50980079100c0e40d4502075403103901010f090303401559010760a80344002070400d031310360300820f10052244d0140001e4124034400c0b190403d03650740d012940d10540040454802c10850f06080009200580d10741c0d01512610a00244c030602900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272577014 1250 272575764 272575769
    0xc0e01090e01060e04020d05041b15080f040602071211101404061d01021b07091407050a0309080c160f050d110a0f0f060f022d0a0b07050c16 62
    0x1466a0020b03483c004050300c200a84000345a805a001e01c6441c2181e0401d20071103104600802d0041c00080d48075480b5814140076410011100a500e114507960710f0708289030603000312503580c0d4441d265480e42841402401101c500401580f02d01c006141599840320020b100d41100c5000d035607440ca03142102100b190103052503104807890300000280400c1050303004011403860303001950503400e0b00d02c6100c0c3c2281d0101e1103c2001c1900010000b1510104010340c0000d07011500d02042805521180c10f000544028001410000e0004840d003015100360020049581c2c060141ca4840c1208803515480320380700d413034405902e24520000280ea00c1c1c2400c0a80468101800c68031a0b90b1042d01c078460300ca83c8900f031300c0d60009031a02000485c2548000c440307009004c1c01d50075182144c01c019004104034007090070281194007607155500c45180600890321300e0312101030880d9100404030702460030840e10a501900e0456040b0130005150b40050003043c1582d404000d071008102850301c003464a140343d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272578264 1250 272577014 272577029
    0x20709050601180e09010e010f0213090203090304170309030303130302240a0f142706150405040f0f060507091208190504030507030302011a0603091b04110309010c0e0109 75
    0x1c3c00402008025060302600020b07604c001185080c2241c1d013207820b513600c84010f003400710360001d4444000441c45d41040050a80d00800b5803450138000c03401650390050b400784c211403000050349000742950810445044a0303000e81134036100e103410000101403405e556419000740c058800030203800b070070010142d1081024603800c2c1c81e69807980c1c2d050034010100c2c010481d89003a502d84401806600794500503214150345024100420002c4541e80c0d4541d000f03101d8400c08d80c0c445800d202002c622000842c24098041d00d00050503921810408001020207001030102c0f441c200d80c0605101c041d8020703e2107283c80b502c46601c96590755410310040c1906a02c040c042480502038581c41283c0142e00540325a92032412a04040e202e440d401c0c1040701030b500440150b9903480c1e404a0344810820500488042111f00d64110710340306040c40e454040d5070805030089a50640340c0d040c50740d2254440c000c107442c040d120726124604085007500030845440361034040b80c20010070002ca07620403040030040e120030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272579514 1250 272578264 272578307
    0x250c051305060a17070e270d050d20070b011a120402060a091e06080703060501120e03040909060b040b061303060506010c06020a020c09090f030703120603050d020709050601 76
    0x4141046030b10801e110740c041020301414000180103602e10a00d6030051080380f0985601c47c0c409207a400c0101400405115103800c0152540001a003210556081003d4104040340300070021103c1e40b405500340101070310700080070450501340410150010306031079000102503800200079020010034040e0031004031440600d48001001414958040d0926a12130b003040c0f00919284d00005030655600180c02c1e003403c0c94a81c007080881d03480380f03140f5040300c40b5060401105043c440001c01c1c0d49044100c070305416442e04840741c1805405c00c201c4000b4102410b0400c0384251900d403200c0074000c100400751040d82440f41d502a41d00d048400c0310003000216019202c400c1c80c5a8640f4083d1400078102da040c81141e1008801103900c5000804500120754090140f540701c01d820001003a0300580080304550022000040400000085800d51a0141400050034000030411009480e558000410902403042901d03982034000804a055030b8034007006111503911003004580100041e41e588645000b13 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272580764 1250 272579514 272579519
    0x10b120304170309040203010e0703230403050a12020c0d08011d010302090907080105040f0210080601020304090f0204030204020a03020a120504022209200f0301091502250c051305060a 81
    0x442c07420341e2903070326105482c140f411001c0020201d8200361b000540300b0100c0010040c50070b505105240c0c50a00c0502e40540001000781d542d86072a0004000a0903c4400a10741c01014081e9501d0780c11b4241c030b00740a55035600305a4421791581142c140c81d10204e03901c40008a42012040020400035850410510240c0c1c65602080320070840609480841e01a00320081040d038000c3c05110720660080405110130b0307034030f1710501980c10200600759040060107414803946a901008031b40407544064000f254030312504540000074400d55000950252002840d0815180c154028004114003038031100034042c1e0300c140f042c0a03520111002940080c1d00c000c000c010501030412041d0406030014002401c4015694120f68003900c0c02d18040c0351126080d5082c0030303141243c403841c0d81d403c0641c0280407644c815914004040e00b00f00044440a4001c82c81645540b2080c1101c1000c2d0910141c140e082c3c03940d410300715100740302130041501a000850f01c10311100460b0041c40d005401c040c00d80d40100c1c0c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272582014 1250 272580764 272580779
    0x106020c041d25030803010303200f060f060307080717010b0307060c0308040c09050907141903020906120304060305010905060a030f02040b0f060a020c040b031c050903030409050108030705010b120304 88
    0xc644482e100040f40c45035000b00200c1d80410256001e1440b079240c0110f1032032004c10340103c500a020f14034000c2e9200303500b0082400b4000c44d405802c440c540d414000203840e003100103170030425950404040c0b4800c0d00b000040006481e50100b9020345048002c01238060768605040e242c008a010721400700e10310600c601c00180c818401d00d90b00034020140032440c40d444200410076a242911003e01e942e202c010700b44150542d0210718040c143d812144a15821074440202900d400c007844080d00c00c0c40450b00081d52900e5402860759100a41c409990380e46856001c040d000700001e0141810380c0e807500300090381c50b0405208000c1680c1d00110030800d030000c503908000281c40394040054001e00d01803100030b100e032514806440854080d07000361400761906404c3c4000c40d08944003851103540000d10b013448141c803241040d2120821440c00590701c1c904480460301c2c510459114442d8103103400000202c050011024ac000f5038840c800a0103a00544420440b9100e0314605959294108100410004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272583264 1250 272582014 272582053
    0xd0206010b070809120109050d0305060a051504080a0f031d01050f16150c0314102c130506060102010c0504060c1502030403020a1506080607030903030e01050106020c041d 75
    0x452052182c240303443d6984c1c02144075048144032617400d680d100c0604100f0800d080c0a001c0404420b41350401c5186400c60000325074850b20710500c4e0013094007440d22a0300c03080c00c00440d406031202200710f5440c09618500442c400d8201e40d025000501e002151b9070004208800b2044200c10503511070307003400c802d500a100701d0f500203c0c14440c5001600c90390380000b000d032120390b00000d191000011b2540c0007218054180c0300808408401d401c181c10402c40000c0d101c2040106a82110030b80301220300c00c0c843c10407000d41030036222012400e00c0c2820030540343c10701000540d416100d50180c0e9025140c1000580c00c0e18108107080d00031503014001448101d00c5a4845058180151450042500511445000c9034000c0c1c030145e0040c3c120310324000030f1090180791098207440b00c00d4208206480c0401c01134980902070031080c10942c942c00b840341030600c2904540c50206003038000b00071a503900e95010355103040c41034446000c1c60400481c2130300d031302040020301050003211018280c00981109505841c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272584514 1250 272583264 272583277
    0x60f020604060513020d06020c1005041709030a1a0a0606020d170603030d021b070f080c0105090402070501140103051209090121080307080907170d0c170d0219020d0206010b 76
    0x10084103201d41002d80e1b1403144003225680610001a0348000022285080804c821001250f00d070a0130f0074070001550408003a0280c01c040380030310f600e07030044400290a041032150040c01d10010302130840c01c1030280f824034a000381042482006800e40d10704069840e220103c000c0c40c041074201c00304c480044a844921036202000500340da14101040c110726040b43c0110304255020261030074114203910040060002400e083e50b20541d1003460004040c7c1d480c1b034007444080c1006000301c4c0c03101103034446030141c8642a50081c024052542e03200442070041c0c20134441507400d40f090b6900d204011050000b228900f49001d00042616800c2c60700301e4001c05403005056054401181d80c2d0000f00e102e4034095400340b120f650f1103100d1400c014411625120325034002c2140001c00342481100a03000040404000c0344030b04291000082608007009081c5500404c08800ca034005805400c4000950040c2480220600050400000d00300126503030103203847d13010007582c800030050001c3c84001005c4c114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272585764 1250 272584514 272584531
    0x609051806060c01020c030c07050924030c06120603060c0f04140f09131406070906030c11030a02010f0e15040b041b0f03051525020a0c1707060f0206040605 69
    0x40c0210110f0104e0880c0d11441e81e0340416000425100002d500c00d10001d002032200310381004090511108082c235403d8010441410038005040c1480389031020f0040c280e00e032200400c0b4940700c142c415000100c4c1c017802c035000352203801050000703116460303204190b44805000c1d50740c041c10a802c5c00c3c0310600c01c40200741c02503400700421030140b18680e40d260210344a0907015003080c5030b2880e14034250000707480c40000040650808410030060710341c800290340032104185000308400c0040101990240c000c4004032003e4040000c07042e12854054002c1c000307440903210304120304038406003500e440701c070b0107154000806038590100d400301c0c4202d1901900140280e04003d110390702240d0340300e103200d91603010302e01e0020460800c0051020600100200e22418400440741c1d1034411003598040310300d00d1070040c00e40d0502c3c1501c101740340700300890070b242170b4000902062582c0b074412110141110099411091180300c8022812030b01c82c0706201d031400703410303002003c607600c89503210030191100510b10203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272587014 1250 272585764 272585767
    0x2c0304060c02040b0a08010c02070902120a0902010c0f11100201091101030c1107030b0105010f05030f04020603090f160f0b0412030c061b08220507090f18030e0a060905180606 77
    0x1d11581d17841c00e80401400c107800009540480000c0c080d06140c043d0b40101581481402443e204400918145a000c0d11071000002d042400f4801601c02e034021010281c4075201d0b0308101d004100c1641142c40c5520021a41c648414619040c00c900f607802c65580141422601e0301031507003650003030b0820214103031350381028421071000901e11403030070b01503901c1542c0e504041b0004002c103503003020080c007104400e46445071445c90802025154080c01810090280d6030002c001965420240300d05a000780c2141c0589040c0c0201d5948400d00720b01078010b47c0c00030640680d00044440b0403000704c40454201400c0c1c40300c2c0d100303a03480035100c00004030801da40d4681c54103400001d5520266a600f5104055100c00500c1c1c1800b04800d03400c507244a60507581114209001c00100b100014590101d6054500100351500050402c201401e464007031482541c803002e040d40101030300050b1802e001d94066480748106030b521001290000414880c882c0c02c44006001d80c40303092042808541c2c0540c010b42280d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272588264 1250 272587014 272587031
    0xb0f0a06050f03090118050706090f080c101809140a05010303090b030a110409050703050c0c031b0715050a120b0a06030b0312040603060e1e06090a0e0706032c0304060c0204 76
    0x1b13000c0007082c0c00c0210b440750007540c410300c000e40e00301d14514041c2410070720a410303090800301c040e942c0d19003918840d0b1080c1c2e4664440003030030748100400c0c41019039000340900d081d5178404172140a08640514072060100e200c0005900c20064461981202d8042d40e801c11001e15000401403903130300280c5210b4000c0c0c0c1b0342064086002c1c0c0c0c6070007030001344901d51000400703250104005089640180100448102c100501a170300304002050700c0c452803400c124080900500c401d024501842d0340c1c060070f07101043c5550071101036000005003418812070303261070b0052102d141c0c40c2c40440e040305000300d511580681d801d12000c0d01c02e902000f0010805400c980799003240450041998010f42d0140c0e000a07100e41d010302c55052040d09050f0820b80c03443c1801c0d0261040040340c5010706000f4039a17400760b55100005030782d401d03454015800704500001a00d0200d51a138800030094013070040501d5006008620465841d40b81d6403600c449a802c41019509007801c01a0407610100d40b40382c1a80c4c403d0301e07010360 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272589514 1250 272588264 272588291
    0x130b090c0607080306090a09050c0f120d0207080f0102030610050306010201020705150a0b0409080703210c08070306080a0f150b090109020706111204060f0906020703030b0f0a06050f030901 83
    0x1045400e004140113038681c50810100304140c0c20081010441c103003802c001000180300040c1503a5405811600315502c615540c0124ac3c1c44c281c044403004040c4944500c10020fa03030080f401409848104041e1207102e40c0f200307026402d0348029665150000c3c1c983c0c0c91150306c9441100a540c000805200151400c3c2c11034660910f0400ea80c1094040c07122103100f403101020f518403510402620981d01030181e0032164135214a10700030404098240300c1c0d000c40e61071001010b030f844089200509a010480740c911904014180c00c0e0460302c45011030714200000c80d0010707000440a5509601c408880c08203100740c0e4070303a9040d0703803200b184068a0341c40c0c4110700803507600d010049010300b0081000586070365041c02c0138000d81d080d1001081d03c0810821481591551015049030b1240d008000480d141c00d91b0b42e5050b008000c0c06030064a10703440440e0354400c0542c59001101950001c460403280080305004110801d1014490b180100d00c3c204403503501c809092000d9540640928000901c42041182 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272590764 1250 272589514 272589517
    0x510030902030604060c02060106020d0912020415081f0204030b0604091407060c0203011b020d0c03140301061e030203090d08090c0a0f030308010b1c090c09240905130b090c06 77
    0x4003205d21303a03199003070070b203907143d0410115004000c10301c024202070340f01c960050202006801800119900034a1540c02e549032500880c0d01c1c2c895003010303840c07502e544645039034450300404e54030b900c070110b02c081c0c60700351000724001d07101507d17000340c401c0303642d51142d1301040010940e00c0c404441389030b9068075118240300240003000003011980c455000350304071031040508603171040c4980e8400150306a14429038550014440c5100701031800c101c940c001c0b0600b026904441d4500c00d40320101070000010612a40c0650161820211000d201001090100b0305900744e0004170f0b44100c0e02d80c0a0f071034161445109251881d0001d40c41010360300d9400d802c90203c0c2d407880c2660001007a0bc01c10301410800c1540c4100710703034014008209040d0030004000868800800364108060303101c0c0d100c800303050038004000000301c0240400f000402201c441c07048103070320414414006641e01c00c101070700001c07080d0290061521800c160100c000400d903a42d9280803001101501c800001e10807210880c00350703100c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272592014 1250 272590764 272590771
    0x110102040603060e0a02280c05030a030207021801060503070e0a05100f0810030f0206071e050c03010c0212030412050c010203040303050f010815160e0d0c080c1203030105100309020306 81
    0xb80c0c04900b180c100709000c0c40c0c040300030301240a00c42c810012800e01c54115445642c0350600b4441c0040d0100c50a44100c0c1e40403a4400003503c540030005480300703450f030150700810f001407007519038024803a00da408280c08002c0911a1101203001040054100f91283d400000e41030030003014010403e8803480403030080c200303480440010901c80e039081704c009a00080001e90196907000e4030074841e415955a14034201d00050002d004400114010080000342c4010f040d4403520b03201e06080300029030030181c1e82c0340e2400040034000e520341440710740514800304d6040321030f07107401c2c08080c5586c545aaa03400c0c80c20b207100844080220501502c41c2c261070a000070340c0541d00982c2c0200301c0c2d040001c10407820382c2c81a4001c01c040d0384a0507402c211083d00c00c013803540c000c0324010b030fa00010541e001c0503103c50f00030380b00540c0d004200c58a40410044581c10f044d0654420108807981d01c114101800309420081b8000c84040c3d00c20b000410480c90103090811500d1000c0c0340c040341040d03450380841d1924000303a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272593264 1250 272592014 272592017
    0x1b0912070816210b0c04030f03090306240b07020301020c06040303021215010804030f0306050a0f03050c0105031306051003080f36041d0607120e0307150209011101020406 75
    0x244030b200102c040004000081c15846115070b07940d900700600e148070340e002c5100007016010b148000030318a5110b070b803e60340216004004030040e91180e1500070301ba01030600044032141e2500c1c80d403003166409000c04000f885180c4500451013404c04e00400025001018100e0389503408000b08644200e0171b004d560300940c82a14050707104c040c1da05004002c00c0004100c6486402c0c048140038075681d2081d00c00360456014245a40d2042028900710040c0250390021038001c1003003100041c000250388084c4040301d010f081a101500c0d0440011a4948800d130383d403c100c1d0789840140c5c804507901c3da2216401c07001c112713040b00f0b03110384d00d075108011500039044807580c904000c1040481d0108544800100c0d4004070008000703041c1d0b01905d00c150f0144085500d00a035a900718400300d5042d86001190900c0c04042240e02e58a00b84030300914180c1e0300d03240c0507112400c0c014014403074500002960340b4568030000240748080c404400c00c0081d048820043e042000b10380c00c000295000f840104050b01c004d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272594514 1250 272593264 272593273
    0x1003080c100c081504090209060904110a15170105010c140f010f0b12070b04092d020405010f180b031302120705190503031608070b010e06181b09120708 67
    0xc8107001e02520130401039000b00c2c10000b400c00140e46400320240c0c4188100c81c0c81400c0e4a5500b04084141c414002c00341d00f0081116010800c045042148a174180484d40c801176484456624154044020311810b804100045042000074440009000046130050102c81543c0c0c94120604d0a603818100c800c200140d441030410901d0a15416134445207011074000c2900702d14101c4190018480e40c41540340c034541c0c80c1c4011041005441200b03216200111140000d034040c000590001c2d4424821240419030201d4803c616501032a00050300340d143c507040c5101c103843c00030041c3c42076000408140c070b600d2510840900690751a800f121400c01c03400300074100c1038180340511040520700e5019014030448181c0401640c1c1d0f00004464804c1c1d80211000803405052402ca40750307000d000b0000780040240000440d62907011300c000e91148801300c41e480000d450552501d05140e0301514400d2200c005001e503441658020802000b41d40005800d03a8101c40c41d00022074200100780d003040c107480c0c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272595764 1250 272594514 272594521
    0x60b06220f15020601060f020a0b1005030f0d0e040207021c050f0f120906090109030b0f06010201110703020c01180504091a0a060b0409111b0303040b09061003080c100c08 75
    0x4038440c00c00c01034001c0c1d160b949070044091074007a66400b014894041002445034211101903c00d20000d18082c0d441024142d0074240f00084a52000160003503034001e10070010403038080100054020b140c880e45071664810402c0e21000d10000e5441140c090340c0141c4081a250b24194404000c0381d0000d005002914102419001c05400c244d40b440c01060305030b01142480383c007134041070125502604200c86095a030707010f540c0181c42001c0760b584081d148000800400a0030030b414241d443c4140826030081000c0800c40003280350a00400b400a4010b0707200c040040081d5010301c10b0750300785c480000f900c505540d40d11400102a02c40001c1d00303c07814170305078803c400f0b0000d0001102d90050902c440910489050445060042c051480b6558150361244082201811680201d8042c0b8140d4012000f07005129141d070390340d030381c403d03101265660f80d0360700014a5860003088003405440110681c401c064510784500165400464014400380500141115008643e00c51140340c1d224907203502070b4518 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272597014 1250 272595764 272595779
    0x150303122c1506010e0312070c080f10050f010b120405010f020c0a050106082b21090201170121140d020d020d030507080c0703030b0312130f12060b0622 67
    0x42c005000b50b4140150511103050340e64000ca0540c242c424213800503500c0d142c8909201000400c45d034013100c0175000e100304a912104011075201c4000c10350031810312258940c9201c80039144424425510241c50a100d4200748400391100305400500510001c00c0d0441696a81d9040341e0005c154454503601441c0484100f000a000304001407400e10040d10b80c100166022101900c0d001c90601d41203c41218400d17095401042d1443c1401010380c0c8001d0840c0c1c202411000800121105901080c08100c00845002d01c1c1c040303442c1658180b21400000b1000c2007040e2221030411f002c1164050107155008030105801c002d07030070101c042507000b051903110000001e0b04000745000c001d01014100380801420304c0e0028003141c1c000358124036083d43c908007424110010500000c2080d0b1500883c410380302407001010161500501c031406040506a6a5113403000185480c0300e0b510080c58540d42c00400708c2d4065000c4940054080e11451414820303840100a185100d28405d03454103001200f0301805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272598264 1250 272597014 272597053
    0x6060519021f0b180106090e130201020a021005040302061201050103050c0c0a0209070c020301050a1d0705091b070b0f041703041e050f0706080406150303122c 70
    0x2103820300241c020034030782c0b5000c540041610416032203070325203c60600400e40c681c5111a801c59070040114001c03940c4510307000341a0080c2e4462040c04081c030402003440030081c00442602070303905070001d19140f603032a403d12807001658040d20b02840300c103010010250325028028900524084102d0301c056052100140c103d81c0c0c0a0300d03101030b40e03400303100a101e00b0000280c4001c0040e011101c149441e603410310125448084084000c1d01035090506011100c030150b00001240741115054002814103400c0380303075a40010b80302e241c0d070203039112020500b10090008a000383c0140150204e25141d440d4446440e00c060544080c00c1c4003404404000038000c0301d100c190401c1c50007410152540c1040c0d00c0e542c201410100940200c4203242208001b0807030100300300301a14420000380c800c4c1542d1400c0140c5002d0044070b05403440350800b041c080d02220079140d40020381e541515610044050300c50f0402c02801428600c4107078440140007164140690007642c1c0a85200354001d114a912000d40c0301f002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272599514 1250 272598264 272598307
    0x3040b070c05031501060504140a1203050304060506061303110f060708070507120209060405070c0c1203020c040c091721071406060f040f0b0405040b010608011401020705040209030f01060605 84
    0x4101d1300005121256001c1d04941c03c0b40e085500740700e812020300c4001020048554071804030b00d04045415401c242d00302000e103104600841e410043c9030b031140309100903031150030f5041c00c00084a240c103100144030302850405200d009005140861101000b113241544116401d079941100131441c0700421204200c2e41c005444e0310314504c03000400c9640416410040030745800c0c841d540f0788000503a268410080020382c1a000440f1401c40360f92480a00c10f07002c4d01000a40060282000d4000d00c0d05042c0159840b0003102d540d0201d41629007103480e4410f20001344002d07054000d4801e0b42c089900e00c0c03030301d080044080040d0541e58010510b000c055088808a41240c0340c0c2149003044142d81d1984005440501c1c162008168034000810f460020a00620300c554031500d00b4050000303000200300711a0691b000d076101c0b1004d9903290110800140201455140140c0c131201c81030103142082d4000d01120000075003146d10300040c85580720f094401d513400050006401240c0301c1c0d03000c0f40ba803070500c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272600764 1250 272599514 272599543
    0x203030304031808030c0a141f021801140a0f2001020d051f1406041a0405180907051003110d0f0f02120109050c09090106030e061b071403040b070c0503 67
    0x2409210b18081c40d07e603960988094801a132401c44440024028407109240011501071403241035170f502504802500300e010203080c030350004e00d013034462540140400d0910040081351075047c0f603401201100c401e08280c01480420a2011801d4050303091202d014513980c000d4400542c5074101400b5120886200030120000d001d500f103181c9070085801c080200a40d041c0e511003614038602840030a4152056600c9000004203100243c500d0030b8115019000b50b031804c03205038010166980d07858003001801d590400264001c0c00342000785160141d511040420710b030402094040491201008680000081c04c218a8444a600341d10400e07030310450204041c882011403c003001c3c06001e100790281401518842599140400d100c003180009071035021000928842d40c1d0744e12071000402424075455920590702c24040804c900250042c5400f00005440e5016400c0181075190840890f180f0000c01c002800100300200383c10245900901394680076407640189180303044141450301e10002018107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272602014 1250 272600764 272600767
    0x60f050702061905190509090a0b03030a08090c1002010e0d0305010b0906030901060b03041515060f0509010c20090c04060903080a05090405010e011e05030c010c030309020303030403180803 83
    0x60b6150070590302581400302284600c94a6000141c40c00d02c01c2c40d5440c125110717a400000c40c1c0710f03031101c000c2129110a54080300b05450b07504890f4103807804200315941c90f0f04140110b0310650721030a0000d82c0141501c08030b540501d06800440d52071003502504c01c0060b51942052070340310303c5c100310086440c01c85180402c01507140c501c80f41142d024074684248200d0000011900d00307182501f10501400350308040d55580e0a25103410004001e555045010050401c1d09440c0008922020001140c4250302c2c0c820704070072039100c01c68556101c605900d051000c10070500c0080344041c0320034402803940c48807407600c0c02003034810419a04001050803031916002c000a00c08250710000b42802c9903030000300c95496a040c2001692280240a80d00c1d411502e008000155040c01c2900181203e5009484031030142400300c2c0f60a600304640a59a0194080990110305510071000050128064500090301410380c0d0300080c1150301c265406d80028170540e10300c1400844600c9940001d1681100a5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272603264 1250 272602014 272602027
    0xc0f03030d090201050409060608010612090f02010507031107030b070329060c0a0605131a100302090903070203070b13051c08030c0d1b081b120c1902010204060f05 72
    0x80e501e100e03031010038404907280c0c1da501c011a40110300f5500582604602481040e0700c03000028140c5800740314080025000032034400290119118100c00300d500007000c050041010780041d0b031190302c943d0f02203040151030030012440711003d02886028620440c2894610308156000130195075140400b54902a0508186000c920307841030050b1003100b0942e591515084150f01031030810003805406840a07080070100300076030380299103601c401c612400c221080c143c030054404100c0c1408690514400403401300900251401c3e49441c0e40c4038000a045902e003091039030209081000f10341c03010668190101d4103080411391300d5540c401500c41510090b500040c0c803100307159001800720016000000010101d4010038441c0222034402a00000c10f200c08003000b59000004e4280525000c00240c043c4041656a4124040c6000c100c91a0118034145010b4a003080305580001d0f200121a0a04010410b4141c925200700c0303a124866800061700c2c2c038030780000501640481c0201008004041000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272604514 1250 272603264 272603269
    0xf0a11071406030a05040f050d0207080607030c0e0f12070b13120f060906060f08100e010501080c01120e0a0803010f0e13030302070c0803030a0903090b0c0703030f0512040f02030c0f 80
    0x40c0c0780e1240c10800e0101c1c951b1035500303140361500401000900345005c1d03a01c01296003034002803e034044034990012601c0503500d01c4021012210101e038000f000940c001c41d010480d2a002d07802144010005010f1810001c0d0b030204145030070410b0348030105161001c0342c00c40c04c081e90f84020a00903c800c0c103090050300207070f588060402c1c40b49030004085e1903076038000c0414040b81c0c3e84201d02070103507108184e20042c1c4882c2400d0b540c001340c824402c0e01030700342403e61110900601680e41200c03d188003d203003c00c0780d00010766212a0502d20040c03c65610002b00d09120000c000b16000103000e00c00c1140e4950511415074181016078210766004207040c0d0a001445285441400c00e494143c580113031910550b20702013403100070320350103050180302c048280500411141d020b140d4079842902d40050480d90344200b48100e0248011055054012500030000f29004100c164110407083c40d000740761807040f01c1c910072401c03c00c3d1016282c40704240107c40840c01c041104c43d1480b0350440d04200c46044a000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272605764 1250 272604514 272604517
    0x50604030206030a0b1005030103050c0a0303081501051903050709232106040302030306030c0a0b1902030d0203010f051305151210090813060c030210050c0f0a11071406 74
    0x8000d00420700000084c130034000f50b03400006019801046504032801100300242690402e000544071402005504105898030217202021a9419240e1148a41e112800490b458035030744122410b00c0002c04c00035445400030020302641c3c1080c0d40b400100c6080c40c040040445501d5000483d400d40e01c03890b07091120300d400d005007254440440380340c880c0f08215050110b101c200d03100140440d01c1001c0a110400d030b0080041d40c480c2e9803e90807540481c1c0c00d40d003080301d215910b2140c1880c0c0c4d081006103ca5813000e0926488055006004076480c0440041420b82203a00903404044178034a0f180d414403103490328200c1481c0e0362400510500250411078451a081c0c090346101d61300c0b61a04080d00c002d100400d0090071024a600c20302000114080e06192000d0350100c01c0454910100d080e010807040c0c010600d011003e034041d402403140300708060001008040141010f01d00074028000c2d01c3e03141d460300d401400f0100550780c40201c1c0180460b400c0b803800031986c0210319003c101a01003451501c42e0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272607014 1250 272605764 272605769
    0x61d010e0c0708040b1809060303120f060301090b180105010902090f10020c04020d0212010506030108100b180c07050f01051e060409080708040e09280c081f0b0a050604 74
    0xc401d2561860b003407400c1c103e284640c0d4001e0600142c0418903007000b403200c0410010824081e292038034141e07142420103803240310744105d61000201c14030101d440c44050541d0a940520040c0c00010303004282d0311000b048410071a6900c52540c00e0240389403403040c0c01e005403401008513160a6084c2140e40000070104d0003540b40d02c50049644919411603144200501988200090400c40d1b843d84052913000107548040c9080c04000b034040000991801c02404590403581c050000d410f404000c400c544004c2c0803070000c1e03654807034041448041c907040c44210780d902980011200c240d4541981c5405401e0810031b241c4940142d14203400c014615002510443d500e0a40007440c603410395498002070014090081c3c0640240c0c0d010031184208564180100f0035107249200d07850060752503074201070307541080003105002446850085103244081074008844584103d000b5030016448082240c0740c0440c0705a4400700e108510b821840e151058071031003011400a42e000510790303040c940030490078805ca1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272608264 1250 272607014 272607031
    0x4030c0f1506060c060b030307081c02190f1805010f03020d02040e0c0a080a020702011e02150a02130e010b03150310020c010906060603090b16050702040e01061d010e 73
    0x3a8005801c0010510440c21a2038110000b00401030b1038040007403c108081c5811610b643c6092500102c03031400005690689034000d00f100d140c1006c202003024820b0b00c00c010303042c0d050740038000c0d140d03005000210748030841210780d280460512001001440c108580d14800c001d94480303e81031200d41d90101c0001101220b5042c05070355600ea4040b950000d1017140d100401030b1341c10006004c02d00507403034010f00030302e9065902c080f416194400d100e4120f01c40c0c2140240031880c00e40400c517030311204800e210720610f03076401951040010202d031001c511000f16602c41c0119030020701c050000e20000c0c400005003a0300301d251256903051411003c0c0310310001e04441e51006030f441c041c0d405c41ea01000f07035440042c1c040400b17544456045408502911010074101d40e00340c00c01e00702140c164424847c0507107542c0c008036245800d850704608551800342071307100d04040200801103030f0056104c0b07010b076070b0040c10307003c00024240d4589480700c400046414541c1e00c0c070343c0751000100440f220300308400d5000030a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272609514 1250 272608264 272608283
    0xe0105040b13051c090905010f05040c02120301140406050d0f12050a0509061b0a030809190f020f03010b120304090b010807090e150a0b03070306080304060f0815030328030504030c 79
    0xb525058640740c5d200d03070202110038140f500100310003000d0b80203801211010b81d414060b8000d990000e91300c440056440c19078441040c0010095084410410b8205020160000802c50b80b1b400100f800000401400e071410300f02c1c58416401c0008420407a43d4252080c6446402e003500f400c0010002e11500320002e100d510040307403510340c900001c405802c140d0f00c0c89003100c1c00200c2c540b4020742a49002c60303000b400da0192101c2070760106041c5204040159204010021120090f0b08201c940b080e0000400c1d0190341e141403280080c0c40f40611850001504402580c81e285048404010b0f0340105d0070085c1041510303410710844a4124002c102603070505207407450160b0f220344014404c43e80550382030360b1004100d100020419144801075020f4451aa400e20125446090040d903920a61054070b00262041060711607051040350410b4200740c2801410007030018000010740786810441a5a40a003130180d203c80c40c10b02181c1460b42c0c10140d6003003d002e1450191005003000360044000340100c4003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272610764 1250 272609514 272609563
    0x9080c010209010e043c0504050f060f01061202071a010807080f1504080c01110a090503060601090602100c110d0315060e03100c03090c0806101d180304090e0105040b1305 75
    0x20828154451b2140d03070042001a031615041c00c55560b0402000c41501c1c3c040d10380454841c0c2c40c01c5941a05803441d81c0c99221440c1d0004e508a00294020300d4191100400802100303000d94885090a00800a00000740a22820030220b58280b048242d00c0e02c103581c0c08a0502480c89a076001030031b901903000b0242544807658038204501400a03015034131442080001c80c041030980000202c4281d80081e8200d50195541000544414616018550243c1c3c022100450b036550143c110404203050792900d01c03800f25149004504d000c041d444001c0c0480c0d20350304500304901c002189103004100394030701500d08102050100c0d440344401d5500480c040c0e100c0c00702940c00c1e070094005440d540e03132280806a08542d1008119240e100a0394122260318103000001407542155403140000d0140801894064175411481d82c800d1a00812a10040c0001d0000050f01010361144000012104001140601d898034010500020081103101c2c242154000d40c404140002000608180d103414600c0c40440e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272612014 1250 272610764 272610851
    0x90603060b25051f02031501050901141b0303040606031406010308041514071104060909032c0310061a07050c0d080418140901020304021e0409080c010209010e04 71
    0x225060301c070784c2a25040130503401d465900e640198820581c01d1580701c4a020b21200442d03080c481d1040742400120907a041040d02c00d0790b40d008042540c03210403030710300001400d0034079411030300304440990f011581c5000070000e0105e01d144424210306150050807503581156101541d900583c013400c1110750080032240c00d2603000d091100c0f42c41c485c581c44940c0350b0100e403401c060300b40c900c414414011420400c0001d1140c940c0c0c020150340541c10b03110490020b241d1682c51240003011249091070105502c00d1a4031510b09000005201d10303c84000b041d8a0b0404108079110b40024080c464450b60420460011070b1021440f80c120300c05c200d6503e1794070b1805081080c101c1c095034100104a003143d074005801009140d001e0380c0d10100d00218035030302c0d6990101060807070000b160040c0d00206001252034203200c4034502010000c400070300020b01d0300035903190070030541c01c22540000c0981d40011070750603e40e00010015007440d000c940c1031000c40280103681030f054905130000c01c0b080030348036652558803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272613264 1250 272612014 272612023
    0x4051b0c1612060b01180b180409050d020d05030c03011404063f020f060a14040f03140601060203090409020d0f080909010b04050102060c0a120507090603060b2505 72
    0x814080a0309021584078924401034025200b01107036000e18003e294000ba5001e0401c19101c0c2c80b5400104020b2841c0c200208410f50000d10b56000d030191769101010640c2e42c5d48503120b50640070b1002840f40f405440000303442c1112901039081070000900800c0581c144402c1228113585602003483c1d0025100c50100b00641680c0d00540304101801c0c1d0046120700086000c82001c000603081c6070820001d940c0031001070a48210301035000005100300b00102c5c1450001062025074615281071038200f40035640b00d16030880d0f000801003518440b410400d00190300c150803640c05600000d030086514007100131395a4410103103400d029a40b102805800d541e54034446a08582c1c1000075291460101d241c0460035a0040c0d4502c4c4c401c2c980c080010800758080800e0754148d54068000700b6098581d241d404c3d00341c1d0000c40521042000ba0b2907011228005401602d0050b40c003034442d0ad01c660704001c5c018080e90080d400c40030541d0300074000b0084103418104005050301602d011190000410300303006080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272614514 1250 272613264 272613283
    0x3070f030e10290a0911040905040807110301150905070e0604030b07110a081213080711030606121c020f0607080105031b0108040312020d180203070504051b0c 70
    0x2d00074811600d0031202150000305803039454560821003a105882e0314483c0308810521140c00c03040f68101804524060303400b01e82c003001c0001096040c1a582c8a42d20140e42085500326081c3c800807883c101001295a50121000c0088000303110030350050b078481404034040e1050b050100d441e840800c00e0a03018210740346824001802031a51191241400f800072901900c0d5140050549002a841d284011138819606a4803d403101e00d44a4401516100c9000c003805e40201c880c034004c400800143d12900070301c0000d109200701400001ca00c810181091b80007400c2d5400788070801d52400e08400081030b8050b040b13461881c8007039200c9103010120300e002641d054499181c450a014040c20a801241490403a0400c40071501441b0011240f2590998214101808902e005022500190145c603c05244c8104030364018180502e040054064030320b400e00c1e01001080700c9880740c040d400d080c0900e01c0503100666040c0b021b820442818030003c041c00b003e0184400e40400c405800700c10074082d1541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272615764 1250 272614514 272614541
    0x70f112d09010b04030b070503060a092f03152806110d1e050d09050303070e09090604020f010c0c0801090b060405070201060b09010c03020a0c060503100b04050603070f03 75
    0x80d1030100a0180340100c4101203030034452a07501e4000140f03e40184200d0f810b59a002d0b0088603151600038040c4c03002c0d00082c10740c0d544401d080101141d98880740c07103000a000e220441501540c2101c0c0304481c031031900258104040d0404000f04211602004001c6803040c50a44402c0c0b0f030045e80c0000f64090b441010800040c1074540c5100040c140d510419111501c0d50700001d0b0f130a29801d1702411348040740001f0000110448000740041c0041c01346001c3e1400c80c00411012039906510783e50035040d030340101c4440c80415003210f002c0440342013501c0b00503480051030000308102d00309174001410102c61506401c0c100b26075801c4400410865400000c010a503d000074401c031003041c600a80300722001c40f4250b0099281c5400549600d205000306021904040c058901d0480d280c0c004648038046868160294421311072400f0020301140542001800d4a5079101d44a0415100d075001d4041a42c0c00041e48800c148420701c601c3e69200e0840c0e80101050034001283c0c100224240e000d01284100d001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272617014 1250 272615764 272615809
    0x20c061e160b0a020304020a030b06010c0203070b030901110715051905010303020703032c0108131e030905010903080d0f0608060f18070e01030b0c040807090e06010b070f11 76
    0x1901203641900307600d19903101d1103400b481c55807001c038040101e0100310741c046d5002d5105203080000c500003103900e50b00030300103141400386069240c000c030303143c4106035100d0341281000204010040500b0b01c41c135004176804441c10791400006485100c0d4044131030303010500959417100410500c550380840c06c0b0b210404101d05112660b0350b070501a49681880c8815004103091103046001d0000c8024041489948180c000750180c50000c011a20194010a40040114404030802c00301350104905903012040c00b80d026001032283c540102105a2503208605011001d40c017800001c042c0410780c0c51a10ba42000011034020050b41c3e4806842075038410600f5000d541c09010f40e15084100c0c1a10400000c60a0054041c002e9030f101c2e03680a00d8440c40001c042040018800140789d04007271a041641441854242600c9500883c1460040c1d40316641042c0c4c1ca111a0b00e01450900041340140b03c04100c49082c007032161540b061102c4803810080c9a0300088001c0f000c255a02d000002c4005003a01680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272618264 1250 272617014 272617027
    0x7030809040e0d03140a05060d12050c0307050c12010207081c0902100f08010e0603031e071a04121d060d0f021813061401050705011103070909140601020c061e 70
    0x1074001e00c25400c40c0851140103030005002c41001d405003038023642002d031501d00501074548a01207816805802d032010402d0401802041001c20030150060b2230151001e0316040000408002640f00e0704603246d480741c0d006000c14000702c0d600506943e006140c9500d18200d01d029240400c000b008000f200039030007801c1004020b03c9603408100b50904240e65114801d6590b201c4000b01c003213080403142c09a043e8030230009896101c60b107c41000d00040041402400e003e580d41d01c00605001100d46c05035440100c0080109000d60990320f071110307800906016001c481c00700f0342c0100c052865030a650103104009682042d840700c80d40700034806d00310300c442192140010301e85011718010001440d0301c1251140b0034966021440c1c030410007143c400f2002c0100600c42807005544c1500b1102054a56558420304c0303440e6046000001d510488095640211a03802d200110040303880c5041640000d1016004110060b40c0014101c8010402103a0080c0c8407268825400f0b28400307000b00c003107007101020481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272619514 1250 272618264 272618267
    0x70c080d020711040b12030405010e0f060c0c01080f0f04020d0f0606080d0207080303060603040215040e0a0f0f09030906140c190c08121603090819020901080a0507030809040e0d 78
    0x401c2e41e010001c40307062040c0c24540c001c00107004008000306c4010b80080004209940c0900c0d91201c9100c8050b1400c400108000000303040d9400c030490042441c1c0069200345040e40c0e0001c121036110040d588120380e80d083c000000c61414000400c001d00440e030b032543c41c206000304628030040d6a40d100c6c5042c403903140c89440050f00e5603c543c18240240c8940e0a000c03443c09030200130789204d2074001d08100d040d5502c41e02008003100c00e00801f516240300810000c9091181180301911a6807841d4011a400c0303040a544000c503103001004401c010701c0c0024840002e60b00c5100c0108039211403402c3d00c045150f03454101c0480c030403600044003503c41c1c80320300b030b40841340340c42c982201600401d420082280d5034052140c031141c803481c000b02c4400c82080102d102c0d2040301d212506942c024a8017010389926a400c50789004d03078004045030060700c4010050304501c2e003204040c1c058030381a005004a9042662050b5580500f8000240b4452000c6980035040d22950720030462002c4400171200d0180c0003040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272620764 1250 272619514 272619533
    0x301020307110c030a051207020103021303051b09060f0d06180302070504150b0a1815120b0604061704060b060f030106020601050307120303020c0a150b03100506030303070c080d0207 80
    0x880441c0d4083c50204040318540800c0f42c081694011010300a500f58514200c80164400700c0c00b02e06060342813000301084070000e03880c64007851066000f0300c4a6034042c1001041c8907410041c0f42e101d55810010403400c1e86a100f4520030300807007514400c1413441c03107203440300240075403000c10380b003d0500e600840c00b850380c0040d000044401c156010050442085500740e5034406a0084210f5140301300044010301303108000c404450b80701c1d414541c0105032034500c41440c56610009010008044c6a1601650060352141000305401200e1061910b45060409801201c014400e8820b0362170000c0024140680c40e045100110801400e5941d42c0c0d8410614a4141d0000e024040c01885224004905400c002603c80d00f55040c1f014005043c403031030fa40c1140a03602a109405480c00362145500c00a07000341186450700144110200b440711170941854a044202d680e00c2500508110a00c44541c5002c030440b0f0f040801494181c20304440c80c14511814494031310341907502440080d0303c40900240c80c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272622014 1250 272620764 272620787
    0x20105090f040906230c070b0103020d0303020f1201150207081009110402031e010603060b030a050415060902041503060e010e040201020f06040c03061103190203060d150506030c011b02011d0301020307 88
    0x5d651280d030780342d2100b4840c0034000c2100040074590024010300146c80e02c4104900c10354031a00d00580740282e8503404404540008105000080d0f051006000001210203013a404a070039100070201c851403c1c40b0300317680340c2600d410088031703999816005090212215000070300180c0504103542c0c90400121410b00071a544e5509500c3e56407c00c004220b0520034083d003011107d2aa001d02e040d81c035881d200c90000e00024008440880680c800703680c20620500a203402004030101c01602d607407409a840600582c412040030400d03140c01c00504c00750f224181000d0640d1030342c520070b0760203640e113200603403416040442c0f40c0560300c1410104010006074090f032500b680e00c11203007401041304107080c400e5280000c2d1816050300c203100010071414410703070b8051940f1080050490f0b00c5044d1a454075100030290035403046800741c40f00208205402c041010600007002841c240c1c080500c5441864040040e15030001c0c104100045041d0540007503900100c0d1201c1b0080085560f0b082c01d14000d0b001400a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272623264 1250 272622014 272622071
    0x80601121406040f0201050a030212040b01030b0c0a09090b01030e060f01090c0903081902011503230a02060d0506040915020a0e030d02030a14040312050d060b07020105090f040906 79
    0x1154456000325940d0b0003140d0084d404c0781c45404907030043d52140c0100c07112008055090001d001800a41200390380160b014456602c20b0b035042d810114000d12008003403010100c4200203001405910610030f0044130304070303100003410200030001200500030220010b8514480c0d4070510250071420810b85040301d880d510100308000d07841c042500c01c13040034440501f00034000d002615a140d03076001c2d50001c003100c1d070bc0000307201d07000400c801c4040000e64000340c40441d60100152a0b8440c00c260816405a01400621040b070740d5a0002c0c4192240d9484114a151210003142d21a15540c22201c222540200181c5100b255400c3c140000d41203901c401e40065000c41064006040c08100705000002a502840c5004145c1e0400da0f00304003800900f001140c010800000030907000b41085180e40c00075910141e946d105802d02800b500c02540140ca00208100103060040c0c0c1c00c1421501c100a055071305456109081d00060000d0040c4200a04480c0c2040c0711400c03005031000444044e031491 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272624514 1250 272623264 272623283
    0x3070b0f0403120906030f0c050d050a0f0e03070614090a02060d020c0a030e010210050712090c0312030606020d0825020307050709020d1103010e0c03131e0b0a0c021b01050408060112 80
    0x4916207400c8d00c8200a0650115400308601100d10b00950001540810403000100d885281019500102c2c0c0d84550442c01c1c541010485c07004004c11750242d001d54203442020000207007400103146031241e02e4003a00030320840c40001c05006841264054404540411040d20b80512803802c0c00781600049415490050292004003c0440c06070f00c107c60080041d0f0340c41ea640011909045c4006280c40030048d900380302801c1d03000000848514404814154a0f40c0c0865404d1a106019150201005420003032200040c104000a9441d640c000e00d0036080640c558441d61034402c09904510407104080c007540503034400407410900c40d0b0014011000c600c0741c100181c4a2244a035005030000380150b00401000d03c000c80c0404851402840e000a1020418a400507655403091205200c0c1c644000b03030941d003c400c10007408401e0508a5000200034014846e0350030400d03009440b408416002c003589005070f00510082d0f44610140da01800c08a01200d04558507a0107808140c1c030301c404211801d412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272625764 1250 272624514 272624531
    0xb070906141614010209030102041d0610081302180f0910090c0e0703020f1201051e030a060c110d110f070b040308090402120f0a0b03060603070b0f040312090603 71
    0x70041120942c000d5000c02072954081c940d2602e008401c0181c4000b59503400b48440b60b202d81d0207200800007030006400d04006110319500d04a196180140014480c000d0810704183c007076040a0301c20b038081c41558034004801c589100080d110f15028907450100c038102410010359141400106005428010441c4c1c410100101d001e0207603405520001c022009242040155680030b81400703404c000d09081c007508210030601004480e400024001c0035030005040104101d090070902003a42c07108900070042c0300d41c0c08101290b41d90030071240042c001036440c840c06951070311030207940c00c119281c44255030158410705070040411000f5540f1140a02851030b58550301000014240101c1e0b003407407941410a40345032603084003500a2403181e60410740802a00c0a440c0c0402d09a44c441c00301c170181c044040c1800840d40084601c40c0300124060b82c000c0080c0001a94000344000880d001c58104075926000c00400074090700650b400109828100d0200e0b0300c12541082d00001964500d43d0100300150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272627014 1250 272625764 272625797
    0x31407090c0203040504020c0708061f090908040b0702010c0b090c04050f27010e07090c17010e011415040306231e0a0216032106050603010b160b070906 67
    0x1d000c00310310000340c1e000f04400c10880c103061700644401d000510649205a5961503c1c5042c40812a002912140041d489400c0076185111080150580c04801c201149a983d60340000348a03500503408800c40204402d005c5a1044200c01e0501d0340c05484050300b070808d0540240d03100d034600740c45845541040e00103245d1810494140c0d1160540e928070800c07400500800c02e110030380c10746120f00507540b12020002c0b80c0f88104501c80050004c9000080c120003490002400500c021b101c805d0b41c4a40e150040005d51103a6540b18155081d8591000b026200d4800207642940d00501600078904c01050000c18004194840e00c15008042c44250041000b03440148074400222055450000e0a0301c0c410500328130207910707a500030034100006180c000070002410030031009020840000300140c5030241c0a01c50310300c48045c1c0c03440e0402c09110f002d06241c000359046c041402815081c800100d119111904141000c0350304540107a070100c2c050922030b000400008a5018032000725200520b07440c0c441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272628264 1250 272627014 272627021
    0x1b040b031b130b0310050612070608070e010206100302040b211e0616080612100506010e03010b0d080a05070c0801020c12030112030c1401060602030408012d1509020403140709 77
    0x83c90004c1c050b22280c00a081c841008207000b9114941086000d10103011403201001104080c0c900754503a91043d103800600104980906201c00d81190000c03c00e1207050800c0d954030b84180c076412a4045050300700394000c00e006000456450034895000f5000704140c607008506045840c1d041d015945240b40d403048516910107050303075005d50b00031040d00c140b04d009201e0444207400c190018449154060442e0115107020b000d010401011540c034010300406603000002c0d0901240d0a0f4000c2c080c0301d04200000b00710441c2c8001c050300c03404000a6404580388141c0c201c6092690090364004455141c0c00321900030340100c1e01d40d1a8920034002010541d00b054815a070490700c898480d00180401d6550480d00300307080d08412204e2258800c040703600b104080c040c07440941515402161181d2405000509450b208940d03d10100e078003aa44030b80303a07503140c40b503440a07110280c004500c030015010054500d00071503008000e41840410301004110380341e029100ea82440700308a4440684a6542c441103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272629514 1250 272628264 272628281
    0x606050102071a0f070209070203090109080607020d11012304060605040603120e011205071119030806010f02031c020307030b3118050a031e021b040b031b13 69
    0x504150100180070901d80001802c0480309080b01318146134282c2d0100d0100308044e40c10030096000880c041c00c0659011400c0300041c00c0b0308000b0001424141400b0b916002d14400903010003a49621110709401c00350414102035000c00b1110791140710300c01080c1c80d6200700f034500301e44003800c0401c0052039250038005e001c2903d411a0300591544804041a1104e00b01018035138103100a41d4102c54400f415441428802d4515840c1e15042c1c004c000c5030103023002c2d031600342c003101050031490903000f0a40c4902c8455104100382401180744070304541c1a40340d4002d0100b146440c8600e010258107105454000e5030055800d51814001c0141d00010042140d5007481c1a68007851070300c54080141d15140039508200104078000200d0400701031350b88803e01c0020505a443d030340405041010194001080008000b130030b00300e4800442c0c0300e00c0094a9a04003102440c034094013002521035551985d000d8401002e008080f84e0303e082c614080398070f985200d030460500c00c00c03030154001184041806408038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272630764 1250 272629514 272629529
    0xa0b09030316140d05040203150103110102070801140a050606040f060e01080702010e06270a08190801141011060a06290702090a060803030a09060b0a140904060b040c0c060605010207 80
    0x4203104d002102000341401002640c0c58400c0c154403a25500001104a029502420000c85e0b100c00c49030000e454400294404a51a0301d0b106800340d01c582ca201900e80c01c00d0f62464082599103c1d4400114280529002040009282c060000381c464100807c0303910b404003a02e800039a5595031509a00302c0345c02803221301150b00000005010b03071100515803d1001c000e484103060511b602615545404000d807800c460b1441c0001d580401910031000c0a203c0f041c00745400c50344e0f58180034850641014a4034140d001703500720f84082c1441401584119a45c030b02040c126407552808402c0328000e400030740f0420100c28000704a016000c1c21441d480c0c030041540c140c0341403070b0645540c248403900300000e14000780743d0f5030360002140440c000d0000b5401010222400318562040d4142001290001781c0180d20508145404110240d190181e5200c0c1c20000c607122662030351907081c8840500000301c40c090307200b8584501000b80c0340d045040d03e00340b603004010801c19280c0b11030040e80c1d80e41083c0a4880c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272632014 1250 272630764 272630767
    0x70503071521110a0e030709150605070602250c061e0e0f04020a02030a030b0a12141e030408070e06010e1e0402070f0b1612020c0a0b0903031614 64
    0x140100342da1200c03003400009003000030030101c03142c0c1c400c4a03070f00300039092000140c078001074020b245420402600906080c403810407615013509440031100c3d44501c24801448004500c000900010f581034460780041b00c200380c0f1081802c40c0c00c43c2c2202c000130f1b404886441c250240820490301c10142d480b0f0034801c125450004031001101580c2c440e0b121020558040f04003421140d103a02e0b51f0000e04801210f1380c0045403659803002000d0140c0b081070244a00410340b20301c003005100a030a188160003500715641102c14141651402d041611940b502080502c60380305814480100100134011950805e0650300c1841e114901d42d04038420507201c0c240001c0900c90200f00d185464416803051000c0051807072003400e0b0850108041c0c0c0c100c003009440521000c41390005001118050562000303108941803440d48d540c4402600e5a001c0007492411a940800c00d60b0300580300300400c129103074000080e0600d0740f41c10318980d03aa0341e00481d89040844520425944007a0050280065a82e07010303c206 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272633264 1250 272632014 272632037
    0x41203031d0c1c050a03050309190312020d0e010e0606030d11120f0c01060902070c0e1006050f0915030a060e1005041a040c0e04050c160b090a05030a020705030715 72
    0x804203042c280d289020030b01a02e55880082d004000001c40181b0984510340c030b900c1c08541890500c1006003c001700b442d0304102100010754000c40c3c0148078821910010384400004c2802c41c01401c14010a1005610380316600e0203680000032070300e20500d0110116140080c400b4000c4803042c0b070310b154149503a400b20403103803100c0c048c4501418901c0d201748912410a082c1c280074500791081e81d48504e02c090350000703010003405030028518024141da50240d0545d810b2807060074a0384652440303038400b0050049041c0410340b03002402c4075114803004126421400d0705103a204659441518080046031408900141c0d40c1041080326100740d2203c540d0100c0030f442c01050101400d140e0f00803940d18046040d000d4020354592090035203a11065036104080910382c0f0505c411900050004040c03004240206140ca525400b000c0c0d6007654001d504d042251521080145851446840140135000110b0800903680d40001e0200444100b00c0071915806d0307969903482c0171071190403c1c8100161581962 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272634514 1250 272633264 272633269
    0x60c0b1303020a150501150305010305060712150609170706300504080909070306141905030a030c0b010b090603040206090a0b04060203120a050c09190308041203031d0c 74
    0x1a040980030340180d44000d942a03a803500f02c0e900b9091094840c07075440c801032102a03581c043c3e0071111044c0303040400c422b50543d21959501c2800074a41001c0110340300b80d40390030940607000681303c8041510041500f40e1145030180684000c0e004440c207032011070070f0181000070005051804c07140700f0f48614802c8040322407404140340c0314031800043c00c80c20640000c07641c14a4032031140b04601442d14181c844840384200000d045010300140701b00b50a003e420302462014030380d4002041e0701289c1c1c406869084000150481303500741e015903414003407400d60400b81600210b4a0350594801e0000190300e80e00d49034a4803860098405007508180240700160050800300003e10400d00000c00303500300b91b65110110180b40d80a0340217400103810205401500a06610b01a03812440c8190188054503020044e05014083c07082d0481c030518540030020480341c0d0018000020715005800c8540d41d50b00c03182111081c4050f800101c0000303280c465032107540e061601da80d1103c640500041e2513040c0c03000c0d04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272635764 1250 272634514 272634541
    0xa02031c090210050d060806040305120901060e070c0302120d06030311030309060109020c010e07091a041b0c230c0a0e06010e06090102100e010f0e1f110c0d08090601060c0b 76
    0x269800000d03031b00e01001c0f030455420800d46124a119540783c84d40c0c2e0007807060011406002a0000c48140e0621000b80240940c481da0654030400303518080c1c007022050b0070200d2910031440003031350300301d200083d000c00c0c844010b811050550b400f0383c480e000182007400405035244403c03603d9022541105005105096041d0001e22400786660000f15154a07680c1d5080e04000300c591110815a5540e00c0c0b0301259070b503c429118041004aa081140c0f0b003110308221482d003d00c00c01803042100c060581d0042010000c00c42c00900341c4080162140c4c05c1e0f04407090340c1c0f8107031010361500c286041c203000504801c9508200e88240c030180d489080c200190b1080c014203030010300e4100c2c154040c003c3c0541d41410b40748944010b66130414008101c081404654000b01c0d1100d6000350b000b50000b000d0038228a00d400010003c10f00c480a0028040d81c100e41035041501030750381a1102405070117607a00250b94083c04590240105000f40d440d40d0b41e0383c1c00140c50040490f88000d0403000c01600144940680390b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272637014 1250 272635764 272635777
    0x10050c0c220212040b09030403080304171303080d1505240f0f090f01020c06070b040f0b0c22180e1e070806010504140411010e060a02031c09021005 65
    0x40c84100c400d8489640030781e08461024541e4000c2d41c000c110900802d011740300d030040e5048010714a05801d41e01d41070750302d20005101030030072030ba80c00004010f601510b0440b50324104d00042040541d4403443c084280740d001c1c00358010031900380801404640202115031040b100024030302c080c2c1d81880200c40f580140c0c0d84e202c1c051421014403008074040c10074002030408940d98022903544401d50001c00260401e0804ea160455100d80d1b896406074a42c402107a114540110030142c1d07554032841d04407484c1040c602e00610094540040c85140f40310040500303400c041048900c1a400508414130903072038014825614002080c851040c1d01101e50351141101c50f03051801e443e5095105011124051400200c85509034484402000002010710245014000031601440019400006078444000c060005064204d80d85526803440c4c2c080c0410a841400c041c003800d48074100f180740a92030390002d0107010b0f101e8001082c403603c1c4003100e01c1800c100c00d41c002c00d47c1d041a08003107402c955a80010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272638264 1250 272637014 272637049
    0x7030b104205041a03040308060d1110030b01030b0d020609043303030206091515210d1704021305070918020d0b01030e2e06031110050c0c 61
    0x2030350395405070856410504000081616220f5403a07240c90900301da44040c0260400082400340184000039078400c8030741e038010404407564110200c4c5400c0ca2106030201c61603075640b1070584020b400c2c4154140d0407051100509803001c000c810440030602c20984c3c80c21500035409601008242c4807807a00d136006da00081e0f212648882c54089400280e240d05a005032a2001c241c5011810002c055040208036031007061640035000300c0c2d080200359501442c02030148030041c10024182d2045071603810340303012070300f580f0f40e81f00c5184200203040580711161040702c10002248100d2513519024026403603401254054000541040040700c044001c00c0040c128a080041404002035505c030702850302d1021480c1c04800503a103d44c224482000c98801c224170505143c100418503035a140003140c0d0481004c000040910b810b8840c0c0721039141c090000a554080c9880c201010042c40050f040c02b42e61040140c8100103110b101d0041568580200c40085103540d000d44590380e60742c2050b00c110000004403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272639514 1250 272638264 272638349
    0x30a0b070e09040b0a0501170604020f13020a0c02040b0427060b09010f0906060c02060a0804080d0f1a0103020f04060e0a090e0610140a03030e180103030207030b10 72
    0x8070000580304000076141961090790b440b06102034210144103080c01008903800110702c08900e603e407651201c100401c0603200700c4035202c00e64402c7d00e0300c03d42d90741402c0000c802150b44415900002d0000303040303608d050307006614000c10900c41e820288100c2081107110700748100e00606258640c102045500e070129101030321001c6191b5641c8030301d0441c034003900328044a1240c0c24103068014040721480da00503401c00030b5840480340503855040c1241e0740b242d690315204446558601b801002445403440564125152001e01141c0350cc19510900c4110720fa817035074442c540800d00044090380100740800c2c4004104200c108060350052005040000e400342815074810b94a40c030131400c0340c800c3d00c1c0c4c601c406c0e04035070100a11090b00d141c20b40c1c090700c0c080c030000e107060046001050196040f070200406100a1001451090f40e9508a403000c0b2141403c402d4841d6850b4500203403185114841103400f039005401244c101e2014036020b0b002c1d03603440e0b18035031030822801c40c180040d01082c802072005010b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 272640764 1250 272639514 272639537
    0x311030a0602070b07020d081b0d0605090705070c0e0601080105130e010207060b1c080d020c19050304050901060305010b4015090f06030c090b0a0305071d030a0b07 72
    0x300c1d40041d0064501882000410b45020795020741403400f00c503007070402c0108400c20402c070400202d20f03850301045076240042d182c00c804103101c402000207812081c0d22020350300c1002401030340203004008880c804c0c0034090106581d500901d08400301540c1c9640452203c400501031804d00366104142c1f42c0303140c0000b0074030703800110000f400c9a200e90300580b881c40d1070318100001400c6c030304e186484a41a520303868044440e40e864181640c0141c040b03500790142c0010f241c01400c0c2040100c01080501700800e1040581e071854000c3e665071051050138002c02d1001d0002900c0c9010744039043c100c07400c001d00c151500c180b03928120b03150806013071031909202222045415500110814503034161040e9154550281000240e4840c50f22540d0240c0c00c0041c02c0c0f009010038030068962404486890402049489001506803110b078110741203460490f03001704104600c0344d41600700758042d0b507840d11030450300d81092420b2207070690702d01032590b0035034480712481000070244000641c0c400d0091402441662 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 272642014 1250 272640764 272640773
    0x130302190b01140f151605100204031109040804060e060d18030e120c0409050309060a0e01140403050d2114060f040605011d030a140616180311030a 65
    0x15038119041d00c01d1044200144190200340701030607425042101d101511016a03400210000c04454941c01984d1004c41e60440302c00180c5860400503510106982201281344000c000a400c544020ba0318401e41c2483c8501904100030170900481d007210786145803d00381141074a0004070b04002d41e0f0080030412400d88031054603c103500200861180c4031081000c1402c00403c91707020b100410344a07512404020f0170300710300010100c1c1490000d90b0045030040b85030038032a00b1409010802c40d08084006a00d07c101940301a0365007000704240c83e01d288010407582c81c5000ca020300d01006086900c4203444aa0190240c01c54120a400450045203801c42a103450001d44a07100c0044012005050600140e8075141c00090820a030649040240c10300e4030f80000d00c0c01c060103140240d0003400c07401e004101d44091024181998000407568a2005050000c41c0e0360401291a81414001000c100c0300f5540300c0d40c0b050b40c2200300c210f051026141541c40c1e1403c0c1c1c41014051a5161144d620144000b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 272643264 1250 272642014 272642053
    0x30103032102031f1e031b0e0903040906060e0901030303020c0f030d02070512130e0403021518060604140a0b01020a02090c040321020d0804020402120c0a0f020c09130302 75
    0x4404c030440382e4425000550450150300503a4100b0800306070ba108815411064440100341140d41220010108041c8640c06030381c0c1300065001030481010403020400a4130f000801801224610001013004135940c0904485c400d007415a0305a10056507801000806d1003a005090a00c1c0313810300352120305401200b001c0ca140e00000c0220101074020540a00344003052001800c87c1c1d4542840303d10380b0280121100d000c00081c000c5d21910304403400441c2c04e05100304000507480c075060540c110242007071080c046044c0780040514201e485810001243e508150140041d0f05120030404800d544600038491301034409074440b14118420318280e035001d40d9400014500601c962a0302942e21415402e03c1d051100140490b108000c11100c107940c440c035030000312550248640e1400400d40c4d11541f0008010f482107603070814001d030703484003400400d10141c1c0c0101b8050711980c8032043d01d05046841079884022420001e40d01608500002d03003103281a1004021481c03081c4103540c1603681521030030501d0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 272644514 1250 272643264 272643271
    0x4060b09040b011802090d031b080c03041a0c06010e22120216080322050d0b070e01030911090702120307090302040c0908030a031d100504230303010303210203 70
    0x210740b540c010008000040300944818003040742c29464004590040b0309075140c9004000c041101000f1400008034503400f03008080759018000c01ea8600903103a1140d03a980050164070103041d098086103080595010488220400300340103400b142c1c0ca020340044030300348020200c0f02d00c0a03171588c03218401c032112404001d0b010b10803c00050f03114664030000b4605804962500710406140340144003204000003035401e0302c8546032010094040c1601000d60050305503102c035130806061301240c0100941554078a100c0c82243d517078100c0f0305000000440c01d4503014900580b05200c940450310300d50811103019036005070940102e5444007a08403068441e0307032045031103a00080c0850018401c62806000d2110b1030100b80c40d0204140c2d007450202e917102c0c40790340521410f059854400c80341c04290b807079981420b00d03207500c01d0f83d0755031048142e644050002281d040741c101c02800c0c3c42c4904013440e4016100401206030056080d80e00b9664242c4003201c9035402c10010581c40d00e50f2210400550008521 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 272645764 1250 272644514 272644523
    0x1e030f0318120a080306031c050c0606091603090204380603040804060804020a09050a02041706070215090a0c0303110d020c030622060501060c0c0f0605090904060b0904 74
    0x26505521114684000e80301d09560344194241d044040008000080aa61441d080409195651500000245401d558103117041a65405045440c80c032030708107000d03168044c1070100351a141d95a007810020881c0c000c41d4685e032080421010f17062164420b60010401e584098800515001e010000050038039013101060080b00c00740c03803400580d48220841d0200d880741a00c000d811802c1c01c0c1c0c0c0f03604442c0180c0c0180c004000100000074103540c3c9458440e4001e0102c00380c00c209038207000d908200a544a0300401c40b1100c02c110a075000307400000384080c891281940074001007540c002410004030000b03014000d05225040c03107c00880d401c04132410055200780c441400c1c61003050409410320310001e544c0300564110004185c120b40380810f46940c0110180d00000480c82c0303050703902410a100d5100608018903020012814541000f42c1e0840e99001c1e58180c1402aa91100d040614000c0c1c026140050020311414000703003041680c40313070850310581c0041030700c0c62140d021900b203003401c0305d040c0c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 272647014 1250 272645764 272645767
    0x5040504020c0a1202030c0703030e0303070c0e010801181203090f061a0111010b090103030f09090e0f0c03030406050708070204020c030309010f1a0307180b0a0303090302010f0f0e1e030f03 83
    0x80400400104c401810b06050000d14103180c55406d50503100d04841c400503040c885a0401c013112035500b0300494000c15885640703100c0c01c5485e04c00924400e08240240c07000766180c9141d483e8808041045280940c0d400605551220302e070402c100c005d0080041c00f1100c41e81c40e9004540000c0890140402c0b030b10320001d8480f80c00d02c040000402071044501e440c501340c0d15100c2800c410392181c5500070b05489d01410100143c5903d0355003100d140840341c0c484507070989400f11180075560301084400310b0031203d10403160300c42e4200c001c158592145102d08030102c0d408001820026803180050007000f4001080142400340311512603086510468400c68240d64510204407114110700c500400d80016080c8050040c20860129948480c00d0040e180d0024024054a0003a01250030000307404d040500780c5108517540745800750250306a40801c0f808500c00d0708000380620f1048175501e40c884c1c4140d4030820380b641000c061103404407140f4043d107a0550529051106c60714100070070800740401c41d0003503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 272648264 1250 272647014 272647033
    0x40e0a05030319060509040201030b01050c15041506380409021b060601141803150702150c0723060106121b02061801062619120f05040504020c 63
    0x843da1110100507050003440c065040c0110f80b00d02400c0e07640541e0a00f00054590686001a18180100030b0303140e50b02d109002040c601c0f4140040d003140554815500f108240b9030141e2000151041400380e40d0101e5880c122501c0000b03281e4200b1240d6000d40c183c1441c0f1413007201c1c01502254825008844101d40018003070101e502e0303080f64924803224002c003805079818018002440c0f130a802c15030a20321040070a04030542c00c001c4140c40020310b00103013103510181c81007070b0310400113004940840160050392891015000010880361081c03601c609494075203c41030780c0703525144200080032000e4400f1101d00304416802044401e0103402592200c1c0300101000454000743d940c0400c49024000c1002c82d01c011098002440b41d8111001c450302410483c6103018090040545520049107883c403005504030840ca070b41030340c01604440c03409441420508072040d40c50413070110001414201041103800010b4800d140352442d084107031403d103260503610340001d130607038001c24008595174210314240d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 272649514 1250 272648264 272648281
    0xf0501050a021b070b0d020a140403060902031c0807050d020c060109020c190807060209131a010f0f081611060c18090f0c03040c05090a0c0311091e040e0a050303 71
    0x1054004003d00205180b50522008007082e00464031140c0020341c0100fa00c1006d903014051a0b00c0d1810300d0508161079554909000002c3e1071a00c000f680a40505034980100c0c0003a00f141c64803603d02c03900e4282d11522004d0040742c040c5d000b440c05070441a801d01283c05019014401d0f2070007030007004000f40e290026203a10350f040c2865101d080042d00c2c86d03940440000780400098400d040d40000740180c846c03040401049040390030311a01411149401c1c0b4031511200301410b0011008000e07643e102e04295144400d0740c42801d1910904007142002c000204481003148403034080008514010400700070000c2c425261400580b0000d00d130880201d184c01d540d28006070001e41d000400c9511a078141010b959070356003650040c140301040c000000c00a010f10041080040c003c06000d0008522858800810002002c0c8003c905001a05200f011300c200141348064552460004000f246e8200c00700d503244c03081a05119103160442c0d00c4055003154084140035071280302c1e020b80e014560300c1c0341c905034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 272650764 1250 272649514 272649547
    0x7061505030c010c1a0c0403050616090e04020108181c02150f2208070b0a0b10030515010c02151612020105071e031508010b04050c0c03160f0501050a02 67
    0x540e04101613800300d01c02048251005000f045400548124103803240d0701740b2510782c400d5030000790841c829801400031003505120310855142d82d41c0d0315039000544074103031500800006d40d4041d0000e503908012907003c507000764505800d12404c0d41115038000a10785040c0d2580f0109280c100980c0110303003d141c058202441031907000b402c0e400e02c549d8915044403034030114031076111566003c00041c40b0001c20080244110f540650b0810144036291800b103111070050700301c6050b854010203855016000f042c0c040e02566003e000074494849200f1080d40c01180c1410844409a901180300c00c84400c40410715001851600300c1580e035010302002034206a411045600050421685080d0800550b80c0d807261030401c0041318090351501041001c4021000f40a862000d010300b110312560000d00e442055000e81061002510280202d40d11242c07042c1290080b41d41c10038031a041000a50b480b80b040d2034914500d04c1c0b00340300c3d5152415803515a02d0845000b00c80081504c0c0e400a88203806440303211 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 272652014 1250 272650764 272650783
    0x210c020a050118030207171002182107050f0a0f2c011503020a020f07090608070f0f120201090e07080f0f1023040f020a1403010f05150706150503 64
    0x140d04040030f040ca513400035902c40051044040003840980484140a000d02c0415030042210390f042d500c0390042000310b2a14159018407900c0366150310640c112406c095100300041d5041840580207080c034050900440b0f0308d41c50b2205a01041d17924020518410041414014003100b04141602250890b001d440c8141340c1e074241004812030700300412121a128005402c100000c0c80d02585540e61103000340e19180c503000005807980a030b1140490280c156034011021299008120362285a07240704500c40100103010b00c617210203c2c034000344a112505e0a103980d4052061402c0c0d000c9503600c040e1030001ca4030950708040000c4001c0e060180262540c44190303080b02c0604004402401d000010380300d500c4691207044d10520103081014014030f0104114011840050028019040b9080500e0300035406891281c0224092030320380402180301c5821b0300d0682e02c0e041c10491520342040c0c100032014002206400e07161404110945c005031050190000c0311a0740741d1045d004509100c00c05003005940c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 272653264 1250 272652014 272652041
    0x708071101140c061302062a061810020c0f06040c03060c0f0f0e030f030d0e06090a020604060c020307050402070f0c0504290a051f08130206040501210c020a0501 71
    0xe203c080d209003408144160002041d940c0c02c0550604d602c00f20300503000719007411145030507100c95100c07a5120100d003200e150034642c0688a0907070352100708a000c400c4124404005601411040703010140f25030041100c02e101c0c00480d901034088800f046d15210080b1400c0f5020b4540813010402c00c00580100c01381c000c050300b0140258014154000d01140c082d459a43c2082541508000c46d41c60a2065803001c48500b416280c1ea003040e000c101024020581c0c102c08103116a5000514000003ca0401d000560040c0340500c0c2c18601081110750f4001d0010aa0b071502502100040c0c2d691284020b141480c8140c1d00380a09007160705040000d801554011800746042882c0300f401000501d01801d6501000d00358840e203680c80d280801c0400700b03590841a0450200700e40700c124000c0c640341c1d415601585950f000007a81d2151407119000d502c0c401e0003500120140002d000541c0985c00c4080c00c6a041e4640390070045918a240d0250b40c4100e81d4100035800041900d001c1c04000e00807501e02d003845 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 272654514 1250 272653264 272653267
    0xa060c0302071a1b0c03070b0105090115050705030c070f05090901090803131505090106031e03020d080a091a01080c060708091005220e0105030609100209010203070807110114 77
    0x3522000c070f42c003800d4680c082040d103031500012400a1031092050084031512851501d8280070740c20f040e070380d5121400907a154416034000003800d1a00c092101e069031003c0b00807445030080c1c0750090340c042e0405c20045a850105200381540078008112240052604690001c00c052801d000d1051709880070f0701c0c1442690502038400c0101d030310601280c1e0010311148a05141040e1820480320540740c19803280c070f0309404c0c4004d0052160054008006580c0514081406c1910b049614490110482c000070301681010b0392a0031454010749070250b000d600d030400854542d0080d03607000282c0c0100f18001c0c0401d114000140508401081011616001552494a0300400307484044140c00b80b440403e20440700c560501403554070604c25214042c2c10605c82900740c1e40d0101511030200070b00d0042900b60042c2400010b003526000481b180600e0300f6101400700810680d6048019502150205066110400c607503000180d030364004040d000c0c0505c00100064000500040080b004a640c80020480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 272655764 1250 272654514 272654527
    0x608090c0d0206130b07060213080a03080408091c0501240501091502030f030f0108151e06010912030305180c09010e07121404020405061014070206040905090a060c0302 74
    0x45101d000700500340c046403125200c0c0c80341c0c10040c055903043d4100c44800100401d96204100e0315802400d94404080907200005480b501501d03a103040e4400040d0000d01c0c22004038022550740001040d8581e000781a02020640000d401c9404c101c041100320349507075403404080a507101d400c00c555034503484d101012102603c0e2000080c0b14503410300400d03144078240504001e882d0700030011250782ca500c5901c195101c0c40c1c050402260010700348504041c0d405020002c500000c034a050700391160f503da040022000707a0a411243c00008010110f074180840a5808a071000030010b564012034425500401d03d46407800300c002c0320801c084800382c0d4940c008004807250740e55804885054840304819001c880d59a500119086c0400b008401d50481c603101805102c5821201010312450082d60240929104c5406004100c400d4110780000585da1502ea105900064801403e046000800880c10300c0c1d2640e29481c112101501c0010155110b500e000c42003000f1070040c1e0312021003504045040aa = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 272657014 1250 272655764 272655769
    0x10501060c060f020c07030309140f06030406020a0c060f0c090506070201020a0b0705190e03010b0f03060c0714010c0f02070b0f030a0c03093908030708030705041d010608090c 77
    0x441c00c2900030400d036243c85030b0808460a41e07041d291751900b100b045038400d551740d040240086a160180c203807188601d41440046042180c29090b0400028003a2031031640c0701c2e01c559000b500064464000c00032000000404580b140c000c0150709c03034044c80c3c00540b076003035106c010340014800c0d0b0107180070b1a0140b000ca00541c1c1c001c01c144500542014610340e50766550041154035203e49040410324052000e03001c66100e40c8a045110824000d030002c000840c150340c108030700880300c00107250303141d031021000940e0019a000039000040c46500d03548601d0007009811800d4504400500c3c0001d100d140108016950401141c001020a03a9400f8541120a25403504c5440000c29602480352203e8100f202e06100b603000390401604101403498041c1d6010000300208501d100140d006a006500201004070b5003048004031000c01c402541f5001881c1d5400296410081c104003d004060000140e07590118070310001e040761320301185403036605190026203000c40c09040304040d580021480440c41c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 272658264 1250 272657014 272657027
    0x90e0307061d060109020a0f052803021e070b0609070c02011b0f0b01151409041d0f01050441100c02100606030e0a030e030a0209041a070201050106 65
    0x1a0490740c04980062203051840d401450000040703542d10801000040303d1225502402d40010950741d9500d088504800031242d5018038110012030710402c2030041205240300324601c2c03158810703040c090700b010301e5481b01087c24402d0001d520400c0b80b0008004040102c4041900c0c0e0000080754079002c181008100140038003038841000341032180510011071140c100c0d6800205c240c1c0d02000d00d4030441c80d1464600a0490f00703100700314100200c10b020f1803202e805840c8100c06020100c02c0d2504cc1030000c010040a0840308800f030702c10403103601c2105180340061100c40d1020000c6400869142418508500d010704082010711640d0305d40000421200041811250114241d5503450520411004400d0610848200b8103030311901e450b1024481d02d4001c078004200061030315003003150960301e58003503080c1c404020b40c10702c240c0c010b451540000f0307008551280700100045c0032285900c0541d03011442211084d10140e0b201c650200e0311000020107100f00c0c5a00107500e10007401254905507021340310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 272659514 1250 272658264 272658277
    0xc040c031b080106120504020109051507050c0616060f1b0903050d030209060301090b120609070305060f09120c01020706020f04050405100f050d050102090a140112021201032405040615090e03 84
    0x5d582e214800700c2c0c150383c800c1040300c019100040180200c0b41c165481981d550b441602d048402e80a80303036020b07680b440e014040e02c01c403010070940580036010555442d001031030f007840079501d403944e18801030404036018910801008025200c19051a0a500301b0300d1070b10307041280000406004120740b444a072920320550b41103070050034000c2007420824000903403c0281e90b031800c000e84134507010481d6000c00026114200ca010390192a4103481d07110b81b00340c3c0c00c10304948007001d95009010103c03010442c1d100801116200d40700050421078075907102c0d0141c0c2c5c440b0500c01c00d208001302c4c0c2442149020300c900d940103c0b00d2881035540c2440c0c0303c4680c4103200e00d40f0940d407103152048460024017500303404030361101d10020322580074a070319003407040048010b00c0c9641c0e000900001009003604041e1084402011101680c803055a2031942c072160f0442d800c00510001942c002e84440303030400540206809548200c40c0071a1132800d54412403c0c200003039101c120143c0c1418103403404a4004800c0710302 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 272660764 1250 272659514 272659547
    0xe0f030f12093a0e0d17160501060f05031b06160515041703130b041a0906010602010b0609010e06030402210102180d03080a0e0c040c031b080106 64
    0x4550745010946007400f0551032200008000a0309890b440c02d40701954407100b500e41d6040c10205410500100d81e00c841080003075800007504100c40000c5455166044030104c3c28040441c6005508101c0800d42005068101c035281e45592041c081403220322000740203014103800810100c98101903c940542900d0307007150160340000f03200741500c2c4000000d13030080384d000b508980070a1011304250342107003811035040c0c0303040d02c10080801000ea00e0604403030140e18400c02d0a04004141d440d0004000c4000c4c200b00d030504001722001c2a00b100340942144510a21809807020390314250000c1c0c21340c5d559414144c130800d002c0103100b0041c6c1e0007205c2d054444406444041c0c6941d01e83c404900d410317912010400008011241407050700d80d05400908000a20f09480e104441b1020140720059921103001804140244005a103000140d4803072040c0d1a03840c1d00b07d8241d0569400803908590361050094002034854040149080c0402c1c410b0851110b2850000010b40c500b441c001e059440c0800080c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 272661870 1106 272660764 272660797
    0xc0d030e091305060a02030a090b011e09110d02130305070e041e0b04240510030308010b0a2a0501050106030516020c130c1e030e0f030f 60
    0x4206910030024082515401882c00103900001e0001030b05560300d400750302c04134030301544e258006d2024200380c0d1340080c04424040d583301101e4003d03060341804c00c03039030451046c1340b08100c881201c0c001e800141c50b000c840300380c0c0801c40d9181c0e201500700c1c4100800880e500c110103500c00c1c010761240345100c040d007400806010b003054020102030545c0d1503280024000c40c0c621251080110080104820028504488002190019505203d06071401502401016001400c40c2d0141c203082d03c626080210003007005040070a8039180b9071910701800000500e83c10bd520300f0a8015907c20000d220641e110302c0b00134020082101e4800d9001c6d04c048070880d11500108085c0500c081c06003616851440240741c82015181c20500c80d0304020400d0591502040494100d8048603040c2d50007080d0758401014071840d00c0000b000c1d80c0c00d503420400c80d01c0c20a0300b02f00e00b03e4a942c0306075885007 = true := by decide +kernel

theorem cover : BRFrame.Cov 272482014 272661870 := by
  have h0 := BRFrame.cov_init 272482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 272482014 ≤ n) (h2 : n < 272661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
