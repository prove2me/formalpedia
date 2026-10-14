-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0952
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:27:54.174331+00:00
-- url     : https://prove2.me/submissions/e8394d54-0cdc-4b16-9905-4db1204ba6f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171043165 ≤ n < 171223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171044415 1250 171043165 171043181
    0x309050603150f06040e011a0d02130501020607080919030302040312030605011b0302120c0a05011d010605040917031b03040c0302181314031e0c070509010e010e0712 73
    0x2151a0302095034200003200340c4543c0c0052107040c040c04284107240240300201d040d1175401e00d10f4041d104092000703841c1c1d07002d02505030b00218000115419440c1c07800320f91400302d840c207800f00d8011307840b003810503a030150b4100d44003071407030f400b08240b4081e072050010400d2501c1d0281c200146403e4994503808a034901070340d540c10100e80c80720010000c1d564448038014140035002588101007095580c002d46500000328050114007010900740d0070024144104c00d4220350040080020b400c0c008102c90700412a00c1c100001d551030108006070b1801c2c203000301010a64840246c4d1101c5000004103c62600003500c210390600540f504902031200910043d4005c070f01901c83c0380000c0d072a6204000680340081043c00d120003404050040e4800500e03140b041d4264080e4402c1d4401e503d400300c079883c5000f000d100c840002d446105041c070342d612007401081d1702c0d51240b099403c101e403582c06028400c0300030321598004500500042200d42281007201e50012003903d0303c1c2c500e80f4100c00001080e1920740e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171045665 1250 171044415 171044431
    0x602031308040f051002030a0806010f0e0d26040f09090c03050a080c01060b04050112090822030b010b03131e080d020a03060806010b09040e1e0307120507080301050d0309050603 78
    0xf0f018092850400e80414500f0003520086282c03c0c0312074401400b841010b04840e042c0410400c0070703148039000300d410807841c000240100c8600c1c0e0175800c0940502d16000810b5a01400c20245a00c49204180c125029160301c000c44c80b010f40d05d45807080300103081300b03c82580e200d145081c002c00001d50a20811101c140618402500d4191425916084442d030354003035a1a20300c200700030005660421030b80305465500407030004149440b410300c0c09841c400c00c0b0b100000340c0005d070b00c003188605105001c00c0903603015011612090381c8078040424148400e81d00d20340241d940c01c2044000801c840c1100000c02028039420105541c0c6a44151054100c2c038423f03e6040c1c0c010403103842e0654184503410003440008028800340d40341142041c5a441501c0ea050b01440e00c603905908560345c01c0102c0240c020b013451200388007410440e03030645c40703422503241215041701c0f00088030b00603842038060301d40881c0c01c582e24030324523468001000002035401d2000c50038170074070140005603603440002942c421000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171046915 1250 171045665 171045689
    0x3010c050c06060a12080901020106081207053c1011120603010507080a020d02040b1b06130b01090b0111120901170f070509030f01020c0c0a0603050f04060203130804 73
    0x303070100c2400c0400092065000306502d810401051045076a00b03c201d0350000d00081d50390119400403405042c04e500440d0701d510981d41031414214801c401400c6d10f60046041d0b5803584041040c45100700c401d50a00f55404d41440a034002201034080b440101c0c4000e0300440e81e01c500b0000e1640c00350b44c03042d0240c609124000c07032044880c4030716052281c0c0c00107084008100c80d02c2c0544010b041141d010302005000b80d400300310030405aa02d45d04680c041c00458000a403904140c481010010b06c1e2106041c56a016642c04150706503000401c0c9410641d1100d210f440e9682000c41c940010800d1f040c0050400c1716080201d4080e81c0d05028602c2e06001d41b100341940c03010000009424100c503103020060400302d08040000d9206170b0711904c1d0b00b04a840c0780881e0354026540000e0302c0c000040808070380d6540300180c3c1400c00070000413220010340d003e50700c030340ba401d1355440c3c15011680212405410b6500301c070300083c00a5802e50056900c07822184c400603107140c45072244d4000e500560440861441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171048165 1250 171046915 171046927
    0x1809050a06090f0903020616020c0909070f0f080604030e010509061b0115050312090d14060405060604021c0b030313030602040306110a051207140309010c0e1f08130203010c05 77
    0x4018000c003c0b00c0c80c0c1c081002e1040070900c0e9402507903084000c03d03415a40c00d51490345540c552080c406040d10a40090609041d400c1c40c820300f90f15200c981c85007210703141c40c2110014040301c8402007207040703030403410260110303130b40300c0c3c50075a50100c0c1080c50030304000d020040399180d90303640005040e550f01903c040c8014000f006801d103007140d803100c07400c0c0ca15418403c0b0400c40e07903900094007941c803a600583c00e0b840b90090710200d200003001410060490745c000480c180007050020300c03a4483e50040044610544407d0f00380030881c401d03043d14149008031903855141c080d6050b0030030b880788100901100d181c0b40000d40c044910103602d41041310590b070001020420320940340213503400a41c1e100d08040c80c1c9100c503070003c4c24a115491189601d00100400100301e03a0103911016000840d07480c02e950760303207004641c42e4020128071911501240b00002003a4413800c04104070f1000e2801d15030015000f030b811701016a51890020006551416a00944d40050b107003801a00d99034065034032180d4681c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171049415 1250 171048165 171048179
    0x7060617010c090f05120a050106080d02010f0c0e010807020c0907020f060f0709121505070e120d0822080406080708010902090d02010302030a022101050f0102010207121809050a06 79
    0x2e038141d070a2404000b40924103101a00d0b00f140d5801c02c80b5401c40d9030000310b850200c442410000d0401000e045940b8104002800c1500441d4030746d25035020358020001803d03414050b000302c590080680001528200c0a0b403d954050414603410075201d0045500308682e100000319038210031292480140c100d046240c43e0a4000c000c45030704042c4113080b00c0c0c0c01c0d01d00300340010002003951080c003e441a6070301c0400c0074072002c404c060f81e43d081c003c982804a8900302c6000381404026a08032030081d84201d2040d01201750108982403410f1306540c6212264139560500362904100b1911440301c0b403400042e03c0000b580b004004d20090065495110a51800910141024905030b002009003401081050042d40c0e8100c0036002060f0b090800580700e07110300d240c4000a004401058800384000e19180d24010005c0000ca412100300b103034001e134802418001242030b406001c800801051002c1040c030001030007400940c0302c00300c609200440380d0750b840f241041038590541e1a40c28841d902e0030240015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171050665 1250 171049415 171049421
    0xa050c030c12130e01140616050a03030510050409030c03050d060513060317030c0708070807060509060609060f1309021c2004020901020a020103050c271306150c0302030706061701 79
    0x704001c400c3c40135150300d45404d8a0020403d41400c900c16000010b5040141c41821000006c940d0480c4c111211003102d80780107001440d041d2401851401c5080001510345080d000f010011a0300d03580741c1800610a6400341c0705500200440c100c42900d900021440f84c4500d95601401c10032010003040551543c10700e84ca4441342e03064144201a0100104a41c4510b03040441c1c0c0f0282c3d114140d141c0e11905030511f100c1a00a02400404141c10300c014401c44c4100044c2c014081d83c400c407140009500ca1104105485441d1408160001d802c0c02c1d207503a107103c17241d11240300507001400060000149990a411101e8a00000c85066221503520303500c1c0c014030f0010800c070041c2950110300c1c048035400047c2d038803040d00d04028105921400003680680892007902c20300101c203441c038481204c12207240c1366440340c50f0003c40c0c058200f4110241c00150385004034022a00e03081d164107034180003420216460260320750183c0541c441040380303100003403440c0300e440c008204032820500c00042c480300c3c2e1800c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171051915 1250 171050665 171050669
    0x1806090409050a0b0106630e15040b030102160309080c031212060a03150905010b0901150f0509180402031e0607110c040c080106080f0c0a050c030c1213 67
    0x4c0055800495207e803031190032501c040c2c041e40c18500260080d0b80b030740710f801d550100c1c46110b41e118642d04001494229011740c41407040904503524446c0c0d00c0f070311000064481150b0820302d03154036048222081c107040d03102d01c0c002d8001400144c50040c1a00b00107485842c8603004900140300340c0e13000c000040007401943c900c418101d01a20101c40d603003040030194091060341d40045000d040104134141d0b60200b5000045038010728054181603021005801031592060640c0d80d94240b08809080340340080e105170580d0040020580d82d008401d20032200d490701006000f050180800002c22581c1d65030b640b107068544c02d03005090291600e4030600d07081003040c17549860390890010454500030070101c2c01c1580300c0164684120303011800148645000c0000000035005481e02c180c04109035481142241a40c1c0b554482c4000c68035100c50716505c03c1010bc03540c88456030144401c12120344100c008000c1940c020b02200e00300f0702140c9413a420311080403a2004114030008034803001c45070480201d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171053165 1250 171051915 171051917
    0xf070e01050a030e010b03060108010e0c0a051003020f120a0f0609020a1706031219090503071212090503030d06090b0a03050601050621010e01031e03051806090409050a0b0106 77
    0x118166140001030802d028071050b0307805240e100c83c01504030000940c40b10740c1048008080b070340703503581d00c0064034002d210b0520b00d1141ca010f10b00b00c2519500f051018036088884c054040715002421440840c000d4002004800c0300d02401c20588400800100c021030107001c62a0000901c5941d12181c00704860715603212001c4140140708074a0b05a03004104440003050400d42008079549140010341400381d042e8001e0f030811404510f0405810460600025410090721480401622030f000c042d81c95450303204091000c4d103070000c0200015401d4603095601712460401403122500c65000a043d5006200240f290365070340c00d81005408028050034154010658142c0c11060840d01c48544403501401361502908001540c540300f1181c0c165035a030108010b45045801d540c640a840c4102c003030a110075940c0200d00c00386900d25075100c903070703900c005a07240d181d242c582214019070f003102c00420f60760380340c2c0003000b840000841d4481e070042969052050703002d05450303500b07480c190403440c90603080303a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171054415 1250 171053165 171053177
    0xc1c0c0f0c0213050402040e0d05131706150f060c0d1d0a05040207080d0603121202030f01090b011106070525020603011802040306060e01060f020d0509040b030703050a0b0f07 77
    0x3400b68842c000a80700c80350503901e000c1656039850020070b0261020140101092040f242c51403800c07079200000e4407200000390038500300390780d03074501200000d003050000d522030b600075002251210032910111040d40c3c401405100848001c5000190070b0341101d0034401c501c0e00502c40410920364000204501145034403281d0310641c1003d00451110985405000d026560000e100310922281c041134922040d0903038014060030380c5030325110b005903030710411040c00319070681842c051450050095074411002140b030317901d540c0c4c42c0440c00b1001d0400303014442d0521189032402c401c2a8400d020092141b00c032612810303521030144000b859415014030100298603078003142403006a1f25142205e046031817400b609079511440400e040c00078030440c0c3c001405140742c43c0c40058411500743d500340c12504c02d5122089025200a07007070f03845410b98600d40c000940100403840d40740c5004c1c1e01140281c0f2001c0c08840e001034030f079a038030f5140182d10941a100d0b5024102080f007a00b1035058101c0e44004145445 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171055665 1250 171054415 171054437
    0x31912020a030e01030209030a02130c08090c01020c040b0d0507091d03160b0c0c01050a0f0c0305100303050c0f190203160f090902120a1a01061103120c1c0c0f 70
    0xf000c000401406604064000031a0500340e5010020124510b80081c10340c0e21403040010280001c01c81407052801007030a480004020110129400d0140001a0050910f00303001504100080c540d403940c05501c8100b280382c0070041901005400041d103410b00c00080c1040c450054080400580402d28145070b004002c0c0c001648080e0602440c8281d1003501c94100d9220310017200403a000d451480f80e5a50711700000c118513440641c010b002c0c64110880100b0056109003800c034203807002100c440c0c013043c03e03203082000080e2040300200041c200d10002d6603000401d40f04a43d0034042c06140d041c1551608440100561405004120840c0c062102c19030405180ca0303c6950000d802d8130500803866905e07081001503440381c5e0380410281f203001042c1d910580b010325000f05100001d640c400b411418140c00418860300842d90401c0500c0381100035402c0601a419000348004002d2244480c614140141d20114100c8020980c5100024001290515411b00e0040007040030712030200811400c0c200c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171056915 1250 171055665 171055667
    0x17010606080606090a0311030316120906030e0316020102010b04020d06140603070f05030c07170d06230d060e010606200601121223070203011805030f1602031912020a03 74
    0xb10760201e03a440f210081030604600d00127400c50180c4401d0380d401e064402506401c00000d03626184800c8400d4451f4205503403600800c0b0100c03010500310b0344541c0d1003005140121a4400400d40802e0310520020607261441c8003c0fa041e80c00c8100041d01da2a2144030501402c02c00140c42c12203c1402d0741d5290a42c500329000030400d40b150301441e401d0090000200c0c41175142503040b100c0356a005000442d142148480c080c0a513801030500c0400e192400801245d4641050b0703001c410020360b500c24440000e03050f400c020003140741001c100d8505945180c0e0000302102070080c1030040805484107a0b035902512814040c22410b410541d100307400050042c072a00b50708141c025031030b5402c03504500f608070081c18182d40004080c1c51050988801ca20341c03000e40b5071000b004003001032080e0001d02c58101a00e5803d2024040d80500604680051000d01c2d28010300e030016003002002d5640b02c0c01444d00e9500400e0034005409124a8026504540c0354240000e000400380811f2481c4004c1802d4031464130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171058165 1250 171056915 171056929
    0x3060a0311040b190305070e1312020313030c1815061d10020a02030f0f06040f061d070812070807030302031f08060f0610090b031f08030705060c0a0801030b0a061701060608060609 79
    0x2001090ac12048038a00e025074820010f4800020800d02868101900c07800c104081105911400c980281850800034040743e0600600c8080020050100c2145086c4501610040034046101880200c14805a900365803078103203010146d40c0c40d070058550301d145401030600300841c003038000c1010f6200200d14000d2140024580303078040c1c0c110904a0000201e0300d4410058200f1481310541e01a640e03940e41b21544003c00c0e0351086403000e400f11660010103828801c52405400405454600c4c18440c040c0820300035001160304c00c51020501001d004010034600114050390043c44150b44030000300455451404500760704545c04a80c0d0078840104488010000640b6020740c56504001001042d1a20418171031210380152010f02080d8042c0c4945010790780c2d4001140c00d440c3ca20440001c035504c85c2d02c40d42121040400e90b07460368890780c02c54079031180c1c181b00900071001c02d550712000020340300060b04c01e490b0000c20f440000315049181010060008d41c01411141c4038680030060203a49540f060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171059415 1250 171058165 171058201
    0x50a060f18050309010804030c02060a09170a0515090a0b0a0510050411180a0518090610060f0f05040b0711030c030111072d14011103060a0311040b190305070e 70
    0x4070746001030ba1f82d20700c1d0440f0030b5500394600940168000c21401e5000c2c1d00072000f60180e940302001d84405440c0180e0440d80e4603a6010b01518a42148c1c2010010030544480340794800708540403031b802d03001c407642c2d50700c0360050444070040c541c0c8e03590b810302c200c068100003000d00408040300c0c00c0c0540000181c40902e148100c21103000b40c141310012100d455154a40040000c0000030040340c61040340701000080c00d00122440386c4e95004080000b5540d5800a054034180c404503603070084003d000d401c1c26a00541851040c0050083c18040040d45c040004020000c035031003883c000300d000308804241450010040091442a41040783c0461081c5800042c4c40405800280c8815030310080801842c42031071702d9542084011684800c50b0500942171640141e0481c0c0d800204004240b00102c080b00b0b0100790f8800f0380c0000380413402c0000c208900034900303038003000500015540141000103030380101c5850b11640801c0480c4010018094148450801090782c0f003007000d010304e070940000d0740c00c6842c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171060665 1250 171059415 171059417
    0x10f1a04140405150603070e09090a231203070c030e1203090103020d02041505070506070305010305120a02010b0a0626040b01050d0c080d031401120c0b030a09050a060f1805030901 79
    0x1420004031140d8401c69200e1000c00c0142400d85d5034180b004004081c021211008c41c00380846501203154070f240020146d42e0107400150b4880100c20500c000001d0100c02c443d450038521440c90601c640034607610007940200f5043d1102280c0004a01d000707442810640c200f03502c500160300c80034546240c0482105c00c002c00c00d1030010b03031b40c0d107080307500780000d01680c1c00801402c0c42854102c5006a0400010722000307020742c0c02c0b10b0065031019003c8064802c2400300822a402c05d0b62481108000034020b010407000b28000498000c2151000c200c07000f419510a5001606810990046000c004103405041d62801e0001b2401d01e8681c903110399811040c030a003030003410019070090a00410300fa059011300956030903180d0041400310001c0c00783c2610100c402140075180300000b16200090007030300101c0c0d445201c0585d56231070082c1003006900300034459800c0c03a44071480c242c0012004c1c4035152195120384070004030222058a01c50480d412140100010b01547c0b0f04440070a200001b980c1a9a0003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171061915 1250 171060665 171060671
    0x126030a080109150b04030b01050906061c1e0924290102070812040e160e0405040318080105150409020d14030403020d20010f0c0201030b030c09010f1a041404 70
    0x282c4c070703284a60150380402d218000c045404801c0040f40380c4040d0481d841156000c145440312010800d0a00c500c1614004941401c070350b11800c0390080d00300b029801001580010340c01d130010751a00a82717a40020441e035211400d951201c050710405003420a031402081d0400100540000c0d03c40b408990040c00c0c804a0b801d4440318215030f01c00c02541c4080c0284405580703600706080910596901700e03000705407400e4038620003e0b010042c500082c0702400711584d201c0d504000b00c241804010303c4081c005800300803400581e0f5140c0007020030601c00400203031000003110f00d05100000114800c1e00c2030607204506040031000540c0c1d4500004144680082c00a11340103138158049286100d207600003508403203d0500c1c5000e00048148041c8a0000030410484401d00e2100442d1080b0f14610340c0d030003054041480c000035521a0f40000e940c61800340c102d50034081010002079806509030310062210310720f8035081c00640806010001c1c90118120480d05050902070054040300007a111035010f00e50b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171063165 1250 171061915 171061931
    0x1090b090d140f041703030a0b03152706070c05100c050f0319150302122805030403080c0601081608070603050a091203060920030403140d050126030a080109 69
    0x3c50443e40180540c0c01c402404c0c2d00001ca10395242d81003200c403010894501050b04195050102c2c0124a87c81201300b540c05980c1c0d40741c50501c004110090f10703211031032001e00300504030320108000e90090001c0c0d01d0745290008540340c07c9162180c81064121040d082c09590000315400c0300a42c3d050744a1324401c9920ba61b22205546c2044d0b070700c1009042e00a0a00c0d020f04103503409004170324140c80c001c4d1644d80c20a48028610380c2e0b07442d00e0500c09918400c040100305040005422001d0242e4400d1007500d18003a03407503c0d541c80c4c0390000300d0124550f8008100402c143d01c070812080408240410060114900c2d081c4601c1e1038421510821041c1741d100c00001c4c0e2207600c80d034004500e0960048000c288504c16900007001010b050040744848c42c0b40581a04c0811a40403002d48202c194000c058615622030ba01241c00e403d196958000c4504140225814048607001ba00d02900d183c000b003e204182c9040601c2d140d01c59200c01c0300c141e400070081c540d007a030381c840501c6e41910760070400450040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171064415 1250 171063165 171063187
    0xf060103031b0c030f02091e0c090303070209150901080a0803040303020306041103100e0603010e19060b0603010816050d03440604050702030a020a0308060406050d030201090b090d14 80
    0x840742c850060010580c4807001c0100300c0c190038138000540c020748035600c0666500042241e94010b101301e25580a41540010310440340c03800080c00c41d200e0260a407800c00c0c0940d030125000d80001d9906900510141081942504124079590300502a0000030180ca56154498201c58400a000034081580000000c3e4054550750480101c8211880350b07583e60346809001814244181e010399003001000e071012500c0d5140c14040c1d51400d041c0400070346441c1000050100200940350070465419440300ba80c10119030381d12016600800d403c0e4003a2551000803d006101c2c2c28803a002540705002c00144800482d03842050b029140c1c203d0382124a03207800d610300d4401c00f80450108020700c81103075032207400389001601049002e44010346080c1708903126600140d031203000346510313140181e0041d0a000040f0307206817250307608104081d00000c0c7c115100d60104160f0003448070154050307910b51544c4070030400310a14081d84881038101030a00c2500b5400014521451101e50410509000c500502d004c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171065665 1250 171064415 171064457
    0x30a0207020a090b040609052e0509041a1e060d0201020f011a010e030a0201050703140d0609020919080714040e0d030b0a09110a030e03160503030114030f06010303 72
    0x150000e080b40d5029540d094004058110200b40c1d500450401e000080c202a9601407a40607031116609001c0071302c0f145045640d840c0c0c01000c440f03a529054400020745072624981d560042c1d0141a5107400d20080640c00f164019011b03011207159040c0728006100c2c403121050403030700224100c401101031401800101d00d400300f24500341105502c0c100b50a118000020b1141520342070a0700ca00d04082483c4040540b100741c160f0004c0c5c0800c0c0208a0540024400d40303208081c241176102031801d088a050381d0008540294106041e80c035800602e0141c5843d00400400d519031881d4155154541809900f64440601d881085103040201c40740030384664454110702040b9000c18200c8668080d2a41c0c010041c20480c2641c4d0b00481d400603001c01c84914a010f1001c841c092800010b2401e41c0c05041240103001d041d005840c00d001c10300c1458003081118001d0080d06001c0ca0003180c5079410310b0810762003043d4490125100fa413068240040c1d08002180e05811643c00d07040121352142d28800304260 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171066915 1250 171065665 171065677
    0x8190e010c0f02040b1503060406060302070b061c0f030206010614030402030c100e1806010912030804020114043602040303080109020a05040e09060a05060904051e01020418020c15130305030a02 85
    0xc821041c6c1a0701004500800186104401c105c40900625580d003600f42c00324410684040e000c541b00e440094a039081100d058203048203071a00c150701241e40d41d2074030601103110450440058000800420131903078402c051403407004010400500d18105a40000c0c0d482d01c1400003107000d0351104484900b860301071031045500c5440505101c02c2c0d507080303c85e40b010240301142d410340450960800401c1543c0042d00841801ea4540c5903150141c90700c1d00151040c1c4546000c1c42e1040508100110340014403040c6115049500013507500c0d0005144403811130703031805c0201c580c3d070907106020130000319610026150444510a00046e507030750b000f000c11600303407150340c000d440e09021081c02d01035505800906070f803043c00040b9040015817079038802c00910810035540036105601440d00e800c1580c21400001494041c9200018a003603030b03480c0391120501e6003034903101c0343c103901042c008000502880100d601c88030750328018105207032001409181010402d409005c001e0b0100009004038050741c11a03070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171068165 1250 171066915 171066919
    0xa09050c070201030c18093606020c0c120a030809060702150606130e09010c050715020c01090605100501020f06100e070e0901030803150d0312020901170408190e010c0f02040b 77
    0x51090b02c440b6401f014081d1003d40c9040841100803a50300304a20000342c604059074000072810030f00460b20707594041d42040261060300c0c01a410541c2c00c50356458400b810515103480604001031850502801c5c519004180701c803141c01a608008443d13501055400407401c1846400301c1036100c89000c640140601c8003c04101c542c41040031503040d000d03541c11343c460701380c0b0002031180b403c040d40200e50901800d54010000c503403804041d40410242d80180071510890000003514041540f52401951000e0301c07080c02040c0040000c2c807240d641402041c1e200141a070040c1118100070b060306020318040c2c42540e0703102c44400042f5112501c04c3c04454480e5000410301207465840c0c2c100a1210b51066603031140440e4846039422540c200081079204a03909921011000056003242501941c0654541410040c0f003545404020340c1d95100035000c5c9c0c0c0101c0b89582c682016110580c41190703400100001d0000c5000c0c040981c2c1e078407840c9010090343c0110600c500391400e101140103080b05903d195 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171069415 1250 171068165 171068207
    0x503061c0b0406020c06010b040812180d0809040c020c09040314040825080a020109051c02130603030206071d010e01200a0309060903050a021519030207020a09050c070201030c 77
    0x1000b4441c0c0f64001d8440c805814080e9401a6030f00c1039010407520440c4589002d03908041d4188482200b01c0380644089280640d070b101680340440009950100c914a00311000c1c03602017001ea400781401d11032404c07801e05034002040040c050b2800034140c410300a0009080000c0e03132070313603c04403c20716083c2c81c000c0602400f29090000c22038a1501015a01c0c03008140c52000c0e00000140c140000031380c0358501d41c041c0c40303410615003801c0511000c0c038451003004801c95880100f0354010b031074000c0702c108104241c3e000011003c2c00d501c1c000303040c044041c2c2580c4c100040d072500c4045484041e04c40c461983d100b4288071840c09114001a245120742e174420300d019804490302034103d14004aa281c800a102e55580352000ea1200c0044e0781e020383d0380c000500140d108001090050514141c45040c150440880f142400c004100041d1000140460700303002a4000c103107503086007054443c1c00007038508032a0a00031464544c0301003405008084010781010344803548019803a008282c1e015101440c010a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171070665 1250 171069415 171069421
    0x100801060f140d2a050306070504030206031503120a030221240409020a0303031505100504060507051203090714030c010804060f0b03060c1c020310330917010506010503061c0b 77
    0x55082120910803a4080d001f500c0001d4016440790080f60700fa2540140000c0c2181c48140000030b0002c0e004140347d030984100c0c2c4581400394410300c09060b4481080d90051703505c8001801000768543d00758200102c0005540602c0815000306c8030060300405185258541182090002000340204080c0030f500701c080140040281035141e00708402d103840300c25545143d6503481d01031100740440e40400d080081e005100c240b05180c03003031f4000c20f030580c02368080b1010070349903104100b21648150340d00c155136801034030100650320464201452000c0308502500554594100107402c040000b040104046c0da60301e0044002c60fa0380e40400242000a4203d50082c40c1620111585e5031103000900300c01060043c09600181150003221312441003080c00d42c0750103140081c8503281003648100250103556010480c200030b1013078650080c2e5900580d46036280365141c02481c1000c00e49520440c09107034140700800c0110798214080720381198040e50140b401c07030344081100ea0b4a0030411001082d801e107180c14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171071915 1250 171070665 171070733
    0x20304080a170408031b0d020408010b0a2705130b190e01020423150d29010e010810030b010306091b06090501030c1403100801060f140d 60
    0x5800341e81100e48414020514a1100411201040f28001c00040040001071002a031411001d100d0040203081c40303003003d03040a103410590304540c1042d03980d0b039969000740e01d0501e0048501c200400e0708405a884074280e9200e404c5542c161074900c3d80c10300d80c44074041b0340f100d5860181403080d076801c0141e1500b81e0401c410741a0816451252150000742000f44504015506100b110100c82c0e10b0207510300c00001c0c01c0b5440680201707054105034402803281c551981e500041e4000c1940315079014001588085125102c03c20820245031903400e55025400840320380d81200c0c41620040f02420088a950f0340c1981c01e40e030301485600001c0450f1100e2000000304002e9411007440d46118803020068041c2d20700075600d19203034a1103064006030b07809200700647e5019034880768241141d03140c6086480b444021450150f88290b60035440240a080100800c0380e0078450341028041c8034598205a51401c0c3d2252441300022004d5880b816180300709c0c130700f0000524012001d01601803400700da15200504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171073165 1250 171071915 171071917
    0xa0c050f010e0c040b0f0405061f0806010810030b070309021c0501020702150a050301061116080c04050a0c09050103240b120603010912030903090f0807030303140114060304110402030408 82
    0x41c9803a42da1041c5070b000815807034030703000d07213100880d001e8428540504d0365020000586005005c541c0c0001c43c024a0304101c55080010007424803640c0c0310500d880c1000340005055040091103111048004101880012070031980590005078914000c61541c000f400021300d2800e25901c0200d540b080300c1003002c1005010b4001d450303150300880711440c0a8203a00c94054a52180100c4071000034010001404003d0044c07129402c64820f4a003100d48403000d0318034018151440382c02c5000707030341d215440803001c92070302e8000c0c80d038003901140c028410151401f00180c4044490b024040c141502c508418810f0030444041d01080c5420115680d1156a68546401280e02c02400c0010f902228000030700c1a080500904440769801041c0449040345890100c0040040c200c04400300b00c940a00003529250015500c0702400d00000a070030b95030b01c1d44c600642220080131680c2003a421401c01000b015901c2ca034071120b040030542c0e82c00e940740e580b460040d002280303124005a0141c070102c05c1c0801c0c00301c420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171074415 1250 171073165 171073181
    0x1a09091f080c0301050c09030c0108070e06030a140703150605070f05150603070801090503030408071a0c0a0f11060a02210103050732040c0302040305060c0a08060a0f09020a0c050f01 80
    0xb0f0020440d80d1182405c0000034859091071a816a004040ca0b2805511070405641d0080c2c1c00d241c501c141c2c8840600017242544190382c0940115160720300f059007070359102125038000c200b600b0200304c8114001c0000001ca6014450502805404505141440703802001c074400709a200040d12107101c5401d141c0e16200005a500700c0c064410448089103d95051055a8006411030002d5040d03076181d0383d4140c043e0307011000460325511848811800d82c0c080c0885603004101c0e2075030240d100c8035200c00c01001c4c2428905411304200c01c1c010040703003081c004214603030481100364015a40707402c0f89070000d0000314641c2d96603035106030000c000400e11202050900540d20514045aa0304942c4490a60100050022404541d03140c40081d1030600d0075078490040d401540c1800350500b03640761116404c0c000101e640c44000d10300094074a031095841410103030701400403070300019902d0400e0f2215070100314501500c00c80c00e5000400780c905500039aa910b640a90003402c4815511040220a02030100c40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171075665 1250 171074415 171074419
    0x50703120c0302100f0b030a030903061503031b0609050d02060708100806071d0414190c051602040615211a010e0a0b0304050d02071a09091f080c 64
    0x1401990640394851061000460740507801002c65140c1c0182d18002007140d0151562003d641d0200c8002648003801030000c1c00b8020348030208540e1850400c01c05a4140d40060444511100c505100003500600c4112904080041e2402c90100074a4890010248c40c007000c0e090344102d40c025151140d002172030038030880d03069642c0e50352900c40070715901026100e401600c403280c10650005891a00c01c3c0c080ca150550100000000c50040f131010504655078114032a044c502e2020030450000070706501c410402c02d611108001c01d0594420043c01c50203403540c50b048440d00201c1e0f0b070083d07540b250880d001902d1400043c0b54007001d00900507096540030507029551141c60701140c00175803a2417040511024a501021032515841c01c011103140c01c012107010740c8030303007000c01c0482c1416042020350310852203a001040050765003e0081c2c5045071592142110204a0340034803002d800910940c1c0d8114000d43d41d44502d41c407528081c0000c5240003802004e179a80c04440090309060005031242d00000c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171076915 1250 171075665 171075683
    0x4080304080a1205040f050609040914010906060b0301060503010e09211b06010b030615040e040303020405090f2403010e0d120b03060402030604030e0607060603030909050a0513020105090103020c0a050703 90
    0x345070800c1c2ca590166116034a06c0d5400c40408002c14104400140800d1300020000100e640290f512050040081d01545d200d0769518040d0302d0030003440d885482c01600419101d2411989482e000400520050081d07070302c3c903160708012440000c000c001055040c1030304400c41050110366400103040d42c214400c00300b00a608100c203030507040004070790103040c0c030040b00c419031841c0d0380c1200b40080e4200d5455140250300007080000740028010300c000f80101e2007581d01680c0d4030302c0d00041007003642000d40384848159021083c48103013641c100300c12006080733a031002a80c6403403050000b8010640c1d441040c2060061030382d0000307030785e6003ea810000f0f40d80380c202c00c004074036006050560b01c2e4012035000707415a002c075000c07802013802400e9005281c4030040c000351628403503550381c500f80d1311380b0f0348110081000b1900a0160090310700409070301c0b020726a820001864400c0001607007640e81c100290620400255840451740700760120b414542586d011101c1007006482c2150343c07075000e44019680480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171078165 1250 171076915 171076943
    0x30b072715090524030705040305060907080601170604061a04020d0e010609020711090411130905070b07050307110a05122107020a15090e040b06010f0906050f0d0204080304080a 78
    0x54102d56844000441d0025210881013606020403a5400a404101072080901000000450401410388240042c8000e485100e240031041b500e40501a0464000c0c20100d0303034091581d800000d0f40540c000d402c101c1c089a6101614030b80080c0340003c04016410500014041c0034884003a085499809641002088050340c0c0e1002a4203d0050a400401040150903481c140b45044804c1d140c00601581070314050a064900040001d000c0b030748460113403911040d8240901a0030300080004203015a1030030301d42009503850075207034030070090004c0c581c000300c0e207800d0b855403074100000d00503040c0a80f1941c81ca0780708001c095a01d56250002004128594045030300c4007580348107965001340d0140585074407900300f100d0b03052a0700c802e015000420402d41e000181011405100c68021405846040c013035040400006008511000b540c40c240700c0352000c1089419417041c2211900410311000e80e0311603c5410400d0701901c5507600140c110310010401150301c8102182c0e80b08414451060441d001d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171079415 1250 171078165 171078169
    0xb03070e0114190509031014090c03160b0309010b060301081f1103220501180614070203030c0c03130305062e1a07060e0106050a050a030b0727150905 66
    0x40700d0000c030044205404243d0414081c0564007522454000a040d2070400001c101c40720200d409841521f483d584410052001410702400349404120090740684895400e05d8200c19811245110381803103080c0000001d80300200a6122003031350b020050016686e035035582842599448041c4d2040c02c1c030f1032040d0b0703850301d154414420809020101e204050135582c40c0c3d072100740031400b00d20400904078005000900062020b100c1c030700461998440d00002e10f0401d0600740211041c1d00030010351031b1000b03000d110751150008280d030707404446c5481c8165528254050b03203095000d500b9004040100c07801c808000c0000200343e02e031080c13458000c40e00ca5030040070780800b40c071100180e503074100a000180a1150182e9039580c0c1006e040002c031101d1815000b40e4418045a400d41c02d12650b90350b443c2c00c14441e501e0580c0c0684020b20f82261200415819500d52014080b0b02504d218240311103803981310601d0825076643c2c41c5011601d8031540c0c02c1603440c2c081d0b8200d2048103620030001503064a01190314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171080665 1250 171079415 171079417
    0x50301121506031103150f070f0507061103010905070203030405060c0c011d030c01180f0308040609080d090201030501060e0315040f02310c081f080d110d03180803060105040b03070e0114 82
    0x110030582503805c0752349034a41e0503140e04500415001c01c04c00204280e0000c42c44a000d0301e448486051200c540e05d40c540f840d83c10481d10302501c00b00071900208144000300b1400529180c00c104c01c221199922200000c0c020700618522103001c0c141c00344060400340d20700b07000c8003905503054018000e114000100031142502e00b80c11074018001460452a000070078410ba01c40d6612038031618000480c20400d450703140780d64000c22080c00301c441d16001c05c01704559040c000c440c01070040303041c909040341c0c001001a0b1914100301800014445400004040c428840300704140560060408140715202010500d800c10040b404d460311200b0322801a0380369200d40c07040e081919445d45d03034802c6540f13400c9d1056a00e820a034003045141081000c001c103103201d0500c030b00c2e107c003091521000c01481042e8802ca007490004031404040c14906901d410865a400202d081a139a22040140d0f80359141c00050b15079000d560050941b42902004005d08280c105070002181c1d5000d803605511007008002030346003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171081915 1250 171080665 171080671
    0x190201020a080a2001020a09140f2205040311071401080411030106090f020d1a0315070309050607031a04060b090d1509030207230105030112150603110315 68
    0x50740014442008507070020040c0c802c000592402d00c030f41610381000300c21000d081412014003039600041462000360814511001882001c8592204d100b05a000171134540f031001500340201c00c00f0b0204103200300308649c0458582c050349000c00c564201801c0042150013990f1003c10103119149000c100f60210540302d0100403030507521407003642e40d2581d50400014451a45540641d03d400e4040f44e000d009001ccd91008007203480c00148c5400c1900038000940c0c3c43c510500411003410f007001d03243e80c1c2700030644410708640250f242c00d503034030f58901c2113004044854000e480fa014540030b0106260345608601d1122507a00c21501c540b190395020001190550301c0340644880c810481a0064207103100424910f0703000d03401031080154a0005031041d244036400813001a04945014403411920780c018141481100301429620301402e40060100e110600070a040e80f1801e00d00300b03040006138651080803018150007401550398030328000311020300e110500e922a005040c098401c900c1c540d1542c0b44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171083165 1250 171081915 171081917
    0x1060c020303030c0a0e030709020a0e0906060f03040201021018020109060e0901090c0c0501090c050301051014060304060e0340031205130b180103020307081b0d09060e190201 77
    0x103e10b80301d8211440442c0d21220100d81409001850203281d44da042c000a40100200b40c00942c0d0b902c5c1c40311004000d416009005480b400d01c40d030134031229840d48015036004c001d10040e019565221400180e00d40094000c4c910707481030400f0b6204041c05406104440014404c1c0c84990741541c036080150340001d0220201c1ea08100701d00b004101c010000c1d0005000c0c01094206205514240d071a0682036039880790090301c2c0480300f80b0702041175003000d06c11994403441000c044900d40b42080040d5440d1940080054402e82011020505110440d0b2110071084420f40869070340741208007001c44a0203c0e140d42010703036074607000440d09180e8074259100d50415100740781c040311811542c6607503140600d11b2041003000b0040c8002004440d003840c05101400e2540c80c2542c880c004c55080b2141ba50031000214109801407043c405025085600140c0010a080b20380c012102401202e01c0380740109103c00d040e0500f0001000140001075002444070f8204bc0103a603c03040c0d00108809400c00040340080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171084415 1250 171083165 171083167
    0x19020703020f010e090f0403110a0305090f0909150603010b040f050f10080c04180803010f030b0109090b13030311030703020403150b0d0312020405030a14150106050f0c0c0904061401060c020303 85
    0x49042e0401403449038001d01c81e003000c6009c6c0f05c0700c2d09580d1600002460840128000050104003441c10b84080503601200301c4021007035240c21004261140b48044240c8004102071000c0782d52030f5000c3d0080b40b0140d00c0a4002c01c603400d022601c50001e448166910000070540c000441c414805954581041c0c46400c0010a0240320807410f101c0100510000499114200345d030540000740b040380214024451a00840c04031405c0d424013241c1c00c84103030b1003031001c28642003a800010300c05000032903000c40c600d114802c04049074103040d03015109a0a091079425000000c0020041e0180e016005072400b030300c120400f20300540102e10803a2004031566502c50200034003040081d2080307002c0c40b02d580a005003d810139560f040400d18003c010482250321000100003000c280030100480b2200000302520050194074004014055204286141014440c0011184d80c658001c1140501940024008110b5498030703040c0380700188485007002c0040300d030348000010154801c910b18428140c004000d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171085665 1250 171084415 171084421
    0x606010f050d06090203040501090203060703020903072601060e10060201090224040314100c030506010e010503060a08071715090706200a030c02030f011a0d060219020703020f010e09 80
    0x607a910740000010003400d40c0c4550000c00c1c05425030001e54011403246001050029041c410103007003610080040741010320500100b02540c1e0001140811180b500341c003003100ba805e40302c0d03081c4106010314104003550308000c80000d842c500034030500d2069910941201c80e41d038030342100324240c4a402c076020358809905d14420701050090010548054070032440305107016900d9444250000c0c03410301a20440d00420102030380c0d11544c1c01000e040071002d1500304800d141820001c1d1020050081c014104034000c80020000c0d1504030f01c5101514032041103c10700c7c1e40c0d80300240c6207511100302c651410f020b00340300301e1100555842480d006422440181800608014084811110001d071544042e03404203803103038041809100c0111014001c0d40c91000d100c42a0041c11f2600740c00303150313100300750303140000813400d00380406032010000108484d540000e07038050030514080d01601366118a0b02c1d01c0c01400741042900055400c080f00d1003507410050106070040192854052090300d29000007800d400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171086915 1250 171085665 171085667
    0x30d080115020a02100903030801060e091801020d150312030c2304090c1d031b120a0203061006080108030f04090b0111070f080f0703050c0d050708160905090606010f 73
    0x403485a100500c100c4034000c00e16000641c018200000100c00310701d06c01414000e144c1d01503440c80c0075144e1801c046000e4004080814520440104884921441d14018614681080d01222110740200340144001c51301640300f035000001c0c520048803000d5032881081141e0340079004401b10300940e61a00003501901404500803c05490b00a584c0c8480400022662118500c51645010580c1d83c41e02482603100c11451500800798a80f24420b0348000324005d5500d8804608102c05081074070b02c5441c004075100c01914108010b00025418004c9000300102543d0445403d03044600341e5070703580090f9030f9884450b5180d2044900110124400700028052480703030f0f81280c0c11041c41031402003031180704001c42270708264454211070352400b214036040240d05401c02418017007500c0726002d89100751445e544d0310b68407490544428001d10700c41c0b6600040c040e0510100000f8104242a280164045002040313060b129000b46030303c0703601d0407000c184480c20010b0308522501c0180c49040c0f059404900c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171088165 1250 171086915 171086939
    0x212030a0e120705150c0706050406020f0714060706021201030302031c05070c0209130606081020041a040f091b03140406110906070620030c03040b0a06080109110a05030d0801 77
    0x200e80403031000100040c000d1b46e001005203c004000325501c1c48d032160f042c1140242021841e80c495150740c0d100310750500131002c03980c8001034501c40c22141103036101082d1030920040e0280444400183c2072000000080c1074020004040304000d804058a4660742c0c40407241c2198800e481c69030009440c45070800041c00e00d44801c58000b04209500d41d0b40c1e1900344d45200540358650060301ca50740100400100c0501d0500500c101c10b2a02003000150304100b0300341054501842c0300c3d1540300c20007400354a01d003c00d4103084070058680421200c04580c0c036a10190082c01002c01c440e402c0100d401910060140309100b1048a92944d107200e000c03a89664a03404003414285a80d1991b40c07104010034440c55541100a1808501c100d4020800d115080c00b00c415040f0021f00f02481c5c0c0d0380400c1042900c480240860f41e001d580b061103c00c2c1c0b0b4882582c224010f00c190b400c40c800342d41c0382141300c505219010050380d25920f07088030b82c00121900d500506858070b00c02944000450401c2005204005900c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171089415 1250 171088165 171088189
    0xe0c0313020d0f23010c021b0a050a03050d18050f010f0201020c0106060929030c070f0804060e1504080d0c0204091a1b0403081c090212030a0e120705 66
    0x42c030181e10101c054a82e00143c1442150481e52111000400c0410495554481902c0c0c002035008110350b0140d1003001c0d403104042d580130b40d10f100741507262030801d80c2d41490603400751a01400c0a10b840380c0340e181466580c107200e40c5c0100819505c014124214035034484c0d6006482015084400e000300c01001921890340c240c0c04036056540034030599801c55030034032900c40102100c1d5a400b804501c0d1000c1c450141c5840b5120130380c4140c03000001c00c010030441040300d40000d6560003056079003056041500e03590305480030017018404005000510f0992100910001103400c9a45810070340c226000601e152003248200c146ea0713040740b000e09403003901034106c8561480c00034102007240080c1daa1b039405031031404002d100c000802201448842c80f0202400c1d514001074403282d40c9810f0858449446500072903000c00301d6000986013001c0b0512098001c0f0400d6607010b800841c450070200711407030b2030f500000c184d2000102100c10a40181c80d2040428107603888106c0034250240c281424000156120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171090665 1250 171089415 171089419
    0x141f200a0306090515150903060115031b08011401031b03110702030a1a010621020a020c090403030209030f07030f11061c020706241404060305070e01030b010e0c031302 74
    0x2a1100042c001d0f91805114413683c501102c030a18050410b041085142c806000c6540c0c0d99401c0c42020001d4800040490541c2c1c00d401060b0074060b49480c04501400400441c919006020311814500c56000001d440c16991280365948013217682100446c00c5403031000c0184004c0e9509000c45405902a50002c98a480110030491070071005401003458400309000c01ca484d82d880d0020302150020850003280503000d68940080c40d00003200841402c0400f40e51115981c40e03002402900c203c2c001c0242009c10360014103814a5450582000b80082d001010214040c0c00fa81610f012050004140c0c04243ca50184004044601540758683c240c00c0c0e02d4001504484d00304419050114000c1d00341034646561400540c0d07075849031800c40195100209800028540d268001c1440442c5d186820266854101001442840070000030050038050340060010b028604000c101d0508044699050b01c0c0500716600c43ca0f640e0386c59215000c04200c8548000035418030110719402c030b0f0b09410685180c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171091915 1250 171090665 171090671
    0x60702060f130c081605031204150302090d11120d050d020c1513050c09040b060904020109050a0306060306060b07120509150c0307110f0109050409050a141f200a03 72
    0x4180c1d20f030310030f04181e500700c03a807242c3c400210740384800303400410070015043c29070180c0300380b0448406582d800d019a0142d401d49900ca540c4c0066558400d9054680380c00c802443c1148092031410420042503103452000d0241818010103024400c002801200105540da556482e00c0d240c8406000250000403908c1da5501079018017600203003402240c10b01136002e42c45541d80400711403401c2e0f032411811010490281d0980c404100105a0f00b00605511010903202d4022982d158030040780c000b00140c1045038003225100005c07007072210796030044003524440e2508000c030b1900c84a444456000e050310052543d0402c0142e02e43d86841240039007143d800c00307000c001d1200c84994800c0b04942006560041a038800300784a0180711051501d020480400c0d80c010200c0441e140000303107594298040c40340150f03111407411007000303002c0060303001481e00704510483e2180715000942d221158461004c40c26100d441232511b075099039110341c90341a540d01c0101042000141d1030341207260000028001490b503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171093165 1250 171091915 171091951
    0xb0f04020111240a0e011e06050102070605040303051c0606020a0b090f06010614160311190c1502030d020d02030402100906080f0c0c0f03040510030b060d050903070501062402060702060f 82
    0x80c003406a41500d15a4580c1100041c8182043c0d10888c0c0d403503405141103500c02d4508205c43d5410100310b5041d03e80514110b607540c45800b400703405044403a01d006802074640350000640543c0805c03203085c201d203d40300b54441c0f170720f4201003c0d6441c0088245160250060001000350500954a40d9400701c00b00600508092103d041402000c14500c0c064020418481110300324000610614104c1c9869605007034250019031100d00a08002340184401c400f001064125000d008106450941d0314444003550b03034800c4900d114000e508156000ca000e45030040c80103070703510b0050069606641c42643d59440c55511040600c4841d44003500348415424200501c0002000078840721400c40c2400001310f071b4481c80c1c8402d015100d10b4200c00c1e50300301458440c58420560f103c40843c5d040c888555070114864071212601e6045124885005080c1d61030a000090308a0b000951969016108010713070b014201440400da840f0360080720030200580014000448802036903481c240c004c90300420b6000041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171094415 1250 171093165 171093191
    0x60b0f0d0509100e1c0201150302060c0c0603010f030501050c16060b120a030201052a0f07031412060a0e0c07060507120905011506020703020a0308030a090b0f04020111240a 76
    0x203001c6080e094141d00000c070200c00710304179561040d030b1104c1a4070080000103002d5296805001c0e55000081c420800011452000c8504000010005100810301d40e5656034403003c80c1d0b01d2031040c4c8803c8845508002c0041c03600c100100a81d4111445500407041c0911250356400080040c400c460b40c2c0510b0400c10b043c80391208004980d45a03100e600001413a05000c2004040c0610028102010b80601c0700180410300c8410140c92407000001c1c4240c0e200c8800b80390070b42d400200d42c03000e14544a40840e00b00c83d1000c5a0708014059801601d050712407585070b0200480258040720703910b0103050f0810035900001e203683d1286074080c4c0e081c6001701204680425410988030100000c0c1d840e80e4440e8034401c1d0011241d0840030007004240000c000e0a86075502080340350615210140c040c04e004400543d44400940001030401d034005100b20440ca408041c41c012090107032030a030f002500c103001c9045103081c0010f40501d00c18244c10f0051003104440240c0041c03104c0207003408281520740c2402c10383c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171095665 1250 171094415 171094421
    0x4021503090610090b1503102c07020303070509090709050909070303021213171c0c030e12190f02041401061701230607050706050d060b0f0d050910 65
    0x281c00c0c40c00a0155400e220200040c101000d0700001102454211085095a00c01c07500d1880050080440c40c1c0781c0d5030b5401161030101c800d60008554100d5030310040004114181d1003003040e0021803041c091a241c2070012681c13070208942400c0480d01c10040042645884503805500160522340824010b8903000414241c0c1c01c01d4500850b141c1c0483c04c103004060301031004000304070011100b5824070303031201c40c0302c0383d0100c06111310300411807500314030501c0c00c40520030400c20100c001188541c1801d800002024130420381c0e01680062400b46070b0781254034201514071075044038030303005028226919105c10146a40100c0072141e103d102c0c0c0074400140c85a016800c04034106c02c80804041d85000000f82184510841280f84141d0000c010701644400109029100303040d20b00011190b140000425494032400c0009080d80c45060700c0040c42c164400014540107030451410301c002903455038014031034021a01d01064010703041c4010640017010b0b0703100c25401740341281140c00617492041c1e202d0803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171096915 1250 171095665 171095671
    0x1091a03011d070503011406010315080f07030b070323091603080901031404080a03090c120b150103060803070b0a09120305090c010906080402090703021b0a05010f0c08010e04021503 80
    0x203407514502010311219001d01c50762000b020283c0090107e020301e003807585400c2c000149000e06040c0d4500001032100c00c4801036402501d40c1d04112581d200c9442c100c2c07a643d005502c4110303421610300000604051203409480e00068503550300c8980c0f042107403004048070308010072608180c4110500c2442c2c80d0900d281c070800843c01a5200e503928444c0400040c10b0b00c0300d5881c0e1111141d03030b1405100000d81c0035002c4072102c55052800240820040c64520361017070282c1c0c000c3e6400f0b4103041c100d900340000041c0f000c0c001d840c220b010b881001045001903013554118466418981c1040c00114046031802c203182d0b501200c07041d80016020000d56401a941900c00400f100103540d840070400c0003003041191005c01402400c0100302c482ca450b4009102990043c0003c1c0202c0001004c104514000e4058498181441c074442c0700075a2204000caa40f040c00c440152515800c01c201ca6010b052076209801101890342d40e092107a03803c001088480420140041307070410500002025210740300d101442c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171098165 1250 171096915 171096941
    0x30c05190c110103060303081b120c0a0921060f021b0a05010f05190c1106180715020303060603040f021917010e03040501030905070909050d0206010e070801091a0301 73
    0x14408200d418000340d10710b05280700505140c50715000f440840d40006045902501c01c11103e50410041c40541245000d42c0031070303108002d0720303a081c07248160149001e0202c0503811740d03414425680d640c1841c20510000b441007595141d44261080221305d1940085078002030030301d805458000d00072210140145e070200d108000750071011005081160070701034100041d004170300c2800340342000b00410184100075039843c070300a81c0d03a500e814080c9009002201c94032a10900795500d40ca07000000c42c1980034001c110100358002c0103000700f4140c4030100700d545040c00030340c0118116501e460030300000d91f201410a85030252041090300060b5280c505000180000001415403d8901000c400c0c600d070b07420ba29414141d050034250350302800d0000a6500701c44017442c000c9603406003801c5c910305000032508012800d0303080c0070307100050240000d201c05080c6a80e500302d80040c2e903102c100d0303120480c090319580009084000108400c843c00d4104982c00c10400004084800011000908461400702014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171099415 1250 171098165 171098177
    0x306030510092a05040c0216090c0912050307120c12051e090f040513050a0501020301050f06030906062218030207060504050105031f0f081c0c050d030c0519 69
    0x4410031029070f02c200e1040c520b4410010996503d6124501a88094000e03030340940c1c1e60308141200184200180a0b03480c02d03414a800800ba01d8010540140140240708000703d4141c1c0d400003041c42055030644c841d181c200016509104095850400944940e6406030400c4100b00c81e6a0106114041210700f1701040c2d02c03240d90356981d0203104040e1028400314078680c400203000b0608162242c00310301c0c1d0107003400c980c00141c0b070b03481d445460b50000485202400343c0c801c130711303150080200550040d0305841c801c8480408400c0030b202004040d20007160203001030b4101c54085071f07250505c03c200c562080c0c100b0303800e0512000d01124510072030300f51200c112140702c00c03908200c4c00d040e01417040c0000b0302030070f11384540340909210020b8414130021307281020749001c202c07044440412294070100540340052818450a603120303040c0f60784904207141d00c0c1c180c03580010303024400341c042d480740716080394810044c2619421681d000e40040030b46001c5401407000c108440c610082c40f41b440c5e00e07000201a2600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171100665 1250 171099415 171099431
    0x1a011d0d060209100c1101080f0f06060f04060c02040b0619030f0b060a0e090604060812030405070e010e0703051302091906031209061806080103080a050d02120105031b01050d0b010306030510 84
    0x10071b00012411001e0303414071151900744075800faa00000507901c51700382c02515110b6218507020400034811304101880e00800408c011485aa00812594040780212400e00003803030b01c20100034440c840c034110f0003c0f1150101481103107500903042144004a10340000401134174440104540354001a0750388001402960500080d14200081d282c01030000c1d60b0400007641000d00b026540d030038000441010030004000113040040070481000a0482280a42500d503075841002e00090029910640400d04240002d0178546480300c240308210707001890140315842e00c41901868540150101e11925100c050200c0821084010b030301c008022995030422041c60100000d0052400103201c03160f4001e01c6000704410b540c1310000e141501e810111065581e8080132090f20349100d80c125110f111400843d0060703011041c405964100e50303080c5c0943c0d0701c5818540c05140308128a41c82c580c0416014408001c0400c8107030310500140d5810b0500080107034582e101c181ca000200300d966004a0b86924207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 171101915 1250 171100665 171100673
    0x90603021c02060a031a04110406020f0a02100c0204021e0405011101020301050d141006090b011e0f030b060705070e040c15050313030905131a011d0d060209100c 71
    0x3444240305051401c0c41020085540041c1030f41c03090800710800c254550000030782c02e0342080382159070308000030001c01900304c0da0105481260018417420700580607aa0310381480c410007054910060394000c0c01194810307100901511490038490090303070020b80c24085d1a515201090180c401410000c403483d480d23500d0400010070031104840e10089a07401030004028175180c106500800b0f40c0d1040c466217800811601c0e0300c0c41d00c64190018100d041c20320900180c18001c69024510701c1c9001e9851200403030044080740440c078846032400001503002490341c00083d121381d110f001c015400805036440c0c44d0751621518604065500040c28686520080c0000c112000203668010521040807258138000752001030414000100140b1a85400442d103100b01803090030010080c0034000d204c06580c41501c0c007114002c0000714010125854070304d000307003140c2d0300130880b20485081c0c400003040411801d406001e1142681c200840d1803070b8007840120440e90b1410250031021340c00765501c140005c66820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 171103165 1250 171101915 171101929
    0x30c01060f0f0b18040e100e1002030f1305100c0207090609091205070c0e01030b040606060908031e09061b070603090b07110705101d030c21030706050109060302 71
    0x4048030099420b00420803501c0141e0303041e5110840c2220124100300c410f0008580078140601001d03400d0f015031b03c01e003411000c99070302042c00b44800c8821611420f1590300e40702e080307100075907800c0a95602d110009a241502e4984014514400c82c159031014282103013220580c0e090340e50001c0560000b40050051003070070712800300248a00e21060015000799100c0301d064089a502c00001c001e4000b6400d41444441a1180010304c0300e80d0144003550b0307480c2008640044d09640840300d4600b88200040c41a10540c0380409460384040a146017001340800c1d2103054484000142443d00d081c040203040f640d034403000d0480041203c50001c0500c2c840c001e000d081650300d401c020140342c500650b07140032800d0440c0c0785600070f403142000c94140109601c0301c0e18098055012941c04010702e250300c0304442c0d0028807041080c85200c12050b01c1c8811703604164480542c080c84940041d038580801c8021000d40c14840b58611000c401c1e02d1070119203440365401d41d4400d030000805d5070348400b8100b0450610302 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 171104415 1250 171103165 171103169
    0x1110a08060f0105070b07110601141221090112020a030606111903050309010b120f0118120f1b050c18040f0204020309070b070b0402041805070b0f0705030c01060f 72
    0x1501800300b40100000a030041c0035003c4064800f50800380020300941c060300c40e5081c10440301c0b0403a403203903070f581ca8204c0a10160b00034190040400e06400406018001600080c0c1c0904051394407807215078070501245600401841410401d0750351215031060154030007001208001c0d500030442500301240a800c6081103504c800141e0301c1504c1d0300781d5001c241c402401103a40e04d45001c40e0f0700c1d120f403203b003805040204282540482d8114045c4420400020080401100d02000344001101d8845043d6a681040701c00f41c0014140100c0480c02c41c402c882060400055041140c81c408010480c1040d19103124012107641e441079051203040d20306207460101000c041c4000280500e015507581c82c80d5809440003c0c051500400407038003c02081c03003290301a060340d6400940300c071080c1c00d010740b100c40251401d900940c54040395480031089100c2e448096174212000301121490054140c65503445291039035840e00d000e0103030b800000d5040c001041c80c1042a80013060440c2400c100c0c900b4500b0356 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 171105665 1250 171104415 171104419
    0xe01080303041104020702040212102313020901020115080a0302011d0c0d0203010b0d030c0c05030604170309010b1c1202010204050a23280812090405070c020301110a0806 75
    0x5004020003e00102d400c412004403d48025031512034501c0890301a000c4d02004210300c040070010801c64a0501c41124101c40c052140000740040b21581d4954206c1541d4040750462810400b9403a1800c20750000c00075035034107200008040c0c00d4652210b20181c0e40c1d400c80e017070030303044405080e05050b82401800b40c10301c000c0500040020024525554494284500a00600766420b586041d99000c0d40000704128015240924100316031134003c5c070032018841c0458a4040030800820315050008415119640c821a0700842034514066104a904010040c8059640340d008600b4140c60701040c50070b642800c0c110011110600d4640345240c56441650241160320612040046640d000480030440d54960283d0b0842442e03148000d2200c4068000c050704005146045141c100581020f400716403000d10320040026213032810103840300084c0d0400c40b031100080c45540840d1800e580103907000aa00c1c00c10302c503c0c402590210342501c3e0100c400d14403501d0081800107043e0342016031683e0008003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 171106915 1250 171105665 171105667
    0x5041505090a03020f04110d230903090603040807081c1803020c04021b030708040806070306030f1e050604120905150f090d05030c0303061e0a09110d090b010e010803 73
    0x7507022400344007603480007034070558526a0024103611264041078110030807400c00307960341040659150280040040c5800300c001c180350068007a0300c900c046240222082c00c042d6142000160230084580c2015200307541850040102d00000350051004041c0b40b562860040720321020020700408448170b03400608190100142245c000035408103061071014400c8400603110070b540c0440080d520f090340c00d280d400e44000110306003030203640c0000d00101d81c0f508040710541c1da11325004a044d14110321004201200389440b82c00091250031181c102d01c0d800901b041e1725000ca5456503440e0840540302540e2401e409000b00303030810703440580b030009442d00755100c81c900805a414040c080c0702d0395a4000040c2c0020072802c01d030f0b60f96400403800040d00718040b651910084500243c42e0781c4142c80882c40f880b00b54078000e41130300e000e02c480c1090b160014071510905140c088041e018041e120851440004104003907030007100702d071144080c018082d9204000d1507041807050401b0b408107070802802540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 171108165 1250 171106915 171106927
    0xc0a050303031e0a060504140a05010807082112040b0405070506120411010314041401050112020d0b07050d06080a02040b0d05030d0902030703240b01050c03040303030203060d0f0305041505 83
    0x4800e052680c0040f0700120780c01d41d0303a03450a090092800b9000258841d007014508010b1480c0c102107680189080f45d003c00550341d850404030399440c3c1a10403282c46800045c90403441e0441c507c2243ca0041803240304924107020240c20805000040b40c0c1100d030620341000b030105100d4104a401702a00301a41e15526040c4151074400c40d034180100020700f08403030140000a00d910a030890610f020b80c0c5d440c1c640040c00e041c07030002090004401402c1c01580fa0800008000c82640c0918024540203403118098083d652a11040a80000c101d00d080c040104142c1e000710000348610303401042103602400c510b02891042205a810f180720161180d04030b0414407020610120803216050601c20000852482c6413010a00740811030b03101401c5000b802407244610381d030740300c08001004a2501c0070000b0003010401924503000390103580ca156842440280300090181c0d00a5821140044c41441802820340c0c0d05004c0351003200c005c800040c07000c142008140b5003c01e00020303c0c0700e00c1c00c100c0c0c1801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 171109415 1250 171108165 171108181
    0x6010b090a0b0d0f4a030705030c1606050f0d152309060a0b0a03060302100c0b06010f2c150c070e0411090406020c0a0c14010504080d05030709080706020c0a05030303 73
    0x5800200552600b4104400702d0a00124817111141020a50b5056035200c42d0182407041d180c0d042091001c61a01441140f6962824040f8481d000e4903d41d071500c0c1e0500250f03042c041c00c0b9411005240d40120b40e05c85142c0d11919080300c281c00205a59844040409200c40016601c00840051031380214840800d010895442c0024034081d0380b00081160b485442c080c8040300034140319031000e50001224900000b196501c00800d03150503000383c103801ca40d512100c00440c3d04441170300005e0005100005041b0304c1c088407412143c01e10032084884450101c00d0300010301000e00d0f150301d540015200003003204071041c00740409002464481d00c146018501034030303804100040489070a21418500c40000c08109460f415902e000700c42c2030840c0c2c40352260b80f034000089880ba00520f501c0c1046601e4110496204600f02c81c2661002c45c041e000c02c0ca0707010f900780d81c01d4201614120501442050102d210b09040003e41d00420740c5078010a4004504d10500c0011491034000c1c1d070194004104200c1d41c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 171110665 1250 171109415 171109481
    0x60c0f02030c0928110d02130b03010609030605150102060402120f1006081606021b0d0f140601090c090e040201020c130501180c0c11040e100b040c0305040506010b090a0b0d0f 77
    0x5070032450056a40c18030804209103908d040d4101c1c8002e282c0c0440042801603018503107409491003070f1010010340d140c14814040c11450710b096540168080400180142408041000b034401d584045030100124044400d040000c00c0e0900744860740c0d610801c0110f48001c129625444450600d40c4020038140b0784002e40703443c48000404100405500024030759103884c46441f56494100d5451f48419403180703810700c80041012003007840d43c41507100214003038125104480301200e264484ea01e00c83c0c82c4c070403110080000200141e05600a121165105441d056000c1078440c100300070001c1d0304e6040c4400c158507407049114101c003181ca03000f02e6180d01c58210b040c0001c6540c01607a0003807914203007400600540b074400880141c0b4080c0255031002d40e120764000e03200004c0210360030300080c040d00c0811030031100200e5001c5d105501c00001000031b054403000a0580302406010150429100c1101130b80c0d07079120303480c0c0f204100d03524040030300c800d0014415070580320344144540a1490103002c0c0000a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 171111915 1250 171110665 171110677
    0x907050706021315021e280203010908120414060c070311010605030d0c03140304050604080c010b06130627090c0c120207031b060c0f02030c092811 65
    0xd1540014070902100003004080e008080c00c000b03503c4c81c1d20032050000d40b150400341d80d00440900268441c0d040a00125400f00150707a002116074041759000641d6541c9a1110401d0303805544c0e500341d9801140101004011856130752010b0326441c1001d24000c0104031004440304059001082846100340c0d0a0048550581d0940340c10300200f040381980c0c0c0d004108591260381d06220300038820202541214858001d14040c0d2120140c2481107407035001c2a01c0202c6006019030082d0000500040c400340c050011000d5a90000620352200008a19164040000b41840000901041054a601281051103481c0c1c0b40c240310010035100c044401854540d000302011389840c2c0c410050703c90700c2a011422415001103043c03150101000340691146018042502e000010050b00303802c00c1c0503000114200c6d866a07464240c0c07500507484000207850000401c99050280092180c980d54480d0b07174240c010780c0d100c106030458440c00c404004440b034942c0c2c10462a9405d01080307403c1c10b075246c026104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 171113165 1250 171111915 171111923
    0x6080a020a0e090f07110303150607030203040e09061005010309030c0605130b1e01060f120b010c0b1e18150405010219020109030306050409020d030e220e01050609070507 75
    0x40c81d0120550140c4445481d810120741024042d42080400c0c1220b55036103008a825403603440130682c2848281c0c0d140d01c021666070480b4000c110901407541080300090020701d010f44142c86c01e094031307008418088042991241a0340d84150140b1110000280e6114010002404d0800c40301540c0d40d0081c0040300340c860700cd040140e803140000c1c910300020080b000c0180e88100242200c5c43c0c110394012045c05101d074403a520350740b0344001003244c03805a54a0720403040c0f191108a4141800c84e61200a011751151650400a251089000140348240701a004d01140841183c3d402c071101c0d40e04042d20b0b001130100c1100c020b030b104900300c0c006020820300329804c1103001c851150794880c2000b41c0688207903008581c1041801d040c00504d198190b00488100d80300ea0b8080c0107543c1d03543d0030041900c8030140081d60100c41140c0441c0007038021141c545004801a10710010407a00c60844400520070100c42030742d190301d550100b18146000e104903070303209004444603410b03814504c800a107940100c2030014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 171114415 1250 171113165 171113167
    0x602010f1a10110a05010f150e0a0e07030614090d0e0d0b0612030a02060f0a0c05030106030e010f180209010b0708030403080c1e04180e03160c03020d082206080a02 72
    0x2c007940c41103024103440198002190040c088500d0700d240244825540035141901d4000410950045002100212007452812a1442d00c0e480c50820041c01070110b030200038441c2000c00800504103000d011044140b5032462081450301d08645400d11001c01c90200401c90407007001402c1c0e5460f01c0045030525040b030450703101c942e04c42021a500b80c090448d12455803002041c00c4c1c4400b40d0006556101c0c034080c0700c0000c640e8441c045280155087e030081d06010800a04c014001c40d44a0b502400914443d079001203401c000c034240c008102c0f0652140c80b04c0c0c08401a03104029400d21005c0f00c1e00429009a07031610300040c544411b48240000f520080070000301401180402420000b911648212803a04400003200c2540d0012954064480e60752542c4100c24618450040c610818404803035601c0a03516081c280d40484005192440e0308072408100c0703013804009a141c11080500840c03140001c10340e80c00c2d01c41862000700110700c2d10f0701495900910140025644605003542043c0580c81c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 171115665 1250 171114415 171114439
    0xc0c200402070f061506080c0403060b0319050c010e030a0b010506030618010b03010e07021603110406080102040909020a081902010e0d080703020a062003130501150308040602010f1a 80
    0x1a0192003801c0c1d014003c2040c407021002408815407110200080c1c0030f0441d068075a8450003942c108000300c6042103d200f040c1301c00c2001c40c503642c0050121940007429103040342c50b0407400148a0316408c60035104c3d90300500d400e22855030000d411710342944d8120001d213640c0c030459992001c480c405006032805400044040307034050303c507100400c040c8020851403070b10390368407010700c100c00741c000b44200c0303ca8030080e101203100c8500206000d22010042d110704803406040d6100c9841440e800c0e00071582095070381100040d510000c2c40601701429000001260b08507890040000011007a008101250084481ca4440c904898050400d1170b0f828207042c0b00200d10080020300c0001030035005040c0c214001398040030540d01140f50004c66216801c10000d105c03003140c24142c1c03040b0b551604440d09204102081c04a003a0b4070301d40013024410300010030045d0329040403858200daa03500071600c1181c0804d0a01119030280100c8188859400d010081801e0b042d10000504c0c0641c4441402100c2142c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 171116915 1250 171115665 171115669
    0x50a05100b0f0d0e19020a05060403020d0605150d0c0f1703030f0421080402090a111e2811030906070f0311120c01050604050103111e220c0c20 63
    0x1100c400d0144100036510894a1741208036081070168800301d1285464100120306442d01c1001c0d01c003030743d030085c1501d00c1c001105c0c1c1d9540e00804010340844220409200c4406181d903030346072429001032203a4a190390f03040c41c2a00c044500f2aa0341c125842018002c02c3c0e00c3c200000001c00e407a445032031400d13a43d2107610b99051480001e400e60555a00400100004010082d0005102c900491099541c52402d5480000c084101c030b013400c1c0000c11540003000760402c1504904200c80c640500003100602d0f02500e600144c0d40c1503650203080c011000700080c60052260407640c003803101b002400c013035481c102c000800601d03640311340f000080120560445000915210360b05000c094501c00d000c5440180f8120742e4150103401008002c5119030030304002444d5810140500d40c100d0741d01401c004035807001607080000c1850041e05041d219070074045851a103036544584912116219280003407a140101103c00070703500548192014070080c00da840d400540d5452003000d00e0b4000b0400326240c0c0a10b100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 171118165 1250 171116915 171116921
    0xb03070c1b05041a011214150a1e1a040806040f1a07030605040b030c0d02061e041d010602060702071502100504200d08030a110913050a05100b0f0d 65
    0x21900649095a0b00b0149030b8280b0b0001304024090301c91510b0040b8940b84602590039003a1280a034010142c04103003012001c1038090000e4200400d412001034072041000f01c0c56881d1444170704004c40c00b107810841c4824810900d040f50710209a007500e0182400740a0781d0781c03076001d04014230315204006481d040c0030220030a00b0140b80302d000495158182110014094801806244d00c5603140c80c00c01c0c1c0641c43c0016440002c1039002e04000d146000980070400319400100920360b10341315604070300040384162001030014042ba0441c0740c90303011090b01c2d9450320000581009040d0352000003440b03192030300001d9100465822a22101901c120102c1c104d04082500c0550748001e0305040510080080002c0504045001100e111090500100800000c45648030f005880303040200046031259409401040d824035040d00c1c00c52a103030304400800c0110452605100c03503580c3e11001d014101125010341600500c1c2007009450076400c00110a0301c070b1044035101c10215400040c00b0401100b0f0f03030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 171119415 1250 171118165 171118169
    0x90703090f06060e0702070f05061b0f0115050a06050318011506110d0203120c0a030615030e0601060302180402030406150303050a0807020303130209090c150d060b03070c1b 76
    0x2500300e28092650b140c6000a415a4044c0e200c0d000c2d000400905064400288030701103580c2c100e00030440e940703050148040d90f440144130f840040d01c04030740c4620001040011a0201c04007000014180300720b46d17002c0040c0b00c11504103030f11440e40841b0811403a0741c00000d403a00201c5890b800c11240341e44696031801003a01c12580b521a00c1103103400a01c1c1d0b904a944801c0c00c54658007503940e072812088040343c9a00c543c48058a0343c82c60740000c210000031060141040d00c0a504000801e1600e40d041e10241e00800420800040e40750700015618010038002c0900401b02ca050960408000d0a1840700021000e100704e401507a001c070015041c0040b54216001a08240c2c001c00125a2a0b04004140d03521040d0f00c030000c1100c010215111510010449115482d15840e003c110340ca554204004280050503a10042c40707080000e50040e0f0301c1ca60f800c2088016052590b644104061544090329140d6001c030035020b8091080000c4d40380c00c88680c10a00b42c0c001c000071408a144010406d0b10302c0b880d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 171120665 1250 171119415 171119423
    0x18030601060201020a0809030435030d0207060b010311160602040b07060c02070602060402030d110f0d020304080f011a060703120203090105060a080607200f030c0a1109040f0209070309 81
    0x200001079810740640c01040e4038091555403180e99503800c117903190b5a104621a01a12001144400f0440720040040500c81c900e5aa100c03080080309108151564201002d180c0d54181c0c001040010031056124800080c1c00071b003410710a42500042512240c050321018250040181d4a4401001255411180905026070f0102d84034411401c00d04018040d1800f5078000d4402c0e41808200c0d14000034015110321b500800410710880880c000321542d40c61441112801d1140042800d280b88051021032106003030b0b507000750340b00c0d4500300e5280d290801c0780e1240c42240e4034026070201c0d4030030460303100c070185d54042e00c0d05503031012103240840c0c601340c4294000d02c2003403001c010f10004140c1900407501500e0110343e0804101d031a181700540f180c200b9034040300440c1c00801008441c0045005082703282d07400b4000c0d02c40c0e900b042c07201142543d03c0100d101c4200e0b040303081d4a800308000300c09560315215090f1490750182ca400d5444202d80600c203140640300d0280341e000128030612a42080f81c9403580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 171121915 1250 171120665 171120673
    0x1e060324070c050a05010b0901081903050904020c0f0d0f050c06060613080d05040e071d04150b1204050105010b07030518191403060604051005090603030f2b020a12021803 75
    0x1030911710b0091410b04182d03880740800c00c0c0001540301e0009020a42c02c56001c035403841000c09542c003580c06030700500140360441d80034000b00b0b00f200800c0c0030030b1604404c540040c00c100160230400420065000402030144041400344c42e401c0c0000041c0da65002505441c225030310904541c10100503401984006c1952041c00d000b010100c0d442405081221080d01c441c0d0001d49980b5002d46991035980907d02148582642c02103031803801e504103042034619890395080c3c0c1900d502495100b40e0242c8402c0c00e003030054106000821400340b00340c500401d50b05d910141000c00958009007188600240aa1a543d03071900302c440c40e0b56185803610218000481c0400c81640d200c19049034036120700c0344284030740030b00e00004156041c07070f00038a1b100d8003d07244910502c03401c0070100892540c0c0649029054130050080499040e60030b4002c2504400c0746d4038014408a0000c0508082c1c400c5019102c07204e40180303c40c4460640140c2ea07000000c520a20150321900b10384018440b80b00d150540b26410700c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 171123165 1250 171121915 171121933
    0x5070f0803070c0506030402010e04051801020c0f070f08030901120f09060c0e04141b04080a1103061803120903070501092009060a051002030c061e060324070c05 71
    0x400080281142407048001d804000d9132841081031074002110068046510420440881d1400e58006940908480d40180010000e888140d007240c01c440e400000550040c80b06148400f410004c1e0002007400c035085054160800f00e040b40c40c1d02810300418140209000c0e0721809440c607400801c04c0250184040003c8803050904402400d8468410800724000c01c84940351410640501c0350b440c814221112129100e400380c4135241c0d070791410140d580c2030701407001240c040800e015044030540906811040c0c0260a81014100035000e00007080308606030024400c10b450200c182c034140c01c81000407081940c5e98038403140c11441140d90003410b6503e0070305075000b0007003c0303030700401d01c2800b00351070f82034680244060021241003545e5140d84212801030422040c40e00300ca01880845040c819a8140002c1e0341e0064a0040c00fa507160130b44034001301820400d0f40011500507403007941200107111500680300c1c004116109500b0740e000708028600003440c40c6001d00040f16000342e2100403294614 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 171124415 1250 171123165 171123179
    0x9050a0605061f0503040b011e031205041a0c0f03030112080702010903140d0207060e010c0209070c080c06070e090f06010c08040807080609010b01020c01050a08060d1e02010e030102032205070f 85
    0x20340103d604440001d0840c0000c160700000c4d001c0500143e00d49c41c030f8058010b0442d00c82d00e10209056024508000c0c08000114a1480c071074440504100c081920503213600c540e541c041d05006c18100052201d0b4402c1c00108800d5400d51210602d81e900000b040d55140d40600040324182407540000e840001c180c6000e00c400400007030040d02c4d801e5141e082d01c400f20f44441084a0301c5034903021140c0040c902490000151070b0100d80e9640041d01810302c3e15075074445a590380e2483d0045e1242d50825080b0201b003100261300480448441030080703820742150716002458142c0110003401090402c03192150301c40422070101c0c01c58000e03100ca0001c49004071303960340d003150b039842c07049a003079940b94205503802a165000050f64568800140c44075424100060700c22a50210000c01466001448078005008a6076458160160030411800c5030b4541d0702c68000074050540b860026070081e172041040041c0000706d01040d41104040400c814142c04083c20983d1901005c0e030400c409950303007103200203155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 171125665 1250 171124415 171124417
    0x406020604030807020c010905150c010603030c060e1203010905070e1c0302010e0715050a0903060906090209250309081308010501060906050403080901080a0e0a080a0905030109050a0605061f05 85
    0x745100750b40300986079486001c2280c03540c040024140c0415070f228010701c00e80c0f0704500c130525a0f0300c1c00880c0780c0c10b1144103a690750a5408980c429004a20937011800c03c0c04850302403c560a00c50000601040c100d203210304405100501c106480075990701c0114942d42c0c40b40d41000484a802800c280358220810390051142c414184118095072074040046402c21010600808880c0741140c079007162581780d881510542c2c0050140d100300420184007100094540c41000081d07070148900003145810351041c0000100040c20f2140c48801c5c1240c055414400c80100c248142c170705107008070303a50310b40786003108d22030051400448080800300c2c00400c1a0a056021504035903072503076054540359851001f40d4043c030030f5000141014104102d406050750040924070340110806a00155920342c64107501e0078081000802c0741c06144c0002da9004140e44400ca52010380001c40081100c04920750b0780741e6071503005000092000d42c81b84002040c0340d640042508001d40320225840c4074031030990300140f007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 171126915 1250 171125665 171125671
    0x1030b0a23040e0309040e070305061f0540020c060402030606010503130b04030c0609030201060e07020304060207030623043f082d0105031207030912080f04060206 72
    0x310a400400d24180392801e03003d10150107020001039440c104141041c40050b001444607400e4611400200000203001000014411501a4030900c2c0513100d0007403149450b035040d48114440c0c80604982441c402c60602141300601c1c441040a15032445242002a84c40c0d904800035481c40c400b040c02c0040200100d0b000d44514800c40a90746190756440040d202c43c0405e0710b2491408040c10400400a88042e40d0960401e00a0821200720300301951100160703545003404500507510340740c0401c960000b8004d5960000074600165083c02d0502c40300958440c1544009000d2a84903011082044c01440c1c1010403128049002c016900c2e141c01c0064940000380b0242c007022a10107400d5030b01d05001c410b0b601c10790b0191012940741c0c0b882510102d40c4100c019240c03110103104c1020400302c044075409400b4510340c0440c0349001c250316000400d4102050300030b05042600c000c104110001e903002010405803210b84c40c0846018043e800d2551030303800740001740041d20100180c003007030fa103800081c5588 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 171128165 1250 171126915 171126959
    0x90803070804030203060f040f080903070308180901050a08030d151707061206030b040b04020f0301050a1406060309070e0a140103032c0a0522050403050a020d020f1b01030b0a 77
    0x8429107c000154028800072100034119140c20b000c82000508200c00411605038000d0481d00004d80b40d440350390300b907886200340f00003110403150f0000706802c1c5409507500414044400340340c1c40b850074041c3c9440c0d100f150110380074256650364002036403030500b5202001c6c00034101995642c0c201d12201a41c0c0d03070380d14000d0034041001640e1100086929000b2041660390104a003003960300c1e00d940b002401300c00604101c0e4400d1420070a85c11a403824401c641c0b0513020f056011030303c4551398004e60304c5000c01800f56401040c0400822500b00750014500084444c0301504032000ea880901c4400202551424020b211465900020501d07910a104007181e05000950b0380319864007010111956001914240d0403a00c2d2010401252501c0500c3c010340d02c00040d400c105c0c40880740b01180c100e9508503000c034042a400700305036607000d6041281c1c1d207006005000400d2402ca403c0d0380c240c4d1b03444400000047c0c0182c450514200c0c4d9101b9001501211f90191111030941d0b19002200d9844407140e415030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 171129415 1250 171128165 171128173
    0xc030f0f0c090513080c0118050d0e0d050705010c02060c060c0307030501050315010e0606040506070f11090106080c07021f031a010c020603130f0b011503050105040c120c090803070804030203 84
    0x101e01a0068883c0502484441d102d01580583e156200c01e0290001c10740c000541d507840070310000782085800d0008081c0d108038045c211002c098440030f8100c00e18003882038012201c1c05600000100d000641038165042420907d8041181d4400140e2038851948481100d000d590706115003054490040c5004a0260b2014000b0340c1c0c0ba40145a0b070b407515407200b080252544401000110180c81034a600304c072000d01082e245c41e4a51002c00c100f548808000c0341c40c800da050007c000c0c84000c0710809a2800102e803864284e502d080d00040040a002c0c100c180300c810300145102c03c554458880072060501c1281008000107202c101600615004550305030031b42003601e0b590b049600c5000f014000031342c01400c40e420340c1c6400e040b450240071101802c07034107040b110912002190407104028020401160301001040150400800781c64040e07108502550500e01c05081c0641c01001200300300d00030000002d22502d03055012684034220fa40100000c1c0000114401801504001401581c0c004d400b15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 171130665 1250 171129415 171129419
    0x406030c050304080a0e0126010302130b0607080a1808010e100204180506040e031210080606060d020703020a0605090a0302071703031602010b36060114070c030f0f0c 73
    0x950700da1000320790040c01141d00b001240c0d050b90050000d401c45000c189019800d1b03441c0319400e00391124407900c02c6000005040010011880d026103101260031400b641480b0142e40503012070327124003649400410740700020500440706031044105d03020290074a481000420759070840140203110700c0e80194240e0060300a102d02d00c103494022a07085840300f034501d600c9103840f0032490000f000c0c0039040c1c1d036001d074464200100c912000c00c0a040c2c44140d17484a00c0c0a07003008100580c1c40307416584842c041750096003c2144ca540e908080c3e940703c450924001d40c1e076040500d412401c200700e0100041c8000e1809090003010900001c041d400719110341c00301d501003900e0756001c00c11140160941d11082d0700c1000001e00185410070490140681400041142c44000703000402d001c401c21100707a01040d0300c103010b03010400320342043c09000b4088162200c950070b10000007802904c03a016581c0b41c8020000f410400c0203004130b40480110713000a030010301c1101518285042c02c1c15540183e030200400c2c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 171131915 1250 171130665 171130667
    0x150807020a0209150a0e010617090a0b06130b03010906020903010b0604030512160c180c0507030206010b09030708070b030414150105040906060905070e1201061d0a0b060a02030406030c 81
    0x2441c101e650300240b45000e241d8031440328081950810315403d800c50618100024070400d107454184c040c11280e1642d4070710240e801d00f0f2551001c4000c190016076404681c01d40003240400305215004041500c4c5002c2005c00d045a10001d03003620200c198040d03207004043c4041c0040e65000d00503100c0110001d1141024904c10404180141e000141058010386140d0684e425820000c2405000f200e80101c203580f4541c903a21598030465020035806a03031a07002d00d421035114401d038212980681403550410050707880c025a201014000c1003640040010507260a69040281310f0046c1b101004645129486040d050400e41003a40e0844504507440500108040003103070700c20a21000341200c060301d80c0b1700420070002d0568081c00b569001e98400c00400c1401d10790180b184181d120b91100c03080d26070721074240b0948007405e01d100f42c0d02d40d1420800344091800304414044800704403101c43c41c0ca40b2084481ca004040c061002640711800041000e641900070010b84115501c0b61401c000ea05840c8030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 171133165 1250 171131915 171131923
    0x3020a17150a2315060f0a080603070503070620030306090406110d05010b0c070b0a050a0c02030102090303160b0a0501030b0406091a070302071e0f020d1a0115080702 73
    0x185808907048415000480c00100c0c004580c040c1d000302c404070b103003440d02d00c1d801600c405000e0340100941e6018100b02c0ba05030030070580d89a9000c1507455170301e4503000f08000c0c0d4007070180104450420803201e002c44e207039903400c04c03500c1c01a050003010f94441c030b99280000b0b41489000d03564069402d04401400690501c04415a482480c01401102e2603a03156030b564002010140005506200d0900004400030101d00c03c1901806840400c40c0c0d5402039004201e01d8225140d024a50300311042202d641000e902c070040c2c6152400300d041c03034000c0d02c52501c00680a4010340b0941703501071001240080c0d903000d02414101e51940640114003041e20782d44041700c15203800740406810303100900d001c2000188a6400103000303a00070a90800300300c01108620b150040e0540307040c0006900441e80307178240207034982102110302d0301c00c0f41e403030703070307440f0659803000c61003101e010217441001009620028410a868104194001e980c40303442c40b581c4407034014551001c01c480c1040020130840c0000c0e580fa00000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 171134415 1250 171133165 171133199
    0x40605030d050306060307050c1b0102011406010e01110708030d0504030f0905100e0315010e0a0e0c030d1404090905031c09021305100305060c090907050f0a0f140706050103020a 78
    0x60390b801d01d1a512001841036603032014081d80c007044010440b19403c440d06100e40c0b480c0550400d1004030240514000900791507d158952205860220500006a802007a100100e09003030030241462507203590b03d00d08002460344090f02c18000000c2081c404401c42c0d2200d40f099100b501d030fa2081c1c005100084076440d0700c2d401525086140c81c40c0c10500301e030086048001c990030080031a44040a0b50841039540c0301d00381c0c06001e000c01c40800740600b01e986401075403070541808000b00a0f03d40e500e400265034074880d03802c0005001c02290055a189498011500504801c42c8103010840141ca0070310380e00d5203c011018014100c03a200e12000e06c0e101c0c0100104241c004081e010041c40c1c500041c801410041c280f030032041d420000c0080000d03424090300c1e104588206d001d0780c0781d46c44681400558600240407004101e020090084420050400d5891111311031a100380900e40d41d40059a4848560281c1d0815130341c0445c0e804100807150300103506a07882500c103450116503488100160401035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 171135665 1250 171134415 171134417
    0x5010809060121080d09050105010f05041e180506091f060803090f030c04090b0f060a06020d0e03120408030a02011113030b100b070b04061103100504050417030702030405040605030d 80
    0x1143c40da600390120264018414080e0040700d1404004c100ca16084076030304203044566035102c10041003044501e80c5010300502c07040da02405041500c02041d03109003a0201c03003c03012951917403001c0210b000341c44100c009551141c00c95842e0704001c0b04640d540c3c40d020310040c1f98110280120100719901e03014040071101401e0085007481015001c001760b0740120089036405201c0e0807103501c1c481e940d40c005c1c44007107801501d8500042c00c280000c070805d8140202507900441094008000c65a030006180250812610b000d07101100c42a00082c10036014a007030f07011a141c045008034031018084024100d4485030f400801000c0c0c91a1108031540c0195031440b94003401074682000402e44944540340e22810030120320328400e0326607004042030380010002740c0c3d5808050040100704103046c8100d54040c03100d840c14604500e0711705d4888010344810300815010b95103a401080400650b09034034103680301d407503800320307128136140310000d580e600144250340c400d50402c0c1c000102c070300307010034402c1d00c100341 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 171136915 1250 171135665 171135689
    0x1005100f030807050a1203091406041a0c0c010c05120f0105030d0c060b120102070c0b03250215070e0a0e010e15010918020301060e1e01030e030702130501050108090601 74
    0x241d41c42d80707070064000c294180c440380503141078000020704000c40800424295100059596001e0409e0840d12048880030f807510760000c03041c40046001121040d10301e4284109016250b0340f220141c016500407028000c01039807c2c580c1c0c0500c0c2ca030b04607005d0500180048145011540c0e84151310110003803e1180079055080a010340c04814452510003202034003480c00403500000207004a41540407110300543c20f0b03540491311b2030400c60326100140c000c211020015055003055651262407202403a91071305601800c00712409198000e020301c059003111000148010b02d420b0310040c2c254009004400d01c02d401c40c40780499040c0c075414800781680e034a080e00c0c2d4500d65602c0031101d403800c0c07402c803c14144424406c001070501c00710340355032030000c51030031000d40c13254174141e4040c10500c0c4007520030344641c2181d81c0c0ba44c1805034200e094560403d00340780200d00c101420441c00c5c15481844c1c0080d401c149a00d0a215454205400c014100c64080e6548001569240300030b5441d07030f8007030181019001c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 171138165 1250 171136915 171136919
    0x60603040b06150405031b030d091a1309050f0109050907060e0d14030c0a0309171f0f060b04030c1508072604060f060504020f0a051303020907021005100f 68
    0x2403480d00d0343e201c000c00c0c00129140c01d49484c0000c0c500b12000180315181042a00301c48045d0400f4484400e1441c03c50901461841c01c04021000d00042c0640340382420b100820803100c110031000841c801400460380070481410f0046e40302c0c3c4400000d015022140d420000482c1e9214400120481211856a00c00718512641e100704240040044c105a6050f904030044039801202070008003210b036a4074008161000c464540038204032242d80c0581094a0f0040100340340708400b01e0a100100360541c1031241c00002c0101c540020100c04460006103480c00002003100c00c100c20080064038054220000a980e0303c0702c0d01c41c1d28480a00c0c4040c006032400000c68003041c000c1c1c034580399a0141080c50070010812182d06c41c200c0d80c0441e0180d030f403291600e010f07480c070308104d00c00c180c00f40c4410b80302546012242c807a80011b611600e0842010000000b171040700b03c080c001c00d410080c5a0060280c2c0c601e040881b0001d503509504c1004681c4280350001080081c01403821a008840c01950020390880c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 171139415 1250 171138165 171138169
    0xb060a0c031d0306090f1005040f030c0c21050606100e06030c04030f0303020a0e03060907150e210d0903110d08070501090b0709060207080601170f0a0812060603040b06 74
    0xc000355000b00d0301c941e040340340e03160503643c1440703014881c80f43c4100600301d050140301ca2628040020021000701c5180009202c04900340c1c000d070118451f00350174109412074452a115403a010300d0b60103d4041810040c08a8080c82d070501c200344aa8090001c41c1c43c5034452400b0008c8111503005504007003a45403580706643e0501c0c0c4c001d03660003041c001d4010304141d03803506c07196030303081c41c40b00200c0020782c2c0069000a03d5030401c031400170039113050b401880d0310710300004180c1e81c400c40c0e401852400c94080c44040782440c400c44001d0100d03000a4644c5100600c81110551106500000e4089a028640044604d141308401d8481100d030018079499041d440a002c1c80043da20a61040e83c2c010402c104050200d002402015513540c8500c9020510340340003d030040001b10705400c0081113400c118070070072440400180c29415100c03410012001554000b0070036162502d4181108124044c0301d29610a2000c200007034080c0f003000d651025040d640b5a001c01c9283d103c22500100108008800f1480300c3c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 171140665 1250 171139415 171139427
    0x6030112020a030f06021314010f03050912040f030605070c05030405011202070f0f05010f1509050c0405090108010b010f090303020a030c170d0902030f030712080a0908040b0306040b060a0c03 84
    0xd240007620030100070791283c540450300d07020400e040e202140c0006002c0791140100070048010001030303015048100c454000206070b90281544031041544034404034080030390030f208203126540301d1850107030350b55550141e50811000c54801510310070b161000180405004130045281d1640c0070b4013551605007800019248280340d020764010340b50b03080c0b10020000d844841d40e011000d0144d0014814132029143c61030a40d03080c1182600046d0a0100f9410456031a11048040e180468408038850342c8850805030f480c021980035990100d00c51000080462041d40110a19030b0280c4e1403101078580c01c03c059441d00132f607110003030060740030070b11303100c08a0b00c1601d508800071300c070701c0012a00004c0c1c4a100b103c4c07900200802c503402942d810109086107030800001e4400c0d48980c01850803c0c40c151524104528951b00d5003051003d140002512000c0550003143c61072b03801455182c07590b45a5141500c660000c6070300c1c9005600e40200e02ca030514002080d40e40a040a40e60301402d4002d541d002c40728 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 171141915 1250 171140665 171140699
    0x40f140103030c1b090f050105060405220b040903180b0909070f0306050303180a120203030708030703020903150708090a0507090b06040f06081e04030509010f05070b0408040501120605060301 84
    0x20540591859010828942240f000030038128102150075031b0108501421104d041c1c0c0441e100da082088200030a8440079083c6032902200c0d400c0607032005050918001038480350b200c00d80d00c2490302008608040d08043d080390000e50703016884954030b44a1a100400341f00c0c8800c080ea01c0001c080c005071038144210412207014800f4a0042102580c4e0400710f40b80d40c06c081500d4410b24143c0d14000c2150810f01100740003003544804203002c0e420a900426100e208050001d00004000030004580c28000d4040700c03040074028046032103614501403504200681501e034100042c11090204994000c0000c540c1541074000020f440300529200e0660001c007007078100c064110b44103100002e007070605030200100170601170311500d80a10708404428840c0e0f5a070f810710301c8800000f009000c0882d50000030b9401070740c0d0a0820340c082e820b80810a4400340221103006010451102c100030401c440c04014104840080e200d03000d110700380c4a494002d4035260702500c2d800000c144010048651000c0d0507441e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 171143165 1250 171141915 171141923
    0x60309051c0e0f0f100203030106030c05130501050f22060e09060306060415090504050c010216060807030c0c0819110c0121060314030405030d111b060408100b040f140103030c 77
    0x4c1c2c209030b000c007194180c40010440b41c05a040840100209509801084259182850060302c1e18005010801070310460b80201030400c8800706024095036844812541030749401c18804800001e940840704100e0382c0c41c01480001089884c1021450805084190140c800107005e000c03981c2c1c42d40d0900008003440311803540d500d00d01c43c90010381800e4510070740d400f940c000c01c0078103001c10616001a1034482c0803108141c01c2c10701c07408104101796002c5a0b60b504910585808516030703903400c504a5a0b206000c00c09401e20100140e40c1d04c200e40c600500d00d51480d000e17118540d44104002c00303542c0b144145c500c3d4a000c0389402051003408802c09100395008003110100103107103a229100c0300f074860320040b40c5e440d10f82d01c006000d00c41482d041000780c050880c149800845a50548405500c5480c0d140001c0902c8103180d081a0312662188241d40142c0b812508070340100c1005030204001e82820414a0b0103035180113500c020900c464080c0781100c50550f40f540031541d2855808031414112124151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 171144415 1250 171143165 171143179
    0xe0d090e280f0504020a06050319200d020c01150f03060e011103070f092c060103240315060308070807140a0f05011508070603110c07060309051c0e0f 66
    0xe98200d10710321401c44035842d5110000b580c0c4c68584103111948020f50404800c1c000248200b201c0340f24a5072131540c0034500303460702003103140800a80b1401104642c80000904402140680d2100016805020080792182c000e02086008000308041c400c0706008444203a41d2040060011506c0e580007403c2401c0901d0000440d510840b40b03500c5180c2080d07c0c203000103250070442c1c10310f00e40d000c5116400361494602c482076212148070460303030940500c0f102c0801104940001503583e03000381c0c0960113001c1240c015540e8006420000c0031041001e0004458510041d04100c110022a02c600025240e101c01d84a14090b000d4880c0c610582080ca0111010504525810280f0400340000c0a440344213900000c1c0c19001c030f217005820764410304003201c0a521094810806200c0c005140801c9403810300300010312420b00c0c18810b45520509a20304a144a80c801c0000c010b039050307000494050290055403204d0303241c2c2d0000051751075401c04680002d80c0c0702e00300104601d0061441d10300194000d00d1a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 171145665 1250 171144415 171144481
    0x5150a05060a1404091b050306101b0f06050a0614150318010212070f110d1404030512030406060b040614030a2a0801060c050613051f0e0d090e 63
    0x9a80c01d44d110341c00032089a9154140001a258019081000040c181c18250f0461030100085803114041c603105038100301d0805850b0b8010b8080030b807601e030096003100300104058104d040c40c0c009414207840e240c0895160034400030300510035142008000d10010024081c16811040e210030a40000d003503c1c0c0702000048003140200d800b440149841200d4204203440c41c40c10030741c042c100c60a0940e1200030300001070401e103d05070020903000360a003030301d06110403004088501440c070341c0241e030001070880c4112150b0012003250308010b1841944120410b11102340c43d103806001c2ca0041e0b202e10004941480c40050555400c1d5002d1644410055400208009856400305101da081c9021600002c1d50b48802c00ca010b90084425024040d5410100d050400c10b640c0c3c20340d01e1600a141071030302440c1c1c0710300c2c0341008003e11035910030800d0742c61034040001d82185c0e030800030400032055202c2440f0711201000c83c1c0b401000380404031509401aa64a43d07540107900541e10090702504c0d800c4000d44c510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 171146915 1250 171145665 171145697
    0x3070905061504090b03010f0b090630010b090129070201020a060501030305070201031b0903111903051e150705090d080a03020405090603010504050604031b020307031505150a05060a 80
    0x7503c01060300c3c40002c034185c0c0c80701c020b05003141d080070030b8199441d09000d002022500e41c1301c406070304040c082e111180c5054401ca03909142c02c0040c03100111100c50b001c0340980140f1b05401144072403e04130380c40744003642e0b0f4451480e2000f034642e04840d4004640465505103200b000e018181080c01801612010f0f851566100200c1750241c004a02007038011482409550313151040d00040c081000c03559a4a42c0c440001412240c038a201c01003080300036031481d00043d110b0002c505420481010500e440d15107900c0c0180e00c8520368030810800700c800347c0410070f4000700000c0600e6076029003004a07140c0d0316000c200729003c2d44200805038000b007007040d0310320000300000300404049050b980c2c0140c035035003002c0411035541c1d400f60246110780c0c10700c400e010214001142144e00240e15042403c20300010003000402040041806945405186400424081c007070505d43d242c403246500c200065940d0102c2d10340c0c0c0c00381085a20307400401c4080140810305003c0021300c1003000900386030744c0b1141901c413 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 171148165 1250 171146915 171146917
    0x3030c0f0b0a02180102010605060d0f020c0d020a0b130b0f060d0b01060e01020c060421050703050d030515010809070e0c0f04030f02010809030f091e0619020c0609030709050615 78
    0x2440141482c0c3c00a024a0104a81002504d001c2c0c0c0900c024450146041b0014100d8042c02c050800070b1036486480e0342103070600d03a04172460a101030003952072180b01024040e4550300082c0f0250f90381c3c192000002e02990800d80540d062540c040c81140b0503403a400310001d003219004258503001858140180f0100d254494054001c080a690300311111480300d00090405040d00d5542e40100400e0005120b0302c514200000c5061a8aa00d042448a41070401034541070582c1d0024013280941341d00001d2650303158002d5449407031000c00108404103081d0046410f1101242c0626040c1c1055400344900030346611070035000f42d0f00c03503120382c204180c50500740340c42c0e031160b4011190f201414003140c0031542c21120243c1e00c84962006503081603005040c50358075200300e02105104d03203081e0349484d0008001c07ca200c200c819000e0700d2940c0f0342c80d403007a840c130200c1040e485a1025109440b0510014a014011919000d0014024003400b81c5407c060002171b1070090000e41c0d1000c041d100c1d003464041404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 171149415 1250 171148165 171148171
    0x80c1c0510090c020309040b010302040f0803032505031602011d0f0d02030301050109090c0c06110304140d050906031b030c040603050c0412030c11150913020702090103030c0f0b 78
    0x11400166a04007800e01c40c820341c200e940200ca469080880754a4169008400d40d04002c2040d10045684a0b92400490007480b42d0382114540308000d440c0031030384281c004059482202031200311025030074010b0040c611071481d43c60000000f04200300290b40c0c0e9440a42d81080c1162030300010582c07a5a40301b51030501a0082c400303401da9030100403110745907881048507050100c547e00140d80b40d541808002080024107000300d50300c298948206070b1600e445405201c0e00150090420007c000e44000301c0c1c85540d00035103041d6064003444815001e132102c049101038000060f03469032840c0c85402c0d800c2c05487d4000400e0017007040020046503440e85036100007503101d440e111050964030790070000b02404445010f03054158540f0180028450241a0b200645026405040001014020b40303080c1144e00004143c0b940c0100d5031a00035082c044042d00600800350080b24010300305525945880100d004410019601c8070f070f00d80040012034040d44417000d109000c0d000030320301c00003a0340310409140c10603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 171150665 1250 171149415 171149467
    0x50402030c070b0606070209070c08070c060e030f0606061e04232707080c0c12180405040b28090f02041b020d050c0f070311101103030106080c 63
    0xb50b441c01c10042c411002d03805101112524248102c580100d001c5e52801854070085c404083c0e003150902c032a50040d50390169001a14111a81e00c0d803000400c00d00d0b401030300501a00c184034001c141c101c80860034510a040240510b41808a940170744880244031052818041c2e03000c000100e01c02e0307071030404081b010741100b20441005c03800e8010f002100080801141d4000b401ca00440e040d21102000c0a820600500e0800c0480e01c0e0013805c0009441101c048080c05d00c240074207915204401c130003a05809980d41801716103e8640303014081038920841c0c000b000d948101d40018180c500c0081351545801130040c40041107500c011001c400c448645a05513400341800281208514003402036901503140700e4008a451102c040000c1d589010105840b400d101010544100641d000c2020604104002d800c8404003a502d042110700380840c40801401184a0803071940071a01885007421f0400d80c28000314510380c6070500c110b645283c0505115a00c0508101c1c3c600440308000c2174520000c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 171151915 1250 171150665 171150667
    0xa0213080304030c05100f2f070f06050a0504170c0603040308060f01050910031a0307170c06090d03031505130518060c070b100905010e0106022b0507020a050402030c 73
    0x15800c04c00101d4030a40d015074400d410b48203503064600e03801907080d2007640321420001004d20f50840e421140c0350501c0100c4a80f08468040100c010358005840c0c0c040701c40c84080305216a03200e810407107a45c417884038880701103942040708000d204540c40a52001d400ea1000b591464503030040061403590040d1025000941501c080c01401d160420404070300c5a400d00701580f4090080d00400e041444026400045c1075031040c8080680409001519540d1002816288400d13140c01418449000200f10000207104e10000725086003854002c075054090000c0c504039035001c01d40d400314040c0144150029903902079160005003a207d140720800e12602294002c1242d1909110890600c80003220281d60365000200384481c2c0c2040d18100d810079a00264401d00c5503481070241a04401c1640c440032070340b46003a00016410806000c00c5050700d003076500703403540c03204011088086404452458444000e0301c403011070341d90b4007650003895050702c0980032050b10355407800094101d0308221142502184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 171153165 1250 171151915 171151919
    0xf060702100606080c0715050703021804060b19020111190210060b1b0a081614030a0512060409020d030201020414010305091216082106180601080a0213080304 70
    0x140500000c000c5500c40402004410f02d03040c0002c0001c1000740000d100554006454018031055540714614040002070030321903400d1400c0c00038000e5002e050b01c100b03281c101d2b1480da402d6141c5130107580f0885255102890804115071000c0b10031491452800c000d666031161010701038660400682400c00c1600011084c20603d04406802c1842620b03189041c00d15001003400550300035404e079800014080ca469a1648500549a18082c03140401070714000340452050596112100700d01c00c101c5c818860328500d04594034000d590303401303441090070200b00c01b03021405800c3c2c0042420340d8840030042c00454400b0081d008502c52040001c8248c00603500044c052215130020030a00340e074a0300030b01e42001071b0700d03081e03410545030100d00d90340c0c25080714005003009142983c0180d441ca40c2d50003920a03075454400702e001d540e40c40c0c0303014901e01c03800310068006241e52912031903250641c0c0c50a40680b1140e03a41c0f500466084100900c210100340c2e0030b0020311341c00340101c80d1141c06001c50200442d41d4034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 171154415 1250 171153165 171153167
    0x714010305010602010c0c1b05040f061502030403050a2d0c080105090703030504030b100b1314120a0611040f030c18091a041707030c060e030a230c0f0607 68
    0x501c1604507806580c10040301c21902584043c462410a80101d85044051490707404010032100b6648280d50060502d00d01c4411580e040c0e05c00001c440300441c2c40340c0352010b81c43c01039850b40110720001e00a034010b491004049000c014041c0d1a4140c0c0c1c0301c031501d01116150703440040200ca003400f91062540c041062000400c24805e16420080c0080188145441c560b0006c0c140e219501004100c08a02e03000b042502148010482c0501004010240c940715144030001d0101c01c2881148a0050404030599550400d18440310b52002801c0c06400042d03103035140c9201500950450049a90703081000103030000b00c0c040203102451085882440302e51901c0045000444072442100c0301c2c4e482c00c031603000061000c8176820307101c600c0c92a241e100d554442c14501c0541085030041c12001c10002451420107903c01c0510004a00c240e030704010036071000c6c00d09070782ca009074050000424525182c09900049500f403444203400d480c200c0b5450003840c1c404590400c0070070b000d0b03136001d80c2c40901400005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 171155665 1250 171154415 171154421
    0x3070308060a21150513060b040507051b070e090d0315050108010614190504030b0f04050c0f040207060911101707081e040b1902030606030408090d0507140103 70
    0x4801c0c02c031400005203007001400341910110700b0420048603100d40c109000c000720245007510ba164004010026440e00d03488460b400e4031426400c07210341c1c2c0303095105040303840c1c2449213a029811954405062558240f50364049105841c2464041c0c07060b07210002e03000510b5402517214602601c0507145460b4141c1c005000e0b40c14403118415100710a0f0410b0160340d83c0070205504487d02d624010a0341416400300c42c0862060703068075450f00309900c00c0040c03041d81041c01081220300c502c401c03a119590f035169034240414150303001440d582060302d110640c2c0c0741541000d59504c03c001d000524203442c668034601140c3c1e05c01d408480000306514001080d2800c01d50a204d04402d41c1442284000c600d04d0700c00984200821080511420748042100b001555100d04510318584510000500341400d00306015002200c0040d03003200a0000b180c02c03c00d0f54002d0700d005010142189007140c035035958007d40d82e00031901e8141c2018010b10b0741004a0410400300c002090001c600e56405800342d0001400d1b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 171156915 1250 171155665 171155671
    0xc090219020a020d12090308030703150e13170405060c01060e070c0f06051803070605060a17030921030714010507030501360c0203030118060b310803070308 69
    0x1550051a103010244e1034104001040c00d42c49861040b41466003a801d6032609640c3e000505045c0020007001045a010b9221101441d6602280030b9065640c07440606500012503400300440e41ca403007210005000040040c0041d031a0340100350802e40c8640204115400050f10591300f40c0d1100c40401451641c03503115604541c0074a800325850760b164a0b407100301c000e80320000380015a81c000040107800820703c00c070340980801c0203803951240789040030303809424103540040c401c10722024002610454021040040e503905801b950910f84000100800c0900c1381d4240000e00301071420802100c20144010944580b2841070171041c80300c0098a542101c0c1c00404220603d8a403400511001c180001036925038965a544003001200344000e511800210350b414019090030309886160032034002c8041c505035000403280000c02c00000e041c2e074090b00c806210f4158408010000207030700d41c100719022490201180307000b0003041c0c1d4000004912200130b50107082a40c1001c80c1c00010554813590407a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 171158165 1250 171156915 171156917
    0x120c0e060303070c030b040203011e05100b1903050907050301020a02060a11270f0907030b090906070e01080c0403021909050a0509030906070c030618140d0e1c0c090219 74
    0x3c1440c1180c1e440804080c424000a0072600c001d2001a0440d6003d40000030100041d04120070390110100c5c5d004043c0009861030000302c01c82c0800407d40780d9054082c1c4141880e0401c28003961841242e09078020a4054940706032402191400701c1d4a8509000a256144281d4010f144030700d0101d102204441110244e080c0c107903001c000c8000c281121904003400307500c80c0f046a2002e110030308002200e0300d0306802c400b9080002c032002c104880c3c2e0180c0c8000d00b050300548800486a031031114107a15000b0171140080031801640104540c3c0d446803400c4d9038020f407040016850300d6101c0e0001090185030b800c0a0005001d0380d41c00740100d010798082d940d0000c00c2c06c8014041400e000e110705807a03001d06001d0030300030b03e404a981018480072043c0b49008540110341040f0140304600c40c4514030881d020309a80d07408001715030408002c0b00044030320080100355108444414200100100f00030001c0e01d032006400e69405100c04205074801d0100204000e800042e50382e2890040c000240d11105100c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 171159415 1250 171158165 171158167
    0x303081008030a090b030901020d090c050103110909070e011404032f01021c0504030b0a051605130302010f0c0b091c09030203121b060112020f090118050a0204120c0e060303 76
    0x90180d6002a2072a003545c00410b451078482c3c1e1840e007001c2c02030091075110f000e100d041501e0382007070201ca03400d00d40c169902031740c00b07101e0720740d082150400510401c0d81d165003084c1030400150056100c1c440c20741c0118130500d04a110711805550000b420740268105486852032100c0c901c03000030b130012002007000f0340c0c000c0e244140e448540001c1d48a500e0a0010500e400800c5e50540705184240708403805568866140442400c00503940b1b002800c08466102008030b5520b4074180c40d0340210b05803815a107150380c100c101c5a0465004540e020302c40341c04402070151104006000401d4070386080c0c800c3d10f00b94000e00b8400b90401e010404504140c80303200910140302020310145c0c4003c500ea4001485200642c2d565030a204441601311040f07850104c0d142c094040045103040610390a50395060007141c011560b10301400801200d44028070546000c141d00e009010315050003500a0340d8004200607006042950395140d46e14814141c040403560380c030036460140321300142c9040c0c098000d00150f0041d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 171160665 1250 171159415 171159427
    0xb0603211c18030203090a050109050607030f03021b1605040606050901030e030903070e0406060905160c031707050c07090506101206050a1215090b0c07170301030308100803 76
    0x1444140c8905001c1c2601c0e8584101001500030003500607902e241003040c01c00710151440d0074025125084100481d20400d416400024258803c82080042e0360005100b10710b00905076070103958040c0300190420a0640a1204016004500018000e00d00104006d054003014240c4000e0343c03007039140c20081c4540e141c44002d120860f4400240c81c09a4800c2c28001001c141c440c00030707440c41c01940711040d03052203581d4001c2410320244c0202d0340254070440042c031440741c0307400300a41613401c102d4508680761058602410b1003441164904070b402e00030709004441c040b100c0f0300c90708220000c8640c04003040000a00762040002000000014030423008204094242400085e0309000c038003511a08102c05460701070000d0f4440d610510080c04001c2100d4041591095118032200215500b035841c075485d1552303050151401d000e05011141d000b1600a1183d4a00e4400316040d000064140d84d0703048144080b1000310b814070015800795000f034980d0486480c0c6000000380d010f80e15080012103800510070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 171161915 1250 171160665 171160723
    0x201050708090303072006090d081605090d0303020c07090608100e0714060f0301090b18060901030201050d0209040e0a060b0a0b040b031510110c0d08090405040305160b0603 76
    0x980340c01810915008070180f0045ca100c0090b46e04100d0030380b100d401810b080c00041900002d0103000c800d2a5111441140d0b5882c0c8143e1195419096841c040744081103159814542030300800300740ea00ca410010300b0450a51141490300c03450350441c41c0441c0c0d96002c02c1c40441c408200f03040e9a43d09520091000403e008080d41d00c401f1140b0400302811100744040030640d41b66025038803001d0035207203000c0d165a5280d545a01030702d407030000720f0f01a91300c01c440c071404004a500c100b4032811005e003105400340d00c1c40d40115215489050402c00840d42071010000030781c1c85025001c02d54600000902c5d00314403a040c070301c04541613071103442d104030101d080801141e540c01c400d90b002c9540c0c0002142d01c941d219040307890303c05185003145906c0080300303460310003658020000c03c032aa0f034600c08032894440c1d01c0342849840000300c1001340401c0c809018030035071031400b6088954018030074075081d8148404147d61440307c043c0d001040310014421010461103041c100404054000c110700380f1000c02d550489 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 171163165 1250 171161915 171161917
    0x60c130317070203030309010510061103091302040807030804090b0f0306070c060b0409050a03080a05150d140610180c050d052505041404090507120f0f0609020102010507080903 78
    0x11006116624440035203410346550815906183d8000d003e40e0b40e0783c43c1c20300805009000c01c58500d11111003050000c24024442c0c20790102500045c001989040845400c200c4582c03a0710711540c2c1d04580030440803030031020038025200103502c141010b45c1c80d5414500c51074291090482040d0069901d04c4110100f540c0001d04107420588500b0009420700150910501600c1603003d00c50f0013074140300192003000b82c00a0319045540c002d903610125512180e030200c0a5030300965540c44101c41c0b05002541030324100d407540014500c01c5880c440c01100641c0d90340d080a00445519211181c100402c00500b0b0b40b206a900607034440081c200804903400c2d9011380203024401c0090141a55080042e1600c400741c07006801403029410704100070b48a40d04003c005034040d020b10556680b441014003014141402280e800c0782d400000340140c1030501300d4003601c41514440503110101540d10740d00200e01c150041c440094005c40340880d5504c59400007909403500980400200060007040010540d0044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 171164415 1250 171163165 171163169
    0x50309010c1b03030503011701060302030718061a040312090308040603050c0705010501090516031e0905100c0507111c080d0222051c0c030305030613020c0f060c13 72
    0x4240801d804009080c140c00e000d140035201e07181040c040102000707058111000e50f048a0820804502c2c259041031034600780c8410303220083d0560f01614080c09102189400075480c0c0c603006000181c1c1641d141d001ca00400d680f4901d1003190300700050240103000740b5510721182c14545041c0341c5660752039552070003414420b5104110030140c0e01c001151500885030120703208250810000e1107156118011000100401d891701d1051101a455000000d0701074010101031849030342c0e144040601a140c3d21010b01001c040c2158a80901645e1120180c01e80c82507001902076540e460f42c0f14001c0303245c1404484803c80303e0901c62020440042c40da80b030055203602c40359900ca19a141c840d407400c1840300180c0201c042c0c1d46010302c8800380503240303900700500f220201c0d44210350f135142c2c48107041e107005584450941d001d8080380d007241c000d00c00b080c051401160415000f43c0294081c001c42801502240c10882d002c2c2059000030051442000301003041d250090b444194480c5800e00d5040c0c0241441298 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 171165665 1250 171164415 171164417
    0x7020c0901030503090f0406080f0d030509160b07030905090403020f0d1b0201030c090810020d0b0a030218061807020303040605060604140111190507060219030e041806020406050408010f0905030901 87
    0x4031b80b41d25031a4446410250040c0241400c8a03003c3d0011400b01e83c5490100e0750300c000192400002484074180010344251102e00020a0402c00742040c0042c40c4a85c000d0b50242c05200c4c401a000415072160720a40d4072441c0030790301030310540c201e0b00c1d80e603428251245509410010709282c0c82407180d121665042c0d10702d44c2401c0008103c002c141040c1e54101d00e0342c0c0040384034003400c16800d5540990742c000b4400d07083c9440041016100310010040544580d0101a411840c0048410b46803501d040502da00000018220354000b40181c440d0042c0001c00c903074900040e040031040c84200000d9010706074001c0703002c503040f41c00c0905100c0032424680b0b034011020304005400c810315840c41c40a01c4562000740085070400134003401400c21030360f101440d01c02d003001480b40034440d40c0070010340740644c00c409501d9a01c040360845003c2c204805030003c041c402c5800d59004034100000758440c070041c802071000d5218951150b01c2c200b9800e086410001032100480e04111403c1c0008502000b00ca40084003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 171166915 1250 171165665 171165679
    0x403091e08070b09041103010605220306050a0f0b01030606020c1011032802060708190b0d060b100c05120a020a1502071709030d030e0309030a0b07020c090103050309 73
    0x1044000c03802034540c69101d41d00074020048041024240d000041102d500184c605108640079000441e10621003403244c00d0000e202071100d8440344800c0300b901c40b01d00c42c00c80341c043e089507240c1d140c0208030b44055802d19040340e0707610944e41c00851180200c8040e1380303007400e00704207035403810001940700c8514070341c55403251000d0150008541d0042209022080c003200c1165151094800e108201c46080c19410610764030500b800c0140c0b074400919184030310f05036540c0c19504d031110500f5080d141182e504455032152100c170320068503140d850114110b80e0142c3d501142d061405001d01403030114000e421030402107114140004282c0000340c00c2402007520462070758500c5c2a0f042282002c0110000400740b0340300d10000340d000c0e210f40d0040c0c96404e024942009141651424510f014030888030303a240c050b001f6002c134421079800f07540040c105410718415a8a003408410009041110905040300c10a01581c1800282581004501800d0b00f083c4e03924852541543c894650b00e0142480e018403401c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 171168165 1250 171166915 171166949
    0x90302040c1b0c030525060e0a050301182d021e090c1c02040303020a030e061b01060305060105030a0515060d020d11040c091503020310030b04030206010e0f040309 72
    0x1220b58424501d0014445103486000d100d898070300c0c0203020900c01501d551140c07440d00d41550303a04845a81c01c0304800405441210324200042c0c13540518240510350052003603100040c01d031000e020300240540710747c40d2216a07401c245041c0c80c0011400015120304c603a20461124845803400d03041c00320f0340d01116104842c1032990079114244280b440c000d500043c054090005e29a0383c0806403404080740c04181c01c0d55848400210201c2c003c0c0d100c090016406520240d000ca40511105221014050291841c00121f091a0400c880030000010700c0c1c0c3e90b44440400070301a0030f0000d21702405084001d080d4800031511104c1d52207010b05000070700c1000301c0d40030810603a81e014111401d0369018000c0c08209801c3d05248910000c40c038050360146040200728074440384155490f006440c0c444598201d05004150701310006d4200601d401d49035020001c010003c10342628010744514030943c014820b130f40c1026688000804060507145044040302d061000290b040340300402614188094018101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 171169415 1250 171168165 171168167
    0x130c320406080a03050309012a08070e0a0f050a05040209090f0903090d06140603121b01020720100c08040506180904050d0f021b0d03050c010f090204060b030403090302040c 76
    0x100c40c65000303074224443c0c40540001c254020003d1071203417480348005c02400c1c42c2c404a980d1213100d0385084048108480008000290150080c1500442d452418109025103203000c0313005e401e00d68225076540c42d40301c2020800c900e002e606000241c0b809440541c105000c00021a4402c08040d120a84844641000075a0b002c01002550103648008006107003044e21402e15034010300c408551650071040c824000b8005080015015101c04110aa224a07050030000703040a0180700d0344d603603680380d5000c00c244c2022070050401c0303108010f198441200b060181e5420004616120025a010301c6200540c000100f800002a5012642c0584d556991000c3c0da18508600c0140103c1d07050740020742c0400d1100b070000018500c410841c1540300d1003800682c02750140e80d905400007070444228540210740c20a803c00c060754560031446800c0460138244141500d071309503010102030384002c668600d0b032501540b5103801030000520222b00d0311440c40c281074800600c4003071135000281c002c50b12248600c0d621 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 171170665 1250 171169415 171169421
    0xf0d02090117070503010905070804020306040201050a360f0305070315020f0d151d060409080c0312190e0604060c05090310020304170a08070c021305130c3204 70
    0x16542e0038003090515018078090b080f500280102d9032214038100c0001c2d072150044001c0c60045030020001c100540d910ba00440d510350003982880108511707040d06040c00007110465104018402c4040350300244001440038007540720760320174682e420344c51a040020030404503008098039041050050961410400c030380291048016680781d00600107924007400c1540d40c412000d001c00701c2031358042d6030b95446040c0ca10320303104560079a1604644c0b01084c4070b89046e6214403841d0b84a05190382c200400e002205045810102e805505c407000d040070040c0d811107000088102411174501045000c0d088004c1c41d80d01c400040004100700e66600381c1015050052059480e2103c00904a07603001803001d40ea60065001600c04a8021042ca0424086681554180c9400456030798079962695601c89040b24454500f00c010703078000d1000c6400c0f003505140c0d40906481400c03859030142070480c0f5031500f010380103003e901c0f4586146130f461420b004088401244070b0021404000028101e0f00d6000003002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 171171915 1250 171170665 171170687
    0xe01090507021e030c07050a05010e0909071d090606010203040308040b03270309090a0506151602060a08010305060901090302060c090102030c01050703054f0c060203030910020f0d020901 82
    0x10f56800e040d281a0314000000051800704000419115001d0f60f400900203101c1a07402060302041d020303980c0504600700011283da0215441c3c0440700040d6841d082440c034020f440c40403114050400c000c22003007140c2040f40c0d540080080c4000c620b000c1c550b8036001290300481c0203000a008000000c00d0000400d150000740041c041d030000c05403111020070142da2a800009164024803403000081c5601d4110300c04c140c41054094401010a0340304401900d281e480030070320740c481c000b1110044002d6151038001c0d003029445915440303465415414070070325000000f445507129a050a114100007a804221b20385c014406d925001d444040c3d110060341503014483c0714818961030b243c1003005490b0b00d600b0050281d00d803030000b0f01d141c9074034a03480c040c0e00340100b40199852042c0840d078071500031350b101c0031102101171009480708607195580f400c0744a4250b51110005038400300520400140611044040c0b00310020118904610152388407042c0c0a8181c076030b11100d9020619994590140140e010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 171173165 1250 171171915 171171943
    0x70e0d060c020c180108010b04110901030b0d0605090303040308010504180318030b04380c0702040204030b13140109050a12030905030406091a0301321314100e0109050702 75
    0x400e070b10044c0c0f580c0351149007486005d101c0d6007046c1941c0c1036400c3c2841341c43d84003410140d0642c60100c030b00e80150301808805102c1c0b504083c1510b04140411000c0c45064040c1d480304000d0b6a03282007a00f001401420185c0089100b2407414028108240c0c00b4407800d0011039060901c80e8100354214443c6095580341d41c00923000340102c20421040145461225010303031003590309c4804951002c0700c000c04003401071030146120a003034000308071040e41c880043d000003840100054a050385a0395044018602613031449c948030703004200581001a01c0e41c080c50302059020080060a00c540c0701c0c3c40d56010414005010014030054800c001c82c8a60030849900d03800c04103c0f42c1d1107a072507a0060031071204c2c0c4a8050340c106541001890355100d6021030b81203950701442c0480f8000d0451031804556038101644a060754108042442603da01c0d2004000d99008140010701a050502c0145050760041c10001c08100c140002e1200096850440d03041d500d880b8000255581c3d01042a840d00030f001c05440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 171174415 1250 171173165 171173179
    0xc0f05030417160b090603041e02060a02210306030a030e03010b060307180b030403090902210901060504110415120e01110309010f0c0f03090206130308070b070e0d060c020c 76
    0x11880001c21031aa00d056060030000107603900c910b1500b0380076404600e030b1b00c40c00030000306010a0700107102800040c1d080c1c00e003074100c007181d034000b80480c1d2004050402603040302c403042c49048200c0d18055004161800001d00e14504200002d48540e07080300f0003803d02910780c1d0b4102c0396440c25480005a40009414141d803801c1000000c1c0010041001d80b02241034080e802141400807103050702d001d1603158075442d40141c1040810000fa42050008000140300c07114460105e0210340005400f1f0041240001803d505203c18441a1042c4003ca050811810082008000310003089070444401e82d00d840c840c02e6903010044005048100ca01d05034540c01c0c0b0f4400c80001d44540b0055000c5c020840c000c0010031401c440b001d00742e5110942c1e031b501050072940440c034014025003020405600c0100001c0c0340505180d2a900f0410460f003007516492404030700790081000b0754131700c030b41c00c4603180c1002030001084000081100000c64070041045807284603c1000e00d000700600c5002010040900c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 171175665 1250 171174415 171174449
    0x5031e01020d06140a0611071202010c0203060f09010b03072d1701050114040c020607050903070e01090903110a0803010302011b0803071107090b060405190b070c060215070c0f050304 80
    0xa000c3d200300702c4c0080d071080c002010f0000f08070f40a4198040f000500c00c000d002c1c4245480032000903c200c61106070b060017403420030900103941c14032501340b144002102c2c035280303400c000311043d007101e008a40842c06507000843c00e200140d2031101d1000b4003542d0341c244c40e24007424a480704000700216484450313141310448181c3c40d246410742015050711071200180b00442a0300017044203481d85440d541e009030300500003081e8040d02c90b800400b40424003600702e0304840d50303c4002030355140c0c0076884031000a070741c1c0100c50704065100c40c41d0000c0c50751100003040300c4d190b0754640304070300d10041c400241440340b184103003403a40c800e150355014035540140420340c59113890400501040c100c80300140180c05001d5001c40c0c4400c00d0702c52200d00f0100a0110390500717080a00342321044010100c0c030314640b420501c0006d401c44550300200b140c80d1040d05031210356450620060b01d45409400a2222006000c01300302500750310100002c0c01507041140f000b0840c80d035043c01d40c214451900301c400740401510103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 171176915 1250 171175665 171175679
    0x102190503070b0c0708180f031005150301060f060c0501061a1804020418050402040207021002070e070822030c020a060309020a0e040203030306060a031b030e100605031e01020d06 79
    0x28000b07440c081c00d0510382641d1002c0034840c90748a4140c00130810f41c0d081c0300b0030310700d101c000840d154203007030140041d02803801590010340740089104510700e003291a9410007141b0708401070018080b000503002405502d0a000d0b00c407062403610b0003031104010401d2000000e001007500410002e000c10030a40389880c600e1011008264805514503900130341c0f59014000c40c2c1024822201292815034003840f0004c1503d07080b60141401a100fa42d001d0b07000e119500242c0c0e04c0b400c01518400b416001071110618040e52543c0d110801095042030003281020800c0d4003200ac13048030b0040301d40410340c0080645919059035071100500780079410030000c45010400300d41503445000600e00845c1c0c50803905030307a6002c0d100035078000c980080d01604144040399407400c006001e0461001681000309401010701640300708031400d5001ca00000c4d131565030440000509100f4210300c408415400e000380c6082c6404aa96404150329804540314292005156030b202903056808095450030107101d40d56440c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 171178165 1250 171176915 171176917
    0xb070b06030c0a03120c06110406030605030d050403030f0507080705070905060112060f0302220c02011d0109020312130906090e0d02030711060d060e041401110a0503150102190503 79
    0x2030054003911038085500e9892070055a01ca080ba0313481440e070301820f14019000c440218001d030044410f50b4403854031020354034071500030b0800340601d55400915140b0300020503150100060080f014040100020700c08607034007a400054200365400d05a654145910303290b41c940c8100140a00a4041d000b004186544980c01160240b03900b60307240c9140d01100025002103a034144998100c50102440400050400f410549c0d09001d140b50580600061280040300361503c2a89100041c0d6503440051481c8480e003460001440c0000003c00900000d540425542c603802c020411141902140060250442c8492a00a803003c01414003906039a1520305019010000c540c0c0707401d014400e403130001c66100000ba00c1a003900491000810500c45061282a5005040581172191140d2002c21403240c2c0c451014011031280c10501c03500b032040318119007160061800180280001c0005000040e880010350b50030160000e2851580d41400005070315040c900c0300c0c0489142440210750050180c088 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 171179415 1250 171178165 171178171
    0x2030a0603020901050a0f1505090901031203140721020c0a0b0103140c01120e030f1c0c03050c07020f030f0d050a0e0d17070204091b081b01020715090b070b 69
    0x80c8540c03043e641c961701044195501170045048210300744500300b02c542442200018800914100940b41c8103a03240442c400ca01300340c20a441c0c88030741e0b812081c03520361b240c403a41d5a0943c3c444600741141c244204010880001c14424510100381141c4490004810340d04603451400e0348421294128200d1809001842c0c0911090702c0c0039000d5174040c0c9107904040741c1495515016940c0d0044411286040c9006021003a01072010b440203000b070462140d0f82c0030041442000001800c0602c042d0050aa0152031400032588101800e140034010340009080981e08800e60485030f1503119aa000301203480c4c800c074803800060380c4c2301c0c1d01d01c51a0b0340f9820600418858a4070750703a01c080c0c804400706000d10000740000003450f4a0012940e48101442e1002a280e00f500c01007000c81c1d0300140303072190400700195040c104504000c9980c104440e1104125030001045007866940081c5130400000c0c1d11080c0604c12541d00c945450030134241d0f9031040c0080030290001c48560380c0c5070032050410301440c2b6030071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171180665 1250 171179415 171179419
    0x30c070315021608070606180204090f0902091504020c010c1e020601050307152c180606120c04080102030c041403151911190201060e0c0403020105070305090402030a060302 76
    0x45400114001c401e07000b01d03140040c003003100c5101d00a1542e2428070550109005a0304c0a986001c08101c00340410710a0414101004025840e103003003600440495081030703581016145001800401621054440c40c1c0c030040d01d5802000760b801c4000806d02904c202419031603154600390707450000c2a0420440e000b09061600500b110100204090740d46160038000c440c0d2541c01004100300004502c0c04000c1c102c840c40c50100c02501054184030700d400808070300b80203a0b00590014115a040c800c922402c5103086071000c010030305081020a0300c41c401c00b11f03e4441d09102c00f0005044003c0ca0080301d00070f004841c021907691900c00c1c0c02000c190807d00601c00c00302a1080400c606190015401503141c004400041d01034030741c1614900ea00d02c160580240c4543c0b201c044a030310103100030151132042d40d4000b10558034400d20711b0003800c4030015000075214130540020702c64032002c210107440c150f990a007170182d0760380d00e2800e0039100d80c0224010184d0080c000810041030442581202040701e1007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171181915 1250 171180665 171180683
    0x9122d040603110a0207030602032214210304060207020a050a0b0d050f0702030d0f0b0d030305100906030f030f091a0c0105010503030a120515040c0809070501031104050120030c0703 80
    0xc1c3c03030100070074480d80341d180e03005034041c003c28000b15903684c0c0211b411405c5030703004005560240c5e0031100d640c003000a003030b2000c40b68079140d500481018000e0100010703400b40012a500c100c483d0400940c08040d00150089070701049090442d01d401a503100a03000051020309400d66a045009a80c0e1140c8420360100341880c3c0841c050003801b4240340d025203041e8001d903003440554003450004114003200b02030071507104d0f090304040340ca076192084042d070300903500420315140c01600302c10100e202d5480b0301c07075607880d2990410100b101c10076801140796041c03801c0648007070200030845035800c0d25003080110062211448215010840050601d000f280000740328030b0f80d8403000c15490340918030095012803020345100502c2180c80c0e010301d078440d0714046449058000400030a00310b40c1c1c09500600030494031000d00c0180700c400c0120100902c02440c01340b040800700760b648980c600551003103c1c140003c1c2040c0024032502e4280391806400402c0403691688144290140d0307a4180d44801e64000f02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171183165 1250 171181915 171181931
    0x41212030203070806060309100203180c0f010c08030405010b030613120e150a11120307090f030f03050c19050c10030203091903210b010f050309122d040603 69
    0x80a07000b500e02c144400d860707000c1c49a580c40240a42684020f150742100d000d5991602c50502e0301d031000c0d6003e001042c1400c10105c2600212070716100b80c56040e503102d4840108061416a48540003000d844e80c40b00c000d0f0b480c0c2e22a0f252150150400c0c84416a040c01200308002c0b030a5a0020002082070013580c00441036100c81201303540c4440d1070000c1513009110321404009130304141004084e01001c03880c05140d0220860a02801d014040000030384442c800410300c41a42e9000090101400c07080402800030340c0b541e078820700d113203c40120040c00d01601040045440e41e050001291451103c241e00f50000d81529005440301181241a446400174000f8250224881d1003a00c0c0b04200c4c01e0011301500322070000500c9600d5070300d103013103003000903004c45c650340140f91540d13110781c080b00b01070080303030000c040310000d050021074010b5002044014010080c40388000601c2c0c5400d8190302424031340c2d65481520b1003542c0e5040c1c012808420306030040c8400e4510220004108881940d6000c2111034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171184415 1250 171183165 171183167
    0x30c060f0b0a061b0804120606080f0606010c0c1e090e01020c070506090a0308040810050a0905210405040c0e040b060c072705150f0102160b1b03041212 67
    0x240e0601d078459001481a0824070009004101c141560b41c1c4101c044018004030b50740c0ea05503603225811a00d441c0d0701d040b20b80c00800c0000d00800b8007416007a00501402008800669a1480c005004078100800b19009200303105601101d60007814500b007001125528154014201c01464400d018189150010004807040f0602c00e0b00d650b0704498019000b0146010100000d42d0003894071154401c02d0041e000000810440041c00141131550241c001012099207900440b10010640b8205504000b03100d8000b59012812030400200b04c2c0075840003203107280381080280034a03008240c10900e03112800c644660080c0e03070b05d41410022202070007080403a03030038052075010307844051545910100051104d00503c11402e09040c1025031450a0b880c1004c5c040015280700b51031042ea51010640a2045428000c4903510040020300007071140d003071081011207000215102d00100e20202180d03d07440001c0c0c661442c4a40705024080360744640d102c6011010199007200f04450007551102400065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171185665 1250 171184415 171184421
    0x90506181003080c12040f030309090b010e0402030a0603060e010905160303080403080a18060506030c0f10050703030b040c08070f0807080601080a0902040905011a0a0f03020f06120103030c060f 85
    0x5101541e0000c5001c80c40c5680308109a08083c42c03c16041c01240c201c1c4004e0440d04005e80020310052942910140ca07604000c0c00505054110710030176424002c00b401c159030400301c5035850303c100b51401a41d84e5102030001008010f140c00080c94581071107003c1c5500001500302c20801c40c0940d080c4c803100f0750b0105100c9034401c080d00c401008903029800140120380140d440c142e21000b0040042006c54184c44c0842220001c1e10088074016074540a100040c1010003480054080035103056224441c8140015013481d00c40c0060810080000360300c2007010702c2600181610030b801391080c04a901032901c09425860200c80303d5000450001e0700342c468601c54800e060140d00300d030f2074070256525071400454025034002d084e60700745615480c20307200503110b502c039014100307014000002d80382e002c2c3d0100c00007003100403401078464503407138000b40f24101d0320103419002c6a5040718071007500c4803a900420240c1c013a140c56043d42c0c00d103c600010a00d034100256100c10b510a1000f001401c50700c1100c6c0d0b0071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171186915 1250 171185665 171185671
    0x1215080724050702030f0a0b010306060b0a0c11040609181208190510080d09140d0209010918080406020d080606190e0112020a3924050109050618 64
    0xc500c4100d41141058042e00003040e00c207001400703940661040107005803070300d070040c201107078981000300041043c0007591044e20003502c184182d0754a02840c3c3c01b0000c1240b04031407070140482c5541140c943c025600c0750300c00401000131601c103000b858041144840c8400c504903054402981c1e605038080010f03c201d134644c0c4200c0641040b10003007079800f030306200100802842900380140d14075000c00c001204211043d454481030303a54250090030b0080c2e5148090035440d00a004e06141c00003107005a0740c080000c2e05441f001000001c0d102013048520f1015030f120600506400d50002c1e011481c1907000c03d528070740149585941005031034410a105561244440c0e280b05e1840009010b52900d2240c01128143d0f40f051404507440006114410100d030701c840c62003008145041412580944d0a0f03500342003070744403401135580480b40e00da910200c000e191080100428414801d40203078101c510388011307604202150800556840d140c108008090544d0141c1c4140d20000051810408440510748 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171188165 1250 171186915 171186959
    0x30512060f0d080d060b0304060903090b030912130b190305011d1602011e0c09050a080c120a060f14060901061e0c05010c02071a030f01030f0312150807 67
    0x10600b021034441904a030040d02801c081103071694030010f803818810340a1070081340a02c138001071901d04c514010300a030099038401100038600b441004042880801d0240039451058201d40c0d0380c82040902180055082e004040d0703044002c150b00d442003240c45a0706a02241d070362800c0046980300c3d42d2454800070304008480c8140d080c01c0c000b9028405020b00000800800d00000c038a140350740440c404540e02c44401900481e9603440c41d1403250358050f114400500c000d8949145103802c04041c035845080003401d944c010307501d40c88500c440220400c841c3c83c40c11f030003402c104a00140f402c0b060003c0c21440045945030851940829802e24194005c14100c800c25200c602000003142c6010220030300703066401040c0980303d250000411800e024007200c0500c81e40c00360002ca070800f69418000c0b010400500801001441008440ca00414240c3c0c1501c0e00070b00344900000581ca0102c4003c42007040c602603d0f07081050001c030000742c0e000c142055a03000c0d42601c8909807200710b03004000c005a10203107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171189415 1250 171188165 171188179
    0x5090304090b011b05060a2003071b060e0615030f07050f1c051c231308030a0206011401031103130f0f11031009020303030609150a03030512060f 64
    0x4445107542c0d00544458030306040c001c80000ca81c0310314060540702488203480c02d800c5030701041a6407040380b04494102c0d4442c04a40ca80c40402c001002d060f00005042d03005102da80c1902c503900300e2003102d031340344402c1c1d00020038440081c260400585848060302d500d8140364000300108118540400e585000d145018011703c8003501d030070308100440020010444e0400e0220080418002129000000c0280554020039042140d07007021840c1110b0500003800708801100100884200b03002003000105040b43d910b521201070084c541c1d010300c081e9101c3c403100e100000300014066000300d41141240d1500c0c0b41d40c00500740203001074003543ca804191004a020400010b0400300d8045d21441e5004e0050300c03400d5031610250b50b034039080c060601041c0c54130500e0904080d20780ca01082010a05101c205050100c035030f1079404a81e480c04041e00e03640c0b04030703615000203601c108112a007000c032030002042c4e0040c407540e90070040c11907232201050304420800d2000060140c1444080c0081c01a0050511 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171190665 1250 171189415 171189419
    0xc030703030507090503030a09050a05040203010509010e09030f0309060f010e09070b0f07020d08040f050a05010c0213150b0a140c0a230d030209030c0d150b01090b0d020a090905090304 81
    0x201d000300340050003070342030000c0444080303041d0320104060f100c41c02c0d013a01d4181c1c2c8036081c0030820140a84c00c0d484a441a40100010703c041d07101e10701902c0c1118480d01e1341700344503202e8400a500398000c0301c1c035401d5824000b0007000358041c13001481c1400755440075400725403641c0b2450000801c5c0e202b10b4515140c1c1d403082d2420040030307042100405080303810b4804d01d030800e001c640c0000c40102c9078000603900701c0c0012505101c1c405030144d204004020807605240f007249070000103400224071038400307882001c6420210642403215044200c5001c901c1e0762600001c0e4071690004200c1c1c000c502041c0c002151058000c90290000c001c5600c0510b00900a1900d451103541e080c0c14280001001d40c40c1040c0c0c030b910019068400c03c25010280c199840150300c43c041e000506207803a07200b1074020b2040380a180d5000104d042140b480e080e10314002400b05140641070010707034064046610101c0090400154802042c1496000c0c207640e801e540e440911580e42d5018080688130143e500c440303190000c1000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171191915 1250 171190665 171190667
    0xa0b13022a0c2e02010507110106030b150f0a08030a0216030b0f1320040c020309010f12021b060f1605040605070c05030d090e07050a080f28060306110c030703 70
    0x4a520700c150520300e91480f0f032080300000d040e0380508074000580c0d180c1081c0700585070860900e060420b0303000001c0104e0741c0345889040c6007880160040b110303503c121658920507114400e071081802c0c4054007031050150365105140c0d80343d202c01100341c0140621100d41c2a19142a00308104594000720044c441d911050074202050b000640291110708034115001c00143d1149410110004000080c000070011441408151003a02c030080d811500700b0844011942c4e008496101801080d18000724140c012021a000901c94401864122400a12900e00001c00001c4103807040d0103a2000b0606500e800350070212100401d0030400c0403c000740b0090100c1e501c0340300507010f028003585803410b000340e0715008681054a200030303182c00075085030010310105001401d00350300000035250461512450071300042600b4800b400700b4406480e0080801d100d841810380000542001012858a1042250307940b0f0080441d880704803500d80c00d00c80c080e900317001c1c5801078032014008400039500d402d610b0340d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171193165 1250 171191915 171191929
    0xf15090f07031d0a05070501170703090305091e040e0c090f04020f0d0b070801080d0917011b0908150105060901121b0201020706050c0c0a0b0a0b13022a0c 68
    0x104020415543e0700282c180c2d00c0f2242c0b01d24210040400141442e5507042c1030041c100041c0303810a5052046c10880311040420114005030300400910300041d4900852030111400d119080d00b882d405401030400d091518502100c031840d491040b10100030301260940e0807074a83c1b01400021b58808075150005030f80d0001881582d40c018030040901244242140c00101600d070b000d1010f8912040b804100106260803d0703429016010360001040d1700d4000c030030700505000d000e026580000300c600755001c0c0325941c250405601003515002a092000703a00b44004e01071607940c81040c40350b1151103510f440c1843c0c1c045200e4142d4001a11580c0740c0011507005641ca6140381008420450ba510403005040c0c04100001d2080041a0b0001d0395905c0c2904000742516800303011802040b00c10489591071f500f00241040c1d565074400014030807035035039440d410001c041001ca016000506070783c0a89280d40c1c2a4004c10003021000d800c91210a141a21458500b0310300032880c0890380282c00a11007407901321 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171194415 1250 171193165 171193171
    0x5060d02011b1a0712230619090204090b010f080f0c160b070e2404031b080601060f0306080d090311240d0506030307051c051b060f15090f 61
    0x181c20102c41d070f0482480d444018110350b09030000701704260301e02e00041d1070b005111002d80000d050010294000b184050295800303000c95100b55001c0d001c0410b20740460040c03100520043c0c20031912143c0d19021031002e4000c031940280010059144445014055602140607070000130361140c0d213644004031000c4560044482c20101e1569a15200003c0c41c21505035102d444141c1d129264904640284103010702901e84280105040854085143e014041640c0413170307403ca684880248000600c51088949070782191146001d60800800c6440e040b40c2c801000d80201da80c1080f105035222146600c3c4c094a180810010f000c0031000c1020550902926411580040c5060205115001c148ac51004455113803004c501c80440d8070b1052012511a4541c0148140e025514122040e07032602d8903003083d00741c005442e50102842d40040f134031603400d640d4000b1081c01d4900c8104a0030b80c002d40e07036450450721070b13641204500c000b540038a45030704040002c0c90041e1420790551580e203408000c2243c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171195665 1250 171194415 171194423
    0x619030312051005100e010305011706040b130c0608041a090c0f0109050303040e010801110306010f030c09030c0308070c080d0f0804020301020915030106090504020306060403030339020105060d02011b 88
    0x101004144d0350b0303038059140c180c1100f40d00c42a6402035040c0c005419601b0580c0003100141052a4108213050003240f85544680d01295210300344d03450480301c2c008a0502c4d00080e00017403400c240401d00740d800407040360295014401c00c5100c04c00d110a10b4980c5082251000700790741201e00d800d00340782007841c0d80000c4060141401026640c03240c001c0380c0340d600300360310107c1c600c41c040b001000911001c0c400c0c00229102460f0661441c500000003a0074495034030f02c0101050f03034590007071040c0d41c40390303421001443d0b00441c944892a81d074100051181c01c864415200030749030703030f0000480c40300c002103a584519039515480d42c00c103e400c13010758541070000c00c16a09950200311041d0207545055082000125024816407030354100400140304c1c005a401441c01148100103000d01c50341e0790419201183e42c10319010460b80044c000d400d046403031201c090400c20035854201c005451403c0380c044400c541c030703600802541e515030302080700c1e4020925010b80800c084400316004107401c068294059402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171196915 1250 171195665 171195691
    0x1505090a111c0525090204030c06050304110d0605040201020f070609121a04051e07050d0b0910050408092803060e0f120a1b0b070813050102030a05061903031205 71
    0x400c0c0c0312181000680103032494000b4161300d40d08007940100da10798028103000c51085013490b081d41d9500c8003086c07040c0204014000301000040402030300300101e9201c00806000110480018a401c3e00a40b134141d0701203002d401030341c20407044c1d03a100241c0070080300c0141d52401a25482d0200c09140302c100440181c8002c00030301100291f8040040c40d20b0b0280d071140300181900c40404410b44503e0351402003200668003c90010495940c1e400c180140172034020b00002c502c1d48490094030300e0030541150703040c11541040d080109000348203010b096402c0c41078480101510035410315101d0190b4643d071030700542040c2103061011404603840704a40c0c0340b81c14103c40c90031156907601890319601d1f00790010483c8000030310414940c3c0c0861000031350324000c01c02040c03040030340d40d440a845000900c440c04104518000274241054409a15400d5411000844d9281040030850b005000c0488041e8010709920325942140c0c15504052001c80e9090755a42210f4002916654003506003d03080e1109464 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171198165 1250 171196915 171196969
    0x20d0204110c010e0303090105090f0703060b30010b010c0203100e2506031128021f060f06050307090603090809060406051c0e0304031506121505090a11 67
    0x34858203e41c0c420044c0103684a00d0100c81d05425210000c140011940001d88101680000044c109003031f242d025038003140030851103000c1410703119a10080c2e1600400e80c2046135200003680c84201044400744001c4c0b121011910041d90a000c040070001e415500507440303c5800021540800300d0f481115056800840340305100015050101171000625803078036408204558151140300c0c0c11640c0700d4070890820135040c5440b070359403002418905c000403090801021561080c0204c42e40511201801d40c0c0140030385025000524160042c0035144107041d5000c500c050040c0251f9206d0281a0741d088081424000c044010341b8403c40c0442d12400b0034040350304140d455402810213080c40d0307a14180c4450a03034004c214002c0d07040c1c0c242001d50b0314244a02c0724003c80807040b50181c1e40c015058210490220400f01c00800065011603182c100d00300080c41000744d0040c051042130f544030f105104035203c1c0b141d016110b0401400060190b0030491841140d8100040c107051014890303103007000f42207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171199415 1250 171198165 171198187
    0xa0803040303050c1506010c20030304060e03100204050d021e090c031e040530070507031a1504050405010e0d0206100f03150b0307030816140604020d020411 69
    0x20300160002c401052022448654107641000600200059144007103540d04121001a000302e001c4140607003051000302c0a012001c810300d5090040750009403c1300d642d6a903482d002050400304180c01482805800c030b42d800c40b880c4034001e85d0113480d0010200350b01e214140d8200642c03c07420301c41c0140e035244804110300480d52098049031040e10104071040e600e281c10113000b04492140007104805503c0042404085000028214155000c040e140c10b14225181101c219465034014a40102c0380000b444004211000c82c441003181c0c072414070084200070844031042c1042c0d0464030300000101000c4400110319107a04040d400c2401003000003203901d00800810704100c0c0c0c034900030025034001d1041c005200341c1e0010704802801482101020341d425a51182001c45110741080100b0740c8450843c251742d030b410b00c03515005691050560b50349000035034a4582200c1c0a003001c1e204204400e001c4000130001040241c4580d038010030000910030545d0800c80148128540450145800e00030301c0049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171200665 1250 171199415 171199417
    0xf0a0c1b090203040c05010c1128120308010b160f0204020d0e011b0203070506011e15020f06070c05101a04060906030501150e07080603100203010b09120721020a0803 73
    0x19080038070780035a40349454140089a13030f813103a0200d41000100d85030300d03000ca04981d59282a50100300c0345002160f00000250300e1160b031148200384078015600c0000b8803034103003078004154541f183c0c6a80c141c50380e0b00c42c031101040c0110031f00d419204e5011000013000507100c0d860018100e100910040c10044100600002c903070440080350040da56a04441c0d81e610562407418403001100d2000b1481c1c44a29522181ca8000602c101002c29816030f2000840b0b82400d00020040c0100391500c40c142540d04500a43d00c0d0814914241540609004100c100c0c2c031418407411401c0c1c012004284ca074a0700d0603c0c81c014412001c04100c1c0e507519156600d00340d130301d902a1100a0442d4000480c2a5046081c8542118400034031155034801c2c1c66020082e104030b130500c03203901449900b020308407a80e0b00f80100707013000175886440000707510000010036100185806010010ba0545101c5032800c40781c8200e0f65540c81602034070682180701001d140070100c00c0011402601d101030891b89080d55145039452075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171201915 1250 171200665 171200669
    0x1404030c060f2c03041a0c0a060c0504061701060c32030a080105060c1207061401030f05060702010501080316021c06060302010813080a050a0201020c0604031808030f0a0c1b 76
    0x22100601e040c5408040819083d41042071002000e58034143c50030200000c1c013a044803204480b10004a011244d4420512064460319049402844501b26400d001801d43d403080c010403000c2140130303402102090502484605032800e949424403c4681501d070740b6a00d0300c1d0070150b0000314040b00d0000440000894041c0945120b0100031510340c03084140283c103202c0142c000d0b5004c2d94080c0000011400f000074108808041290410b5a540890402d07001400070582c0014080707901100000400600880340307000e40d40150192200c40e15854000c03801d0700d0b800c2c400c40e62180c0c01405030342400801c0710200c0c00100e200400d9248419040d50040d050401151001c0e241241d8405c400c200350350704451010751000c0ea41100e40d4407209103030384070032840c040d1700c0801003000008034841040038001d504071514035030303103404840c00762030075160040c000075400003002000c2c8400030780001da4100001c203a40b4002200180c42d8101a042d038411201c6160f00101a04c41010000c0d045000c2400c081070600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171203165 1250 171201915 171201941
    0x507030605090c01081003030e13090b01031a040507030201030c02100905060601020708030412030507020f120c010e0a1d0a060e070206011409041e0804170606030c041404030c060f 79
    0x1441e29265070ba00d81001900307500039040c40300c0c102c1080104428a1070010560b0b525040040d00c111080c07011039180400c11b020a00014680300d00d89041c030110100d16070403248910b1420b400c9242c00100885518410f407001005680304041c02e000541c000d400a0b03080790007a10464580e501d5042c000d0003a541000802d4070150040d6047c0002549d0520007803019044e031000540c0b400b460144c1002540d1b5800c04050200300000c2100070466a621241c403c000c01c009107a00e135061000f8004e1074a60b0000c000c2c6c1801304040011258040c00c00603094070485500c2c00c181e0408007070b03c8806802164005280d503d0b8660b0f036800103c0d0a8100d0040b881c0030300500d0303000f80003640c148002a451120005030152180c0d0510082000055842e00316908045020205144200e803a107003c030064040d541154492444002c4128005000001c80714401c11084040342c400c2c95080c0e0501c000c680706000f08994000400307000070b02107030041c1da16419680c0714074030004483d0107060a82d4201c441b90480d9407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171204415 1250 171203165 171203171
    0x503271006080114070c060507181d0106180506070501111308071d07050705010b1c0318060e090903090d0b0402040c08090303060d0228180b03030706020d0905070306 73
    0xc014500d00740b280c0801c6000d02c40107815641007100c0082c0002c01d002d034000b0012901d88e0300040c21244501c401400304107542081006603611500306070b40b4055800034000b2a050500000030354284103109030a04950021082c80d01c003802e0070103002e4141d211303550540c2c0c1c40d900c90810b04c1d411034a80b001030210a0110119000769402c1c00901410500c82d90710100405400c001915080501d0101080c3c0100e00c0382040d5a68a8984ca440e5014000c6446210340c051a5100c0d10900c002200014070039240c07080e0f5075100e2400c08004480e903c0040b5014840c00070b551000b6a07900b0b0f081001450741c10001100031282400c00400028002480054040310034090020910045080500515140c2c01d080e003020262894101901390350307400001c1265105044600c013070b10554841070607009a608240580c41c808514110030002100121f214040000f4442400e0240f9503c440c4a0085c0890008000c4d51034403060380c8a0002a40141c80098030103a580c1c6c0100f00000c03010030020700214400c15008c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171205665 1250 171204415 171204419
    0x215030907080606060901030911120102090406050103020c030405040b120f031e07030c11010306081005060111120f07081c09020906030c0604030602030c040b181507030503271006 79
    0x150034088075501c50741003948890144440341c1d89110a54581d000c0a190004100c040c80c2001c199040004041ca5044a01662841b649100640052402c0c2000360f800b071001c1580c5400440491058080344010b90300148418803162400e0b130411061483d0061403000006a024001c9048c80034020026006a0000a00700d25850702100c1c51101c00300b08070085402c1c088540c42c007406032080300c0e0004184018862030001140e00070f90002020f00104001c6030190b0340e03110a101c00410302034070704a0119000d10340841600b0400140d0511300700c6d50714149403c00110501030302c503980001c1000c4074012001d00c007180341c3d10283c089802600701c15400105081e941c600511411100207000e45002c0c2e0081d400e9058140caa8004407821a90b10890043e56a80d825102d21018001c641000c504418001000468000041d20308401408222035030710380d074178080c801c1708020300c5124002004540180700084080b1114a80c880c4880340240340501c14584500015080400c100209000c0302d94501c03003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171206915 1250 171205665 171205681
    0x40602060a05060a0e18030f07030216080d12020702040902090403021f0b0a0302060d0e160806010e100308071b1710060e04020613030203030a0801090b19090c0903021503 75
    0x340b0350400820350340f403102541025080502c5110040400342c0c1c00c208402c0c8031755000d4080046030b1402d041c80188030780320314061400a40742c0c81e046103504040c1c40c41504c042003045004c40c1c6858980019283d0807a00388441880724069084004140c1c0e1140c4d03208900c01c0035840b0030030a1b91040d486907000e414110350f41569806070100c00d000e00d41d0080c0c07800080c2119074658035200c10540390100c440544566140007020050079440820081c603024801400000000009046065030400001c0e514507a0301c540e000f402d1130b24200c440c1031507900140350800205041000401d4554041d1058955050f1401030f401c0c0c00c4050b030381c40a01220f4a5603046020741400b0700644200c000304210a1120b1444d00c010300018580150000c0d218002c0003440d4500a05590585001142c1c0601a00d8448a080e40d000e00700039424802c0306040c1e400d0844c4036a45242a9083c00310140e4580300f00049641400c500000511000400d5030510512400100c00343c2c2c3d80340a0322010041820300107503640b03481d00e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171208165 1250 171206915 171206921
    0x80c0706030c03050711070501031109030a0809030f030903192a140f180910060b031519290f1803030304030903080307051605010501240203041a070206040602060a 72
    0x2040141c2140b401b101c2050129462040791400d02e4085014448241070780c09070300c2410403180c0d161041c0c0075a903040011010103444c44030422025118a1990b0060241e1603105c0d6481e401e5164228a44203d43c0d44001012460f820380619820000117400000c7c0b50220804c52841111700b00f0504820495400b68001c20070031428203684d803521020360301c030200d014900d8140d0551000044000003070b0b0301c210100581c481c282c45001c424040a507942111180c0b560094401307440c2501da145101c402170420b8070b203040c0c2c400380404d040c0347d49500c5c140e00b16103564241d410000c400c00e07440e0096110302c0710002c060450728070b88481043c0d640d11151001494030760750900f100d020750403e1080001003600005410100d07600440443da6a40d00c2078001c490506c03c88500101c414028204541408015030050b4142c840d0405020540e49040d514209042c12035245100103038400c100602030321503500307401c1c030500c5011803426081070301682c0052000c2e005600a8001a80450100071205100340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171209415 1250 171208165 171208171
    0x40302160801090804290a0f080a020301031a0703020c12030a1506020d050702181305010605010914010c02030705100f12060506090402180909010603300804080c0706030c0305 77
    0x1100802868210340c0e44d0b940c160059214480000c1005806c2c44103041800c0c1441250441c6a05466940c0c00e03100c001400314010010700b0340000c4c0c500d200242c4201e140b4800c0341c9c16207400502c0c0240d140c2c5113504070080204001d001c2010180c00f8400144141030800c000b007104074151281a841c1e03d48030070303844212043c480c02005140d01140041200701d4001c01c6a1442c4207040c03511035600d407410300200f0300140007003100e0740203501e911081100e4854240c02d10320099128100038080d0316655001145c400701c15024030015840c0c0040c035500258098400c04114610180c1900c1c2d910743d0b030f200062800d2404a00200220f5100700c1c0e41009181e00000450300d800101c04104034641c1013802003a507a0058500e91b9002d1070340051780705018918443e40b1502c200c4c00a204440c2850040c9000c0c1c060002440200ca416000d10300c03c0301200140c8100d04004042e10500e400c000f43e49080844d05041c02a0059030b00341001c011002d907a10060081e58007501098601040000d50b400d0300400700d035402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171210665 1250 171209415 171209429
    0x30102040617090718021909030c09020d0e01020c030c071a0d020703021006140312090916122307021911030f01060e0708010f030f1709030604030216 66
    0x401007402115049520050300018070b008010841c0c0d1280541490800c060b000010040306100c41c0d00034210303281d0010080c0110059a0350400d40766031500b50741c1710032140402440b0505040c8103210003052a40039080c4128108008205003003400d14aa02f241d1181308001e003560800214401400341c10400310004000c01e000118005c541f21605500074000c0740c444030541600000d5080a0500c20001c48185807444c40040044d1079403400003050652194080e54001d020b030300c0645103180d04070000e992903100003038500511955002d116860780c1158802038814440d80d001c0448800d00603201d1300e10303980814a101c0302001c80140c0a241e1a110050181c1c00319840201c480b0054060801c25681680c2d1100c1c40149800300000040e05100007032142c20115032900c48001402c002c1c040c205802000e81c1d441e40010340c0d8031151401c00e4001e207808042c0c1a5080c01e03c1410018030200300052503500480225800c02c074010000a0038008140d078140d006922108002a03d9039a000c180c100800403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171211915 1250 171210665 171210667
    0x80706090b0c03070b0a0608060f0402012a060209010203040e0f061302070819030b120a11010801050109171e010903110c100309050f0d02060a0501050d0f12110f010b0f030102 77
    0x1000c4002c030f80d03034454448002d03c00710a00020030840881504600054220b030000c3c2d65103850440300401007140215000c0e4000b850500000c0b41540311046011000c03070b07055070b5003440114140c80711000395001e4500281140b2007004000345162550015174001d549005aa00d030f1801d100040011010040902289607481044454000f413200000c03103460004405580d8010a11828107800030080c5041c8560040700c00e80f05c550b9408004143d04440d5445641c00b200c02c3c490301401150151001d005907400700706032010502614000c40c2602c03400794070340c0e401c5818400b00070041c860306480c0340805400d580e45440349002015000340000e40c4c2d45e0307090f01c0180100d14400300016050314640b10003900341542c2e50494824000c4c01c0c48900c072140009070894855110070b0034004d40d41c02e000c40e200c0c03180f40e203840000f1609280c0000801c20b804d8000c007036580c040c01c00b030326218000d07450050700000380030030314045a080140a219001d0411429000019008800810f020420919074120703803090744 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171213165 1250 171211915 171211927
    0x1051308030f0a021b0609040b04110408010c1e0e0108180d0f1b110d020102120f0301030b070203090312090f030d120b060403020a03030309080c06090703021503040c05010f0203070b01080706090b 86
    0x4401c8140d5201d140c04a48c00701e00003582a001c503001303025004184c1c402440000c1d000c00c40042c15041011942c9490383d84000c030600469040c0301c40d000c0041c2000000303101001801480d071207100ca041d0000c4240c08150344c844110100c05103040440d0746c80c20042118241202e8003103401403c1c0d140011403038048a0f00340d80c2140c0d41d403030356100500c040b1780c410481c40383c0d14002d40e4420011461443d4203003000a03038403441d0003402460703034209220468070384503071000040441d03102009550b41d01001400900c05070448076031402c00d1703801201c2400c0d000203041a40441d195020004d400c5240015160b1b050307400c4a4034014000d44c2d03007403000d05004500c10803040006031a91010441265050700d00014580b1027441d010903079104410105076076105c3c03e000d00400103804102502101e03c2183c44621400346402c0d104030501080b00c02a2424000100400065000b20030a00c41c0c19000e2041da80f8082c40756a801401010070380206401e0b50003918140202900150100040c0c00600032503814a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171214415 1250 171213165 171213169
    0xb0a080403030c050409090822060206040206300a060f030f060e1504060b09220611040b07030e03060a02040806010303030207020a0914071e0c0201051308030f0a021b 73
    0x200010304010105075075403a480708501d2086060b1400350582d010300303100c402210f04201c1441d0300b0540400005045800300c0381110006400c1e041d04440b007a40203001c140e0342d01d80030051076070003510000000d1041c4800d010392009500c010b98054605040309403745091000300f03d82240d042d60006c11422080d060144042060300baa000310141d405000032590b85800040703a424818504103c1000692030b0062004001258000d42102c0c0d000740c4190344140d44100011a108410304100c01c0d244042d500c90300044ac98a420110b1103140700c400440c40c095460810600f02d80c040c00042e40000c81c520955209882e09010054115003c1d20055090505040010751540c0041c0310080c2810f034000342c0e050464a440c40d180005100300e0100304100c0d80a10030100d44103404543c81c1c0001289100d44807406410f07403c2841070104c0541e182010b000082c0c0c01034032103900221b03800604031100c0c100068140d0f0100028140c0d500080b00030740d01e846401c00013030303d00007404240915a0500c0b0308028030903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171215665 1250 171214415 171214427
    0x4030c020d060c021f1a04050a0f0c02030c010506060a1d0406052106010b090a170c03030a08070e04050c0405060c030909090f070f030b070e010c0f05010b0a0803040f030b09100e070509010b0a 84
    0x1d1b4084a00080b29100e261001c0c00038841050a0300d902070400c40785240a94000c80601450020303038000340680c0d6160010448588202c588000200725500406030302e400c05640300d000b8208012b0030000d101a22600001c200c009034078082144c11000a207011032150042c0405c2d801495614201410403507044006036801c4054082e88038001c51280f18003000d00000c11412950410180507244d680e0400a0010a031000440e1118007061031141c05004d84c1c103080c400c1c0c1b4420886816400d0905040008021541e0320030784c1942d8040c80148001c2c881e079a00e80303056a000749143c500821114140202041c201a09540240f95824001c075040004c60619602e6542c0903c0500d4207440c46100c000050381c461304125405400341002e41106030402c04154001811241d00b00e0308000c004e6aa501019641e2090b400f0302c0350315a0944c101000002d482968107a080300302801518000c5030b00c810449c0c00c03103003600c0b0341c5010313507011010800c01424400b42040c09030080390022450f01c0340604d40a009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171216915 1250 171215665 171215711
    0xd0e031806070f14060406051320130e0a02010e100503060405180109050f06090f03120406140a0212060105030403020d201e0d030b0904030c020d060c021f 68
    0x51800010181e0410980c0c0f5821242c8a43c008044180f185500c03980a42d0f515048400301c414500e4800032802c41404c0000100c8642e52003020b40c1d44400848003440700c040300111116070010500040302d80d025007103018403400c12130344000904074003d041c00010500716110040a0003401c80c00d070512841170348841240d61102003070700c000c03d40751241d01c250200d015100340f00c41000d518204000e4100280492038001aa40b940215080ca03110824000e440f480d40090115099004200b1011030a103110360300c41c1c1c4240503910005041d24100f1455229580440c2c0b840e505c02d81c001000f600b488041a0110b801400030700e8442d08500d0b207550080c0d43e0741e03284040d100905c001c00340d80540e081e4000035200d00e1450004162640c0600701403840188110042c030101d2140a10021450118803900c604400b039400144514550b0720380e51001e42c0c980581c044207a03088218148032001081150244000100869000b070400e1410f080000d1203998110520708102410160154401f240780415408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171218165 1250 171216915 171216919
    0x4140c04030b040f0807060c03050c13061b020a0e0106030f02040e0a02030411040f0605010e0411091909020f04230a0603020a09030519051204050108040609110310020d0e0318 77
    0x40f0303200d0b0b0030143c0420000382030041c03140c40300140d5401040b001d80c105e0351031448151030500c5142c07151203482c1040c1c0203010303050b1201d0031400010031074503105031a011042d404800c8201c1100078250041031000d03003a03401001d40b0300030260040103205e605218100201c10120400c600b070506042c03407505140e00203000303400d80a8012001c00d05201050b150800c40a01c0100200131035000c0d9034141020304150b2040034041090450408402e04243c0203100200102031802c83c50480d440040050701001c50044607150101c2c07100220711510705100030700c032902d82c404080e511245000741c0404840d04c084000c691040c5c2004400505803502045042a03a4160a0140c1c4501c90280e0444a07511a5070000c0d145114515072982080c151040400500d0b0103807050300c3c00103d48500c000c10b1407145128050001b6086400100810540e50101c1c40305445040d4800c2c940203c80002850700e0142e0560300400c550008032088024211f11501d00300071b0f0341c000918189419004105050880c1680e014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171219415 1250 171218165 171218183
    0x906090a020f060918060a060c0f020907170403020c040f020a020a06020d020c1e010507080708060d060e100605040b01211a1f03180b07031d03040b0904140c0403 71
    0x2d4541d84981c1038031140d079006803503140c08081c403010364414141c00750340080c042c0e0310181010403a40d214000e5200400e40000007003515030410b609002121200504020422141010303005400c0d50308001c03030307020310b0280e40140020010390f0100001c030341275800043d180074410400d4080c525004908014030a4000074010384510030740c0e4065010748100c155054150203030b5200b0201d01c820b00082d1880c00e0f081140204015950014140d03990f0f10f043d030b5410b001c11503020000b003151800d10402c1d40e0013840303007138049000a50740c90b203207142c540703140b40d00610795840e0b2000b84020305140c42042c1d8942002d01c0c18059032404070162000e20301e03030500d10415103612203e104010040c0ca40c4c1e01c04403884003602c0c1c800003500c1e42c03800c0d200904a0307030346a1001a04041417105c06c001c0c10703c540241d86800000707240c49621079034400d80060540c000d462402c0449150320580707050051001d80b00401c0c0550415944203d04800c00c8219a0400b600c00362000c00182800303542e124071419a0b0030303079a0080e450f03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171220665 1250 171219415 171219439
    0x92d01290906091e0702070521100e070308090f040507020f0d0201020f0414040b03030703080103061808030c0c1519150806060d03120f090b0a060b030a0c031103100303080906090a02 80
    0x1b24240800c44d0082c58100b0328500c009040c44001e0000d1603000503403041500c2c011504100c4c80e4090b220052000312450340051424808545140018800348800030200c28816200c1d80100702a034800b1180c20700560003030b06c01100b12180500400da010820751008500d41201c0000340c0e041809a4001c0400000e04048240010780340c40d807140d645003d00400302c1c0c1d00c450041c64028110f1000340021a0090308124400c0401c495400341140c406601485181c2103684174811621641c0002c0001e48072441001c000344400c00c544d0b4078490180102c0300071030050f000d9517004001502c2d1443c0810034241c0c07140c1420410382c0c1010030115000b582c03c0310080990452420211032205040c04951200c1e89007074401d4150036425441142250f03c0b51310b20301459a00c45020703804031000c6210303039403600c0c2d401c00000d0803221a9a00c6092800c42c141400228a80610300801e4560002c841c076540b030108408080c8181034000881ca40d102404100420300e600d400e0a1440d103c0c0040c400081c010310040c40d013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171221915 1250 171220665 171220667
    0x30105070e090a0902030c0a0b091302120f2806060314101205030c010f050a0e150c0d020d140a1b020705060a0302040909050c09092d01290906091e07 66
    0x5000c142c10300007070020002646450f881549c652000790700394410301c9032884220300004c26009a900000c00803020120319078404041d0240341000a0142d8441d0340051260b50342d051103480200507500d403014001400c036003400000385c100c40e4002d8103034121145003020011200720100c03013242601c8901c10b500600d050140760140c607501030080180c03070303a5007001c4600c0203464190b4016481803086180900041c008848069210401390f0030f070300a42450140001c0c481121000140340b5125012001854510350001520469070100c4200151100c82018080c1e141b2841c002e0034030900d00000d51003030040380c0080c0a580e44045205140c041c08011401902c03850095050350014100c0740c1050040c94564a452625100c11500a61085200341c02041d55040c0008504140f0680018595a510317215190600045007201d4010155926104851104540042c040d140200b48a08500e0070301003000c1000200e000047c1a140100d0184007001020314010603406282d100c0c40200c0880c50703c40002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171223021 1106 171221915 171221923
    0x303050909060a081501031b080714030115320622050d1a0606070b06010503090114130311010c0915031514030105070e090a090203 58
    0x305900303207410401c0c0040d400410080c2003001ca00e55414090307142c01505580c2010840900e00100b0811610001030190700340e50700700141c0158245280b480e1b54a0013480f60b0100040800642070f040d84080d8040c8074011400c5240040752030b110b40b03140380e80070091800d80720a51f007021080b11000c00204916941c1302c000030640b03481d0103010210480b1030505c01a400d4425130042c040080c00d07a940038820402c0c3c038032600104120303404810a008070410000e00407070080c202048840002842c404081d64000000d0900c03648032785840e800c050041c41c000c54502c0341c0301d01c8074043c0b00c84881e14070148020701d4800e61307919503036000c003c80540c240e48458002a000c1492000144502e05031504200400003040c0740010340e285c501100780081200651042e400551040c071948881e0034213015030ba5020015080c03452100d601c0c2c0e8049240168000c00301c094540c2d4401c030200866400740 = true := by decide +kernel

theorem cover : BRFrame.Cov 171043165 171223021 := by
  have h0 := BRFrame.cov_init 171043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171043165 ≤ n) (h2 : n < 171223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
