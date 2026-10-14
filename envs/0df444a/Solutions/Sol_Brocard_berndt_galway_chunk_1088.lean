-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:11:16.786539+00:00
-- url     : https://prove2.me/submissions/bb545e7b-a5ab-4a81-a8b8-de955425d317

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 195503597 ≤ n < 195683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 195504847 1250 195503597 195503603
    0x4080c09070c0336060e0307030b060f030f01060608041a0402060a1409151e120c0f16121b0c1509090f141e01050103020901110a0501050108070b04030519 68
    0x700d44c120404408183c0207141c3e40071003001200804092021542098480c10102070480c000c12403c1c0c29a40d0b40c6200b120064002405049490b0449206030b605206650720380613564020480c2c11f64481e001489184240c809940f0003022800401150081e00d1110b445503401805e018500081c040c012103040c8080000c06015000a1200a00c41c0e690601003410452403d0306282c2c4806807100c41c250307240400381501c580e40b01d0030030000c060011460041c5901c040b240080030340300d42c08902c00041d14401c41205d13034000040800494200300700711900b48115a081d68501b40c03000c241800e111a003c100d46030180c500d04824104000120300740b01100c8400c0c605181141015030381d1001d141c152002899004050fa480e075030f011941041e00510198400900400d044640044c903154684149040c02044d0405800041116190340641101c000c1c3d600008100d171b0041600303040c103074000c0c6028010301c485070140d40000606990900180d90503a80c100c805004208900c154500020421074011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 195506097 1250 195504847 195504887
    0x6040f0f051f0510080c060c0c091014010f080a0c0207120c080622060905150c090901050303031009090c090204030302070614041a09010c020307090204080c09070c03 73
    0x31000281d0a021001510440140d40349038100303003944400540364001c0c5200203107640000d00b0882182c00050b24012901c05560007955403046406c0c05e401c003005228a941c022440206000760081d1211821080307401c000d0308000407056007001101c1048240d40d01030001614100403440c0e820040d4407050740c452150046500311030f078664101000d03810201059611100c800801c03c0b14031800d2080c41d0780605120340114000340104c00d00403034500c0c022409001641e48204490030880104542c0440a036072101583d4a4070701a0301d10f805540c4441c004901070f1580400008003810000241d034050351959030842c0a072420706190900070302c1d03000710690b144210254001480c508520041c8003550080c0e000c2d140881c01d115000e0040380c500d0689061402040204029603480640911410341e2100c032103568446207440101d401c1403640401a5050050a50015803515154010305c00c80d01d0620549200c080d03100e040081c004011181000400c040700100000a03105103d4100b00c03100711080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 195507347 1250 195506097 195506123
    0xe090c03010e101b05030f0a1503080a02010c0305010308091005070206030f10082409100e0f1011030f0601050d0614090a1506030f0603050313140d0506040f 69
    0x81d09480c518203061815400120282d49000c070a4002d5101002c400c081c0100d0381220113000414920000700700381e000445180c0451070715546c0f1b8000c8502c0900c44006140099100d0905050940c48001c8400156281413404000c4501034017545049a401000031070078001000309120342142c0c003d02d1003040100c1081803000507a107200186004008450380b0f00310500d011f0300e040030120070b560000b072000c0d80f05912580b258402510f81440303124414a4281d101e80b21945400d00c1c0c9200000719010143c02d010b011a80380b10000740742c60f6400d410700120b9480c08014000d0000319400d0015001901c001000040c3d4201c482c2100c6c150424410b161941c545880c108441048400343c0d04001c07074a085507aa07154081c82d010f006960425078101c010044090000302c04071040d8030f6445031310705058442c800c1080741c80380e59105100071504603066035076401a50349407030b1084005024002016800020809042c10008410f06550f94020000c011503211610f41100004025500325440c0d5000e41c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 195508597 1250 195507347 195507349
    0x306170607120f09080301050306010b030f04030c110d0515010909050c0d0812100303030b0117060d020616030305091002070206030103170409020721110d08090106030501060f09060906050a0e090c 86
    0x8110701c2c044d07018021468aa50401d03003090304002d41a48004d0300e00c0002c0c014001740340702c0203452039005079150502c4040400c46240c000c907156103296035107900c40c03420080c0fa804e020307004c9034071b5041030000c0c80d000c15181e89609806040340c0179104090051383c440801d00d507890415040084009008051aa00700303002081c071503461180c12180d860065007400f0003001015010301a0380083c00003402e062504200203c0d10b0110002c00412140c0300742e460001c0d0400b03645a140072600301400c03032110b590054543e801c1c081e0141005a89600c0580300b0341012000c0300c521403080d11201c50780213042034036503441c0d03440e204d0b101c116901040052000c10800000e15800c1440145030151051740d103c04040910000c0701c13401c015102c0030a00f03100e801c400c01141c412021500d4030818140e03007090301003a00c41030001e034010310036a0001444c0d90310305000407407220343c0c20780c0317410842e00401c2040c45581e13142c03814030040c3e400620403a074000f26480d00510280e4845c880c0c0350b501010042c02c803425004600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 195509847 1250 195508597 195508601
    0x603191e1d19080d15060f0e0f01080a090303090215040302010806060705060c0319090f0203010f060f092d060806010b0c071205030c01110a030e071a0f04080105040b06010306170607120f 82
    0x1c1c0c00340780131940300320703041f00354603001070404d034400200f200c40101041c08040040c0107034030002d0590442d10b07130752103108007014020341c041c0040303d070040c05a211001c401c1c40803212a512a0105a000c21801b600040c410703d0040111103003c2c3d0b00c44041c180688416040b85000e40010348850303500302d2030402a19003080c0307920a50340880e0040750200b40b200114018103013154a40c0c030000070b2450400e081407086640c00c0745800100c540043d0002950b1701e0900c0c1c492003280c0d40311b2014a61180c40300401d2094040c0d1340010080e0354841003a070301140d0346c8090380c41b090301c94220b1b040346075007144004101005a40c01040e8820380540143c0e03262002c03880d100e43c211011008541c24034a40451601c40e1150f06105030061108010002c040e042d0418074070815240c1c5021303a1042c07000000400b0f0a81c0a000d8040d01c00070b240300002404a820649403848096500302c6102e40001e00c0c00c440020000b1414241052401210002c0c000c00e84590508407120710000c0b00c0f080390207443d100701c001050501c3c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 195511097 1250 195509847 195509849
    0x51f030203130b09100501060305131101050d020d060608092a0d080304060e0c03010204030807021507120903050c0a0311120f0f0f1006050603191e1d19080d15 70
    0xc1002d0400e17100c60b05100000c0b0b400680180007050310b0b14042106101085074643e02c0c090700030b41060400d190140040f1980c0c4280002540b105001107401604515142c20140c266a0706840b032400c5660b070500151b50b5248010741001d040f003e002429410049010081121424050000141501c068954818950068604a800c0c0e50b8840300035a00d4003003444001e04420b4128000c2d03180a1a6880744d05160181e0100a0702c035220080e994480c0d103500504883e03a255004158107095107400e800038020f035000e48000d490340c0c0110580c2001e00d07e4000021001c0c1c030380c49001c11000da032842c018070028040c000389058891150300042d0701102c808108150300211041e00500ba4081101c000070f003014201d01c1c100b010103041c40001d0286580300700590342d00280440d0251800350030074901101030100c581500301c0706905203801d1008051543c1208005400ca105050704c40390301c1100b45aa95030390765a20202c2e98007190341d03500015138108020036000c000320b000030411540340c3c04801e805c6c01203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 195512347 1250 195511097 195511111
    0x41a04080f0705101a1e0402090315070e0a0b03070309021912020f040c0813050a0611071e0203030a030b0a030c060905011d0d38010f051f030203130b 66
    0x1031040703410070390054050030131080d03008040d60700551108404646c81c40b400c40c0d84503190203800002c1c0c110725110341e0705403400460b00400710340b1038107440e1090f48050301d410b98840d4005645001100454108108020304544079841c9a41c074554503028210000e1040100c22640550451403412490520703503803050162014261381e100c008143e20400440421005a480c095030802c00140285604039013200e900c03540b000d550300c411054500c0e12034106119000c000300320b1481e01c00703c8504002210043c0002d42e01c60032161480c0745200908200c0c0200b4a40020b6241c1d0081040d036640600c20780122900c8030020381420100d0761290f0312010344600b207070000742c009074200400700041d40e07110400c90002c1c0c00d040da001c1c0d020707907800000c14000d088000e40504000c404c0c21040140c0c0051041551420044100d04210140e0f03514211800e400c0078850712804814501d000306051504200c0c10581550300c1c0015408154691030540107500020b1100002445522880010480b4080c4c01842a25 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 195513597 1250 195512347 195512353
    0x70e091005040606080402030c1c060c02030a0f030902030601090f0612050f0105100f140105190c03020d0509011709030c0d0e030106090b030606010315050301150302030d030203041a04080f0705 85
    0x10800d810b0104940356540904200700d004014403002d620089903c444440060743d6420110003003800b000705200108000501c02850244200f181382d80c040058540a0041d40d14524010b2645030210182c555005010b0351540001c4010041c0d041d541d4010300c240105402c022881c00e81e07820120701103601011040d502c5400c040541d05c000d01081c81a05ea01103100920489118200400700b00b4143c064061000c003541581950042c9030300810039146020b40d4a00048402d4a031204001d00e81c1c06018030450251184c003580814040c090f5054035003007481a9250100040c1c0b54070103892a52018054180c240002c000c2080e001d48180305d039800c000d8444d100c00000c0f00d20382c2c05240c00c42c1e0340c6a02104071146040700d2901240d03070109165412050900e00030a61070034015081d080003140380d000c0b0741d0540c604813400c000d25805003800011607000f1820b0390381c400d941200030b80907031208440c000e00320800c8030080e02082059410443d049402500001d0030b000341118100c509a02c50710064915038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 195514847 1250 195513597 195513599
    0x2060327070906030510180b04021804110a09201b070f0e01090203061807030b030d0f1106010501020703021311120a0c09150c11090c030702070b030606070803070e0910 74
    0x8081200c08594600030a08111240c800f0100c075111f0b00c1e904100410303210303807000403405645e14110013124070a42421074070443d007020300d400040302e9102207549010b8100040006446e50843c4544d070808103000c0060807071100090402d90719944480a070801c0050421241e41b0980000c002c2980074081c00c03171102c1c200300c0c00c103107040f1042c890591050030482e004204000b600e0302e9102c200d400a40700c40f100e40c003070307621000d00c250b001c0c1c21884500340d05480382c00c517283d4000e5800186000c6103441c0b034603803140302c48074a4041a1501824002c00d405030b80086010001402c0c01030384001c580520180009521203440e00c0903950764802800282e0030302c842c0080c080b50031124418562008090300b494240686400f010300d1210000c0c00c9800107001007482100d082c0300d001d509501c144280140075500d68500011020700903002521000014400d45101181d10241e5000303c03806104001d100904065466580302095803009007804200000d21518480c55190b400e141030180c004121f03065515 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 195516097 1250 195514847 195514853
    0x109091e08032203020d0e010e041a0f0d32120304030908030a0903150608010608010f0605190320130b0411130b03090c1f0206130206032707090603 65
    0x80c800c003164500f034031120b0094100000380c0006100300d0860050030171182840390003005880004034003100c00d4109081c09180e44050800e078810351103403001103a40410344510b00040c001c4a035000b24004081d84008a542d16040628012515841c2000300200c21400d014145541c20101c4c15200b1500040010041c00201030300301e8410b00140c5280b000842c200080040020184a501d00c0302520155640b1803640207084241c05c00c00241c0300300c0c0000d005a5a40300401030082070300c0e103030040710613291540c00b250900e0014400c4683e05003c030029842d803400c5482c0c01d03800d800b000c41600d0885003060b584001a4541d580c05030682115880000707030b0849560280010b40300384a105001012042000001114036030440c01c3c2514500c509280d1641c0e6180c20f11f903d020794400203e41c3c05803145030140604400500c4512040060b0303401d032205a11105283c0b0b00800c0f05243c000e5215101b400064031810640580c84d13803002c07550500c4c006203071074100c105081280035004a9803d80d1911014024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 195517347 1250 195516097 195516121
    0xa11040807180c08150406172103040b0a0c0c020a0608100e010602030a140d1e110f0306010c03020705120106030b0c03070c031d0901090902011706010203030109091e0803 75
    0x940b0b40000b020b106140301d5003802008040001c0c2103130341d10031071109442c4080d20385a00c6003000e0000c01501c09941c000c00000165a1480500032844038440703910300600b210014000d8070b004590068100400ba141e1262080281a001a07800100324001321070034056a038154041d002041580c03105502814200441103041d00c1942000241d50781d10f41c01080b03080ea0010859444070a070303141405180240b605050310510814184074201800d081110826014a910741000c9203142c40c81004a045d4205c0d41008030f0043d8800f442d2400024400207040d940640e0003c24030b40c1c868419034140300d0322480000c4c03a01d071040c8520f0340c0580d540c200500c00c1000c0340301503540100c000c880150171480d002400418601d181000142041030300080415812568603a6440104004014203042d6031136600d14002003860400c240e0001d040000c0020344010b250401500980041c0d018501d50380c20031101c400a44002141100c14003050700c80c1201c10b02a82103441c10080c8600b1004da920b04026618640c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 195518597 1250 195517347 195517379
    0xb07020405060a23030102070804060306050307060206090c01030e030c060405011a010809060109020c070b1c0c0c0c0e07110609060601110d09150318060e010f020903060f0a11040807 80
    0x10041d4500c1c042413101039030311980d0203130455029a80250002d00301001c43d01a00504000070000d52000c6008184c543d05904088166401601200d0400c1c2d91100100d948800582d90185241c10486818103654400d4100368034104481c012a1325200e10080040e00c0c00e44100c60507540344c0d48d150324800300f0024080342c440209000340f8000c1e0181c28007903001c0d078542506100304102540c0c00a002e00400d602172001c0703002080741070009610344060303100c10880ba00e4001503110025103004c041c00c04090080304802441074124441044560801200030003059005d80401d0621802110b494400001008198031500003000941910308081001600800c0c0127800c01a560b008580030650142e40a44000c04540000a51008041055005070000c2401401800c1d03041a01850b10050110a4100c60038003200c01000b000010036040c109e1b8128012030010503817540164001c242150024400e180e000142e440700000ca00d0b50f1441d884490313901c198000c12164101c0c06003000a0051002040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 195519847 1250 195518597 195518599
    0x10c03110702062208250f08030711030102040902040314010c09080d030504030311071a010b040b0f0f160b0403020d03020708070f0c030c08030c0c0a050306040f0611040b0702040506 80
    0x2800e20050b540041c005000d21248040d524403000701018002c0083c4204000400419041e00d40300407900103071907000540200e0359010540d0030740d00080c8060100c5510002c640030760b40650b041c0307056a56080049a00c44241e10b6041d034080c04007140305441440107000962040c24222041011141d40600b5101803c0d607402c10f1200341e4078100540391380844c403c2c2000704075144c0002c2d140d555217003d40003000940809840c40b840424410704001100480402e280d00011100401ea03907598502201ca226a00a000e47e00c403050013081074070540c0201410f2222101c64030181011300b408030b0015041a400002d40f461004203051005040d01402034a89140070381c03500b545030240704e8171802040d05c00c4038801000014040301c21000c1c8510868100055a07100003c00d030803980d110240c0340d40740c00034030110b2190300941c00c44240500d1f03c00402070464a01802400c2e40e60750b16110101c2c0340c51011803d58034035840e480040d15000c0c90784020806800e080b25519212040b40c0140310455000409203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 195521097 1250 195519847 195519881
    0xc010b030102030f060d05070e13020f04060501020d0c110411040e010f06081528150c020315130807080703090e04050a0b07050c01020d0617030a14030403090e09010c03 74
    0x1201030480c4d8801042e901203415074882006441c0c5150440c038059059001003142d140d07034001c1c0320841d01c69210b0541d08034022903e51100c07040300ca00b084121000c0e403241b280564812100520000d0003012100d10450141400180610081f004035091700d44051b1101240080014180301220901003428094410202444840d03414541c0242c02140050038180040d94030107140b60b055a680c0c440c100285000300c03550401c0e001380700c1c40510389102d107001e1010700e80030101c81c151400303204050380e9200d07540042c010305500c4020700030000d01c1c1c04003900840c1007d09280103140401d800300002e01d0902d01c251112a503803001810020700c1c041c8150050698100d200c4184004520006072819003680c00502c0400b0310385880700305a81071b20444810307442d55400032a1185200540e50302c014101c03070846c4030aa00c401b11134030000e43c5a02c030300b4a4040c0402d40101e21407014a10300c2d4040d40c6d219202c1c1c2010340200e52031391174600c56500f0444003000c80b13a4440c10403c0e015035150181c2e2105d459900a5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 195522347 1250 195521097 195521101
    0x105090604140303010b07060b1f080405010c0e0303120907150c05070e0c09040b030c04180215090306070c1104020c01051017070b031306021b0c0306040c120f0c06050c010b03010203 80
    0x1210514850100041d1a48e502e8400003000d40d5a4030300d03c3c0c5840d5400341d200103005d41400c070700540780c01c01c122016102c0e0f5103880d02810080740900c02017a61504020080c510308452248106001d0f03030040c00d10b003501d221725640030039212284190000b43c542161034100010565240a5107003032902d03000501c4c0300b00e1440901c42c110300e07164162140e03031004460100d07504a207100840e2400001d01c0308143c0c454108070006846001d06421405058000d40b0301c1429060042c24100b0b151054a6030281c055000c0300004507010711800284080030310600800050240f00400541070740c2000c1410707800d50f59100240100c2c4525090b11600030a410720740d00c80000e03220741d500d43e1107080d00d12411020320341c000006000010261141c6058660041782103448000c050460301e0311070003004c03002655101c1d200304803a0b00e00e40050501d218075805201c008045041400c5154030311803103201150701203441102d800001d070ba1028250043c1c0030a603121038440416000b1703c1e0945070203852050080c0d10405c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 195523597 1250 195522347 195522359
    0xd030b090406020c0f0322120f0213020c030304030503160207060f03020c12040305060601021b0f040c020a0204060626010b09040c1b03080f010509070c0b060d05010509060414030301 80
    0x5595001d500084016242c01e20484180c0c180707204201542c49a000001300c5094604448460220340c444100215103a03d031a0000000482c44481019280000c038050100061903c2408012032201d1a0030240c180200c03402220300d580c1007518100d001c40d2001c0204691203c2582d00c11070862042e1006000c4a4a089006801c58250b40044010150000f41d01304c0249010803194036200500d0100300d85d41d47d60390400341d0310b4070380a441040c01400303104041c10240008065210240500521607000038516000700002080300030b035614254003d10a502c800360780e4a204540003030121b9203920300801c01440c001c110081500c12541d0b007a404c1c12006109070b03507041042d03d50300c2c1000c1c1c50000b020004180e090340e18118000d00b8240d070005401e01c42d800c141d07010351540c4c09008880300d21251640c0380c004101e081a011100d400000b5410308844002c00c0102d0b0f00250840800342034441024100c2d01c800d030075118125080f04690b0302c0b1034148010400303842986441c01c002007000d18110b5042031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 195524847 1250 195523597 195523609
    0x121104051905150a0308030106020c1504091e290d0f02090601050405090103060b01091706042604080318010e100e04230403031406130f0207050a0807050d030b 70
    0x419800707001603035240010003032000c031030481503000001801e106005a40b86071103a0554001d004e03c2c0014040c100300e0b40b0007030030b10300366100c400c03810302d585a82440c1c00c009086001f400e0101c1903034107110326450800103a015500c502102ca4800035008103403a50702c40810295030808480d00344c0110700440001d00800d40411002d40816411603819000d0b85a03400121598000c503000154441100b400000c200411580b040403520800e8071440c202550b40d82c494000c0820802d40c030782e10343d08514000380008a21a54592040304040641c2000c0d0b642ca0201e074411f81c1043d00110340a40c8005000054804c040748000c28816091902c1c4000e08003100c0818144404060018140306d0902c690141c50ba1f0799030004c0900c0c00100c0a29200750040d080c2982c10680181d074141d010915180c3ea0740710621400403102d2103070700b001d0120403d005113285d60360000c1032003100c0b80f00e181d40d091040a0004809000c04288d16004e8018562210041e080c810305200392090500d051500d0a409071540352506 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 195526097 1250 195524847 195524881
    0x151003080306240d05070203040513020c0a0c0b0a020714030703123c0c1707020a0b0307020303060a0f03030806040c020c150301060f11120c120412110405 68
    0x9440341c1c40b9220000850100b0032030070300d440d6002101d00c1083c2c802c1003003c4050414007a00340001d021549842a00313076140c0c80303140503207a041600b650307442242c2c409036001000c220515a044070408502030302e82019a03c500c0d00600300f004000648049800d0703040240c074014007001303400b1403130850030740001a039074203e1480001d22818103110450061760041010810107503000c094500c2c441042e40c4540100520742d03140040c606800c0042c50030b070510035081c081c906688a80381001e03241e02c1482d8400c140d0854802281d1102d132419012640103114405540200400d0300155280e06040307003040015003141c1c00140700401816020404280d20190321034000c0019940003c00c43c8810710201c2c00c1c0180d003005a070700450418054014242c60720011f40c126001c95880c944106091103003110000300a07019806594481d5400440032842c100082100d407549400300d5440084070200041f0a0f001a40940803440540d0ba01e0000e02c182ea04a03051121001c440800052600005500e448401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 195527347 1250 195526097 195526103
    0x414100e1b03150c070b01080319030e06070315051306060905060c0c010302160515190903020a080c071e050a060903050a0f060b03010f1509060b0703050315120c0102151003 76
    0x3d0200482c58907031400084071415034000d6804002c541c2c40d0000241c1e2940841c65030100076a05000000e09280b092040d00a81401e503c0074200c2c81c1c035900000c9016100307003604040288100301c00003420307070f58002c01282204101e00012540a207492800740c29251315a00090250f08100892026254027052121200310242801612060f00b6080c200c0340c041400c000920030303c03400c030320081c078581084552885003240000c80a00440440b034000c05403901c1c0b030030060169008001d20703000102c0280241c131800e1803004c01c54480c0c3d80c3c0d51186858030f00f5108043c42156826500501103400e01034940d102400d81c84c00c040d800d003072855a82030342d9034000700d0016191000341e24200c1c2c10085281c1202e00002c00c010b0003480b050f035240d10010002c140f4a10450403032100b050303000036220241c3c0a00003c48070740c140c1681c2420314075101998590b00c010301c9446e1f0400301481501c2c89503220340340102007020400c010411800480c1c00a454160002c01d020342a11411082260480c48410740e40142c80e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 195528597 1250 195527347 195527383
    0xc0f04060f02010b060c0102070b0c18041a0301020316120c0905010c03092d12081b1005040f0605090c0f01030c0201090506070503040c0905070e090414100e1b03 71
    0x568080704034014860071007640e601240008102100300e0301500501702d503030f014280c005919180c4c11004400c52091200314071075042640005000d1f4503296000750803104e106038401042c642e0a0002a00720f92040b0354075010101c060101262603071380121700d010007581d82002008581d80010b009840381c1c880d445164100595036400384201403080d501c0c0c10040c0280004400d2545015495495030502070b15500c11001c4400c00c001050308100121700c2c0f007180c0080c1001d242010191860300c05101002d060b8046104800601c104416903100d0a8801c9002d240c0c01104510f161410505942010b403104c0d4072580704502e17a0300e059462400380070648209080c00120501440720507400360201442c05000c60085c07204000d1000e80003801544506d216003903c0301020380710040c010032554195050000110f16035010000c41c10401e40860308940a1040a608001e07000211380ca4a4840701d4003540300c50300c8144880782c00100300004400501d280f0104201031400c10046a9034040107415014910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 195529847 1250 195528597 195528617
    0x606030a0902120708030406030c02191e140312060603071d0a0902030112050106050a0b070b06060706020a021b010207050325120c030203061302010c11010207080a030908060c0f0406 80
    0x26030340440f4034070001c00f18015543c40940d183d10302616504144228000300f410141480c03c1681702241004881070200d46d120400c00f2a62103805c6890030001c0442181c2d00410036000104e90b07128120300702e50f098240199501c1402100d41c000503540541150302901c014414050b040360002c0381c000c0468a05d00e40c01e809a55864001100414a9030160114600c000004501100c88003030000f00d240c050030081c03040c25610f00a00c4441902482540d440200c203100400002d201200c04982108008004504020b030380d0704d4070401c03a8010341581c800759104031401c8003039401641c07007401040c80c01d0000d44103503072402010030344034001800003070807030900201c001a4217000d8500040107080117210314200700109180034070094600c2e0005030300c00c0c0700d22000201810100da201400550b8181e5030351600462a540b2400005800143c00d4103600403080003003520403040104a6926019a5540c90136500d421085418044080c1482c0f0444400b000403107120924041120104e81091800346124 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 195531097 1250 195529847 195529849
    0x8010819051f05010f320303042106051602030a050708120112150c0509062b0902090c07080a120605060d0e0c09010302010f0f0c02060403060603030809060606030a0902 74
    0x450b002c1010081c00790102168600c01e652a50b001c28182c03584062943c00b02034940300012003c0c0020500c0000e81500b031103403813040d101003460b051020100a81100e0806850f4441e00c0085881101d00070740c00c842c4944443c040c44030764051203400c81e0350304184019002440400039120b10950117401c1c05d0100000700e003c02c0164120880b03c1c00c1100360f031800c3d45075031180250940401c90791000d85078804070190741c0e58407428512035465119450340383c3c40d1920344076800b0b00403a900075002c2d24101e11082045d01ca054a41c07080319a00040c43c49400007102c2400344100304c10362401138104480c424051248400182d1103200300d440035002c50074402d070031b00702d003021001c050200390f0055504801e000c030310482c5030013664001c840d403d00000251884c0c2d058580c03e2000809003484080d00080440142c00100e0f401100264100c04642c50700800c10455038000c209150301552044a000390b48043c100b081c1584039000070b070081e6100018164030309110002170024000540518012903481002c0411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 195532347 1250 195531097 195531103
    0x60d0206040b131a0405180406090c080105060a060905030705150c071806121106030702070e04050328080604020d06090504050a06180818030a05070b0a0f0801081905 73
    0x1000e084203210342d5086a244543d607162190f00c2401400e103c00c0344400080400038081c2c0303007a100d02414400c01840d0941d10340400c4030001d0010740c1e03000c2c0e9031a5010b0106900c11001c0015048400001c40c0c035050000900059081a5022200300b01500c02c092040c3d580c00f14451003102c404172402a03030904628a012080d1182e40300e214941c0c03189840026010140c1c00003a11800008981000f0003543d411000d10301103035120b802441c640d403d0101d9503961400f50044e580204141c4100e0380e11f907498000880d2a05025101034a040c0d00c04a2000c4040381d840400048401e8100526011030100150183c00c500780508507a100c0c0d0740218040030825020f40c01103008085542d424080c50610707050131074440110f24029951a070401d21350098111019074a008815845800585403050000e0b00740100c0c4a507243c61a4580559080c11000c280c2c1005140c000d0001c41000564944820802800309182d00d5914000c0c048400e0040003d1030307000c110a140b040c04542d481d040f1107460311306181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 195533597 1250 195532347 195532349
    0x4180b041b181d0303100302090f0601050a030c020115060905100512010902091c0b0a0c0f140d09020603010605030114150a050307022529090d031202070818100503060d020604 77
    0x43c41c0c800401040684c020750400d14085a00a54514a154440345111400400d00b01c4906001c00d8007000f42241080c40b86c0d1100080b9601c81c8000155030451303050203801d40d502c1d680710f03000086003060184003d183c03500003c2e00000440c2800c602d4541d01245440402c03005101c0c82d4542035003c200c40610b5120148400c280765850980030010740c0803450035042d58401500c0c240ba0041c0340c9587d010720a40140b0102d0380d06426612188804088207105051a50003480c0e00300c603a81d21462808011385034000654040d0429440300c648a6040401e4800d00003548001c0d03521075902440030601d951840c404a45254000d4908603640b560741040983c540166100c5400c0341030003c40210248082c0c288000c010380350302500c661130103540c1c0304240c02940c04100e8080e556075030810103120f05207020f0224045030b03403003407d0200000b44078203001012070708004415030700808000746156005a40c40450344500c5e00454031601150542d400090590000400442c042c2d00c815400c60207558610096074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 195534847 1250 195533597 195533651
    0x60105210105010905070e040c08130204061703030403020609160302100e0d050c0f2202090109120302010f051602060f1b0706090501180f0b0604180b041b18 69
    0x1220b02d50b0764440c050f004050445206c07000501600c429039051901d409003450000a980ea24211074030741c0d528202030300014181c2240d001c0d544441c0000e1002c0106010035264144030091134580c070f050f05001e41080b030f0007007264505400c00e270311480102e9400401401583d0f019942c05a400c1c0e5014415a0340300103e840260340100206034000c100035001445005620702554895512000c1005000c10750008491420410b50a125400c2201c80c4560240075410014501482c141d07503100318003d802d04600c0070980040c0d4513032030646404e070110302629030403c4a0000d142840780d1601310003521000d015005c2c00c0c100d040103011030420b1030140310712040c07440c4400310b881d07841501b858901c00410545400b120f00c0e500340b08500076028280c90100c56616040320710005401c44c0c541e0b420417000300080a050380a03075200700c20741d0703001c400d80040d040880c40340c60b0795105810301c3e050040c40102c1c00c1c6141046220005030600039402441c82200b0701070701189001c205503034440c08218000321250195 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 195536097 1250 195534847 195534851
    0x40212150421020705040b0a0509040303020903190b180115060c0c1e120611030a09060e0d02030901141b0318010c0201080f040c050306011203030b040e0601052101 72
    0x103003806001401685010340d100e00b86a4a40c641c45241a0b000ca400122000c00903030040d000401082c2030540003e40120001040c00d4030040c5c403200024a6400140d0307094000a81c045131400150408021005002c01400c01e40203c4000c2d036a100317100d000b4000c1072044980b4040c44e1880903150250094005c210b101ca400302c01e016140c0300020080340c2c2c040001e450b03200c808038002030180c1e0401910041c0003100c4d070f0441841c60402110380c1e48059000790444903150f8800a8500441c00c6401a5002e02c0c41000041184512402c005054600c4414000f1150f0861410701119940000c01c0740c0042d02c0a007003100d01c00c289a00b03100d5550282405816240403000c07000f84150a021008250390b0040c8445100480449001150f40c0c0c071110700024007183d00103000c1080309440344051940540300d2541314542075152800709041ca03400b82d004124128452280c1410107800d03001d407802c1030340140c0e001c008030610103c01e540e4412041c45000d010314200c0c420701090310b0750a9545020b008100000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 195537347 1250 195536097 195536113
    0x501060e15060730031404051c11011e0b0301150909051c030b031c0909110c07080106050103140c030403050c190308040201080610090501211109180108030f03040212 73
    0x103500c1000f99814008030009160206c601c00040b8140c8049019581250081c011252542d0091070303200d9210a001040c4441c10400c200051024082e03001030034405040619407120003002001562801440c3c00d110364180366420300b6443c2502d00117012109100c0300480c0608680c2803e0f810850000521258081c840c10720f41c0c02d15406400200d89080180c00700c401c20b28584481c2c01e44c0a4030b085000c8002101240100a0015a904100c1d540c0424000440c40e0032041c8080904e414038a0b4014401c0340d4640c28204110768152145805402c81041030300d1880c9070405004983c1e100081c8002c061100c003040d014840b84040150043c0c0e203550b032071052400044d40c10007418a04045500b24001605200020942e003081c0480c4440031280d0345074480c02a003000019126552840440c802881c40c00380e178104805458060215078440e034090ba5030380e4070884410f10000e801c1400b607441d4050304030401044145400421030382208040c225058580e110362001030529150043d9991007841644a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 195538597 1250 195537347 195537413
    0x403060f0603021002030c1b15030708090c01020a021f050f030906010e070507081215031e010501060e01080106030507090e01090c0f021605010e1512040501060e150607 74
    0x201c420182c0f402100c0204908800100403130f40c030310614001c10700c82d8210403048284040a04140c1c40020301c01403a6103100407107641000c1107508112191800540240305000b07400209110303695040201b1300c007400d840e02054001c6074070384d075410602d0300210700300c00707003808030741d807081040c0c806041c1c51000d200d0382e0303040110405c0d40c4c4803000e0140e01e408002e41c9d4003140c0c0f01405a02114245a800406541024500511000318110081110102060300d200840055405019007126801c0c011140d001d070114001c1d510b030844030140c00030000d104809841c41c100303a801000701e6044071018a80802c1655900c1da085641c290264803801c8c1e007100b54000414420305a4205ca1211001030307945015103010b91504a82c0c0e40980d2000e1074151541c0501400030754825007107084220b0020340141380600380840720703100c2da40c400381c6400f003040d10500a00040040a00540004041c140c1c4040840d04000489114043c1c05c40d07001c0c0d2203a540020000c0c20816070501d1010220680d050078416001421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 195539847 1250 195538597 195538601
    0x11011803170603010c0e0907020f0d020a1e0f140a050703060204060f09050609100c020319120302040b16030318060c031103010b0a0c03020f010608100501090e10020f0403060f 77
    0x1080e00c2088030070001400328101449030b0400d942040e035070a20b401d21500301f80a400d58010b0005411070080b1405103286d0307441080305841064180d801080c4150490074540f10844104050b80d80d140d00000802c0081100d54070620741c0b06401112801c0328403c14050ae42c42d114003180000d141d406003c00010902c0800e5001d8030455010762100341c80c08000031403c070740c1c4c0c00003402501d0b44840c0c20711491032513080503c080d4842d0740a40c21302502c104803503000603142407000c50104501103038603200c20041110516224101107064141542841c0c240001c00d0341d940a081944e9110143c0c403100a07092500c660170601007180700d03011a0b607040f1050704000e00540b80b031380f107000080390903c00d941421524901c00c60307040b98441c141c4941032140320203040702c6104940d5016070440c423a0748292500a00203118401c0100303c00301c0280b00c550001415002030b614141d1241c1c070158a03021402c42c0c035202c0802c5040c40030089040040c2d50790a090300408103409140c02c0a8400340c581850440254020303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 195541097 1250 195539847 195539867
    0x60c0f0706050a03060902070c060305090106180b030d0f080a05060f0409060b0118030308011a1902060402090708040b06010804021f020303011a0f07030c06060302060f03150a0b0a11011803 83
    0x1070344e050000c01d4031942c45030140d20410200401d4000c10030002c201d25842540f105810041c44000414140e503100d0141d012000c1201c040c3d00c4195940001990616007004420ba810416060000c04180c03611805440004004c0c42c0802040e100c10020303d1a0b41da1150301000d0160080007040400090b0030440c00801000c000580417410311b003412640320074034542100c11280c0c9581d940c0c42c0c6a0070403804904804919455140d002000d10000510541700120890170b03a40940c0181034910b4a401000030030382c0040d007290140300c458000d01010425240342c1d15070084003820001402d486030310202d8018115003031502c1010401700c40e1b66460941c040f006504945a1800d5a042a5031102c1c040bd12845001c14142109c9000c0000301c000031f0180400402c907900500c1c00261044d9290086841c80c1d20507a400c0c42c03035000c0082000041c10902d001044041000e441d01c01540d82000c42146140c030a2804900c2807007000c0e00e202c141200c0c00d4100041d44a0025460808440c041c034000d0320143c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 195542347 1250 195541097 195541117
    0xf0e0f0c06040810180204021612031e231303020609030406080112030203070b040f02180108030d0905101d0706050c06010918050601030b01080c04110702060c0f070605 74
    0x954064900185010300036a4151116400900700d003400c2420160002d01742c81403281500902c401e898809031350307544040c01020100740d608021944040c50000200c0030141640400e0500e0300e03600010410040910702158940f200700068540d10210007083e40b403014051501101e4050410010880c4c003a12882042622980843d81c050b225030142c1c035281c1c01140148030004408000421603606000f2040112038001d006403444c0a12549542c0d42c83d05040300c00307aa07107030a04141d100031400c4c400c290a08a0381c0080c00c0101c00d5040ca85842c1c1c0f01c0c8100002c541c142511112281c00340102884504141e05043c4410002c012022901712209051400001c14074000d1001c000340160207007044030344009101c009004503038200014030009148400000140c0390940014600240c0d042001501071401103014004030744c07604d124a4940309901082502542c140303610351001710040030656040380c0e811100799072590040c0040f50f240800500c0c000f143d5110b65940020000c2d0040024040411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 195543597 1250 195542347 195542353
    0x4090212160504090f03080c0d050a06150c02130b04020c1615170705070f140c120721050a051b010e040504030c0b0a150303020309100906140d0f0e0f 66
    0xc2e44804200440d01003c0b4080c0c004a52943d4542c00a44104003039580080c2c42c040c0c0701e0500c598451070100302c52045a030f10740401d07600d101c244040403201068028000d014503041c544802564085862008d4040c605040030380c6540d103940302a5500d40507912240ca112048903402d0084110314030564106101da1802c80184030640004103100d410b002e6035403038800400e1421500c5521040f1041e900c803641c00c0d0340e4403100441c160000b88050700107075005c401450092401e5039441d0304015044800c00391011042c2d010840030020201c640094960102c403288110b4044c902c241070650074019a0362009085000d4105c0c820a080b00c00c0d800810075800070380e90410148000c1c0148030807070340255005000324840c12079072400207903500d59869026115040108a0030000c0001007104602070b001100542c202044044e8641810340fa54000c4005d03c2c47c0c400d0b540340c604030019241c0219103004442c8150005603010065007207400c00010301d41e0401040180301820501c0b240c80390200701000110340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 195544847 1250 195543597 195543599
    0x71e1206060806150a020a02060d05040203070503011b0c05030409050103050709050603150c09040b04060f0911120105010c06060f0e04060506180c13050d060c110a0809040b0409021216 81
    0x151054907000d01c02c3d0340c00f811841400c05102c4581c5982d40108514004500c28070b1722007001a102d031000703003140031080030020411b8105841010b051a47e035800a5009130715150321000c3c400c081003290000414141468481001d03d4101242984643e82000c00e22a080c41c00000070454000794980869448040810039515184209138550007000b0b035a818505000700803882c0d03d0784242c0109a004001400020742c076040700080303800e540095103c007a1605007100f08108001d11402440621401c2040c40c6203449004462102c16a1040c001c4038104002c01040740100f21003039200d540680f803055050428280e817040c0a080094045030202e030f03441d0501010030081c0c00d00300803055030352191003140d16066861054484040d013001072a0f060340c0f525640d00140c180c4540c00c4000015002d090040303191180d00101a00111691001040d142c0c4000005004660b0742c0c0d05845215000b00c4020034841c1c40040041c002e0b15508078083d6003e41255402003640900040e10214072018003003c241c12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 195546097 1250 195544847 195544859
    0x5071e020c06030115030209090405030301090e06041e03140c0a0c08030c0604060b040b04020d090506060a150f0504080f071401021603120c1b0e060901120308071e1206 74
    0x80c01e00e200025812400c180018054003c091a0841c5528005e2500509100d4039400040c02243e007502c0c103a4903a000040144071180141c00340018102c445c078010204c13801c2503078580240007d415005140030400341c1514042602c5000c0051075141c0200607203442d610201c440300c2d02d51100d0b81d0204c2d0703404042000054001e0780070041e00c0d003120708603000d41020b13503e40d10f030000501000c1c0d0029902c580c1d03402514285030382c1c40c8050070480c0b1161000251600081ca052441c03d4005081188902c21041041015020000c2e11512041c040d1900f0480c480c590942030321140640d402c0300006004a00f2440020040017444004a9440d1140201d552300c0c1c0d40c0042e6200c1701c4003117a50981c0b10090f4401c0c008544a030300d840b09071601c18a00030005000320b4647c010401c06400f410340100801240401903881e0009649412100440d07400e495035250104c02ca00e0182c0c070110040031b024090300054030035070003240c400040c0746007222804240c0e0301441c001808404941c07800780c00030b407500c1d1002c104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 195547347 1250 195546097 195546103
    0x7050a05012a02100b04020d14040c17030703030c09030c03050606100e0a030206071103061906060801060804021306151101140103050c2b06050f070201050402011d0a0905071e02 78
    0x100407803940250000713103c562680c101400341d5000701c0741c0140e0200310f4400b002d4030360b00c00c88c04001c03494400c200f00d6061030303c0e040c2e00c0c0c03c906512013041c3c0a0305a4041964400c040210745105500d400c0c0007913003104400007664402c10326800179007951048200041408400714400748105000c89050300001e9010a0941e0820030ba2210181c015180c3e010900c010300300700c6c0c010685640030380c1c054441203441c07100003490400115000c1c60f1004a041c4844c6c0c41d2440ca01466001d00303914241074040d0360401da801840000001c0002c0c0c41a001d10b5504000510310341e204802801007420b800500405140300030300040209402c103140e9620302881c0d4440e2844003141c85050720383c0040900001603030702081000c20310340100c40030002100300c813070506120101d02c030701280e441c0300c1e42001c642e41c07520b903100c40c0d41e1940003000101907904100070400181e86c4110450034216441449a800c20440000720700340e200c04d0f8104d4440303185090240007000342c010750744800080b035a0000443c00c072058041261 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 195548597 1250 195547347 195547421
    0x1308040f140a150c0512030109060302010212030601020c010309060207060c031d0105090709020a12020414010806030a0308010e090c120a0c0f06050a0e010e060703030e0c0406120b060607050a0501 86
    0x61001400c050a0309a1813084040107212030164085480610034148901859407080c0e000607080d9580c0c0c0c10420455030180031074804000864401400c40c40c1040000c1d480d0311024070f08604055035040041c040100703c1e81661900c64200c00100300c076982a1101400405004050f00845001c20980c46800c250501489100b0304035003024101039403901e401500a03410504801090004099456440000c148041c00041551700f079840e82c08020030001408881010303000c680039800405504020035000030ba1541182d40d1803201a00690311310700c48038185980c2e1451550f2115031010307503880c21540003c0038100940150001d40e0081c4c0c0e111090305c0004114442d036000303e06e003405182d909901032501e604865606042034079840c036204002031019032005200b05c010941e10b04080503203500403c0389001d90b6800340c0c0d007000900e09058003640360944841d0014850f80421000030301c0e94072441b05542c41c0d55404811610006403500d4110b0280115440207400d41107401c0c1d11002840c240e4501c3d007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 195549847 1250 195548597 195548609
    0xe0105010e180303070519090803120403320a030e1501050a0b030c030610020c060703120606030501030f060e01061706040c05060f0702040b0d0c0e090f0102031510170703020a02060109060e0c031308040f140a 91
    0x41b01000d418611034172160451500cfc8018180d90708602c8030b41c250144481d80301c6e4007204464291a41c105000c1140b552a540c01114040300140308000010440b401100e400030400c40d400104401003602c101c1c6400340b80b13400740c2c0d00002c0100d210002c0540000000130340780c034241e9043c002d8a4a800d804c4089400910019240004007982d18020552036030200070015000310000c1100740d123480d00b26140d00e221403031110443e400700d010081403141e80c00074840030b0542210038614000c03d07004619800d005064000e44569500c2c0b5140a0030750320800140c084030f0340038200001450781d5484190001c07504891101c500e00601c2440a44801d041c4200ca00c01c01200c4d901a400c21203007010302502c813046031156014007081170108a54421080c0c4d0b90b900c00c0700c40d07640141c0e80d001c0d801802070402c0c01c1030b1702024070982003a00c1800302100504041e5481200d50750103035160f540d400c4c0c49220016170750750050415980003602050f1502c5d0328012000381c40e5040c030f0450707124003c4420300c142d6807103500c208 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 195551097 1250 195549847 195549917
    0x718021603050f04030203120a030b04111b1e0102071b050d0b06130f0629030c03070c0606030c0509010b1603050d0e0105010e180303070519090803120403 68
    0x3400080d000d2005003052074016540641040e48a13401300b03243c004002c00080c41b1490125100115030740c10302410501e484107882c1400138040e9100c000700030740540d501c40320f0100400418080940b00030001070001914031581515002c020b240b01034000e41c405142502c0e9004102703152802070903a81c820304111600680446d0704000180c07241c4201d100e02a0200e40c0c031000c418004c076105901406101411003503894002510703860324411071502440741c00300e1042c900000100141210206064a503c40381000c0c0b038981c2d035907903003004450400150000500282c50924040240100c4501c1074065502c10341c1c00d800b26980b00c1d041980ea0380070700400c1c01d480c00312074000c000c000f80c4505c001e84580c0210020105003090078607440c50940d04c007600700041440d8410200300404400d8542d00742001019800365243d4241140003c0c1180b09491130302d110b0304141040700182e03510400d040401080c0210a43e6102c07140c00011445809040d08c055001074403082c0710005c0d124640b8000200c410590700c0c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 195552347 1250 195551097 195551137
    0xc03010306090c0801020a09090e07050d060504240e2a0f0103060504110c0105010b0f0406080702150c1207020c1323090307050f010207020d0308040f08040602071802 73
    0x1501c0d018242400048905552843e0300040c04042400980100389a5807281000f01e400c1c0000001282c0c44003400841d42c0d480007a003003100f03446441303031240d031725070004000b04a0b41d0300c4e400c100c010000c3c400300d4003260801d0038a40541041544d40301010f03101510301a40c0e143c40840440c0081081003010140c40c910714044540401d01d0412481d5007100c10604001c1400f81d030f1000054111034182c80d0b00d1091200c005100f0340445400c3c4901409807518501081c2010300046184c0c8190081c0c0c0104001d118421003c01c1140d4002c000414070b0341381810700d07514a881c000e0140b02807a045046003050413914040892040c50000c902ca04a400c07020340070f80c00da4444581002c8c05020f1411841d109418101c5181b000340c0010386006116002c26070003036645007140c0c54090b00c1c202c84040044e0341a441400008010b99800300014040364040ca8005000d440b00d0404031840d5981c910001e140c2200010009100c60f000b052020488810040c0061f9025901d0701400580c40703071501d82f40196221a031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 195553597 1250 195552347 195552353
    0x203031902300c0f010e0312010506070323070501020316020f0a03021c050403080a170109050411280f06090602030c060a0c0908070915080d09090b0f1c0b07080c030103 74
    0x2000c3c0140061240032140d244500b04106801c40d1004d80c800c0c2e0040e0800140c00841c041c0070a900c50041105032131280c43e1502c1c07900d0003400004c0780c1c40c0707442c01c40f0035aa050340e6084890000340c0d2078068002c40219905d05104903582580303c05803220740c0141c01080d000a1613210003003503154800b601600900703000c8a204204000c80d10002080006001d0240404404162960007070500208151114500710b000d243d0f010700c4184c07050344203540c080c1c101408c210000302d03000030345d002c0d403001a00c1c000c8204415074105c0d02610090500d00e0100031103a0304c00652440c2d1014a44111581e644868520b00c0d02c2c0c2104036100d01c5501c4804005510450104088200c0c590108c811540395281092010b81c90b1442c1d581400941e5215144203521a4107505210f0801800e1400511004000b84441451030001910301c40c09403040c2216140d642c0c2c400e81054031410001c80b08004010494410082c402c03816031042d1011900540c1d0040d04880001c00450144506a006095034494542907a10f15a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 195554847 1250 195553597 195553693
    0x12060e1f0e1e010c17010303050927100501030c02160e060a0f0b0c0c040c0c11010909060f0e060103140411131d0c100e01030e03070203031902 63
    0x124154210b07200d0b0002c5124240141c00707604a80308919400401c000c0c2035188020039107400704a80030b040d50040001000000d8108048680c0c264098030f0041400e136000c0843c0030880441d068100065004030300b040003901006512030b0580c0d10036241009801c0b2982812a625030f1706007811441410b50450030b0040d80000800160310032001019007059075124038064010311081c3d40300346400400851441c0d20141e05020407020340703100b030b50204003540e004e20004103505000700b00501101402e901c0c980b100d034440c003605c070013410441d0002d2018a40d60303400504080741c548102c40c9000011380105e4a20b610078042ea003411200c0344140903e0307444944402c2600b58200c9601a40000c0c085100202200b090086800e4400d80035180b1041201000c8214140400040c05910a504001245514681100c0c0394181c0900a20380000d1041e41d541c0318034954441e4242c041d62600c8041641c43c070740c22401000c54005105582544c1d61500c8490210b2880b1381c5041c1c442004038050007110500c2a554 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 195556097 1250 195554847 195554861
    0xf070f0605071707020d05030304030305090a0c060807110f030904060504110703260708040b1e1305150406091506060e010e0301140106051908011505160c12060e1f 72
    0x2800c1c40f649801c4d0030303070f000a8403400700420844641d0004400c21050680500c590740c2c2c0895850050080b01b805a0758000080c00380d03008174014007240e01e0200d1095803080071180c03048541a011a032203002c003070119135503c0d006040b600c0d2280b42000c2e80400d40d81017074010048141d2070000c240d4100001c90b98103803081c0e41c161a0190300941c8010b07089000c4070f0300c1010f40b4010700341380e1603010140c1420b040861116100500e810101302202031504503804e2144142c6501500940038844010500d240485c14400214214111110381c0800e11040c3f0590342e214a010612816028620012503001c60090356010b20941c40070410300340300c6812650050300d90b41c16841e0014000604810f0400c150001d101c4283c105d070300003680204400c04996000401e07554154400c0c21715040d1989010411100307400400006d1007049800302d00c54140c224000141c0da01c50f5030104482044a0b00d44c218014002c19215055403007509014818288040209a04c003500901007040e0101c02c0f04080c4c000c02038240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 195557347 1250 195556097 195556133
    0xb0a05060a0305220c2606040b060111030d14060102150105060702060c16090c03090c0b130e150a0504020405011b0510060e100503060f0412090e090f070f060507 71
    0xc024100306401480c6110030f003014811210600b84c24200011040c10f07030f820f4840da1b0181c9400207800001c081000526540c8540d00484c0b9090564924004a0b51041c2c06620302e5054400400c0001840080380c100703440c4840b1882d841c022542d01d9000481c0c1d10035000528505002a0400512143c00e0400080040380c1c006040d2070301e0000d281d8841c3c6e24014118401400c2e02c05403400a025842050042c0200ca102904d020302070340c41c05403030348040003103a8446c0c100c40b80740004010700407000c2c14241e070740204103801e4404000d251440e104a403404800501701d00c6807000724070103c1d8504d454404e0740c0642e0750694900745500c000d181d9038420040d5000050342d15210380000c1c40032501d96801024003422200075080f5a0b81800a0b00783c08580c101c0c0c0216109070407100420581c0013441c4031495126030486146602c903643c521064516010941090740d20022840030840308050000358440e803d0345800443d02c001e41e440c039206203000f68601402c00068010400b6401240320f4105503480044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 195558597 1250 195557347 195557371
    0x70309020604030305070303050a0219080405010902040606090e010e16050a0c140a0b0901090b0601080a14180d180501140c0313030c0f080a030c0302010b1801090b0a05060a0305 78
    0x88240c00090154015a00440020780c001804908240d414050710340c0100d071117842582028017090144001c954024180c1d01007080c2c0100050910800750040025960094010020300c0e85a001c01403045806009042000d0308000002800703422141c1c0003803183c83c01350208078210071020022a12036000000030820000d286d0b110f4008035984c0703082c0d20b001600400051481d00781d00d1501d048124801400d13030309140d01d000220b0011414000c0081e07880711003481c007001d43d0b90300c09000e40e001b003505180c0c40201c291010204131500398802c0920758180340c141d08848800e2403404040f0f4022050440c405048000302c0c10070021540941208078003500d03070800c110b0401070b0701c150152440d0010400c1010340030208608005100c0802900006032100300c0c0c40d0380382c2d40e0511811076915420050300404000201840c801454400c4d809280f0185004148182140c50800a051000d50070302a0f485a240717081d980786505d141c01d41410045640c05452141400c90603403041c0c005241c000c080f00b000003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 195559847 1250 195558597 195558611
    0x9060a030b0f041d0708030909071b1202010501050111190305210a0204050a08060903120c0c06090a021018051003060e010b040905011a12072024010612050703 70
    0x3d5281d0080c1c9000e91031540944080c002c4011000303160401c29440342d616608104610072180d00c41c1c1076503a500003c0b13400c25500c041402c0c0502d2495140b1a9806003403801d0303012000d4040d95040d0033160403608241e95480081564030036540d11030302c0405c80960540c60607030345000003e00400c040c2800c404d1204001c8054141d1402d0160081811200300a03104c0e40041e00380814604150b1405c080e180d03220044c0390b140342c05015642c2c0e81c0724503140c0c500c20300c0e840400103610656850807036005251000a44440c0e0030f0500d00240d455000d500c040348141b0030b90040000d114401d80d07801f10031448501401164500c1e00061010503070341c0e4103806080548400020881c0000140c0582c002e000b402d40d440c0da1645444c00d20ba08030741068000151007130203901c1a100c042c2c1c488003520b07541110003140341c407961147c840950f440000403002c8055503e0080004143c160003040d075148140c40c4c680503400180321403d6080c901d0364240641c0d07002c28640841a80b08240b982c0c0420303070201e01d60500141e80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 195561097 1250 195559847 195559849
    0x3010f0218180103230a0818011205060307060503091006061112031b1305030613020f03010b060f0a030b0a24090501021207260301030209010b09060a030b0f 69
    0x664440d010903410900302000e902240d040881c01042c10184182a0b481c82e541144e45550b00c440d0340e0195001d0250a4850500b1030881c28400460b0440e8031000c101d540380311410351134150340207002c10603010500c42007116840c0a49802510f1003a54028058000c982c100030301130f00c081c0c00141150109200b4900841c0342c81e4020711810002d07000d15200d210f8001da004010702c2c90030700360900070a8041000d10a114400001e00701d040c002c1c00d10884420344600180c2c08003043c0e03c10725802241d00d0310031901481a1042404190940d0900030390b103420070f14003040c0c2494243d030301390760400c1d42001c000c205456001c85844003418081c0203a00d0042044005440004c05404094020f24030000b24145080d031003084082006008102600340b20b07000314540000031b91907810034030103815a00c400142070000c01230441d021803090068a11aa0304e0740c10394118000103600300b400300304c0c000c1c940c40d80007242205070942500c4010760010041480d0041402c4118058000005155004103c04200c2045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 195562347 1250 195561097 195561101
    0x100e060403030302042301020d12090507090b040b041b1107030501020d050f06032407051303060e0f07140d02040f0c020c280306020f041203020f0d08012303010f 71
    0x45000f50760258441c1e043c41910329020060b0340480c1e0b2020381c62468100c030b5076004220f034200d15920b828170400c038441c2e81c5e001c4c0c4041e1070b04003002407550080c0440400c1101855101d240c03911029a8100031203640107041c4070407200d591900799226699002d00742209481035400c4006640b2400c01e4a01030741d0f030b0307541e010700760703040034000351034083c1c4034800c21914501201c82c440d4450f00c124020030032400c0e01c00241d02e211008507079400d064180c1d600040c154a0083c0115081c4460b24500d00300718903a0307400d0000042045481054240c0104e14202d030300c4800000750300c4103607a282481d4542d5502034038204001c0154101d01260019160b00070b40c0b80303111341d500c00c1c0050740d03410707402508504448104015a807105003240304e1041c0c58140200316850414090b180a49501c1400140c0d01c68000300d1042c400d0256501000e100c210750000d020801d035000c521402041d298004403600140c0108040d00c0e1070400340207641c0c2c1d09107140781a600c2400380200078504c0d0380c03001d4000207888d6054886401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 195563597 1250 195562347 195562349
    0x507030b150a1202011404080f0708010f06080d030f0b100806040b09090a0803100b1c06052d0f090a09020108060906061b10020301030b180a080405100e0604 69
    0x50301969401009551051071444012441c42140e001c84802c0c24012400c01d40000160040d04104071a811101c5030140c141c104c0d40501600c0b011506503844540c003c2d03617500e0031030040101c3d6500f040c1c035035a03200f006030103040b00341c800d02405000342142c40300d401c9006104c0074032481101a2030701780900040c0c5441c0c41c1c01603110b001da91640020300d0942c0901c410b542444e201a800381c0407800401101d0040450b0094090368400178103981d0f9141c140040300e502c8660342020006403000610f18034080405003400d510018502428414150fa032300801840c40c6915100700c4490400118100540e03402400300c03a0440070041c00d40b0451550794011482c180030451301a10400d0755490204290361700600c48944c4408100c5080d199450304501040f007030701600790340002030b02c214aa080702d03440301400380710001c1c5041c07070f421512582d49040901100d482a200541035402442000400d0b07000401e00c03040098001e2040c1346014600802c0c4100144289201010040e214200ca82d95a0361000180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 195564847 1250 195563597 195563603
    0x5040e0a020a1d010912050c060c03130e07091214060c0d06080303130f02120a0b0612210d09061802030c12060105011407020d0f0b0703110904050603030403050703 72
    0x180c0302c5042420243c1a800704142d500a40700304035614003000e070380c4190540141c9041210b0040801d1051500c98a40980350103c150302440200b078520789600000081c1080c103882a603a840c5503655801031850a1b04103481900010392140001c0c401810b24103451030720b81d0704ca00e00c124203240740000101c1c00d010096901510307030480020001300d00040380c01040d020b0190745020798a03506105254003040e5420750700090408054010200170340d6201c02503031003501801002e0302c010042c1460690003004088503001e100c0c0002c1400e03051140c100081c901c40c40c004040072100d030094085a840b07915000308002e01c503000c1c0ca40d082200000d065005103080282400000c1c5039152031031040500f02000f1444c02c6004620701c0c0c1c8103c00340030000940c1d504469082c01c0090040f4000c0580412034854160041d400c0140407203048100300703180e040e1140e1070303004510a062540303558400724240c94159031941c180c110244440300561038541d0000350440d200a00312490183e0300da0f145820244035603c15 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 195566097 1250 195564847 195564851
    0x913120c06050c09060412021807170705040e06042004080a150513080a0309020d1a1602100b060408010e0f06060d1713050604080304090f09030c02010f05040e0a 71
    0x24030100852401a20f42203c507141c0c06504002c8100086031050040d44501c91545031145000340c25501d481d407240c85080125038850245190410025101d022000c5036404c0d840e56410015050314403490a50382a01c0c0700c246103440903100e29040101404032207144e601d070b80c200c13500220705600b410f000610052101c40302500004400d0b04182c1410301301d82d00300c0c0301160300b08000c00111542000054035880d50042d034054036050451030840007082900301c0250801000c003c03100610401681124500369007020050880e0740e15007800d0b0705d140c414044640964401e6005103109803c98000c51488440541880d05040d84c41d000c00342596074803408640780d0340018041c1070426000780540740d409500ad035003007280744406030390b01c242e807d51607480005000c1d00800c2041e00011070501c030030000c00c0014885a1200c0e00d80c0327102a126800741c8100b41015207031010803a100c3c14103025160406400d0b4940c45407400795500152002550140030b001005020007002c0b50a0184140860142d0071180d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 195567347 1250 195566097 195566117
    0xa020102011b0519030b090a09062405040e010b03060703022703030406030b060702100f02010b0a031205030c0d02030a0912031506120608030403111503040c05091312 73
    0x19003103400481585103a260504040070802d50401c2c1181c4820441c1100000f02d22a5610102c0042030006011580120140140104550603400002960f40641e2081050032011065000d00c01d0ba1801c0c1910410f100748001c204604e0603901141090620f1000441e55002c80070000c3c3c100030341107803c80c0100c0e40c08203c100084901c402c410724105580210b1940c514a2213000968074002c910984082546800500b18180c44039030a990003181d000d06200103c0325500c2002e40359091310085000150b1800c0741080080c50010744007000c0b83d4011132520324585040c2c004a546a100810030760413a0380411604074a90036900c002c2d4414028003070006204583c9c1c1c40d080c0700508041104004050620540d540d100180c55034050869540c1c3c1410303070840020020450280901e580710040c03601002c98000180441446421000702045490b01c07100014601903540a01080d9005407441c42d07811018030207402e001c11066000020200d40103203890141e92059054030b0740d000c8840008081d182 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 195568597 1250 195567347 195567349
    0xa0204030506010b0c0616110d02060403080a0c14070309030f060504050d0e060901030e0708030f0c010509010207030503010605070f060c0c03080901020412080706060e07081501020d050a0503190507020a02 90
    0x80381c2c09043d0b2080600e240c001c000d03485640d60300c40034155203200c0104004c2d200415004602440c00000408c040d10109090780d44080c8d00c40030f00321400d80c0030071807010004000c440d9500c1341c40301c201d110fa140c014008503240b803046040d81082d0b40c124140400c10801001051101c18003151082c402c000c0415980741030b29050381030485d03411410062202064080311142d07294016110703103034009c2ca400140015580c1640d454484158440710341800b0001c4d02d800c42448880040c02c0c10450700c4028401901c0300a01c4a00300d110340c020190018030b0a00060143c1c604c1480205101801101030010004060b1600c400319000082da82c4080b503480c40c840c50800d41c2024803580c1c820400c0700214101444d000481c003512491201c01003030800700065040030040251710202c054a00300000d4501c40c54068406014175600352480100c0d888016000000d541c800600e41e012130b03089585090915415040a5038a6003000c0d00314401700c01c80280c81c901135109403140350f101d418070364010300390050940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 195569847 1250 195568597 195568603
    0x70f090e12030a020307121b110607020307031d040f0c020c0a030b0a0b03010221060109090207150209060c01090525080a0b0c040305150717060108070e030a0b0a02040305 75
    0x4215160141c101c0740c590500d4a40140641e0f40c41245248003590700e80c0d495500301c1d002d01c0303041801043e4134900060400688541001c4441000c5e468507401d102850703101c81749543c0d0740308a0340301006070300400c00400000c2c4101100b40d440c0c68400a940205c4a1080c0010181d8030401c0c890380280d07039034989450002e68100311070010103c01341c44181c1801d055807075020000d18010001e107a943c0d1504007a50b07040d00c0c2581294484201d600c03141d1004036502201010742c070400d41da0707a8001100c0180c0810084500e02c21564401d900c42101c0207000e2005068201030b402081e142e50340040300740006200c00400f8080c10198074801e0002e004003503802155104000d0140300006410804038900b40603130300002607400040742c1c2140030005540c1d101c1002d03c82c0c5120700d1f00000c110b40560b0810400615542041c103000380107030f4881d81c074520042e0764400c12002c0222070880c0080c0f858804145030a024038860240d850010f03056596111007500c075003008d2082503c465101e00d03070000c5c4c2041401014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 195571097 1250 195569847 195569861
    0xa0c1b121b0c05011805061308010c080f070804030e03030c07050907030b0d08090d1703010312050a020c12100c08090705010c2d0b07030f0e0705060a0c14070f09 71
    0x96a408203001c8515140c40c000d500c0580140760500c501e602904500390580c000340030051400800107556221450700e50040224588180c241940c200301501d5040e6000303005941c80740d103d10480b21890b54904a007214282809403007a410300400103188030761500c00740001c012218014008013401480c0105009088030014210000c051401030f5900c066074814510542e250380101d82d040d15145c2100010303202c2c100752040140628442007840306004100710145040700d008100c03040c0071011007481580d43d4410301d10300c0c0c0e0050304105400d540e203103442007011480629001c211280c0b8000c06403110101c401c012526008140b1400410020003010440740019000030320304030760000b1b9241d0b9210540500034030340090981c410301440d11b030040c0020f0703603240894000c0c00140b018106108050001c0840103450908a81080a16582100009003200844102800007807822280d0305040b60103402e040c004a40041499111410568080040c140501101481c008500b071410b01c3c140122044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 195572347 1250 195571097 195571127
    0x418030806100c0303050a020f120a06060302090a091815060e16050906180a031119150e01020102040317031e01060c030c050a0203010c03020c100209090a0c1b12 71
    0x10031544001c015441100410f010b5890304010070300361940ca11840180c003c0079545415503038003058000020821102184c003d810071242001500d0b10b0305000c4050380325070094a0f41240c0500c104008908030759104502407035888298014140c2d00d17035540100400c4e0781c030318030841c151610800e018400c854400690414209081c1d040820041c40000d800d9000784055070340302c1c40005c1828400f1a00d026450041f00c14010074110f065030702d91514045a405103d1130724062030113240700c4e808031032200d4100c1d4141c848002d1100c058951f142ca040303030215034a240060455400348400000120103001100540152883c0c490703c9292240301c440c0c9610000c101540c000f586c04004100c040d8000804101e090f81510b00580034201d2414144e01c0c0c1038118800035051361030142c50306c8407140c1c0765014040b019000c0050300d0020301825081e1050340506440268090718100100f40780300e100794007600019009c1c0c00d04080c2450400002d01402c402040d040e16001e0380c008244d80d050740e0050b501c4400d288 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 195573597 1250 195572347 195572359
    0xd091506061115101205070e0604021606020d060308030c0c0d08131101030204170705040b0d15020702040e030f03070305131a090f030a05040e01080d0c120e0418030806 74
    0x41900b40c0036075107441850008a51515107404149401002030080028103407000d4000c8259200d858102d81e02c6865101d040d28480c1c2c03100200342d2902c0c00340200c49034141d81c1c10f0914441c03903968480700c0c02580b05400041d200e0b0b6503010f00200054408002d180b01d22150a58039490b55200311581c0d04100d0404015070811140c241003203099010b207003101070000c0d00284040403079403691700164003d00c00c0d504034962407900c0b04d602c841040400620384054680980e000d00814603080180f09400040703c80080511450003444272011103da4041e000c2c1c140010008207154801049090a650010081003100d0b2070000420903d6501801807541000100c031054000e40720540b0b98403040010340034040d150f400c00c80b001c01c1380c0840801488498104000a40b9903038004144041c00c1544a0b00ca00c0004c41007071400050b1032000071850512420f2140c5070200b8442042d40d60501861012030a0300502111b8640720004d51a18400c0ca10082c1400e65104001d40c2103040c00307000800000e0405100352 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 195574847 1250 195573597 195573617
    0xc0209010e04081e091309020a0e0c1210030206070c1406072103060305010e03070b0a06050f060a1202040906080606090c1b0c030d03230103050703170d09150606 71
    0x5251800b11007000da250701d50440b50110f03110b40b140c800c1c03188500081d400703507503050041b170100216440b094a40e8800c6544400147d5140409000200304407050340ca00c1405200300d12103600b280d03411640c054101d400081015481c1d60001d80c0351341101d5016940f4080e18071003030181900504900c07900580c11581d10b8100745c6d4664580d412480c54002c13440ea82050b03c48010301c6140250440c0003d142d002c40244001d1800b8003480e680c0b034200c0b91040d80c081042102059000d80584501c606486000e4100a5094600c50900c84540c0c4000d0403031302004100b0500c40760343e0307a041c4050310181400f80004141c0d40e150000ca00d01d840ca000e440144900c024805006000a80c0e2044584640988182a500501c1411801e040c240c01540064040c0a0795803c1c0100d603616078003460340580054101d440380001c9810051800794240001003030391740708100a0010031042111400c00c05c1c051a401440c2550601c1c1282c07e0b40c20488007103581d4404c41c0300c8542c43d01c1e540d00075075025020300e00d4103036001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 195576097 1250 195574847 195574853
    0x50102192d0507020111010509100f02070507122d0c06030213030201180810150f030b0a09060204091a0f04090807020d02120307050c0103140105030d110c0307060c0209010e04 77
    0xc056804088420b00600080450459009961103066508203400820451404101058541c800c0b00a051402c91800d80d400c1c0c0350050a20a8611090700180240b0200d400d0803c0700c0c04640c5004800d9500d003400b40e6002405c4102d5450f0a40620303a034216001812045162001180304141c02031402d160043c0305102049100c13142c5141202d40907e880a58951400200040035035940c00410040c01020000d0100c503040b500000041208a080c40160b07a541c1d80e54202c0301e2001d40001400050020003080340c541c0d40741c0001c19150f0048500619141d52114403000b20b6a14540c0400e0440024005050743d00e081c8800404c9984281d8080c84a1070785aa108580c0e4451014024400c080c7c02e21941c042d9201c00401d03603c2c0412003011255644c0b00350525543e0b0b4080c0340d600d0b0380001c0c200304406000d0300003005118100c808c082c0003410002c50b00c0e02c01303461608110074001928401c000322a8000d5030704000e84402020a0740740d14207103101d80c3c0180000b4541c140c00c0103074450002d00c248800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 195577347 1250 195576097 195576167
    0x603140703050705040b0c030720150904290306010905061c050a020a030813090615031a0310150b0a0207060f0302120a0f1811010c080705010219 64
    0x101a056180c00540d03582c0f40001610240900d8000a800c950041070103442450b0000003012001c1c0100782000e0704d00024644020300d0052807143c103402440381950803044200d10703170140150480051011a05c3c180c0ca94030450000080e039801c039000301400440030442e00f002d102540c05880c002006010300d103840c0d00442d802c200109500f94001810b00500d105100d130502071000c1ca194000d29002c0aa980c90610100503000417201c00c0e15040c011800041c03004180c07007a44c045511003100000c2c4401e80c5030b01a0010407500250003c882c01403007407484560390900c107034003440719080d0300014070180c0000c0101400c0c03215001000040010000c0651068000a85c90100c2d0072911302480c041e841440300b140170f401400d00304a4601c800805119007009542c0019203201512402080a03030801540c41050400180c40900345241c54100421903511514140e00c160b80981c1c800c0d8a40b4517940d8844d400c80e4071501c6200f00034095440080d00f401d40c00164940d051075102400740400c58488080c0702 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 195578597 1250 195577347 195577351
    0x1509090c090c130f270507020606060d02090a0303081501030603052d01020408101407080a020904020c10060f080d02030d0213050418110423090a05030c0c0a060314 72
    0x8220b0100c1e01540e1500b01c082001e014280e4990030b10009540c5060440510055035090f080c00c40258801305070b00b410601c5407900c80c0181e0350050000f600c03151b0901c20503a004150140d803007a0204074049240d00d540c04d400c2e009510a50360748030f00c1d01d01189075044030280756800504150608500b04041080062400c854901c3c0705213280c401041c0c0c1c075210b5001c480d940c0a60443e54004100050b207040c01050a040d101c00c0e40805204100302c1207544504000100c030180007040e0100003180800105a01405205130050001880d10241120350791805070100c070191400e40e00c0d15824064812042e0051005051060042c03641400c240d80194490249958a052996021455003c4c50300d090000f0b200900c000f40c410444600201c020aa0100188000356a210645243c0b03c040f4102072080c00c401c0064640c2c02c900d80d81101980014040e4041d003000c0c0c81c0c1c0308141040002c540300340001c021ba0018000140881800d85007401200c00c2540d10850605280c9a086005001000b40441d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 195579847 1250 195578597 195578611
    0x1506050d0c140307030f110a060816030e071d0610020706140304210c060b0a05030c040b0621101509030201030e0f030a050418060803041a040803031509090c09 70
    0x48081c02c4040200c2d141109591010701551160b0042105101c11021180c008860564100c02000d8035180c0c1560608400e441e03260325082040002200c9a100354407a224a11100c002e590701c1a9035148580d414001d05008403002007003000511103d894110b404c846260f015002400e621071034490f001c1c112000c08101c241c00440c0005c0010104041080c06223819809401042c00c0c3d010355a80c000c8c0b038104c880c001200c5d4640b1f01500010301d8a0300080210403540e00600824140700c02c882440301400ca0000d0694114100303010340125a1010108940c040d404002640c040340342c0301c00c006440007140e901251130a542c0308503903112160b016103403005a07034080c02c001c1207070000c24401501d0000c081d03444079070900012401c81550741d40400240b04070748000c108195500c0110300b45400b200c0b0140b21f9116194003c10041142d0076a100e18615a00301440e89281042d42d500f4003103046500c00c50340580c00c2c80003c0c0000d00b003860400e1203603400035000d00041103a400b00d030010038486030016040b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 195581097 1250 195579847 195579869
    0x40804030f11040c030b040c02010b0f060a02010b04020f19030b132703030c020c090c04060e060c0a11040501060c0c0302060f090a030b0609160e09150d1506050d0c 72
    0xc090101442c40c590300202e010b0400c01c90b411110070000c000b01a07202ca0284a43c2c1000c0d0700b81410342c0b050003002d0341b1031002071000d00341819a10030404180e2103440000150354881c65104141d503154405880103811010140b55244440d0100e014409680c40442c4280f62030b00b00918425141c0403402c0c4402c0c8401c0400040c400742003500403d11000c10350003491018404a409010198560405c0001c0f0255408880000010000b0810140030441e01d02c0c2c503103041408104050f902c100d20300b0b888510040c03c19494000600c9585060014105043e80e200c00000840708060415108841c010b0410b807908042c24985a6201c1e401c07500548000380c418000810343c5503000200104440d440d040c02440002e0b1250b5910b4403998000085445600c610000c038005170384008050415002d50b05550343d42e0003010403260410400b4a009000507031a28100d210004160301c0780340c00b0481060051603a15050444865600d080d50781e1034001900400e07a004003e00000e095503012401d44000d1141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 195582347 1250 195581097 195581123
    0xb030112030c0305090402031008010608120702240301080109031205010b180a21230d0f0509040603080904060f0501020a0320010203040827221407091d04080403 71
    0xf0864150007404081e5500c0b0740700100384010a10207212103c100c4451f41c000340211941c41c04107039280c0340d544d020800ca42004100c254014502105100e441c800130204126201d42281c03009500d0b60030036042806141c2d542c20004c4207054000540d0100c02c1d845803070500156041800000083c0a03428502e6580c69007800740031441d64401c2001d202601c0c1003c074014400411b8031001c0301d00f40c4c210304c040d81c00500e400d5174004a80411401e84c1c10001c429001020312201c10141201c41103848402d0b10100001400f880d8003030741d52805420000e501130301100b600c506446040000f00c0314598084070428513449020040391b40c020132022074958050030300d0400b002c00c0307100c4170301c044441c0020010030f54400400c00003081103000152000507810403820405030303a05134240000034818010280c2c440c10144010442d00ba443c220341d0051100d03c07101140703014044007942c4545100b0303103121020442405041c00303102ca140c0c1104180c0e40c04000b14991030b04107038840c48684e1046000c02381c900307030040007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 195583597 1250 195582347 195582353
    0xa030905010c11060309012301051513080102161208012301020c03150f0c0304020f090c07210e0613050108070c0c0902030601080906040308062206140405010b030112030c 75
    0x65000403860f40606819503902e050700301c45008080c40910310b8681852a60140850402e52130310b03505036440034000c9640c0c1d20000c07102d0401a0454000380604603102840800d40c980c0030300203404d03140c103084254030840706603180956610203241183c1042194441c0100039503441e80392003501e41071b00e440190000801300720040b424141004942501881007000003011901c1c12146603104110300b44030b0740d02c00d440300501d04880c4c1c031083d5000395104010504002e95445c010009942000d801c0d0b40c150300d8031040c0e0b41c47c0d98002e4102d03010300400200401e4003607410780d0400c60fa0002440b0071604a860000400c8094122048a00540341041242e00021703206074002c9200e01107080d0410f00e108111030307072280050007a43c021142c00d400031b5204004903414840000d0518082c0740e25840e115010b9031018248841754403a41054005020462607180020303040d4400e60001d080a4001c0001c036030020f5060000307a0340181e0184298034020001000b840410b10503a000c0f085e454982085600c0d400c1c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 195584847 1250 195583597 195583613
    0xb0907030b010e03030301180501050108040807031b1b05010e030a0203300f19050903060703090303062c090c09010b0904020708040b1e040612050a150605030405010b030a030905010c 80
    0x101d10f60380501c0000300101d40b01d0510703441107008009400041c0043d030b172101d0046410920994009006101c14002000000d0241c03141ca040807028185079010341080d61103044e540300511210344800756261f001030206503884050094504401e800504980f98a036010a541e503050206c0321800480032112441c6100041302071501039a8104d02840d210207030502c000b0320300c1d480315400c6500721405140380744000e8010020f44030040c1c401000340c075556407685825000351040400803000c2507a20100418001401c60380d00b820b0000f130405021014800c840c03108141d02019002c0b4071254002c8169113026510580a00c0c1512000740c4807d4482020b4404980607000c1c00f0b07070081c100d1002180200d50b1400c040054041c484901a242845c09051068070090744580d0007080d000490f001000b0706035842540000f03400004050001030850a0300403070030745401a40d0064030001d07400205102c2400303000d026404400008401a280b501000d550242150195109603814800d031a0036a9090004036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 195586097 1250 195584847 195584867
    0x9030403050102300103081801030e030a0909150503070302100c0203060403030e0d080c0d0b011704030e2701050918070b130e06030c0607021518040b01030b0907030b01 74
    0x21100035510b07000011000161619600012460144000c03140c0e86602c04c4003a50f1412a03804c008001d14016014078440481000c0304802c03810725458090820b442c8a0410040c8140402550380480180c2080504000e03902c00c05040c50380b800301a0b600303110a58022030006d04803a81183c610a40e4443e0403026a50000581d1001e9454041e1400300b0090541580003020f250b00c04500b941d8110360041c0b001d980385181034a40d445c0804060200c42d4105949034080e045041c5e05040081000c9000c0101468107a4211000c81c001050041040043e08044183c403081c0c8091411107a00d01e607020500c64100312051003494420381981c000f2030078004411070388111101c82e4a0585d503002e80c4481c102640ea42c4219107008000c90340c03080000300078a0141440b805400000e0140038140d500c9400c000c241e400a0038180e82c03049084030201c009a00c150b00800c1130500943c0700a14000300841088101c0e240c4000d03007030505081c201541b140c0e9941c690901e90005850800003104640c41004807590284 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 195587347 1250 195586097 195586103
    0x130605091518180702072c090c09160e06071e050105010e2d07180e0618041104051009060909021003150e0712020301030f0203071a1209030403 63
    0x1002500b03960585a12403501422802a1420b0452401980c0301c00443c8004641c0303100141c20010090200b100c2200402c1c240d189142c0b11700944010780c541c500c50381d00c81520103115692211103640080e0804841041e400302c05000d996660402e17800c1d003d40341078401e40d480d9200f0b05002845404000d00ba00304403a01d2000554031403004901403078214001c00b42805101609010140090911608103060303464002d0f174402128080962080704010340c0c070002d41400140040502011000d41203440600001d2400780a20841410200180043e0402e8112900c85c901c040c802088089114000e601e500080d06440006160780d8002c030100640703030542c21050941d0b080c001c00140003e00c60704030400c80c5008071050a200a8031030819170440302c07201140142c07000c030365100f081801003029516612020702d041a00034100d0001c00201207a100741c00440f400c1d400c100005003581400c01801f0050940e14844901d960180c09541e0385c28041c0a1920050008120001d0003c0c1400d10a44c0d00442e8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 195588597 1250 195587347 195587389
    0x210212070503030a0b04054f03090b180d03030b03010f06050103061d04030c0807020324090f060c0f07150b030609032503020a15021b010213060509 65
    0x40d8914049031690b206941030b1300c5090516440a100c1c1c580342c8903290041000042003000e084c00c01035219291481c24803c00680500c1900c002c201c00e07000c84418900a02c9210758800c00c44543c607000d000303a40903400a205102042c410009041c4002003210540da00403070f51480a80028642100909a0b0702d001541650130944408580c000581000c410345509807010f12405460b4040101e204010608104030b050080000c600402d002e0000100b1040c0909101441c0400c641c011030f01d051010003451200404031641402051803411000e07401016500c05010252003100000e0f076581c10103865050014000160828448050300c04c8030000c41d840f5001030010a41c0307089480040042c030000300c1c040d00441002455880d0f0120895501241c0002070b1240d8807981502042040d450210031015881190a01c90106400120001c0078220040b0b01517620a811000c45410101c003400015180c1e0040c8462031001e00c0480d402c10580c0e49601e0000d8031044610300064981281c9104055101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 195589847 1250 195588597 195588607
    0x30d0b0d150608070501140406080601090b0f0304021807080103120c050615010315080703261210080d020601050409060204050a06020115060903150c140a0c02090108060103210212 79
    0x1002540150045940c0d2100391003445a517500150b900d540002d001c488104c40800c4140107503401a0300d80d5070403a0b0180361a07400d0303075203440702c5000c0e0368050689108002404000c000440c03a2048001800703540c0e0302c0a00c03c003800c0020003c0c0c40614103000c010318071907a40b011599400d100300040045940c00070111f07031880c01d10044140e100a454080a40001d0410130300903c0010901d8100f0119081c42e0010108580b03181c981e0385101060070303055050008101000003400d080103000e8883ea0034900aa40340a050240707024044442d55800b2100781c2d0008182c4042c80e41c2c01080031411100240c0300030480240d286040c4d8020f1080ba000180d100c6042d02c0042080c681c1540301802e060100d050302400e05803265000c2d54090128440140386140409408a6041c00c80c1c100c0700c820041410500b01c031100101c1e50050310b40003002d52000152601c160720056142c440100e60043c51401c020f45015411a112602c144221f0240d00c02c1d21340b8402c41c16107406208000551983e2000403c1c26111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 195591097 1250 195589847 195589883
    0xd0f1b0f030212031306050a230a0e030606030a02040f0209030613061401050f190b18040f0212070f02070e07031406030106051e03010902120f10020903030d0b0d 71
    0xa0155408103030f001e0543c00d1001150001d0010849030a038025101c50000c60b40b074110101c4099200150103010000030f80d42c034038807290380610720b0a40302c198074520588a41c0243c40040c803030301003240d070548070354420000c0c044651070100e038074210702d9010b48010501d491010074800c0a8400c421001e509440782904120243c501c0011350100d4900c505000d0008004480c4402c000d220b0a01035550b010b004903c1e0070546141c94000103044131010b0900e00d41c3c0795036036150701041d0340103195528442c5100d1409801c2d685843d1042c1040301d0380148045082c24600552045c0c4038500a2001c3d0034440c0c0b0100c1d16034441d0003001700e00020300c2c1496a030882c070f14141b94001d014095664080f0804841c440210b02d0514041c06102c2c19160081c240c4034410016031103820030b5040d030203c3c65405550f141401030268440120480302080c1c90b40051070075411900e0a41e1900440411100302544140043d01865401000325841002c00780c0b008140c0e03004076000030303035460031601008200c00c500d00d04031201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 195592347 1250 195591097 195591119
    0x2805090106050304200102060f06012d03060603021317030c030d020a081e360a02010215040804120819020d0f020f030d020f09030d2109020d0f1b 64
    0xb069109440400c0c2c80600302c40180012a002c05a031401f68005030001116400e000c005584d005505240041441403580445a551309004001d004501112001e4202107905030040d00024542e0303180451134140c2500501800e90300c10700a8288034010541d880e58045403c0081e10140d5441d0420f82c0c6d560b40c21016120002c0d40000e03124804541c100c0c00103000d019010640303146880d54a03020980c42d50302c5003850480d00380200148455400d80407060020100004644404407140b071004044001040c0006440c2102031004910a4200d250410001070075071300c280e030122072142c100c18080b480d9600d0445c0e03050280089292181404a544400070b59001502289078401c641b01d010390401081c10407615410320300d82012541c0e104014000502966900419a241540c51183d040000c071400090404c800d007504000015802d210000b0f0610b1b0f90b4003000154440c08108005400d07165020402d141c1505a025010f101c3c0c060180052202003004101805280700c4000552070b211038103011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 195593597 1250 195592347 195592351
    0x60a0f080d0909020c06040605101e18060f170106030609150c0f0203070209250f080903181e0a090c030f0b300312150f28050901060503 60
    0xc001002c1d03120014081541d8030803260404100e0001c0d20295071292203810290401800958162500600005003a030813032240310400c0c0b21b5420200035107171030015410082c0c84000c1143e01440e03d000010000c004c0c1c450001021901a0003252280c10307080b030000c50040c50b155101500e210300307150880040000408511440c0d2508503402c01601094441c1214651018070140016a10402181c0050326040011a600040072200036080c202d000c040b00c0c41003004040c44e0b001103600c02000d44402604172403150751003680b900055040c040302c94044003c0c860101c0041d0300440243c0c01c01125104a56402c550111014203107040003540e80c1c24040007004c014070703507000081c900305c0104440100784c010140c003040c0080507604030f810900715410f0a85040354100f0b03000740e20a55a0b802c03111050009d05100001503040e0083c034600740399110380d40201200514461025000741e07a086603140420f9480f1406060091520303219640401c078400e2056400150b8011426000014843d0748000214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 195594847 1250 195593597 195593623
    0xb090a080d06031a04051009020a050301021b0f010c050a0c080d0c0e010908150609070c060f0911220209011803050105010302100c050a02062a0703210512060a0f08 72
    0xc0e0328100302103404c1158420503140140f56810026070704200401c10380040a03018001480041c3d1159104002422a4405480400c195561114010148400b0711958800d11807000c024021a1102c0c00b0003040d03840340ca6001030901203150320400c203100081058034012501e0740020404c0075809803001c1e2445170842c50305800942010004208100d010540807060081c180345038000d5101d9004110180200401000c100212490010041746a9020342a1030240760f400c0010060300794189101c48086a40e0128001d4000080300e03410080e8148280707c40e0b04119070300685400480c00100c410100da041200f140c50040305d408010302906500260480e44200c40400455030014070680d1051182880030700240c2207151098054140800146a1418080081c540c00005585020018200c4076005000340e40000014420090a00f0301d4a6081d444a09050105c624010307008000b80728915440070213003c8140420314036100c003207c3c0340c003504503101c01c2140760382c59441003a500d0307241ca0084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 195596097 1250 195594847 195594863
    0x402040e070803190309050a0b04020307120803072f1b010e010f03020705150a0509120c07090e19050d090902071203091104060906060e09060108040b090a080d0603 72
    0x200800110001e220400c6405607005181400602080c450015800410300c2c014151512151000180180243c0041920408134942982000d005140c40d001c5c1d96042541141c020510000105070300009803688030810b458000036100c05003c1044c03040801c180c290600c000d80c010041c400c10b8012500041080b90320613009108511000111401c11a090b1002d01040f0200724200b9120300c02c2d0000d05945020300300b00c5c0c0803003d4443c010350492404403000c030300f505d43e102d060114110b000d00402100d0500642c0c114241081030803170300d40720102d901c034820103265510030348108140180501140420441c005c00f01d01002820701c1611703408110000350010303940380e0340460226603501c00c1c0c4210b550404034484600c2d0301440140c000b450135200030b81d0101500310103904181e503940a00c0c0080d089444020444c645410340251000b91071707401c2c1e14465240c2504106060341c0c0841070944c4144c00403940c81c0340341c89444c0e8190030454101ca000e803400c400000c1c1503442e09540c0e00114112440344d4a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 195597347 1250 195596097 195596111
    0x6120533130603030e06072d031b020f12010912020606010206090f06040311010e0d0302130506120c09010c080304030906080a020a09051215010815010b0c030f160515040204 76
    0x840e80c50f40001004904580003006840c1401000382801030701c1007100703034007422045d100c0903503076101d102030f5280384020000ea0f201010740c060b000703074091191117081da0a070041542c0000c0a08190640c02e6028500490781c02117604000d403c4111202c0e0824921a054100383c8002900c45904440740d5000d0700c550400b06e102501d001030841d060206850203458640c03074958007180c120540045010345592a140b0748400000c05000300b080c680d0440d00d0042e542c0c0481c0700016403d4100d40d0000f0f01c10241480481c040f007281808907036000070b0003003041d9134030a003001c01a5146030320000054103404000c41040200364104401c00e051310401c1c0c03203210032699003a542d0b000340d2281f1000100080e0690004020b20308180d42407098014021047c0c90000917681949100e41600b68001501940616079100002c040b6104280c0500700c84036078640381107039005010b69648100184e8410300a000030f02081d965030405645140c0c1d66000302558000079440d01c55202e070300b00c180c0301644124a0109 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 195598597 1250 195597347 195597379
    0x20306180a060527010903030b120a0b060d080304060605130e0c12190c1a04050d0f0201050d020a030507021501060e010c050f121b0706120533 63
    0x24900e6584900c010080420000341d42e540e002034880a040d1100804d0749020908030020840750400140114200000b0501282d003070040903111604420381c00740c40501c0140400e0030010800341121904254040c078030344c0715040480d00b020721301ca8014120400100502c0204070207038002e0300407540111800550a100d440b041d104581403145845190351001d6082c10706424075443d035501600c2d5502c01e82e4000c2ca002401010141c1a0701c1c01118290030020b07090068840f07540f00c0102c0440340c0790200b404d150400000c10702240c1c0040e806426910070706254811a8410f40407542d0103000c0d100d00755200e135210b00c0041d010b003070700303803103140246c05502041443d903c44031955034107e400c0303603580c029420a54801500e54408100042e00d0902504642c91241171003004081c410301c11011100b03541c0e0315110b440b01e041000e2030000c0380c01c81d00480700400449600c18240030b05082c00c400c00054545a02c049410400781074140c2c244119230341c4d40101e203981c003000801d0743d0b0b03a01d05030380713240c0b00141c0d0070f03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 195599847 1250 195598597 195598621
    0x8370206010504230411040e0102090a08070b0f0309032a0c01170703090602271008040b011701020d0c0503100b03010f0e0709080a08070c0801020c0703020f030703060612020306 78
    0x30030904c105038001c01d081d01e0402426042c0c0044c081d0400019081410000c54191b40014081a029a400007492035031410520780a20040101d070b009801803030f0800d140c0303e125106040d2102d4401901001207480d48001f40300300c41a05c48465185e503a611511150700d81c2034413441203081c9140c098035504401e0395000740051a113241c0041c462040c3c0b6503410809400501090b0340544400b1750074000360065400c8101040080c05940c0310071520444488100000d18a5550341e940400400c802030000040f604d9000b01e05440458040900b03030000c2da0056402030180d12b0034007280e00d06004261303950307640100085018810f405103100d252511419666210720081c1309500043e20484010010412400c2080780c11180901c4c2419100740e4811180349005d112100c16900d5600001308801044160260380e00145401c1c0c000b941458110343c492601e0381d40030300c000381c01810144ca03c410309980c244100006180d000600b04602070f11101707141c1c1030082a21080b4000d10620000c01e112421107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 195601097 1250 195599847 195599861
    0x3030609020a02150907091109040e1903080c07120801050306090a05030d0203060a0806070206090c0a05010804020f01140a09050411030c0403030e0f0a030302030c10060b0708370206010504 83
    0x540051001c404c2c4120301c9201d40b480205030040d07500401502003000d4800d030280e00752075103c21140c291100e51400c00c000c1150032556001a5035409802c40c0c401c040000260114a80d070103040c102c0b0b0543d40c907002d00115101e80a4020321710314031a04589885030700f240f000313810f813802a0100c907500e40d03981450f10f654211808004c0c203158030601c482001c6181d160025903110001900748090180d841e0300b26890108191207a002681062081000f60705042007060030b2804103c814805180c60080049c4c0800009000039004414038841d042c2c01d82d000d0301d06100c0d0440501400751b07940f5035516004141e240940100381c843c0341010034130a601503402041c1c4c1c2c00748086030361940c80c2525556040e2462103d542160b90820300640c03c43d00c0550b102c605070001180a5005580c0d03036031400300494101500e00c84074000842c83c15009209141e0248141c81c0e07003d5010202554a400c0d4210340c1403c088541c000c44203032420310048a000500007071207450309041e00d40844601e0790302c54040005a4600c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 195602347 1250 195601097 195601117
    0xf11120c03010b0403110f040603030c0b07140706050a09020a0f0305060906070917010b03030a030501060806030601180b060c0105090307031d010e010e12010507031509090206030a0203100f0608040303060902 91
    0x5100034001b0880840560814000c003c0025003070811004c0410299002540158041803903808500c2c1800206155942e2092007890485480203c007885440680505031b409000240c1c1d86c0700040309100300c1d0380300c0a1040c0c1c00900c4112030543d584d040700070607122804100da0074014040030514a41e40001c0070303801f425890300c400301d2a60400d101c83d0b0300b003101d0390030003885503403195640c1e00c92317803414401810302d0740450f0340100f410342c10034401400000740900014000d501c080010440608601c80002c440e1302483d402081e1914840b0008400c0e004100c12500795529200910002407400401400058825191041209045119038041c200d8000100380811110160500c0302d40c031501c180c3d510740c14018201c0002181c080360090171160220355070030100355142110128101007518500040000d10310a0000c00c20340c0e40810003e000c00b400c01c0044071b8001c0085079000144000a0010b4815a5a1300e290980d8a8000a2082d4410368064010038540a00402c50f004c69008136040601 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 195603597 1250 195602347 195602369
    0x9091103070c020109030b0a0203060906030a0201081f03020402040b19020a0308271f0e0a080f07060905060c0a090e090c0114041a07060506010c02011e02010f11120c0301 75
    0x19862206803140b86452604a04028464001200003080043c2e858021200d40c000141c503464840f05024041c000a4150340c401d030700c104040d40c0141e9000ba640d560014544611000c0d0151180319000f00b00000c0d08025403117400070401282c101000409449120b940700e100507411680104181d03110454420003800043c58440010400ca201f07500030300090b80848103407902c140d42501418200704210300440f40300c2050341078401e0480d800d80038105840000802400d04440e40d039450b54114030032403400d80e44c4503401281420038400b040c0c0c004007000d50401c00303076003840ca0031500283c0d19512040d417180102b5605d071000303d2815504071506200742c18007030003000c0310b103601401510344075100d1060251400c402c00c000704005080c501008200c032074120000f5140e0150f4a000c0098800050001c0d0403c5002e0200303402503039001241e4809140040b066280e00200780500b24058040d41070b14103012820103602c0310419841d42d00904000c40161004031064031400303011016488284502041d40c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 195604847 1250 195603597 195603601
    0x5060f1906030c020a0804170d02120d050907030c06051b060705090105071b060905040e0312011503060902070804030203060702062401090503060406140c07050304300b060109091103 80
    0x80c025400028030118900407203045104a46d115861640960030145a5101d600d14011611904221044103000c550008d0080000c0e119094800c60141841e041c1c890783d2298082004500705210a2010315082203070107109544540380905140c1c042c5002d9035101ca070f0340407814512040410700c14003d600c0c2e0b945440c60091000011151030b04100d00541d6001000825540c12802d46240d09000b0811902e48901d0f891a10003000300326203039201c503041a41c0042069240043d43d41c3d84160540d000725884070520384903000110001c10894000c0450381d840026a1428005108050011284201c08543c03072541c581b0003c0780c40d01c6013a5a0a116140c1c41102002d644200302d000c00b802d05018500401019074500000b842c1040545042d20030507580d07880400281101c0c801194003200c240502071800c0081d95480c1e5076481240303d00c2e40d0303030b201820000c000c0d031996100703a0100e08070400821201850b03a04024801c0340c0305540050101e109004002054030103801a2001907400b0b1004600315 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 195606097 1250 195604847 195604859
    0x50a03060f18110f03030909131a100f0617070503090a0f21020d0c020d0c090221071404120618030210110c300a0305060f19 55
    0x908001d00352414419264560000c00c114190740d0341e48080d0080000c400f071010002c0c103010800740904040e60290300200905840c44c0c40d04902a070304250280c00600c20a075242c20318000001d0a2600c070141d07190444188003031540c0c980c3c0c1400c141d41889a00c00c07080ea940d100182c904e2080754120414800b9500002500e29000340051a4001488404d41e5610f24003961040798411140c54103c5950208050401c0d42c10240403408905040e03030300080010901c031450181002c00a030f02c00900c1400c40c0d8540d1b80401500030650f00080410400c15911400600500fa03140c4844404101d002486031001800c254402c0c40c1104c0d1500155000501d0700c0d0801d1100d110024558030103841c4aa10cc03244800709911564804020314042c1d8090003090701c5103242501580c06880004109032400c0c0400702642601007841e445c01450f58400c441204260b61030000c2241080e90b44803442c8001040080300e19400d80c000611459040b12402e604190f044200301064030348410801d101c0050060500c25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 195607347 1250 195606097 195606101
    0x50a0902032a04050d03021501080102090604030b0403180303050a232a1905010b030102040308030a1d030307050a08060306331309030807030504050303061c0203010c090f0f050a0306 80
    0x8a412039007001803a084c0c562000c2403d450368450101d00590104101224103600c8201403405881c0000c004c1d850007111a001075458021401b014000b070700d02c800803400300b600036a01c07408040048042d0042c0b040d928140a4081e4200542e02c00c081071a107804180c201c825200c802070100388003003c190404040b00380000020b00030101d070110f5a81c510110103c881303020042000e03d078550342c2040d484882d0a24100d400d4900030200305000c0e0380140414000101200c058940c4402050300005007052540e441d003c8041e28400d0741500c1e8000003042c070202070303403043c000d1585414585800174552103180c2850b5841030105c4081c1d03102d192288210042c1031824034403400c40340c125070b000c441009030000056014544682000256991954000708142d08912055407100303280c03c0400c11031829481d1070b9107900c40105071512900a810082c2d41140450403060700301600540200044424201c025201c01802e00410044d42001000000c40210101d801001d81d40090004590035107159100c0300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 195608597 1250 195607347 195607411
    0x60206070e010c0804080303100801020906041a09040e0c010906020615210d020109060f090f02040509010204120f02151c0f090501140f01062d020c0303040906050a090203 75
    0x410049141c4183c004100403002800c00313080030802035a03a03424805041c0d401c0c065150f110441c1a401031208000c0c41e40d40005941c111403d030282e0815595030380c2070504440c03092030300b4141d200c1d1030030850104002001030b0078500c0ea01c003a02d0320008982c40b070009a944000c04c60b128486110560700450700c0f030502595801a1009078407000c9001450f1104260400d00e0210101c0c4c0107039910149401400703c2401815250342c1c4008040003640d40c192200b0812403142440640201e4030b4a007c00c0307503450f00350b044800410011203002c030b02e404e582c541045030711501c80007030f031041e04000c04d084001038003d402c550681c14010143c00c4690300c0c4a0015020b401c000703401001207a0b484200001140702070041c007549186050905000e4a00a0707044c02c091001a04040c04205690b07200c01c16401c3d540c11655114031a0342c618201858a0f60012890603241c0450a60540800700c0c0000b1501303d00c0e002481940c208071003081815449a42400032404100c810020188489480003d0320001400c10702e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 195609847 1250 195608597 195608599
    0x703020309030706020a051c020a020103091103030f040f05030705060d0e190f0611040b0d11070804030c0f050603060105370f140c0a0318050315060102060f01060206070e 75
    0x2401d003035019000070306102ca59481000907802002581041010510003007100305c0085069580f034500c407410080d03a0b1261520020b052540e40c0c0e190500f403008001c1800309458000303084995030990182c0c0b0801139003062185c4403603951681c5003c940747c9030119184042c1c1c0e0303000d400c05090404d409a00d4000e00701a07481409140102e25164402c032107041e4000c80c2d00d038040c9811030781c964480d207080e600700c03401210f26003a240c40c188428841d04c00ea280c1110030f08002c00c14040ba075810301030003010700c078400c80c807004002d240002000010840a00100000c9990086403030103026940c0003889098442100c55a0011700104071121000d55034000190b4280d00340f10501c41104900b0307240ca02038504058565000c64004955058240c1d801459114015414014203040001079034030304c0d80d00c903078912004050140c500c0c041c0d1540c0c484070800100030700004003254071030070103c0220001c491050390380f640140545400900018244c4081034101e682c158004c01250307a40c0b20301241c00b038480c1d070441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 195611097 1250 195609847 195609853
    0x120506043003090b0f0f062404060e0a0605040308090d060930020a050a060b01050d020a05180105070b060907030e160e06100f030216140c010e04060515070302 70
    0x2200c0c04101d2415100d402085078500080c801114188018a010020a03074001d000103074003082201e6591003001c641280f01900e44960341031500d07805004136034041d0798038000500003042c006001503000c881200905c400f6a041001241c88000480d2103215601020300340301d6081141540e541002994080f401d0700400c00014a40c00c1c075034609010300c2e20000c540802c2003d0000340d090121580a0701c0c1da4841190005207403074441a43e4190319040c41d10700213003011741c0c1c846008000c1d90092084400f410043d020856030b03030310036032006030054101c00d0202d0071502080b41e10b080c0550007002103442d4280c0000346007040f5501c0804000c08036500504070001c00d619a04945805e184c204a548114082c10280110070740c2400440340f940c12000b0308441c404c41900112a05090700000fa280c10b1120905e0b0259880082800303290760b002e4403506c02007032030f011040070b600c032400b010074500c404140903658142c01d0790b00c2c4810041601c050340504c0394001c0000380c48400307205010008080480c428016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 195612347 1250 195611097 195611153
    0xc032d0f11030118050708030c1005060d0c03050303040632060a05040204170d0309080d090f020d05010509010f0b0f06161407030506070201060e07180e010909050712050604 76
    0x4a829641382c21a0040d401550b00c40b624100001070100401402280d8000c1d8200340b501e51540d580e898001500c0c4003003a503100d000c20141d49514003211007803030b00a40d0501c5482e94a20740305d90350798821102980da1500e49001e08a003626070060315421030000d800014804007288010030200c08010b000260300105841d0002041d40781c5001400050440051088132048110019403e112250720704d20f04051510301608001850f05c025036481c441006400103011030285020b901208000b04003a512a240c200c0020400c201508620720502c1071000a01c80c1c240d0b800680019070701c103918000c2c0d11165500040c5500d04040010b0301e01c120024861010404658031a501d0f94020149a01400e8006450910510204008080e0440e07614402080307075a11701942c51740e03000350181c040ea040000140d46081007091a04041001e8110100a10325659540d101100144400d810451301c0b401035520020301610346d0040c10b0341c000c0e000805031503d551750703986401000d9080c413190406400203c3e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 195613597 1250 195612347 195612349
    0xa0c031508030901230f0703020f10020d1407120e0106090212060117010f05090a0b03010608011b0801080d1b0b010e06010e060a020a0305030606070b040c032d0f11 72
    0x460310300070511140955503038215a0001441e42400c83c08522031741c1e0b101c18080e030b016a00c140446451215a00c68903856107810300e8100c6c144110071007401d0981c401c8032022071042d070701c40e80101001c8071a03810403c0402451594a020f1200491f0200086140d80807850b480812035009070300382503001800020a1070701d4001d00b008036048491b1f02c5211503000c0003005829608040460f078000014030f0000c0c15503141811200b480040c900a0a0042c0b00351030218006000301e80100c020752600400a210b050345a5582e02d0080c001070341c1c0600565240041e540c0101d002c0c0b00d000d070580381c0001c06440f101c05254070a5601001d14003820f100e0b48070203101c11001c10744819405004c0c152956100c182c5040900c0010030781c004a80c0214131600040004e00c010b1500050500308007a454100251a03603182c4c3c0c002089070190f0796014240f03007001c004000401c00b000c140c0600703513407041c03688400341c4040d47c0c0b00d10fa00207070b0401c200308550751113203294010a086048002009104403c24160302050b54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 195614847 1250 195613597 195613631
    0x30304080307090e1005010516080313050615010203090f0d0803010e01081002270a1a0903010509030901020a240c03050711120405060c100212070207120305030a0c03 73
    0x11000d54628401000307000802d40e01c421914010704107446248842e06040114143c0c00c401c0c2d100740d5041c80b00c0003c0441c00d00d41101c0301401c2d107903000a100c640787d1030b08840c00100700c0000e58085481d4029240007681c1d5075844032a0048280c0182c0c011030800ca940d000380030b01c01006181541d4841030030380300e0400003001500154068407207003000400355454110000d00e030948500c0c850036118010b1120340540b110110b140420800001d054880c0d02c00000c0202d005054650004400c40420704017241e0b01c0000e5030003c040d402000e070020002985e400a440341c807401010600da00681015034418045600e940213043c1150500080c20a055503016003041147d50311010100400e890741c040120031500010b04481d1112003c3c058001019407070381d103081c82e10460107114862680401c034003001e11801c00c03142c290b40080314011503850080c00c00300070032010105c1c0c03100d006100d07174100880d0019210a941000030780c540c80f102e0540d140c00544102522110607000200740d40c81a5902c000c111030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 195616097 1250 195614847 195614851
    0x213030516080105100b0d0218040204230d02030d0503040302010b030d0c02090f010b16050c0409030903142404021305070509040c02030c030d0902131a0a052e09080303 74
    0x300040c07252031401c10342c2400e44a005240c0e5010a10103501000454016811180086480700005030b4072800e0b80303040d0344000c07074468200f90064408038000c0f6000c920302c4444d48103285892581d030f0003000c0450410003100b03540311000750550020090203054070b00035000b56030032900c64000414050210004286415007003550000061550701140056091007042d1b1600020407640f890859810841c03000010712400000c0040d600c1900502000e100d0240031142480d0001002400309171070505005104070594001943c0031500e001c401032a1040000e6440011400a200c07480c40c20683c07800e0100b2400300400c00da03007051289514004a80a9203e82c0d446282030740c0301ea43c0c81c0c00c199800d0000301e03104440ca58056500c20071596213901d0340041512001102c2c2c4001150111051000c82c0e405000d0003203000900781000050580020101c3d983c2403000030607a10000a5a0b0b941c0c2005095212504110350f0390b4400051818041240400030700302c400319040449503035030707281310141c035650007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 195617347 1250 195616097 195616123
    0x1e0709020316080105270c041a04140612060409030e03100507020f0c0a12050304031a1b040b0a03090c0b04060e0f04050105011e0318030f090603020a1202130305 71
    0x510840201c00d904803d0081c090201951006050805000c910b410b07810155850f91041c0c0d69040002c01101c15403044401811a041403100da032401401c00c80d010b42c00a0050300c5081c203500150410500700101130f1030b031a44513016030001c1070b140e02c0c003884010090303000164200000b0403071072801c0740c40070042050428440e0400095900c0d24200083c2080d5030990b83d08419000280547c41c1a40d4503407140301900c542e2000b042500e03030507207080d40ca0741c815584024440c1d03140124103800500078020052280409440c600306c2100d0549601c05184100e00429031405001d1100072062480799105102e0300d4030402045001a441e443c40b080550001d0b40042c0000c0c481d410204089c1c00c00c42c207a00c4444401340d80c14030003541480000703084243c070700d40d40b00f00014020705002503140c07081d00180c100c01c000051a481100b01420000c04c8481030340c028101094000703074000790261291080b01e03400380156560442c21400480540d000e0b41c0604203213030072107032500d1000c008648280410403034000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 195618597 1250 195617347 195617371
    0x4110406020f010f0e100b041d06041101030c1b020f040f0209040b0f0612090102091008060405090c060a0e03070509070315060c0f2a0801050106110f1e07090203 71
    0x110010560079240f2003001132160f00d050049064504100041311003030440024808915551b2500105004102001559003d00034010024003e0140800c00700e000714010b40d98404000b442c24015000e89030305400c0000090400c00b021004a68441c4a14424a1008007242d500c0b403800c2c800a03003551550350301d1541042c0d002910b121546450b03c101c0d8905d110543e65420001c8469002460f80e008a4903032100e03c21170000041c140b00029030481e12030000041c03051a045a003000000c1045800321021070003180b5210200790341c58400664070700244c400400d4186040400001103070800030020340d040d05841a140c020919989210000703100f52007aa4000616008070440342c4003405c042c1d480b0200703221042c080c01c404a007044050151a41d080080ba00040d070050040450682e0005020a82d030f10800a02241e080300640285048441c60740c0d03801e400c04c118414068440b07881e0001007845a000c2e1145503100c0d80c9001c031920a807141482910500d070707901c80d1108240c1e03108980c1c2c01041d403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 195619847 1250 195618597 195618613
    0x2161101050903061009060602160618090504031e020610060e060c12130b030103031b0f0506130c080d050d09030e120109170a0c0b040c05030f060103050606010c17090411040602 78
    0x607980e403061f00000d0155200420100841c2041c0000c0d515642c040c0c0410080c0c0c0c2c0701c107003001d44400c89580c802090012001c0003545090700300145280b02d03c079041802040c4034013104d80c41610001e107290148e00700f0b218030002280f910780c09580141100c40f00c10b8100e10140444010303080280b10300f140525000f40301907910256001d42d000c040ca01c0380c10a9074140400d20041c4003083c1e0104003260004601540303084001034034240741c4c20001c0a40001445441280200240d2070366448441c0c4085115954031445030307440302c1489031114108005000001c2081c4010410166990416010710b4040e08140f40048910000b14441008011a10000b40c1d10b0300104810403640400280078503070864040c60030725080030030082c48000c00c032034050095545100800d052200c0400e02200402c1c1c001c0031507541100d1446401d80300d442c02d10003990540621000070b000795010300c3e4107510981d41305107066041d60100c100861942c00440c2d809811556604602504445080040c4090021500200190307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 195621097 1250 195619847 195619859
    0x3041524120c06020708100218120d030605040203070e011b05240702060105061b1015031506080a030f090b0304060515150d091119050102060901021611010509030610 73
    0x400b040d40c001011540055001c00c0a0300c5c000c103070001107a614420260766a03114120105c45210380d080c0c0c0503030180c5003910b101d0001e64001545a5144c038180ca052050560f10750402c0101c1c001100d00030041014100061120b43c45210f0802050000290007540710b01a6103801d031500c2e0418080c900340d00000107442e45000c02503c3c1c007a40c40302c501c0c40204941d606150200340c40d40100c803000c0c281c00c82c01131942003610200340403000d006541c06e401080010a240310710445003243d44407d8443c503802070100244200140944c0003503d000030001d2001d81c030155011144642d0840c0c80004114030f40d1004920841d40c00011030081d030282c400498281002807890312407040c9000c40340d00c61500c50480942c08410360b0180d42c0034500c80070b00024098140c2c1414040e40c80c0c1d0038501c9502480800184820122004154080d240207a085905599401c07100710300300c0c0f013111416000c520000001d080044c1d1242c00d80d4501075018908241040c4410010030715001041e0f45880260014040c01c1c020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 195622347 1250 195621097 195621113
    0xf1e0b0d0b040b1b0313020111030706050c090f0d0807020603090a050a060506090603060910020310080a15050f01140d060204030615060f020c06030c031b0c0307050d03020304152412 80
    0xc0c13a4150f8010a146040400c040e80d911541154002d051007140c45a55080c10301c1401900d0300039812420520140c500070a140702c4c1139000000b03243c41080c2000f405502070414699a4606590061f020740c603043d203540800c81171b43c100802a140c903108224442d40041c40c18404460070030f1103540040303180e003480c10410040d40d000408980c040d82c40f04040083c10400014082d4204007a038400680e2900c80c542400030000c125000ba0f1054403ca1014000300503040d4650b00407203c0c050002c001585450403000c9090704288120007240e5509183c3c4c50b090b00d444601c800d41144104401450721350f40c0c0e6540d4065585903903044412144056003000200d41043d0901d01c81c844500c068004602e1240010703055002c0505041d01c21180800012020744081c0795003149001641c10342c548800507000015903a0b03105520490b8075004122111540602a009690007141c1c00503003184080c95040f1490024100300003500503102000f200310210300e1015070203a02a2003208401180c403446414a030403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 195623597 1250 195622347 195622381
    0x1a09130f030e040f29062106100516031103070204180204050f071b0204110c0303070e010507020f10020111030108031b12070308040c081507030f1e0b0d0b040b 70
    0x103189424003420744c440c5d0060b5400d0500f030261444120612503d10400f00f24103000e200071001d045051a040303024501c950040d101d21441c4111408814002030500869050007000255820703140700c0000c08001034018030900402c2041c07681183d06150040e00081c007684c01c07903030611110794000590041036090a0003081d40c003c00020781032a9906008800030840041c03c4225070903240c581c00c0365000c65071641c202c1c014039050240c070b0703a4030307541030315103081d10399005864030004a41182400046540500700f84d500d0b05030005c00ca46405501c10050204401d02820a60f0441d50f85103c00e960028140340a50f01034481030008640341c0342c402c20715101d24181e094000722203921984400d0030520414080380c180307581c035150580642d152071400c8003c034912500b22a080b4018803050003207499070300c0340311481590342c1e40c0c090100141d600c2c1c0600c01c03186002001030311890a1440c2e6030184032182c0041e8040740000d882141e0200c5030340c5038500c80b80000e850480348102c4e0141400b079041c00800200e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 195624847 1250 195623597 195623621
    0x1206090a1b120b090103030206060f0f030102071b12031e02031204080912070311060a051b0127051c05091534060504170705010903121a09130f030e04 66
    0x4e019419920069900c01004007024840c4000c8040c0c081192100d40b80004c4402010340259100c0d800d510709012804110318000500c8142100d000900500208082180c2605512444198034000319608486071584003240190322042240c40c0f03090041c0404180301d54020703e60300c1d8541010104001d050300c2545580c8401c0d0740440401e2010513035458540c141c4040c1150103668a070110b0700162400d01501240012940440075040c0e145d0806400400104100700d0321001c114031082c08035500107100d1000648158084e00030611112800308042c00208014240345050282880000c2c1003a1140c940c0b40031014800300f0033a01411212241e10780d01a810200303d40c07201000b4030014510041c140020741240e4442c0040380a1050f0308070050080e0200c09529980c4507840e05226000c0e0079002c41c100e001910000f0740c0e00186c11039208844141415280850012080071700b000004200984891280d0b085e90701440c0010310018202c10455200c0d48904544c001c2d0a001c0200711405684a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 195626097 1250 195624847 195624859
    0x43b090f03131e0e01030605010816081504021c030903050106120201020307060216060603060207030207090e1e0c0909060f070e010c0206031306020a02030d050c1206090a1b120b 78
    0x2014610160642825504806448010200e04030304551082d442603201600c0d0002c21300021013070049642155041c3c6505d4001c071000c0e2a008101a2120380c02c9104008882c1c00c81e88030007500c9003039200c81c1d03a00240000d01021590071500c8410038071480780d0500f14045032501404208100d07080c01103178018a0400180c9125044580002c0c2d2240708040004200950000d403409403000005081010316800c01e2041100c25101c1c46c3c2131000b0b41c401d440580c0584a03820001900d58480c0c000d03040e0b81c2040301c1c0505241000340e110140000c494400c00703042e030300418610302d082d41c4a500146114060110083c24182424022038081c0703200070301090104400710369281d503d83d8000900414181d4180c8040f41d507a507071603060440e03140c050754005202600000324201d510354000003509200241c045c04001a8581854150403482001608100b00d6079920004103185800841d0940c495880000442c20346803038260001c40788420603001c00410a5080d105007900c0d0280301c1c0741c0c4588015201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 195627347 1250 195626097 195626107
    0xc030a050a02120111030705090f040b0a120f02030a05071d06101422060905011e030203092524140a020a0206030a020d050903030c043b090f03 63
    0x14190700c07400d4003000a4026800081c480c00d07510000d600c4050a043c0135000940c503030505800042855012003407440c401d2401008058603031629202c0c00212010042074000c031545442c40c84001808015420381d0414080f010b03140160b107080c0110801148514081d127011030501645000f0300f4a09005980e800e007041007040015100ca05402da1402c0403820b004803800805000f551080c81440603445000c1075040540e04102c08021282003a140f582e151140000e0300c0788011282d205017410f804100c82c000680d545c420078045c2d4000d40c0c00404c1c682c03c3d40d1100d1400454510070600181070501e1621713405d68100b1290003101d040c0c0c4940030a84081001440075000001c01b030306c1c8a20804240c0603400207654503a54001c000700441264007419950300c0c0d140c00c040310002500b2246c142d407c481d04010000b00c0340700b004412244160b4000e041d007424a81080c4403143c01400d4600b030740995080c1d00c0d4880e4240c928911509030300d071000ca07001414610b00380317081a0804035222809207a50b44107100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 195628597 1250 195627347 195627353
    0x203060a06020721021f11120a0918110f0c1c050a030c0e03010c0207090f0902091b090d050604060b190605070c15050304030e0906010f0c060605060a020d020c030a 72
    0x40354035404211340481c00e07607446070000070b481c45040340700441402080d448a150080d013041480140d19011b03000d650080801e458820000d108003110300e40000c690107818041081d003c0c3c010040c8802c807100020b0f03a121141101c0d0019400303408065003c0001250080700c002e000c04ca20155a003a07015001c04040e100c503009013150060450390014103482d110040300c0640b14500001c0480300c02002403020107955500a034894007a406486120340c200784003a039009500703015041e2071f6030b40605104465620390000380c526845101c04001060420040003100e55252030b8209401030207100a0701b004c0c01c02d890007100303d5024081d40b50081c0360130301c1944010385d8108034403802c035000c0303040280d90340180b49007040d2026041c0e00f00284000345056207690490340003001d13620551090315070414040900382080780700e110440b65540041c8a040c001004917109410305a0311510814011540948400000300190001604440180d2110445200081d41002211650981640a095032041c030b61 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 195629847 1250 195628597 195628619
    0x3020a09090302010905100617070b0403080f211e06090601030e010f050a0b012003030c0903100606270e0114060c010903090f090e070501031802130203060a060207 72
    0xc480e480440d580e070030741d01c0d0030726000b0341080710765643c410103a5440407840c03071054008002038024076400201d0720b511400021000155042503405564071306080619594a20ba030552054000041060f4148081003203005d02d001520b0383d2400c60540290946480c9482e0488040c0560b00c04124030030041c00d01409890b03001409800c89020302e004117060a41860346c5014002c11003100b9001407810041202c002d070150300c0595003d000340e88810803e41d0010040d48000000040092590000c00c04101d100c2d0410340203000b4080040c060722000000b000800c000c40d0b4580e44070f00c001c03c00401860140f144858814a0304204503441343c612142000303064410388105024055a80c42e011080c0b407510b0395101d054914070403045c07000b80901e98180ca0000c20f21300241c81403848000d0b1242c404602074245000b1200e504001c48010f10000e89044011030240103103802c424011481f100280d80036032950215041098182c01e00542c0d01c0c1040303024802200b845a208001b1508001070034400900d040b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 195631097 1250 195629847 195629849
    0x10203071205090a0213020901090803070506010509070c02060a11070605040b070b0a061e05040b0f0319061506081509011a0c030409020408010b041505030a0303021e03040c1a0403020a 81
    0x407681c0040d8643c3c40c04440b43c5000c1035003c01a41c0003280d030000c41070b6041c080c1c00418010600b81c0e500140c581d900e40d412035981c029840c0040c004e400900062010b07040c20b002e2203611003905d142c00880c08407250082401c2ea48105420800220301503074020400000b089000028609840d00c0c0346410714142c6100350600403a003000307081c081a0b001161884804e5000039000d00b424254007540810403c1b054600c440381449224000c909090100a00e881c05c02c03440f454001e40a030242c50403a42081e41040745c0e0328034035000c03030704140c0c1d90340d0744075081c030744903050310054601d64490010714101100b000640300e202c000c005216001c1400140038102c0a1050604280c0d80c5040858940101d01050307819801345030450407400b4800b080010f105281500082c3c011107098404120b11103070b02c0b411200d16080d50060ba40c040d8032900c0c048002a1096004000a0341d003a001e01100304641d125070480d543c03081d102514034008042060002489445107400c501d019101e44c649041e00d154040394425a103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 195632347 1250 195631097 195631127
    0x301050a3503031905060d120c0b31030905091902030c07110a03031b0c080109050309090c0a0f03020702040906060e0114010801080316020a0e130b0901020307 70
    0xa003207201500114903038041900c000c000801c062101004184940e502d800c2101d2902d132184440102c4500c000e000d110b218000d0300042c1c48401e2518140c1c464043c4403c418800c2e8040001d003c6203030022440c04040b25000749200002482c01c984500885142070080c00301e44012051100e10440000e90000601c1c8c0446030185d89100495131502c1c00e80403100b214444011555000000b00000c1210b01001000c01034030035080d80d03100e80400070904c80195500d000041c0807410486c250b41002010783d200d400c0303692042900e10812070f16060200c0c00c1d40d240940807160740d4004284040180f400380e8100740d11510381009a0305000d0941030040003031358034050010a050b80014550159143c90700709142460b0892014071501c3e580314801d0213a803100f485022550b1000781e00300b8002d50b1080c0c22080c101c8800e4002141000d91b01714241d880c0fa20b000700200d0f402103098400142a031442d210551085c040c2e00b0047e886406182003d41001d80c008042001c0c691040081100c0c01ea0001004481c1217070b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 195633597 1250 195632347 195632369
    0x18050d02030a05070305010b010327110d080d0c08061e010f200c030c0406050303030a0f061502010c08071b030f140706061d0103080315030c091302040b060301050a 72
    0x8150011034105120803002401da4024070308040300340a015009003050520a0340e00700044001c400341440682400c03003200740e820140f0034142005c40c051a4560504440050119040d5801c0d0340c1c480d240e940c00700003e59038003500d807001e042e503854208040755400001600c5511101244040110111450800403814440304180c800c13026480348281801c08602001840801103001002558a41ca540740c1144640b044000150f0141483e01940084580107001582107071103015030035018181240b40034004c140d85200c0060080581d12041401001715000018500101c0a0040900c40000d090405112620b100100022100c806d9004903d406243c0001000e48074a02103031a11054003401c1d003041c10105900050007603d50215045452010009038001c0c2d50485903401c803502448081c10184042c030010364401d10f07110803251000701c010155800049007c0000c0c0e0025010b40799008007000004481d030441c10a40300e118541c0704201c88640c2990715003800141c20b50054062044204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 195634847 1250 195633597 195633619
    0x302060a111f05041407080309040b0d06020f0d0b0319030c0302010615020d110d0c2006120108060901050912090a030f030c120c030c0f021908010c030b011805 70
    0x50001e0081c0744024448984282c031002207500c050015180c02d9800b61041866107402c84903101000030040101d030782c20390184d41045450310801c001003988121407900055241000030000381d80b48024280c00b100c0480380e80d1210000a0007100f1152007080c0a4042d0380b2012103003810701e13004c1141085840e23243c50192030030300d010300e812030140c10789070304c22845a0400c240c0410000d4010a1340340c100c0410b5034806444c95986801c55690343c07803001c4c105001c951a0b283ca0300100b4824111500c042c3c1c5d20a1000100e60b0814007c10425030007817134005014140300340148166942400041c0d040b1030f402000b400103061405880d40c0350008031450f0140c4140004024455454011001c0001e43d08084041c4691140d814042d0500c00048411200d096601e0b00807042903008507031444044da09942ca01c03d000d5019541d042d000710142505a03400310604801500c0d02d0a250950300280c00114008241104a45405000e4824000100307050294a01d044085490b01d04295012510110345500c025 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 195636097 1250 195634847 195634877
    0x19030509060d02070b0a0608010c0302030f06010c17120105130b01090e090703060906050406060e010308041a0d020a020a0c121a1b0a0e01091406191b0b060906010305010302060a 78
    0xc3c1302d4401c0040010308031108022082c0c01a901c44011501110001d100c80c01c491013089049100485d01d0040358101c103004103000354802c240c403813803031031240381c1d281c3d0410f14182240345c403038100d1581581000c1080b401481f41c0c0c202420380f410740200ca50300038084003035110000f80810031a80140c4034070241007400215032200030040303000259004030003000340b14003a040c184041c1c0004c8400361841403c1000024403d02400c80c03c80c1200d42005a4600301402c10f40c158031540741c501c42d00c070b04510b0107200704540e01d40207200908090b1602d4008006541d16481c0025010325168000004000000c204d100440c1e0801101060300c890118400220742d00c2d010815408100c46c2c140c002c0855001c640211481c0c0c00040c0b00c050010240c071020010b41d90f07854008114481010340a4000b94140b0111820804070795251480010714207002d00487c1d40304d00300d02c4030204191020b842009965003409500c0c104299035540281c420710b020b000c95030454011500030b2080341445010041c1002100c509 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 195637347 1250 195636097 195636101
    0x20c0f011b0f0204110c06040809190b0d06080102090a140409050d11070819080306031c050a030b0d0323090901030b09061303020706031e0905030301060219030509060d 74
    0x8020700800150510001410404940075154008a003d0344c9424500065103821310b0a80d42480440d000808195a640d6203481c41070304080345440c0c00020014081d00d03099001d400010103000403907152903d03060342007130080580d8500c0e40f0400643e4410071180c001500c8038500142610441540720700070003503442c003044c02062402c2025045001d0380d24108103050f405055a40d02040c04022101c0381da403a40d060131b860b00c0d000f56400103402100109640010000400707154880002015200c400d0308200030321000400d07100d4000001000003070712515868042c071420f41d8001055071070044006180d90040c0001d441c0a00e10301c071041c0e5140d916000808104215104d10348c01910068543d6500d24011004000550314141d1a000f4440060044060503001d0200c03a45c25030700600006181101c00d90084c08103040710200200340540c000c01502d041e000796a10741d48100001c1d80d80750714255009083c17006030000c0030000d5243c2e10400c408280d00c20150340d40d00c00115001503036103f00ea090000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 195638597 1250 195637347 195637367
    0xb100c020613080705100807080411040b10020d12050f0103020d0c081002090a090b1807050c01020304050f010b010801120303050c19030504030906050c1b01180306061e06020c0f01 79
    0x186000c1c0e10342c40800d129001003020800c50740295a4198541084030060703441110446080000910b642d000401207164542c9241300d180003d0000104548460b0110394042c4a0070400005a4000814440025030211910b06240205082000a07042515a075440700c4018071000e8070640703040ca81c000134804c03030007243e81c010408002107602044009429a01941101c5201889000d42d2840040d04416030b015401130200020f12100700c0e41a040300700a03864101900c110104103080c840352501000c24401140114082c400078038180349811001420749010340700560412120f80010044c0c1c141d000e00c0410782d145d1500700403032541d54841c40c81d421400303190103055003403448042004141d034040c0c0c0320034003543c0203a4170309085545400b4144d0341c41c4100c4038220800e60200b00610020400e00360006800389051521754500b007c1c0c47c981c1d00c544111500213a9001d030307540381e0030804405003031039581c602072030301c2e4507003103141e10b0004083c0d11100f8035608680141c84407418410b1982c40340003210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 195639847 1250 195638597 195638617
    0xb06030f091516020706030b01020607030f0b030d03020705070501050901050703110c13050f0a020405012001150b0d1b050904090f0602030a0f0605060903030f0d0608031605100b100c0206 82
    0x900103140001e0220326103c180540c040160160420101c0c0d180d200e030190342204141a001420f807030701d4101045000b400300580070f030321445da106c0c0d00c0c00140c0c0c2e05008403c05c40d500c40d0350140e1200b1041c20802d081060315400203052000402c010034071130342c004064400c0b89405091542c06035444d10412410101510ba0607948400303032400f02d41210116030b00150046142c1244400c43e9079446c4000d104038030a1303010b09800700d5516034040d440300f400042c1d071245200100e000410301606c0340850b9111819207800c2444100004178907550070b01c0851083c002d0440b00d0b034403c1104201c6440d005082840b030700100b14011074451011a0a110751000b000041c0307984100b04554a10f00212044010001e4010a9080d142040c1e40042c07e41f800700c1c00d44050010040295103001000c00418030182d1020079507030015a1503520002d240242400540040c0188454510040855140c62403c2c0b8980380c0c55190030501c1c01d50045100c2d1980c51000c4821800e038204901502010300010300c507401640124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 195641097 1250 195639847 195639883
    0x30408040308030f07080f010308040909320607081003080702031f0b030c0a0f090507020a050a06050109180f021002030904060306060611060c0d020d02040b030901050601120b06030f09 81
    0x8440d44d07607180382501d8070582040d980c041960f00e0301c0c412018154000c0c4070107481a103080c003003400440c54a5011610181c45244402d4114003070488608407001031035110111044c82804d0f10685540038460306602c42480e190403c1d440c688109035044403071203030101a00112004c07034204210748042045911a1a220b203602045501d050a01c01c0035141c0070103a14001d0040c40c01002907800c211400e0b07400e40f5544501c101504c1c0c00e00681c85e004203001050242140300700c030707159004500280303c01c00026004140100d030701d60500305170341e00b0396075020550324808820a48941c0400e03100d00d0704260b05941264140102d08524504074a9030082e15411b6a00030b19009001081217002d601072001c0b101c82d0384030841c80e550803030521515040100d80740f10035220f080045aa50510540c0104803458030728900505107903d03440012149c0c1c10403190f0000e640c0d913440c24800c0e95030704064a003001e002d981300b040c40040c44d48808921140000b801d810740c4402a40080740f8040018031825128411042c96 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 195642347 1250 195641097 195641101
    0x7021f0b06130503070b040e041b030f15060e07021c09090e0f0d0206040203030a0c0206070602031e090705030d0c0627060f020307090b0702030a08191e0c030503040804030803 77
    0x51480010300c41d02c103d9120f481052000211101c0c03013001da44c00c1300e41d1080101102d030780310746446120302000340b0340c602040c075910004000244901c19900c0c1060007070391158146d1000104000445034039030401d0460741c9950082200850340010401105000d0b03080b0250505410003098403d0f21007904a0488241000c0403d001c2100010312042299400012111001d042c00c07016a01d6003020b50340a50150800c00c40001610300504a8501701f80c4007404c01450050951204401c03a0800c1c0c3e2199401c03078100300051034152040241076000001e050140030082d280c00d0000355240d03c1d0f10007007005d000c404035008040c840c1c107034002d916240417640165044181d219148405000f601421030740c0e9480c0c8060761800c90340714070a9900c28038590701c6c0d4008442c108031007000140c0061000701c0c3e052003485007510014a07103001030710600303641c413090b100d03c0181010040d103030318000c1034001d40e0500182624209994494201652144c0504065559413110b09100402e03205a8001a1a101001007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 195643597 1250 195642347 195642367
    0x1308032d011d0c040608040813030f0b0124020303012105070801060e0a0b0d030e0f03010903031d03121303090f080a060b120705040b0d14070801060e07021f0b06 71
    0x4a01c6000101c0e9030114001d99456040f8040c4a009034002d0700700143c010400a00082c0c0000002d1042c0704c08240700000c516a039640c1c114562a05500840e0a604044010802e610b48141022a501c0380041c10405440e02b0000c003e58a0005100399954000b00160f1012038450314003200c061550841c007514100c9481d24041406407916204607503007404448001044e2601304d00c05c3c480d50384001045410a10507a46048448815004850b030303008030380c801c1240041c0d409202c0c24000d10301c00d4602086c046188200114900c4040300f447c1300740c0e001002302007240f945d0840340943c8041070300c40c4140d003202d803410b044072114056006035191004040010400900009560070a00e115002c00e100c0646100b00f88102c80b40c010140211a901c601b500348070604c0d1a130080e080500b80034019042d1800b413615a440503004c034008200c0a0b8001038800d0009900c28042d41010341344030300070fa0420f0700b020a402507035021320f14046c101079900302e010388403030080c02e40100b4014000144502e8943c803540c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 195644847 1250 195643597 195643619
    0x60803130807050102061302010804080409051003060e0307020303040e15090106090e0124030b0616140118170d110f09011101060f05120a140d081308032d01 69
    0x1009501e014807a039072000425610004a040c4140c3c1c020880134070252050340191014440500300321080c00c4280004070301010b040c4280e5108134400c5401402d2145541490b4084a40165404580382c004110000241e10000100c0341101d08103244847d40f56140d000c054200a02011500e5100c0e0400c400020030317540c011481d0303003510400c004d80c038101d90381c40800c9400da110003070401d1452030a0591400f0700c00d001c1ea1010702e90074405410245090f002c541d10b00510320388a4021a0704075076060700112403031400d00c00c58049100c03480c2005202d0710b480d15070796448420110141d40069000419036214192071308400c0840180e6903820743c07120b08502c50446c0580006145a002942c422030502d04207405006038022580804929841c031818042401f003082425504c0710101c1c8105001140066846003510000f4604040030f44542585103100030100d130720142c0f18030f01510441c8260408661368800700c980042c442c0d040c104102c5100002c2c620450b283c001c04a14081066000086030781040b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 195646097 1250 195644847 195644849
    0x503030309060a0b010206010302151308030a110c0402030405031204060e01050a061712040504020f070b0709260613030c0b07020601090f05160e010203040807030f0c0b0a080a0f06080313 82
    0x40003881360325090401207030b99800900c4081e520017015030034582038881d030000900d070450401d0030210b01c268640c061a0320f10343c80310050328005848000d000041600c01e014001c90301604503419803541c1801d0302c407165280a242c07000c82c81c1044c800301003420080a680030110648900009101034a00a00c0d605c1c0203224a1158006400000800318401100415540314811407030640c00d0400f0f0404007800700a4110341011a00004200612400301305016441032040005070350b1030b89110f041032024040d000d1a10405801c2044000e00c90040140c0401c0c10b5622220300290742c2d0381540141000c807005c1850402c0a8486802902401a615408601e49050f61281ca109200d1040710030400b00881c6c0b42140c1c14a00950803402c0050102c2c441c40100d42d00080c144101c03420184c072106880d040100a600c22030b4081d086001c031314100414108400300600701e03120044d051080b148030161110000600c0248410341d1150390161106241d8001b402801070001103075256540c04080504024103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 195647347 1250 195646097 195646111
    0xa0e0604150e1504120e061303031805120708010608070b0d0c12090308040201180303200708030a03020903150c0a0305040c080304090b04050901061203080411060d020a120c05040b0310050303030906 87
    0x286000c6ca054508021080301c0030800c4013041c10041c14a1901c00304d8a003050780d1209285c40d100550700142d40d90320113014140e010358440103002d6180c0b90881d9a42115038691200d0300b03541004000f00001c904110a5a2204202031404070f00c030100d02c03108440405050341121081450038860809140d8407008203442a8400c2e01c405880019100701e00500180320300c40240000c001c85120740c448048050724041001c1ea2404640c9526120810f9a0558018184c000c0003e540410110707264a000c0007104031303959081c0d40c861140c4c00c2c840b90102075485104140b006164498021a040204201d0000010560030040d60b854503244c804a10180550080c480c0c8140d0400c00483c880c2d62041c07040b401207038510405031030148125034056070b6524008200b60b0310f54058550032240f03500c03841d00034080d0150060006136a50012840502000c03440314031014000d103070031003080d2010b4025040318266404040c086460781d54000180c0c0500783c20340c2019405000100520501820004050303011700c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 195648597 1250 195647347 195647357
    0xa1716030c03080c0c0d0e150a11061e071d060a09170309011715100f1d090112051212181203060d03020c03070605030a0e0604150e150412 61
    0x403444c3d6503441c01d0055840d1002076400041d07000c1c0310301e4010900e004858002900715004030300c0288580c040c9030000e05114000c64825400d4505200007801541e9104024070005100e0807014000485141b0004002c6824407107000254103400d00055210243d02034010001640c481c1d581c003009100304141d121b03074003280715011000c4ac6034010210980b0a105c20680d6079010350030418046001c284409801d111020002d00c054490940f0350780d4400241a0135921058001c0c03d1218000300000d00800c0400c0c8001c7c014400700c036003541d0700c400c042c0c11500d81f001d00907801059410010f0030f0080d8100491300c217410010324070a4442c40a1500c030300c540303113200d0554901c550310a0200d80351a001703071f4200e500031410800105e140c50003465604420f4003a204940c0402d400390082483c01109402050200f4804000c01c02d0b0074225004060001036204040c20303280c2096596040c2d20203080c0e41001e400d2b40c503002c40400c451010041190221a054880301903800d050500044180c2d1800c403c00001e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 195649847 1250 195648597 195648601
    0x30e10021f050403090306020f03070f0509030d080a060b0c0c030c09010e04150f1a0906040603020a0302060c120a12110a0c0b060f040f0b0f010c02030a1716030c0308 73
    0x9400898070091103107112040c11880003007503441c0c0004040090044091041c03600c0d011001c100584040d0040b00100310109940f401c2c141005490011382c580e10008010080040c1100e03602c1c0810580200311b024249810141c892911100107440550050140d10b5008545a440b0000020300c90300c000c0c2c0c09500ba12070841c410003c2c442c115000f40a80c6551414917030109000515101081d400307420785800000f02c0324118020322096803821f00d4000c4a2480148140140341b038020700c0981c100c00202c5d070404c101c1e45903501003003c407115440040d01c01ca9000c109040704090034050380541100b810543c50761540c81c4000a00001c01e900300030700c555841c0c4407070592665040307000c80d080d100c000e86074003551450715517682c1410840101000c1c1c01401c031078480c00890300d890051440b54180300c078000c103400320500140800000800d9295041050000291025850104a507180150040b40c1819108044c025981e5507201b04010003405205001e40c0f401419405590405501c0c400d40d6490219 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 195651097 1250 195649847 195649879
    0x210102070c14040203070503010e1e070206060108060603010612050405031204050a052a040b0411031302030606040506061c140f040605071815140c030301051f02030702100e03010603030e 82
    0x280022107412000c15030030401405441c0c12030ac125540308994480510319003030010203940740301c64103559920140c0c1c400c80038400d042d07130400d451a0b4008402c2d05c08904541c94458000e04003a007444c0b002e0402980d4602042c2801420b200b101e001c040c0800c0791000908052070300d565500348111058610380110712080c0e0025400840c403241e0909000c10f00001c1c07a400340100001016030100d6150301aa407020307007003907030201000558070a11400c400b410301c91100b80140750070500e008220a101c0ca1902040261954981d001e0f55040e4140c007072400c18101a0340c02047c0241440e481d08080e074800c030410030071a04141010140300d54802c1c5004d020b40d4903503c4003519104c1c1c106601c44100250341d0b07403d0005a0070186840b02440851400c4122901010014445940300e14021009900000010b1085003050300103180c0c1007100303a08048010302081130080d200c0c05014030081c40f496240117007440c0c981c40307025a071220220050082282645e245006000c1400090f80315028581d40e0781d1940c49 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 195652347 1250 195651097 195651101
    0x4050d11210c0313061e052712030c0d030c0e03060601210204290f090d060e060a09020405010506090d0b0919080304032309210102070c1404 62
    0x66101e41901d24140008201800d800d107402848412000d0f00c01441500810900030b411000101180e0f00d4420351180c01d5007502071541c01030b01d000014482d0030401d06461244941e0014007600491880d03c0c24030f00315000080f840005104d11426a110204020309282c00108002d54640c25a440401414111581c10b61300349003800745565041d003000b0002130745940105441c4c0265407241480e203c0300b010040c0c941040742c01036003108103001c64100094003e101c111900754002040b02246509100c20300c503030391505105050840b40903481c1c0309003c504012040d000f0340481310220703080d1039451070241818401442031031000c1c1d00c220b04200000405007800d4044618042c0080d18504000700d890b144c05101090241c0801103610a034908022122508111050800d01c2550840c0c0c3c0c034103150400a100780e002d541d0341c81d80d420250106e035141c60310002c112405607405651100005c0030b91412040728400c030562680c41540001051404c0010003034504069a0040049410b00203524050100b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 195653597 1250 195652347 195652363
    0x10e04030f0807090906060c060f0e0a15090b0f09010606030c1202070c0807030c0305060105030105220512040803130b0c06061905060a031d0a03021011090904050d11 73
    0x808100804800308441e44521801076109a46003404100c2d140c0d13901d1410b04032143c2e9400ba10001e402041900208080ea0080c024002801a400d22032500d018110380d4546107803c80050020000381941c83c0c8694040d00410262034100e00600aa03140507902c0004d0300d07500726081c15044d440c000000c00c0e190b0091040706000c02e8541d5070380070f05681941c0c030100258081d41056890399400440000c80b101c0c10454180950704c00c80714004558a545010792504a06810481c032a904102c20003070a01c2403051020180420410601d410280a00340641401144d001059031000009400301c1d08040c0080184100141c81e0b031030144e0640e0b140840305d854040c91051070b140b07801078004030b9518905082d030300701d0160103883c98403c11543d441c0069510703440540118003081d00e4000751190890030300c0d4010a001c415034003400b42078a05030b074025254484220301c00c983c1c96586410010000c13042003900d68814000c2c0000815040034100a95a50107025a5900041154a01c2082d007034012403550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 195654847 1250 195653597 195653603
    0x2070e2e1403012d0e03180102060f0405030a050a120f020406020c0306060603040b040804090509010506010306080a2103060b04080c0a050a080a0321020a08010e2d1503060108060f010e04 82
    0x8401d55402e03010215604075020040c03018a17131590031900102c4428002130900101c0d20103803030302c81c0403480300180c10000010001c00020b00310804020100380d01100701d4107407001b14075060fa0b892494403025204807800310341c000d1040d850300c07600801c0a8000e50081c41174400c56021661848800420580c0da40c80440d0800d0300300c0c0040c40414005041054403c0d0042e1150308005d007400d4565080100320340b0202d8403106281c2d100c03824401c40f0f58262140801030b08060001c0d14280c0503584038842c2d08215210700d80c01280007590000b40c1c05100740d20030405031044990311595265207215050b03496180308902441201c2003400020031b0325004500b54101d03806103000d0080d0351f100381c405858041e0400ba40d4041600d10510011420446100500c1440d2450322001c1c1a541883c2c10841d6810f40201442c06045040204040c292403981046046a103030b0203040090340e503070b6050016450700340c0061941511517440003180c2002c022070560701c034555040e512f0b0600c0c0e80e100052900b08030f00761806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 195656097 1250 195654847 195654881
    0x9010504031203020708070c0509010b03010b191803061d07050a0902070602040f081005090118060908090301060b0315010e0a06081503030f041406070302070e2e140301 74
    0x410006402c041c880045a4072410014101a510f80712035074181d11080741200d43c48030410b82400b8a2420703030340f09400340900c4404242550f0600c160010340b8880d40d0703141c4209100860b440e007810b17131046c6000c0c00480d80c5140740028555891402501501180071410450244031107001d00c4001c4c009042d500f110802000007019a1a1518500c020b610007041a180300746c080001054040e8071030360000080c541c00c002400c5115408200004450026010545590400600c1049025020700c6254038603044a4001040710540ca00b800f01442140d01068040d420035200182442801026611446d5445442030a500d005001100c40c102e40c0c84445074080580003007401a5807140700f511350b000400d9181103000181c0c40d80000d1464200101006114030005024014080701c1d85038200c028a003521f91030b0418600c1c2d074029407a01e100c1d01503501034585810000b11464804909074200d5108054004d0348050450f108804040160003400803034454080404090b042c14410311012140d04540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 195657347 1250 195656097 195656099
    0x21b0907080105011808010504080a021603020f10020114070c020102060708040209150d020a090203060103061d06091e0708070e0d030f030b01051c05010314070e04020f0a080d0906020105090309010504 88
    0x15503091618104104005e134a00c100031812200c00d116240c0a540a400c80c141c652a1800009142050003810f0b090220b001c0002080103840d0842c00b0b65403103c00300c6800303a0856801200302d0040c0241143d03d1601c040440510841700e0300302510054540c002c2e804e446d099620b500c000c2e24504000e80c2c0017074000b02c0d00d0380050034022180500629401c00180007a00107503190b0005651a00d040c5c1043d00c0c07240d4004180b025540c2c1501c5410000c000f4880d04800540c0c06241141c840700d0010403031405200040e00062500300210444060400f090100c0f040600300038500410440040321050b0200360b61052450a6141180110745a40d9060352603090311640d1000444c00303880e14520442c14008244840b500022042045000e820303405000003500d0f614508041c418000010310b201d0341d54120810601c01d5181210009038481e406840b6044400241000b04150a400f42d11880050081d02d45420060fa80701d0300e1034080710569402400141c40c3c0d807002903202d202d41014503011a1301044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 195658597 1250 195657347 195657349
    0x10321020601082d2a040902150703020102090a08030904050618070e030c031002090916020d03111201030b06090c161506030506070801031a01140904020f030706021b0907080105 78
    0x103016107074071141309500000c4100b01600c61510303110b0307003450301c13550301110380300841304009141c0d00b140b05070468003400082007a8000c54480700c10b620b11035000180c00034260b414107002b5012101802d1340a0088401d90350744200c0c56859400a40300c9522450500000c01c00519144001c0a00402c00c40c00d6000180c42d0050117594888604203910717013602030250b026185940600c0030040031180f4402c0035076100000b50800a64180c0248a42900c03212a001e480110758005003486a5440381d00b400100e0710740c003460403075184c004c8581000c1c08480120000c02000400c1c10880c0c058201a50324618070785600710149214003402004a465007960a43d00c808184206226000621500c0001401c55213036141c050500104858107408122210010401c1051004120032080c480e8055800e0301d504040707003140c2d4019070840481c03040c605030b000305080d55501ca8003661001030007012508000da031040d0203911010036103115001d054240403d190681808004244a1205540d495400ba82088 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 195659847 1250 195658597 195658633
    0x1090b0604090c08061006230301060f03020c011d0c0a0308030c070807060204060c0302060c0a12560604051c050604030801181a0103020a050c0601032102060108 71
    0xa00703840842c60b03d4400218a41d082c8440c0d0301805c8089280ca00b031905001015101811301c1c0045150003100c00072342c5203a1100042071b00e045d02c1141c41e00c5100c060a8032000c4019010f00114442207510f0b003000740c91880041d0360b030b40b08a580c501e01641d034101c01d10401c1000c050b1302c42c40060040c020800015407039869110080040d42d00c291011410000d541e210b0a040360081d42062012a03100003603a0107045e010400315901c107500c0781e072013803400f80c070354000030b1122548410000d5800d445007500c1011822000700c4005641c2840d000390105081d802500410134500c2e00d01c000c07032204801005509141100c1030809140c1c01804491900d4507003024850120442c2d01004001001c41e44100c00054050000c42d018600a949010265041444030040707520000c201c2e602041c60460300c082d07a104aa070005500c2103090034016201c0454000649080c41503650710040ca01034440007001304880848100c82c901d168080c1004030160010080c2da840500b03000320031464bc002050500d44104034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 195661097 1250 195659847 195659861
    0x80d021215130f20031b033601090303050f10050a14010c021e090708070c0b0601230d1109011b081218010f180b0c13080703060e01090b0604 62
    0x11002030124104c14154080c049103100c92080720740700005210300804c4000d40d58051441d41c01150b8076600f4105400c507011000c0103d80034140d0401690311001c03509810724415205d05400080c000104c80c0d00c4e008000341270849582c4040c0d00d0010114100004c0c0e003200740c0c1901c4025000481c00c509212301e0110710104e00c41c8290410090080420060300e94110003440800b007903043c1c1c402c441c0c041e801c0040d02c000041c50001006074200401100319800030113504241d0b001251882039840f0368004941c803000c20b1845000e0300c00655880440e140c81e05005002c0b0107603461007001180721244003a003492041071000740c00500c800d45400c072601c10300f081102d88107200b140218500b40341c4201d045243c1e401143c0112071566010000c0206032800c5c011b0808a12840904101070300d20240c440041c06070340003000c0c00d5441c01d000007419103144001120402200c11804030b10440d51510000d9450300e09000885d402070034110517002c041d01c1401648105684041007015640d10700302400300034003070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 195662347 1250 195661097 195661121
    0x70b09030d060807080c0108040b130302120a09030b0105030601031211010905161418070f0e030106030803090f030a0206010501050d1b05180604050609011b080d02121513 75
    0x41004031030741c40710507441420020300810001e0049030f407070070780014207080d090441141400000010880006e680b0303200c03264003091007020240c0c01d4416041c12407a00903130b5400c806003250006000e5000c6174100ba204070840b88142407480d0261780b41c1c0241511850300f031000405801c0d400c15200d1105008400c0764900719108400010600000d848031031034400e01000b85440304041d0f482c20700011070182c501c01081e030000d81c1d182031a404100071400a12000901540170407224004c05038515120300c000004142005000384055030b2241000310ba240d0041d14a0300c41d61007000000c1c08981300100030b980303400b201138014008680c84d09005403000da02c80e090344004c0a40d50245000c081101d000d5055211565603655600d84c4006611104000303070581c841d52044a0a010821041e6644004c1b660407030001c0c41c2000c1000044007040310403440845000306008001f09034404098019030240844c008903046503045925041569041003140010854200b456102c0c2483c1c10441c641200019007d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 195663597 1250 195662347 195662353
    0x60309112101060b0a09060e0a030602091908010e0f070e011a0f0a02010c030c0903020f120c12010b01030501151205090304050a1202030c041104031104200d1b0203070b09 75
    0x4000d0500b070842d0800d80180d2680c400c0402c0c0329100b141d008aa40000e007242d420703c80821340c581c100141d172403141444000d02c2c1680000340d10720203803a00031503032180c0c90140d07030414180c40c0c4034400d0902924180c50030480354815440701c0b8080c05400504bc43c204d42903c504d4005590070111540d40218041401d642c1010f000c12803850329803e044010540d4201039800080c2c0c00c09000001010b0b240d500a15508010b8846410b002507a110b40d9a1150800c04440d40c0d801c400c25480d9503404c4c5040002d5180c0d100045001c01344007002c06410181c204a0243e8040000f603880d4000c862110707023800e000c3c00c002884000700d9801c0e004568040c1d904260020700b2039050541d624000b8070903200c141c2104100e08400b083c3c51085003820045101d1030b2000715014440101190203218950040c0d02c4013404d03540810050900380d84555105003040e410304901402c00b00c114010340d44d05c2d540311070107100c0c83d10715200b51044000d524940c2c080d4010b43c230750b010310314144454644400000300a054094580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 195664847 1250 195663597 195663649
    0x5030c040b061b01020f04240206190203040c0b0f180904080a030203040f122001020a02191704030b09060a0b0906060901090503030a02070f06030510170312010806060a06030911 78
    0xc3c0e104050401020b22300d00581c4421038a1031803d1854038004100819548040c090020103003814651114183c29280010703101d03500c038140001c1c102500d1340400000c010001d0207481441d41c100003440104150910684a440044207100c0c0e550303001c0301e0151850200340a0121858822340095030003d001d5840d880481c2c045444895031036080501c0700e4080303011209495410311400c0c18068054445000840c1804030840001e5164517800303a0000500b601503a5207400c1061030103400700001481d0b001c0d0703503e40b074680c6040c2036000390541d0036030810700c211000520031111500404001c103074041c04960340354070707100240603017504510b5981d0705100c8000d4000c00c16071070030006040100803d90007805900d00d0100b190008c035080b43c11000030141490300f04150610610300d0003046520041d03162020404403260303d400d6028003030007802443d5020000280102e000114180240011103084003130350350351700c4258115038000b00000d1245482d00d240003038528160416107038610885070b60321420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 195666097 1250 195664847 195664867
    0x71101081b18061207050409180f0831050f0f0307030204021e030a020307030b0a06210209030d0309020f011b08030424020c010c21050a110a05030105030c040b061b0102 74
    0x805000c80e02c2c1000180046400c2202092501480702086149027482e01d0f11442602c921502e45013808006e09042030004e140c603450304000344281032034140415424201404100103d594850511a0621500820a044440e41340c50303c0740041c5107030006d000f01401499582400f000c1e4014070501409010201c4c101d001d004801d1000b94440d64096000580e2854001c5c4058212114082054050b030110641400301c141c020b0081e02c0001c644c2d0410500740c014164000b0007034801c0100c080c1c0c25020300c5d2107110ae03654141e000804600e10841f010340b44003100500445409104c1500f5101d454000c014010118003072500441c1c00c40d0013030809001480300030450245d003844245c98880815400900c481c1d92407406c1c400c002c1301503414a085161046052401c00364402150012000070382d030b440128810310780c503030305c003140c602082074149448201c3d504010703000742c1092003060300a000d041c02228040c40c1a10901152582c020304403800c2c80203019a12480308070507184031146640c00c00c420049 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 195667347 1250 195666097 195666127
    0x314060909010e03210f01030b040f050703170a1d030d14121314010612031b1502040e060904050d05070c0302061b0f0c0310110f071101081b1806 64
    0x2e0410403407019030103400384401c0f0400c45c00c002820804001010070040c00000c104003181c0b038005810102d00c00f5020420b0600604281c42d41e84000c041410785c0140000c1c101500000e40b101ea002526100341e12106884d441d0020200c1c081259031503003102002d40019805016607900e1607044494150521140e43d450918011040e100e070002e4200c0d00442d0b600300025140c103c41c85880100c000d0110518012541a8403401d946c0024140507d4607003040d0070101e00f000040941e0781040b01059888511500300c4003d40c450301516400f5100b1000050311420410340701070040da485130091051248807001103a1580003180101c0d06038080c1c18000000d40d50300c101400c00b6030400c40140b920408a0304e60300b41b4281c00b1041203100d40d082402c0524140d03a001c201c9120410030300c4408240c80915044c030b0441440382d26030035071013603602040013414440c50010000300c203002a00c840f08251039111a085c0c504480102040586004110381c110703010b165031032440e0413480648400d042c0340c006680c001d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 195668597 1250 195667347 195667357
    0x10f0b0d2004032901030b0c0c06010303081f05030a020d03090b07030905130903080c1309020309011b0c0c03030509040b03010f090b01051801050d03170f060307060314060909010e03 80
    0x654194040750a00c14402d07454241e10b4844d10503111200e0512140c581901011014071000e005086080005460f0b20441d03401c86100d4103610741610700968503490040c0540c00142e410040000551072810100300308070b0302a0341501c800034018000c00f54130344c0c03c0240740c030752400d8200d00700001400005640000d8101421141c0d100e911600486400e0034248030000c0d10f4040c0b01040d00b818900c036400031039001214a9002025098066034603055840c2403095005143e0110488034400010410012819448800c82c14550181910513400c0d0440494480c10001e101070a003404c0642d003000024080c50084c2450319020344046200c0c0c02003070019007110400f0b2205403500381c4550030030f010030080b2507005014110442d80c04416040840d1031a0300c0a2050107098080c040d41036811040c1401540c062320781f81e040c516510308c0c2c3d25003170fa0b005001d610306445940c003a1142c54400f01b0303124001d001c2c041002219640501903542c0300703800c001240b40c024103149019580c40c4824580c203001800101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 195669847 1250 195668597 195668651
    0xb030106030b0f061008070e1201020405030d09091503021806030c1f090f120b1b0c0d0e040903080a0507090305010e1608030c0304050d080c011b17010f0b0d 69
    0x2441e0f84c80c000c0d0074881d4943c410707540305080103034203020001c2140e0000f101041851040d2061a01e45030030044281c02446140c202950500c02c1c944d40700000c0b58005c04010a13560580000d0042a40c40c00c0c0200c0d4400590000960161306c60144036000c175010400540d10210003000c99880740600d4012444000306591940180c01d05603246080d06904041460020319204680204461a104c02d40050521301c0344004c200400391b030082400c00e0000000c15010520143c20641c0c1c1d0308040c0101030761031840c07039203041c04070f8080d41c10040e581c50944a4012140d40645402001e56030f9801084c000303141c014200300501c03518800c0480403650910400d4881d070b88a00007400440c40c155a084040305256100c3c0003e5030080020410440f00881920229802aa04600d04070710626084070a070150321240d1000d503283c40349000349003003807490401504400e911900c1c060441341c8901c120442d824005c04c100344d40ca001c001c001003201c02d0000c0c084007080361800911050000709000101c0601c2d00c1c0c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 195671097 1250 195669847 195669871
    0xc030c0b07050f06060a0501030f0e01050709031202212b06050a120c0303050901050f19030c030b10110c0d05010c1b05070605090d0f06140a0209130b030106030b 71
    0x6030401c00100403c0601024103001090340b4549500010a1a4024040ca82c101a101c0c008500807107090703049881014100785c002d12482c940504014088003252200341c40026440952a00050001c41c4800300c2041d42c0c800d00c4410340b817611203004a40e1010540b94a034050b1020548001c010a10004030050080030000c640140340608000300e2030b1098000c140d0342d841ca42d01a200013002688084100d03a03040c280a512118a4401038071640548403a4040c14031000540f1030008811074030401c0c3d071900c0d45d00c0c00c10004040b02c2c412000c40da5018a829042180d000c603a01c90503000b09002810105d43e2822076007803d00d00008500c42c6420120100d484d6916200e2065406800c100320101149448007140f00340f240075142c582e51084584104803e0100014080100e5181d11505805c15034128030f58039503a560310701c0d04c20005c142070132181d01714100003008603141414038021102003400042241410b0801c0114200084c200a0295641590b0f81c0c400000000d0031207860b144515185904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 195672347 1250 195671097 195671107
    0x904150302150a0818120703020102040602060a020c0a15060b070c030c060e010c030f05091806041b02030a03051009140703110703081f030501050123090108070b03040c030c0b 77
    0x602012442a40c66a8003562003407011540c5103512810a690080344041c4055025440c10705d014200301c2214505645104c00203185c01c14180c05400600c1107407015402c60300f1990391050182c04a004052401646421110245005c1414102d0464610500a49c00a0000d40d90b00c0010200d600141080342c0d8559042c030200140011100d2050007840141022006080850300090002c0c41109008052001c1c260494030080d00c00c400b602c40024014103a02c00d030185030802e01800c0141110a148114109100c401e1481850451800c0300000c0360000c509001c15132900380c0c040c100003000b1140c64801e00d080050148120301408604170400400f100843c2001d0000806131a41c00f03c0410075404208210303000a43c1c400740d0a5032207001c1d0724403030091710b00c0c2e0229404500382d2035001500c590f003814004180300c00c4803501c04d000703100c64900c0c0410804840c4107200c580d40091180f1080e03900103960030402032001000555001e880b0780380494045442c1c0e600c15020814a82007881c039008089a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 195673597 1250 195672347 195672349
    0x40c12050108121617280f050a030c020c040906090516050a05010f0315080d020c1210050402061b010b090c120a0b0616080904140c1801050904150302 66
    0x45030078050003444010b84155012410400d1544c0b180d40300081c02c0c00000380100d0144104040c81102c1402150b140c43c2c1c0c2e030100c03000341c440101d40c035280d65160032981e0700c4000c8100d80110082c810103207850f2192810074041c01020360080071480800b2056015a4802c1e1546613124401c0c200c680707124520018519000d414018031384003194402c505c82d44421203041c0310b655070b00c401260866109190801401d071840400f24007a05001103022042c9441e00c2010800c200f011840548545180c0c0c21940c202089a04000925010610540301c541081d003441c00000000d07000690310500103040e407464880700740c224801c034502840c0c038030409035903840c1c86d01444d20f400c07500950095403101541d418001340a00e00495604081e1800300c1d01c60340c0740541c00041d04c4603001e45000503242000c0154400c818104041aa4443c402151240c1c0c6018029018003c80e0302400340101c50007010b950a00e08035104041c05480080303c1c03141070200a0001145542d00d41c002c2115401c5201c0703a0240e044d10b148 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 195674847 1250 195673597 195673601
    0x20d0b0708060a060e0904030c0b0423030708040909050321010602010b04090809040906060506041418070206010b0a030f0513060c081303030513140a1b030b0106050703030605040c12 80
    0x54182d81c0f0840c0700840411100d039004e118048010300488200300c240c0c480b0700d425200c006114200500d500d100d40104421b001c941030078059860240103e0030b5682c1c1c2c001003c19164840c00e40010306035001480140400b0601360702c00c804052040d82220701d001d15041000140c03449010251100d00c45040040c40b469a081c091005d40c1801914203220413403036035440714254041c0c80031043c0100d503a0b607281c00900a01c1c0e00030200411004c0e08656481c3d0301c8072032a0410080301120345008404949141c0b965109100d0710a10441e0350b0f41c090a096400e003500817000b980001e1603c0d08140e102d44030504800081d1040074000ca0700c58410342500102891304034241c4280250b00340600c50f100c8104080704038000d01426050707925140018059443e07071002d482c510300c9007030060240750020401d0401d1042c0003a2840000d4003845208500403008108914807100e02c3c000141201d031440c00411020740200c0c06050094403904003c5040c60700d40c1e0100303048034408503540001461034000800484014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 195676097 1250 195674847 195674851
    0x30a0516060212030109020901121e11091011010f062301140d020c010e0a0305130e070e01080c0918062409011103040b030a0204090e0a02010e010f0c020d0b0708 71
    0xc1c00074020000d99400f401119020500c101c55030f664002070000c40580c41150044080c1d90915002c001c90700b0303044001900420300d0050540701c907140034401c1340383c6d41031081510041200200511725100c00070300116410816151400c03001d6490380d9000c0508529805424054070304580000c81401c055800e00d030700c0c000107126480c1402541d9047c41a0762525008032120b804862802507910161906028010711120bc000345850040040390347c01c26500000910030030b140c0441d130341700c82e64868401c1800d40c04c003512000040f03007044d01c3c640815401000643e0303018040c00c01e100c0c180300b50000070668403054001c40e880028007a2040240600c0c141032038002080c54050119882204907032400d10300c7c865407003028103204894610100b03481c001c01c22200581050705040e51203041442c420b40c040d4003e03004840c165410b140d081440200d001903007029540c0c05a44200a1a444200640755140b8034003c100030410444442009620fa0100c03800c009403103501c0380d960510304150024110100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 195677347 1250 195676097 195676109
    0x2409060e03100c02151906050105041d040309080a120f110a0b040c08070b0c0c0108072f071206060609030203070e0c090d030e122811030a0516 63
    0x40d0200c03000261000591190411120003000070b081181500c140d20301460550b40b0300c0d451041c541040444420411240304904040f081440140e8840c00117640c10f010350701030b5030b0300e06006420580010b44c0310300f44203401c2402410240285a00d0762501800d00c00520020344c1c80150303440c2d0741d0680d540c0c044041105201d81e0301e8405440c484220242d51910b181040c0600003110340b10106061106480c40790006102c45000c81b420747d039903407103440c081d0340061000046070701542c1d070031080f19401440301d02d21070541131b9280c16190a0031140000d41c900e400c0c4454449940c2401e140510398010080d040180c151000048a01c0481d8540b90080d00c2d5103801400421034551820401610000307116002d0322840c441d0b00e502a030f20303c0c0500e1510700614101682c01580b1a64000526400c21095014680142c42d01452142043c0f000d0365503050526144c007541c028150344c52203411a104c00d903005c0600c50126155010342d2180041e207418118201034030307160841c02800c0b420607030201c1d0090051003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 195678597 1250 195677347 195677357
    0x100905010503033009061006090608060904030905060301260313050904060207050a0809030114070518040f02030a140703060305030307030f0e0706030c091a0403110307240906 77
    0x1c100000b0a459014202c140c02c08030405103842c0076a0015120b000c0040306514203400480d02c0c002211980c0c4401c15100d00c24216545074020070720034441d2141a060340c0c465100c0310842d440d04c42c20b02a02000080050301004012100441c07280d84a500441c02040c042c1d14611800181d102d90754960208086080400d6000f04002c0d40c030211007843c040100c4000b02d42c001000d41c0c442c01e04078041d10612200030102d01511110008111480f4090041a2000d4000300100e016400548100e110107984020100c1c0d03042c0214a10100c41d070079040c000043c040e10100e2120042e07030051050381c100b5a5501500b50f00c5400310f0030890800d03041d50350310004928091204500d90384555440e0712018140104140e2500302d4080b0fa5402038000c21141c85201c4d0890b00c401c0d5440c40010f000b0704c480b2951200050803c08006514010010860b1003080b0001e01c00d441c00d89940d880c030b10344548000341399405000700b0b070001888025600c5405410300c207540d2528a01c8580360001014a07881e60481000c0c44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 195679847 1250 195678597 195678599
    0xd200304030b010302010302090105040902041508090d1709153103050a03230a0506100908100f0e07080309011b030c0b040302011b051306080601080c0a200610090501 73
    0x82d00e030308211411a9020700700142e070b0f030074184012280d0b4410368220002980c00041c0c0012604e40241440100c400342d59203080b42030b203440418544510700c0e41152070008426074148810480c0540805410065180480765a00d07104102c501520300d0032500001c2490404d0301800c6035410546040130310079801152482c00c0103080d43d02401601454510f42c0815694181d6a1019074040d1005003984440b888280030702e14050741c005028200840302e040c05800d00c0002c03c4000ca0203810381301c0030b8510b100c1c00390103121078444000e00140300c0154038032000c0ba1a0320099980081c00d2182c2006003000c88061950380c80f6080000d040c0c4064001c0482c10710791101003d04c0881c0e840001c0401280d88060070444c44e8840c0e007000c902404030003608210741c0300166101d021041e000401024602d0a5101502445a45003025148410201d4542d40855015400161040d0b04000106500d00c410300f1701c0c080806038800359080c15007211107030708040e030300a40c00c0c0007400490004100050824172028050341d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 195681097 1250 195679847 195679853
    0x90c0b0304120804030207350111070f0236090606011e090819020a0801050402010c080a1e050c01050a09051c030f0f27120807110d20030403 62
    0x401a5414071008103c2c0b00e00104041502c24403028004017041c40c2107803c105060501c21040c444009080c000c0d10460307807200d0408020600402001c244084105424603034079441e101004012854102d90152089204c1815008103140c81c1004000c0b90741d203001007154000d658604240c0c0500000f8007a0300800801900342c0c0e001240001d150f000c02d809650001c44c1d003200352134601040c0c02001031809058201940311070381140b010036441c000c45040704155030f0b82e06010708131841a54041d0010354100100da010441503002003c0b2000e5514000b82c0c4080c0d86039a00f401520342205c0c400014100207003e0300305c0e80c000d00916401a5064804102c66110b075903445503101c03100030761141e100741002195091103000b50310000c421104017105014807164400c051005148900030311103044840c21a0b56075804900011243c00b6a200144540060284405440340000100340d00200f18010100c545118000d201442000340b541d240c0c0c00303011009150803038000406002d644081d0740144020404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 195682347 1250 195681097 195681113
    0x2010509101b0c02030a1406061c1709031207060f05061002070905190213090c050a081f050d03020a0605070c0201170604020403081303020103060f080c0f041d01090c0b0304 76
    0x10b0303810a003000712002e503041c400b090030540540c8015000c410405041404144003007aa0307407182000b04c0741034500c41e00702d602c1c2c180041002c0714003608420701e8041d8001c01e82d01c51002000820300041c100c800e0301c0c40c01c080c403a41e1307907000e85000c0361040d4035096004080101402400c1c1c0096048580c2442d2182c085402541c0300214410425642d13100d00105080d405101c19028461180c88000c0d55510110804100c140c41548214042c013840c1180d1180240c1c03094060f02d54a018954a43c20180c4940712182c8c02041000880455a211140009500d94400c40412001440f0340c0260030182e5032414034804498005000c10144050608410b00507031380411543e600b020310b40c0e580080d07911803401140080c0075541005088560009030805c7c00f1003800c401404030391007640e00740581074980400c60340d400e540340304145d040e900c41c040305c0c4468070b8806607007415600058030010f4400118030711040800c811016400459543d11448800d00260070710311009054505016469420155641d0344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 195683453 1106 195682347 195682391
    0x1107060e090a02040b1c1b180e0c070b1305070b07050f03071109060d020a0906050405011d0f070c0b0c09100c02060a1209060204060201050910 63
    0x249489503000b11000d6540d040d82640c103000300c2e10035017203140740e83c2044810102d8841e43c80c401c284403003061038000d20074030342d823026041c4040b0a2642440c4c030044d0401c4508000308010400012106000c40e0b40c226030150000701d9607541c100e242e080e880d2401a005045010300c500004540e0701c54006068600e00038402d032820031107072504181e542c1c415207900800d141c1c03104070f22400625102c0d640302c0e40103102400c2c1002c00c3ca80f940c009680b10320b01da004046a2a554201841079003040d11030396000d01250300900c12407080c40c070700e000d9a4080c0204085503441c0b11304009030804c0c6c49540e54550145d48483c64403181e00345803c0410058000301e074003d002c0c8401036885400d040c4200400f900094015040601c1c01c4c101300310490340000081c5920340d84070b807035a00320310001d01203100410040c05140e000003402e00745040354908041100c103524540e10304201036501c0c801c009002000b = true := by decide +kernel

theorem cover : BRFrame.Cov 195503597 195683453 := by
  have h0 := BRFrame.cov_init 195503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 195503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 195503597 ≤ n) (h2 : n < 195683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
